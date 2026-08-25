/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Interp
import QLambda.TTPhysicalEmbedding

/-!
# Minimal physical primitives for the two-dimensional TT model

This module gives a small, concrete primitive signature for a qubit register.
Every primitive is represented by an existing finite physical instrument and
then embedded into `TTContinuationPower 2`.  Choice remains an explicit
assumption needed only when the general term interpreter is used; no
`HasComputationChoice` instance is asserted here.
-/

namespace QLambda

open Scott1972.ContinuousLattice

universe u

namespace TTPhysicalPrimitives

/-- A minimal qubit primitive signature.  Each constructor records the
classical value or values returned by its physical operation. -/
inductive QubitPrimitive (D : Type u) where
  | ret (value : D)
  | pauliX (value : D)
  | measureZ (zeroValue oneValue : D)

/-- The finite physical computation represented by a qubit primitive. -/
def finiteInstrument {D : Type u} :
    QubitPrimitive D → FiniteInstrumentComp 2 D
  | .ret d => FiniteInstrumentComp.unit (n := 2) d
  | .pauliX d =>
      FiniteInstrumentComp.ofOperation Qubit.pauliXOp d
  | .measureZ d₀ d₁ =>
      Qubit.measureZComp.map fun b => if b then d₁ else d₀

@[simp]
theorem finiteInstrument_ret {D : Type u} (d : D) :
    finiteInstrument (.ret d) =
      FiniteInstrumentComp.unit (n := 2) d :=
  rfl

@[simp]
theorem finiteInstrument_pauliX {D : Type u} (d : D) :
    finiteInstrument (.pauliX d) =
      FiniteInstrumentComp.ofOperation Qubit.pauliXOp d :=
  rfl

@[simp]
theorem finiteInstrument_measureZ {D : Type u} (d₀ d₁ : D) :
    finiteInstrument (.measureZ d₀ d₁) =
      Qubit.measureZComp.map (fun b => if b then d₁ else d₀) :=
  rfl

/-- Physical denotation of a primitive in the two-dimensional TT
continuation model. -/
noncomputable def denote {D : Type u} [CompleteLattice D]
    (p : QubitPrimitive D) :
    TTContinuation.TTContinuationPower 2 D :=
  TTPhysicalEmbedding.embed (finiteInstrument p)

/-- Deterministic return is exactly continuation return, not merely related
to it by refinement. -/
@[simp]
theorem denote_ret {D : Type u} [CompleteLattice D] (d : D) :
    denote (.ret d) = TTContinuation.unit (n := 2) d := by
  exact TTPhysicalEmbedding.embed_unit d

@[simp]
theorem denote_pauliX {D : Type u} [CompleteLattice D] (d : D) :
    denote (.pauliX d) =
      TTPhysicalEmbedding.embed
        (FiniteInstrumentComp.ofOperation Qubit.pauliXOp d) :=
  rfl

@[simp]
theorem denote_measureZ {D : Type u} [CompleteLattice D] (d₀ d₁ : D) :
    denote (.measureZ d₀ d₁) =
      TTPhysicalEmbedding.embed
        (Qubit.measureZComp.map fun b => if b then d₁ else d₀) :=
  rfl

section Interpreter

variable (D₀ : QDomain.{0})
variable (j₀ : IsContinuousLatticeProjection D₀.carrier
  (QuantumFunctor
    (QModel (TTContinuation.TTContinuationPower 2))
    D₀.carrier))

/-- The primitive signature at the recursive value domain of the
two-dimensional TT continuation model. -/
abbrev SemanticQubitPrimitive :=
  QubitPrimitive
    (SemanticValue
      (TTContinuation.TTContinuationPower 2) D₀ j₀)

/-- The concrete primitive interpretation consumed by `interp`. -/
noncomputable def semanticPrimitive :
    SemanticQubitPrimitive D₀ j₀ →
      SemanticComp
        (TTContinuation.TTContinuationPower 2) D₀ j₀ :=
  denote

variable
  [HasComputationChoice
    (SemanticComp
      (TTContinuation.TTContinuationPower 2) D₀ j₀)]

/-- Primitive terms are environment independent. -/
@[simp]
theorem interp_primitive (p : SemanticQubitPrimitive D₀ j₀)
    (ρ : Env
      (SemanticValue
        (TTContinuation.TTContinuationPower 2) D₀ j₀)) :
    interp (Q := TTContinuation.TTContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (semanticPrimitive D₀ j₀) (.prim p) ρ =
      semanticPrimitive D₀ j₀ p :=
  rfl

/-- In particular, a physical deterministic return is interpreted by the
TT continuation unit exactly. -/
@[simp]
theorem interp_ret
    (d : SemanticValue
      (TTContinuation.TTContinuationPower 2) D₀ j₀)
    (ρ : Env
      (SemanticValue
        (TTContinuation.TTContinuationPower 2) D₀ j₀)) :
    interp (Q := TTContinuation.TTContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (semanticPrimitive D₀ j₀)
        (.prim (.ret d)) ρ =
      TTContinuation.unit (n := 2) d := by
  rw [interp_primitive]
  exact denote_ret d

@[simp]
theorem interp_pauliX
    (d : SemanticValue
      (TTContinuation.TTContinuationPower 2) D₀ j₀)
    (ρ : Env
      (SemanticValue
        (TTContinuation.TTContinuationPower 2) D₀ j₀)) :
    interp (Q := TTContinuation.TTContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (semanticPrimitive D₀ j₀)
        (.prim (.pauliX d)) ρ =
      TTPhysicalEmbedding.embed
        (FiniteInstrumentComp.ofOperation Qubit.pauliXOp d) := by
  rfl

@[simp]
theorem interp_measureZ
    (d₀ d₁ :
      SemanticValue
        (TTContinuation.TTContinuationPower 2) D₀ j₀)
    (ρ : Env
      (SemanticValue
        (TTContinuation.TTContinuationPower 2) D₀ j₀)) :
    interp (Q := TTContinuation.TTContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (semanticPrimitive D₀ j₀)
        (.prim (.measureZ d₀ d₁)) ρ =
      TTPhysicalEmbedding.embed
        (Qubit.measureZComp.map fun b => if b then d₁ else d₀) := by
  rfl

theorem interp_primitive_environment_independent
    (p : SemanticQubitPrimitive D₀ j₀)
    (ρ σ : Env
      (SemanticValue
        (TTContinuation.TTContinuationPower 2) D₀ j₀)) :
    interp (Q := TTContinuation.TTContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (semanticPrimitive D₀ j₀) (.prim p) ρ =
      interp (Q := TTContinuation.TTContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (semanticPrimitive D₀ j₀) (.prim p) σ := by
  rw [interp_primitive, interp_primitive]

end Interpreter

end TTPhysicalPrimitives

end QLambda
