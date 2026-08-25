/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.TTPhysicalPrimitives

/-!
# A hardware-faithful qubit abstract machine

This module gives a call-by-value CEK machine whose executable configurations
contain an actual normalized qubit density matrix.  Quantum transitions use
the existing Kraus matrices directly.  Internal, probabilistic, and
environment-selected transitions are deliberately separate.

Kraus histories are proof/debugging metadata (`GhostHistory`), not part of an
executable `Config`.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QLambda
namespace HardwareOperational

open TTPhysicalPrimitives

/-- A normalized finite-dimensional density matrix. -/
structure NormalizedDensity (n : ℕ) where
  mat : Matrix (Fin n) (Fin n) ℂ
  posSemidef : mat.PosSemidef
  trace_eq_one : Matrix.trace mat = 1

namespace NormalizedDensity

variable {n m : ℕ}

@[ext]
theorem ext {ρ σ : NormalizedDensity n} (h : ρ.mat = σ.mat) : ρ = σ := by
  cases ρ
  cases σ
  congr

/-- The Born weight of a Kraus branch on a normalized state. -/
def bornWeight (K : KrausFamily n m) (ρ : NormalizedDensity n) : ℝ :=
  (Matrix.trace (KrausFamily.applyMat K ρ.mat)).re

theorem bornWeight_nonneg (K : KrausFamily n m) (ρ : NormalizedDensity n) :
    0 ≤ bornWeight K ρ := by
  have hpos :=
    KrausFamily.applyMat_posSemidef K ρ.posSemidef
  simpa [bornWeight, Matrix.trace] using
    (Finset.sum_nonneg fun (i : Fin m) (_ : i ∈ Finset.univ) =>
      (Complex.nonneg_iff.mp hpos.diag_nonneg).1)

/-- Normalize a nonzero Kraus branch.  The strict positivity hypothesis is
exactly the condition under which the hardware branch can occur. -/
noncomputable def normalizeBranch (K : KrausFamily n m)
    (ρ : NormalizedDensity n) (h : 0 < bornWeight K ρ) :
    NormalizedDensity m where
  mat := (bornWeight K ρ)⁻¹ • KrausFamily.applyMat K ρ.mat
  posSemidef :=
    (KrausFamily.applyMat_posSemidef K ρ.posSemidef).smul
      (inv_nonneg.mpr (le_of_lt h))
  trace_eq_one := by
    rw [Matrix.trace_smul]
    have hpos :=
      KrausFamily.applyMat_posSemidef K ρ.posSemidef
    have him :
        (Matrix.trace (KrausFamily.applyMat K ρ.mat)).im = 0 := by
      simpa [Matrix.trace] using
        (Finset.sum_eq_zero fun (i : Fin m) (_ : i ∈ Finset.univ) =>
          (Complex.nonneg_iff.mp hpos.diag_nonneg).2.symm)
    have htrace :
        Matrix.trace (KrausFamily.applyMat K ρ.mat) =
          (bornWeight K ρ : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using him
    rw [htrace]
    simp [ne_of_gt h]

@[simp]
theorem normalizeBranch_mat (K : KrausFamily n m)
    (ρ : NormalizedDensity n) (h : 0 < bornWeight K ρ) :
    (normalizeBranch K ρ h).mat =
      (bornWeight K ρ)⁻¹ • KrausFamily.applyMat K ρ.mat :=
  rfl

/-- Pauli-X preserves normalization, so it is an internal deterministic
hardware transition rather than a weighted branch. -/
def pauliX (ρ : NormalizedDensity 2) : NormalizedDensity 2 where
  mat := KrausFamily.applyMat Qubit.pauliXOp.kraus ρ.mat
  posSemidef :=
    KrausFamily.applyMat_posSemidef Qubit.pauliXOp.kraus ρ.posSemidef
  trace_eq_one := by
    exact (KrausFamily.trace_applyMat_isometry Qubit.pauliX
      Qubit.pauliX_mul_self ρ.mat).trans ρ.trace_eq_one

end NormalizedDensity

/-- Runtime values retain lexical closures.  Primitive results use the generic
classical payload `C`. -/
inductive RuntimeValue (C : Type) where
  | payload (value : C)
  | closure (arg : Name) (body : Term (QubitPrimitive C))
      (env : List (Name × RuntimeValue C))
  | recClosure (self arg : Name) (body : Term (QubitPrimitive C))
      (env : List (Name × RuntimeValue C))

abbrev RuntimeEnv (C : Type) := List (Name × RuntimeValue C)

namespace RuntimeEnv

/-- Most-recent-binding lookup for lexical environments. -/
def lookup {C : Type} (x : Name) : RuntimeEnv C → Option (RuntimeValue C)
  | [] => none
  | (y, v) :: ρ => if x = y then some v else lookup x ρ

/-- Extend a lexical environment with one binding. -/
def bind {C : Type} (x : Name) (v : RuntimeValue C)
    (ρ : RuntimeEnv C) : RuntimeEnv C :=
  (x, v) :: ρ

end RuntimeEnv

/-- Call-by-value CEK frames. -/
inductive Frame (C : Type) where
  | argument (arg : Term (QubitPrimitive C)) (env : RuntimeEnv C)
  | function (fn : RuntimeValue C)

abbrev EvalStack (C : Type) := List (Frame C)

/-- The current CEK control component. -/
inductive Control (C : Type) where
  | term (code : Term (QubitPrimitive C))
  | value (result : RuntimeValue C)

/-- Executable machine configuration.  It contains syntax, ordinary runtime
data, and one concrete normalized qubit state; no denotational-domain object
or continuation powerdomain is present. -/
structure Config (C : Type) where
  control : Control C
  env : RuntimeEnv C
  stack : EvalStack C
  quantum : NormalizedDensity 2

/-- Initial hardware configuration for a closed program.  The quantum
register is concrete; lexical environment and continuation stack are empty. -/
def initialConfig {C : Type} (code : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2) : Config C where
  control := .term code
  env := []
  stack := []
  quantum := quantum

/-- Optional proof/debugging metadata.  Keeping this wrapper separate ensures
that Kraus presentations are not runtime state. -/
structure GhostHistory (C : Type) where
  config : Config C
  kraus : List (KrausFamily 2 2)

/-- The actual branch family used by computational-basis measurement. -/
def measureBranch (b : Bool) : KrausFamily 2 2 :=
  Qubit.measureZComp.branch b

/-- Born probability for one computational-basis outcome. -/
def measureProbability {C : Type} (s : Config C) (b : Bool) : ℝ :=
  NormalizedDensity.bornWeight (measureBranch b) s.quantum

theorem measureProbability_nonneg {C : Type} (s : Config C) (b : Bool) :
    0 ≤ measureProbability s b :=
  NormalizedDensity.bornWeight_nonneg _ _

/-- The two Z-measurement Born probabilities exhaust unit mass on a
normalized input state. -/
theorem measureProbability_false_add_true {C : Type} (s : Config C) :
    measureProbability s false + measureProbability s true = 1 := by
  change
    (Matrix.trace (KrausFamily.applyMat [Qubit.proj0] s.quantum.mat)).re +
        (Matrix.trace
          (KrausFamily.applyMat [Qubit.proj1] s.quantum.mat)).re =
      1
  rw [Qubit.trace_proj_apply Qubit.proj0 Qubit.proj0_mul_self
      Qubit.proj0_conjTranspose,
    Qubit.trace_proj_apply Qubit.proj1 Qubit.proj1_mul_self
      Qubit.proj1_conjTranspose,
    ← Complex.add_re, ← Matrix.trace_add, ← Matrix.add_mul,
    Qubit.proj0_add_proj1, Matrix.one_mul, s.quantum.trace_eq_one]
  rfl

theorem measureProbability_le_one {C : Type} (s : Config C) (b : Bool) :
    measureProbability s b ≤ 1 := by
  cases b
  · nlinarith [measureProbability_nonneg s true,
      measureProbability_false_add_true s]
  · nlinarith [measureProbability_nonneg s false,
      measureProbability_false_add_true s]

/-- The normalized post-measurement state for a nonzero outcome. -/
noncomputable def measuredState {C : Type} (s : Config C) (b : Bool)
    (h : 0 < measureProbability s b) : NormalizedDensity 2 :=
  NormalizedDensity.normalizeBranch (measureBranch b) s.quantum h

/-- Administrative CEK reduction, β-reduction, internal choice, deterministic
return, and Pauli-X.  These steps carry no probabilistic weight. -/
inductive InternalStep {C : Type} : Config C → Config C → Prop where
  | variable {s : Config C} {x : Name} {v : RuntimeValue C}
      (h : RuntimeEnv.lookup x s.env = some v) :
      InternalStep { s with control := .term (.var x) }
        { s with control := .value v }
  | lambda {s : Config C} {x : Name} {body : Term (QubitPrimitive C)} :
      InternalStep { s with control := .term (.lam x body) }
        { s with control := .value (.closure x body s.env) }
  | recursive {s : Config C} {self arg : Name}
      {body : Term (QubitPrimitive C)} :
      InternalStep { s with control := .term (.recLam self arg body) }
        { s with control := .value (.recClosure self arg body s.env) }
  | application {s : Config C} {fn arg : Term (QubitPrimitive C)} :
      InternalStep { s with control := .term (.app fn arg) }
        { s with
          control := .term fn
          stack := .argument arg s.env :: s.stack }
  | evaluateArgument {s : Config C} {fn : RuntimeValue C}
      {arg : Term (QubitPrimitive C)} {callEnv : RuntimeEnv C}
      {rest : EvalStack C} :
      InternalStep
        { s with control := .value fn
                 stack := .argument arg callEnv :: rest }
        { s with control := .term arg
                 env := callEnv
                 stack := .function fn :: rest }
  | beta {s : Config C} {x : Name} {body : Term (QubitPrimitive C)}
      {closureEnv : RuntimeEnv C} {arg : RuntimeValue C}
      {rest : EvalStack C} :
      InternalStep
        { s with control := .value arg
                 stack := .function (.closure x body closureEnv) :: rest }
        { s with control := .term body
                 env := RuntimeEnv.bind x arg closureEnv
                 stack := rest }
  | recBeta {s : Config C} {self x : Name}
      {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
      {arg : RuntimeValue C} {rest : EvalStack C} :
      InternalStep
        { s with control := .value arg
                 stack :=
                   .function (.recClosure self x body closureEnv) :: rest }
        { s with control := .term body
                 env :=
                   RuntimeEnv.bind x arg
                     (RuntimeEnv.bind self
                       (.recClosure self x body closureEnv) closureEnv)
                 stack := rest }
  | returnPrimitive {s : Config C} {value : C} :
      InternalStep { s with control := .term (.prim (.ret value)) }
        { s with control := .value (.payload value) }
  | pauliXPrimitive {s : Config C} {value : C} :
      InternalStep { s with control := .term (.prim (.pauliX value)) }
        { s with
          control := .value (.payload value)
          quantum := NormalizedDensity.pauliX s.quantum }
  | internalLeft {s : Config C} {left right : Term (QubitPrimitive C)} :
      InternalStep { s with control := .term (.intern left right) }
        { s with control := .term left }
  | internalRight {s : Config C} {left right : Term (QubitPrimitive C)} :
      InternalStep { s with control := .term (.intern left right) }
        { s with control := .term right }

/-- Weighted transitions.  Source-level probabilistic choice retains its
declared weight; measurement uses the Born weight and only constructs a
normalized target when that weight is strictly positive. -/
inductive WeightedStep {C : Type} : Config C → ℝ → Config C → Prop where
  | probabilityLeft {s : Config C} {p : ℝ}
      {left right : Term (QubitPrimitive C)}
      (hp : 0 < p) (hp1 : p ≤ 1) :
      WeightedStep { s with control := .term (.prob p left right) } p
        { s with control := .term left }
  | probabilityRight {s : Config C} {p : ℝ}
      {left right : Term (QubitPrimitive C)}
      (hp : 0 ≤ p) (hp1 : p < 1) :
      WeightedStep { s with control := .term (.prob p left right) } (1 - p)
        { s with control := .term right }
  | measurement {s : Config C} {zeroValue oneValue : C} {b : Bool}
      (h : 0 < measureProbability s b) :
      WeightedStep
        { s with
          control := .term (.prim (.measureZ zeroValue oneValue)) }
        (measureProbability s b)
        { s with
          control := .value (.payload (if b then oneValue else zeroValue))
          quantum := measuredState s b h }

/-- External choice is resolved only by an explicit Boolean selector. -/
inductive ExternalStep {C : Type} : Config C → Bool → Config C → Prop where
  | selectFalse {s : Config C} {left right : Term (QubitPrimitive C)} :
      ExternalStep { s with control := .term (.extern left right) } false
        { s with control := .term left }
  | selectTrue {s : Config C} {left right : Term (QubitPrimitive C)} :
      ExternalStep { s with control := .term (.extern left right) } true
        { s with control := .term right }

end HardwareOperational
end QLambda
