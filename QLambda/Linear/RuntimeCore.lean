/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Composer.MatrixSemantics
import QLambda.QuantumRuntimeState
import QLambda.Linear.Operational

/-!
# Finite-register runtime semantics for the linear calculus

Source `Term` deliberately has no wire literal and no probability constructor.
This module supplies both at the machine boundary.  A runtime configuration
contains a fixed-capacity finite register, runtime-only wire handles, and a
normalized density matrix.  Inactive register positions are reset when
allocated, which gives allocation a concrete meaning without changing the
matrix dimension.

The machine is the quantum kernel reached by the source progress theorem's
`QuantumBlocked` case.  Unary gates and reset are deterministic transitions.
`CX` first produces a runtime closure over its control wire and changes the
register only when the target application saturates it.  Measurement is a
separate Born-weighted transition and never inserts probability into `Term`.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QLambda.Linear.Runtime

abbrev RegisterState (q : Nat) :=
  NormalizedDensity (CQ.QDim q)

namespace RegisterState

variable {q : Nat}

/-- Apply an isometry to a normalized register. -/
noncomputable def applyIsometry
    (U : KrausOperator (CQ.QDim q) (CQ.QDim q))
    (hU : Uᴴ * U = 1) (ρ : RegisterState q) : RegisterState q where
  mat := KrausFamily.applyMat [U] ρ.mat
  posSemidef := KrausFamily.applyMat_posSemidef [U] ρ.posSemidef
  trace_eq_one :=
    (KrausFamily.trace_applyMat_isometry U hU ρ.mat).trans ρ.trace_eq_one

/-- Apply one gate from the canonical Composer matrix model. -/
noncomputable def applyGate : Composer.Gate q → RegisterState q → RegisterState q
  | .x w, ρ =>
      applyIsometry (Composer.xMatrix w) (Composer.xMatrix_isometry w) ρ
  | .h w, ρ =>
      applyIsometry (Composer.hMatrix w) (Composer.hMatrix_isometry w) ρ
  | .t w, ρ =>
      applyIsometry (Composer.tMatrix w) (Composer.tMatrix_isometry w) ρ
  | .ry θ w, ρ =>
      applyIsometry (Composer.ryMatrix θ.eval w)
        (Composer.ryMatrix_isometry θ.eval w) ρ
  | .cx control target, ρ =>
      applyIsometry (Composer.cxMatrix control target)
        (Composer.cxMatrix_isometry control target) ρ

/-- Reset one fixed-register position to `|0⟩`. -/
noncomputable def reset (w : Fin q) (ρ : RegisterState q) : RegisterState q where
  mat :=
    KrausFamily.applyMat
      [Composer.resetKraus w false, Composer.resetKraus w true] ρ.mat
  posSemidef :=
    KrausFamily.applyMat_posSemidef
      [Composer.resetKraus w false, Composer.resetKraus w true] ρ.posSemidef
  trace_eq_one :=
    (Composer.trace_applyMat_pair_of_completeness _ _
      (Composer.resetKraus_completeness w) ρ.mat).trans ρ.trace_eq_one

/-- The actual Kraus branch used for runtime measurement. -/
noncomputable def measureBranch (w : Fin q) (b : Bool) :
    KrausFamily (CQ.QDim q) (CQ.QDim q) :=
  [Composer.projector w b]

/-- Born probability of one computational-basis outcome. -/
noncomputable def measureProbability (ρ : RegisterState q)
    (w : Fin q) (b : Bool) : Real :=
  NormalizedDensity.bornWeight (measureBranch w b) ρ

theorem measureProbability_nonneg (ρ : RegisterState q)
    (w : Fin q) (b : Bool) :
    0 ≤ measureProbability ρ w b :=
  NormalizedDensity.bornWeight_nonneg _ _

private theorem trace_projector_apply (ρ : RegisterState q)
    (w : Fin q) (b : Bool) :
    Matrix.trace (KrausFamily.applyMat [Composer.projector w b] ρ.mat) =
      Matrix.trace (Composer.projector w b * ρ.mat) := by
  rw [KrausFamily.applyMat_single,
    Matrix.trace_mul_comm (Composer.projector w b * ρ.mat)
      (Composer.projector w b)ᴴ,
    Composer.projector_conjTranspose, ← Matrix.mul_assoc,
    Composer.projector_mul_self]

/-- The two runtime measurement branches exhaust unit probability. -/
theorem measureProbability_false_add_true (ρ : RegisterState q) (w : Fin q) :
    measureProbability ρ w false + measureProbability ρ w true = 1 := by
  change
    (Matrix.trace
      (KrausFamily.applyMat [Composer.projector w false] ρ.mat)).re +
      (Matrix.trace
        (KrausFamily.applyMat [Composer.projector w true] ρ.mat)).re = 1
  rw [trace_projector_apply, trace_projector_apply, ← Complex.add_re,
    ← Matrix.trace_add, ← Matrix.add_mul, Composer.projector_completeness,
    Matrix.one_mul, ρ.trace_eq_one]
  rfl

theorem measureProbability_le_one (ρ : RegisterState q)
    (w : Fin q) (b : Bool) :
    measureProbability ρ w b ≤ 1 := by
  cases b
  · nlinarith [measureProbability_nonneg ρ w true,
      measureProbability_false_add_true ρ w]
  · nlinarith [measureProbability_nonneg ρ w false,
      measureProbability_false_add_true ρ w]

/-- Normalize a positive measurement branch.  Zero-probability branches do
not become machine transitions. -/
noncomputable def measured (ρ : RegisterState q) (w : Fin q) (b : Bool)
    (h : 0 < measureProbability ρ w b) : RegisterState q :=
  NormalizedDensity.normalizeBranch (measureBranch w b) ρ h

/-- Gate execution is exactly application of the corresponding canonical
Composer operation, not an unrelated abstract unitary. -/
theorem applyGate_canonical (g : Composer.Gate q) (ρ : RegisterState q) :
    (applyGate g ρ).mat =
      KrausFamily.applyMat ((Composer.canonicalModel q 0).gate g).kraus ρ.mat := by
  cases g <;> rfl

theorem reset_canonical (w : Fin q) (ρ : RegisterState q) :
    (reset w ρ).mat =
      KrausFamily.applyMat ((Composer.canonicalModel q 0).reset w).kraus ρ.mat := by
  rfl

theorem measureBranch_canonical (w : Fin q) (b : Bool) :
    measureBranch w b =
      ((Composer.canonicalModel q 0).measure w).branch
        (if b then (1 : Fin 2) else (0 : Fin 2)) := by
  cases b <;> simp [measureBranch, Composer.canonicalModel, Composer.measure]

end RegisterState

/-- Runtime values.  In particular, `wire` and `cxControl` are not constructors
of source `Term`. -/
inductive Value (q : Nat) where
  | unit
  | bit (value : Bool)
  | pair (left right : Value q)
  | prim (p : Prim)
  | wire (index : Fin q)
  | cxControl (control : Fin q)
  deriving Repr

namespace Value

variable {q : Nat}

/-- Physical wire handles retained by a runtime value. -/
def wires : Value q → Finset (Fin q)
  | .unit | .bit _ | .prim _ => ∅
  | .pair left right => wires left ∪ wires right
  | .wire w | .cxControl w => {w}

/-- Runtime type, including the internal closure created by partial `CX`. -/
def typeOf : Value q → Ty
  | .unit => .unit
  | .bit _ => .bit
  | .pair left right => .tensor left.typeOf right.typeOf
  | .prim p => primTy p
  | .wire _ => .qubit
  | .cxControl _ => .arrow .lin .qubit (.tensor .qubit .qubit)

/-- Runtime values own each wire at most once. -/
inductive Valid : Value q → Prop where
  | unit : Valid .unit
  | bit {b} : Valid (.bit b)
  | prim {p} : Valid (.prim p)
  | wire {w} : Valid (.wire w)
  | cxControl {w} : Valid (.cxControl w)
  | pair {left right} :
      Valid left → Valid right → Disjoint left.wires right.wires →
      Valid (.pair left right)

end Value

/-- Quantum-kernel control.  Source evaluation supplies applications and
measurement requests after evaluating their operands to runtime values. -/
inductive Control (q : Nat) where
  | ret (value : Value q)
  | app (fn arg : Value q)
  | measure (qubit : Value q)
  deriving Repr

namespace Control

variable {q : Nat}

def wires : Control q → Finset (Fin q)
  | .ret value => value.wires
  | .app fn arg => fn.wires ∪ arg.wires
  | .measure qubit => qubit.wires

/-- Syntax-directed type of quantum-kernel control. -/
def typeOf : Control q → Option Ty
  | .ret value => some value.typeOf
  | .app fn arg =>
      match fn.typeOf with
      | .arrow .lin A B => if arg.typeOf = A then some B else none
      | _ => none
  | .measure qubit =>
      if qubit.typeOf = .qubit then some (.tensor .bit .qubit) else none

/-- Linear validity of a pending runtime request. -/
inductive Valid : Control q → Prop where
  | ret {value} : value.Valid → Valid (.ret value)
  | app {fn arg} :
      fn.Valid → arg.Valid → Disjoint fn.wires arg.wires →
      Valid (.app fn arg)
  | measure {qubit} : qubit.Valid → Valid (.measure qubit)

end Control


end QLambda.Linear.Runtime
