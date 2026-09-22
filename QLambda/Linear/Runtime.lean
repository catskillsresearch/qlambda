/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Composer.MatrixSemantics
import QLambda.HardwareOperational
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
  HardwareOperational.NormalizedDensity (CQ.QDim q)

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
def measureBranch (w : Fin q) (b : Bool) :
    KrausFamily (CQ.QDim q) (CQ.QDim q) :=
  [Composer.projector w b]

/-- Born probability of one computational-basis outcome. -/
noncomputable def measureProbability (ρ : RegisterState q)
    (w : Fin q) (b : Bool) : Real :=
  HardwareOperational.NormalizedDensity.bornWeight (measureBranch w b) ρ

theorem measureProbability_nonneg (ρ : RegisterState q)
    (w : Fin q) (b : Bool) :
    0 ≤ measureProbability ρ w b :=
  HardwareOperational.NormalizedDensity.bornWeight_nonneg _ _

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
  HardwareOperational.NormalizedDensity.normalizeBranch (measureBranch w b) ρ h

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
      (Composer.canonicalModel q 0).measure w |>.branch
        (if b then (1 : Fin 2) else (0 : Fin 2)) := by
  cases b <;> rfl

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

/-- A fixed finite quantum register and a quantum-kernel control state.
`frame` records live wires owned by the surrounding source evaluation
context; control-owned wires are tracked structurally. -/
structure Config (q : Nat) where
  state : RegisterState q
  frame : Finset (Fin q)
  control : Control q

namespace Config

variable {q : Nat}

def live (s : Config q) : Finset (Fin q) :=
  s.frame ∪ s.control.wires

/-- Static configuration typing: the control has the requested source type,
contains no aliased wire, and is disjoint from wires owned by its frame. -/
def WellTyped (s : Config q) (A : Ty) : Prop :=
  s.control.typeOf = some A ∧
    s.control.Valid ∧
    Disjoint s.control.wires s.frame

/-- A final runtime configuration contains a returned value. -/
def Normal (s : Config q) : Prop :=
  ∃ value, s.control = .ret value

/-- Allocation is the only capacity-sensitive request. -/
def OutOfWires (s : Config q) : Prop :=
  s.control = .app (.prim .new0) .unit ∧ ∀ w : Fin q, w ∈ s.live

end Config

/-- Deterministic quantum transitions.  Allocation resets an unused physical
slot.  Applying `CX` to its control is administrative; only saturation with a
distinct target changes the register. -/
inductive InternalStep {q : Nat} : Config q → Config q → Prop where
  | allocate {s : Config q} {w : Fin q} (hfree : w ∉ s.frame) :
      InternalStep
        {s with control := .app (.prim .new0) .unit}
        {s with
          state := RegisterState.reset w s.state
          control := .ret (.wire w)}
  | x {s : Config q} {w : Fin q} :
      InternalStep
        {s with control := .app (.prim .x) (.wire w)}
        {s with
          state := RegisterState.applyGate (.x w) s.state
          control := .ret (.wire w)}
  | h {s : Config q} {w : Fin q} :
      InternalStep
        {s with control := .app (.prim .h) (.wire w)}
        {s with
          state := RegisterState.applyGate (.h w) s.state
          control := .ret (.wire w)}
  | t {s : Config q} {w : Fin q} :
      InternalStep
        {s with control := .app (.prim .t) (.wire w)}
        {s with
          state := RegisterState.applyGate (.t w) s.state
          control := .ret (.wire w)}
  | ry {s : Config q} {angle : Rat} {w : Fin q} :
      InternalStep
        {s with control := .app (.prim (.ry angle)) (.wire w)}
        {s with
          state :=
            RegisterState.applyGate (.ry (.rational angle) w) s.state
          control := .ret (.wire w)}
  | cxControl {s : Config q} {control : Fin q} :
      InternalStep
        {s with control := .app (.prim .cx) (.wire control)}
        {s with control := .ret (.cxControl control)}
  | cx {s : Config q} {control target : Fin q}
      (hne : control ≠ target) :
      InternalStep
        {s with control := .app (.cxControl control) (.wire target)}
        {s with
          state := RegisterState.applyGate (.cx control target) s.state
          control := .ret (.pair (.wire control) (.wire target))}
  | reset {s : Config q} {w : Fin q} :
      InternalStep
        {s with control := .app (.prim .reset) (.wire w)}
        {s with
          state := RegisterState.reset w s.state
          control := .ret (.wire w)}

/-- Born-weighted instrument transition.  The target is normalized and exists
only for a positive-probability outcome. -/
inductive MeasurementStep {q : Nat} : Config q → Real → Bool → Config q → Prop where
  | branch {s : Config q} {w : Fin q} {b : Bool}
      (hpositive : 0 < RegisterState.measureProbability s.state w b) :
      MeasurementStep
        {s with control := .measure (.wire w)}
        (RegisterState.measureProbability s.state w b) b
        {s with
          state := RegisterState.measured s.state w b hpositive
          control := .ret (.pair (.bit b) (.wire w))}

theorem internal_preservation {q : Nat} {s s' : Config q} {A : Ty}
    (ht : s.WellTyped A) (hs : InternalStep s s') :
    s'.WellTyped A := by
  cases hs <;>
    simp_all [Config.WellTyped, Control.typeOf, Control.wires,
      Control.Valid, Value.typeOf, Value.wires, Value.Valid,
      Finset.disjoint_left]

theorem measurement_preservation {q : Nat} {s s' : Config q}
    {weight : Real} {outcome : Bool} {A : Ty}
    (ht : s.WellTyped A) (hs : MeasurementStep s weight outcome s') :
    s'.WellTyped A := by
  cases hs
  simp_all [Config.WellTyped, Control.typeOf, Control.wires,
    Control.Valid, Value.typeOf, Value.wires, Value.Valid,
    Finset.disjoint_left]

theorem measurement_weight_nonneg {q : Nat} {s s' : Config q}
    {weight : Real} {outcome : Bool}
    (hs : MeasurementStep s weight outcome s') :
    0 ≤ weight := by
  cases hs with
  | branch hpositive => exact hpositive.le

theorem measurement_weight_le_one {q : Nat} {s s' : Config q}
    {weight : Real} {outcome : Bool}
    (hs : MeasurementStep s weight outcome s') :
    weight ≤ 1 := by
  cases hs
  exact RegisterState.measureProbability_le_one _ _ _

/-- Every well-typed kernel request returns, takes a deterministic step,
takes a positive Born branch, or reports finite-register exhaustion. -/
theorem progress {q : Nat} {s : Config q} {A : Ty}
    (ht : s.WellTyped A) :
    s.Normal ∨ s.OutOfWires ∨
      (∃ s', InternalStep s s') ∨
      (∃ weight outcome s', MeasurementStep s weight outcome s') := by
  rcases ht with ⟨htype, hvalid, hframe⟩
  cases hcontrol : s.control with
  | ret value =>
      exact Or.inl ⟨value, hcontrol⟩
  | measure qubit =>
      subst hcontrol
      cases qubit with
      | unit => simp [Control.typeOf, Value.typeOf] at htype
      | bit b => simp [Control.typeOf, Value.typeOf] at htype
      | pair left right => simp [Control.typeOf, Value.typeOf] at htype
      | prim p => cases p <;> simp [Control.typeOf, Value.typeOf, primTy] at htype
      | cxControl control => simp [Control.typeOf, Value.typeOf] at htype
      | wire w =>
          have hsum :=
            RegisterState.measureProbability_false_add_true s.state w
          by_cases hzero :
              0 < RegisterState.measureProbability s.state w false
          · exact Or.inr (Or.inr (Or.inr
              ⟨_, false, _, MeasurementStep.branch hzero⟩))
          · have hone :
                0 < RegisterState.measureProbability s.state w true := by
              have hnonneg :=
                RegisterState.measureProbability_nonneg s.state w false
              nlinarith
            exact Or.inr (Or.inr (Or.inr
              ⟨_, true, _, MeasurementStep.branch hone⟩))
  | app fn arg =>
      subst hcontrol
      cases fn with
      | unit => simp [Control.typeOf, Value.typeOf] at htype
      | bit b => simp [Control.typeOf, Value.typeOf] at htype
      | pair left right => simp [Control.typeOf, Value.typeOf] at htype
      | wire w => simp [Control.typeOf, Value.typeOf] at htype
      | cxControl control =>
          cases arg with
          | unit => simp [Control.typeOf, Value.typeOf] at htype
          | bit b => simp [Control.typeOf, Value.typeOf] at htype
          | pair left right => simp [Control.typeOf, Value.typeOf] at htype
          | prim p => simp [Control.typeOf, Value.typeOf] at htype
          | cxControl w => simp [Control.typeOf, Value.typeOf] at htype
          | wire target =>
              cases hvalid with
              | app _ _ hdisjoint =>
                  have hne : control ≠ target := by
                    simpa [Value.wires, Finset.disjoint_singleton_left] using hdisjoint
                  exact Or.inr (Or.inr (Or.inl ⟨_, InternalStep.cx hne⟩))
      | prim p =>
          cases p with
          | new0 =>
              cases arg with
              | unit =>
                  by_cases hfull : ∀ w : Fin q, w ∈ s.frame
                  · exact Or.inr (Or.inl ⟨rfl, by
                      intro w
                      simp [Config.live, Control.wires, Value.wires, hfull w]⟩)
                  · push_neg at hfull
                    obtain ⟨w, hw⟩ := hfull
                    exact Or.inr (Or.inr (Or.inl
                      ⟨_, InternalStep.allocate hw⟩))
              | bit b => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | pair left right => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | prim p => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | wire w => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | cxControl w => simp [Control.typeOf, Value.typeOf, primTy] at htype
          | x =>
              cases arg <;> simp [Control.typeOf, Value.typeOf, primTy] at htype
              exact Or.inr (Or.inr (Or.inl ⟨_, InternalStep.x⟩))
          | h =>
              cases arg <;> simp [Control.typeOf, Value.typeOf, primTy] at htype
              exact Or.inr (Or.inr (Or.inl ⟨_, InternalStep.h⟩))
          | t =>
              cases arg <;> simp [Control.typeOf, Value.typeOf, primTy] at htype
              exact Or.inr (Or.inr (Or.inl ⟨_, InternalStep.t⟩))
          | ry angle =>
              cases arg <;> simp [Control.typeOf, Value.typeOf, primTy] at htype
              exact Or.inr (Or.inr (Or.inl ⟨_, InternalStep.ry⟩))
          | cx =>
              cases arg <;> simp [Control.typeOf, Value.typeOf, primTy] at htype
              exact Or.inr (Or.inr (Or.inl ⟨_, InternalStep.cxControl⟩))
          | reset =>
              cases arg <;> simp [Control.typeOf, Value.typeOf, primTy] at htype
              exact Or.inr (Or.inr (Or.inl ⟨_, InternalStep.reset⟩))

/-- For well-typed configurations, being stuck with no transition means
exactly either returning a value or exhausting the finite allocation pool. -/
theorem normal_or_exhausted_of_no_step {q : Nat} {s : Config q} {A : Ty}
    (ht : s.WellTyped A)
    (hi : ¬ ∃ s', InternalStep s s')
    (hm : ¬ ∃ weight outcome s', MeasurementStep s weight outcome s') :
    s.Normal ∨ s.OutOfWires := by
  rcases progress ht with hn | ho | hi' | hm'
  · exact Or.inl hn
  · exact Or.inr ho
  · exact (hi hi').elim
  · exact (hm hm').elim

/-- All deterministic targets remain normalized by construction. -/
theorem internal_normalization {q : Nat} {s s' : Config q}
    (_hs : InternalStep s s') :
    Matrix.trace s'.state.mat = 1 :=
  s'.state.trace_eq_one

/-- All positive measurement targets are normalized by construction. -/
theorem measurement_normalization {q : Nat} {s s' : Config q}
    {weight : Real} {outcome : Bool}
    (_hs : MeasurementStep s weight outcome s') :
    Matrix.trace s'.state.mat = 1 :=
  s'.state.trace_eq_one

end QLambda.Linear.Runtime
