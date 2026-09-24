/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.Config

/-!
# Finite-register runtime transitions and measurement
-/

namespace QLambda.Linear.Runtime

open Matrix
open scoped MatrixOrder ComplexOrder


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
  rcases ht with ⟨htype, hvalid, hframe⟩
  cases hs with
  | allocate hfree =>
      have hA : A = .qubit := by
        simpa [Control.typeOf, Value.typeOf, primTy] using htype.symm
      subst A
      exact ⟨rfl, .ret .wire, by
        simpa [Control.wires, Value.wires, Finset.disjoint_left] using hfree⟩
  | x | h | t | ry =>
      have hA : A = .qubit := by
        simpa [Control.typeOf, Value.typeOf, primTy] using htype.symm
      subst A
      exact ⟨rfl, .ret .wire, by
        simpa [Control.wires, Value.wires] using hframe⟩
  | cxControl =>
      have hA :
          A = .arrow .lin .qubit (.tensor .qubit .qubit) := by
        simpa [Control.typeOf, Value.typeOf, primTy] using htype.symm
      subst A
      exact ⟨rfl, .ret .cxControl, by
        simpa [Control.wires, Value.wires] using hframe⟩
  | cx hne =>
      have hA : A = .tensor .qubit .qubit := by
        simpa [Control.typeOf, Value.typeOf] using htype.symm
      subst A
      cases hvalid with
      | app _ _ hdisjoint =>
          exact ⟨rfl,
            .ret (.pair .wire .wire hdisjoint),
            by simpa [Control.wires, Value.wires] using hframe⟩
  | reset =>
      have hA : A = .qubit := by
        simpa [Control.typeOf, Value.typeOf, primTy] using htype.symm
      subst A
      exact ⟨rfl, .ret .wire, by
        simpa [Control.wires, Value.wires] using hframe⟩

theorem measurement_preservation {q : Nat} {s s' : Config q}
    {weight : Real} {outcome : Bool} {A : Ty}
    (ht : s.WellTyped A) (hs : MeasurementStep s weight outcome s') :
    s'.WellTyped A := by
  rcases ht with ⟨htype, hvalid, hframe⟩
  cases hs
  have hA : A = .tensor .bit .qubit := by
    simpa [Control.typeOf, Value.typeOf] using htype.symm
  subst A
  exact ⟨rfl,
    .ret (.pair .bit .wire (by simp [Value.wires])),
    by simpa [Control.wires, Value.wires] using hframe⟩

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
      have hs : s = {s with control := .measure qubit} := by
        cases s
        simp_all
      rw [hs] at htype hvalid hframe ⊢
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
      have hs : s = {s with control := .app fn arg} := by
        cases s
        simp_all
      rw [hs] at htype hvalid hframe ⊢
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
          | prim p =>
              cases p <;> simp [Control.typeOf, Value.typeOf, primTy] at htype
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
                  · push Not at hfull
                    obtain ⟨w, hw⟩ := hfull
                    exact Or.inr (Or.inr (Or.inl
                      ⟨_, InternalStep.allocate hw⟩))
              | bit b => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | pair left right => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | prim p =>
                  cases p <;> simp [Control.typeOf, Value.typeOf, primTy] at htype
              | wire w => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | cxControl w => simp [Control.typeOf, Value.typeOf, primTy] at htype
          | x =>
              cases arg with
              | unit => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | bit b => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | pair l r => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | prim p =>
                  cases p <;> simp [Control.typeOf, Value.typeOf, primTy] at htype
              | cxControl w => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | wire w =>
                  exact Or.inr (Or.inr (Or.inl ⟨_, InternalStep.x⟩))
          | h =>
              cases arg with
              | unit => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | bit b => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | pair l r => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | prim p =>
                  cases p <;> simp [Control.typeOf, Value.typeOf, primTy] at htype
              | cxControl w => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | wire w =>
                  exact Or.inr (Or.inr (Or.inl ⟨_, InternalStep.h⟩))
          | t =>
              cases arg with
              | unit => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | bit b => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | pair l r => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | prim p =>
                  cases p <;> simp [Control.typeOf, Value.typeOf, primTy] at htype
              | cxControl w => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | wire w =>
                  exact Or.inr (Or.inr (Or.inl ⟨_, InternalStep.t⟩))
          | ry angle =>
              cases arg with
              | unit => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | bit b => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | pair l r => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | prim p =>
                  cases p <;> simp [Control.typeOf, Value.typeOf, primTy] at htype
              | cxControl w => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | wire w =>
                  exact Or.inr (Or.inr (Or.inl ⟨_, InternalStep.ry⟩))
          | cx =>
              cases arg with
              | unit => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | bit b => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | pair l r => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | prim p =>
                  cases p <;> simp [Control.typeOf, Value.typeOf, primTy] at htype
              | cxControl w => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | wire w =>
                  exact Or.inr (Or.inr (Or.inl ⟨_, InternalStep.cxControl⟩))
          | reset =>
              cases arg with
              | unit => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | bit b => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | pair l r => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | prim p =>
                  cases p <;> simp [Control.typeOf, Value.typeOf, primTy] at htype
              | cxControl w => simp [Control.typeOf, Value.typeOf, primTy] at htype
              | wire w =>
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
