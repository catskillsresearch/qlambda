/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.Syntax

/-!
# Type formation for the linear calculus

Types use de Bruijn indices for recursive variables.  This file separates the
proof-level formation judgments from their executable Boolean checkers and
proves that the two presentations agree.
-/

namespace QLambda.Linear.Ty

/-- Proof-level scoping judgment for type variables. -/
def WellScopedAt : Nat → Ty → Prop
  | n, .var i => i < n
  | _, .unit => True
  | _, .bit => True
  | _, .qubit => True
  | n, .tensor A B => WellScopedAt n A ∧ WellScopedAt n B
  | n, .arrow _ A B => WellScopedAt n A ∧ WellScopedAt n B
  | n, .mu A => WellScopedAt (n + 1) A

/-- Executable checker for `WellScopedAt`. -/
def wellScopedAt : Nat → Ty → Bool
  | n, .var i => decide (i < n)
  | _, .unit => true
  | _, .bit => true
  | _, .qubit => true
  | n, .tensor A B => wellScopedAt n A && wellScopedAt n B
  | n, .arrow _ A B => wellScopedAt n A && wellScopedAt n B
  | n, .mu A => wellScopedAt (n + 1) A

theorem wellScopedAt_eq_true_iff {n A} :
    wellScopedAt n A = true ↔ WellScopedAt n A := by
  induction A generalizing n with
  | var i => simp [wellScopedAt, WellScopedAt]
  | unit => simp [wellScopedAt, WellScopedAt]
  | bit => simp [wellScopedAt, WellScopedAt]
  | qubit => simp [wellScopedAt, WellScopedAt]
  | tensor A B ihA ihB =>
      simp [wellScopedAt, WellScopedAt, ihA, ihB]
  | arrow κ A B ihA ihB =>
      simp [wellScopedAt, WellScopedAt, ihA, ihB]
  | mu A ih =>
      simp [wellScopedAt, WellScopedAt, ih]

/-- The type variable selected by `target` does not occur in the type. -/
def DoesNotContainAt : Nat → Ty → Prop
  | target, .var i => i ≠ target
  | _, .unit => True
  | _, .bit => True
  | _, .qubit => True
  | target, .tensor A B =>
      DoesNotContainAt target A ∧ DoesNotContainAt target B
  | target, .arrow _ A B =>
      DoesNotContainAt target A ∧ DoesNotContainAt target B
  | target, .mu A => DoesNotContainAt (target + 1) A

/-- Executable checker for absence of a selected recursive variable. -/
def doesNotContainAt : Nat → Ty → Bool
  | target, .var i => decide (i ≠ target)
  | _, .unit => true
  | _, .bit => true
  | _, .qubit => true
  | target, .tensor A B =>
      doesNotContainAt target A && doesNotContainAt target B
  | target, .arrow _ A B =>
      doesNotContainAt target A && doesNotContainAt target B
  | target, .mu A => doesNotContainAt (target + 1) A

theorem doesNotContainAt_eq_true_iff {target A} :
    doesNotContainAt target A = true ↔ DoesNotContainAt target A := by
  induction A generalizing target with
  | var i => simp [doesNotContainAt, DoesNotContainAt]
  | unit => simp [doesNotContainAt, DoesNotContainAt]
  | bit => simp [doesNotContainAt, DoesNotContainAt]
  | qubit => simp [doesNotContainAt, DoesNotContainAt]
  | tensor A B ihA ihB =>
      simp [doesNotContainAt, DoesNotContainAt, ihA, ihB]
  | arrow κ A B ihA ihB =>
      simp [doesNotContainAt, DoesNotContainAt, ihA, ihB]
  | mu A ih =>
      simp [doesNotContainAt, DoesNotContainAt, ih]

/-- Strict positivity of the selected recursive variable.

The variable may occur in products and function codomains, but it must be
absent from function domains.  Entering another `mu` shifts the selected
de Bruijn index.
-/
def StrictlyPositiveAt : Nat → Ty → Prop
  | _, .var _ => True
  | _, .unit => True
  | _, .bit => True
  | _, .qubit => True
  | target, .tensor A B =>
      StrictlyPositiveAt target A ∧ StrictlyPositiveAt target B
  | target, .arrow _ A B =>
      DoesNotContainAt target A ∧ StrictlyPositiveAt target B
  | target, .mu A => StrictlyPositiveAt (target + 1) A

/-- Executable strict-positivity checker. -/
def strictlyPositiveAt : Nat → Ty → Bool
  | _, .var _ => true
  | _, .unit => true
  | _, .bit => true
  | _, .qubit => true
  | target, .tensor A B =>
      strictlyPositiveAt target A && strictlyPositiveAt target B
  | target, .arrow _ A B =>
      doesNotContainAt target A && strictlyPositiveAt target B
  | target, .mu A => strictlyPositiveAt (target + 1) A

theorem strictlyPositiveAt_eq_true_iff {target A} :
    strictlyPositiveAt target A = true ↔ StrictlyPositiveAt target A := by
  induction A generalizing target with
  | var i => simp [strictlyPositiveAt, StrictlyPositiveAt]
  | unit => simp [strictlyPositiveAt, StrictlyPositiveAt]
  | bit => simp [strictlyPositiveAt, StrictlyPositiveAt]
  | qubit => simp [strictlyPositiveAt, StrictlyPositiveAt]
  | tensor A B ihA ihB =>
      simp [strictlyPositiveAt, StrictlyPositiveAt, ihA, ihB]
  | arrow κ A B ihA ihB =>
      simp [strictlyPositiveAt, StrictlyPositiveAt,
        doesNotContainAt_eq_true_iff, ihB]
  | mu A ih =>
      simp [strictlyPositiveAt, StrictlyPositiveAt, ih]

/-- Every recursive body in a type is strictly positive in its own binder. -/
def PositiveRec : Ty → Prop
  | .var _ => True
  | .unit => True
  | .bit => True
  | .qubit => True
  | .tensor A B => PositiveRec A ∧ PositiveRec B
  | .arrow _ A B => PositiveRec A ∧ PositiveRec B
  | .mu A => StrictlyPositiveAt 0 A ∧ PositiveRec A

/-- Executable checker for positivity of all recursive binders. -/
def positiveRec : Ty → Bool
  | .var _ => true
  | .unit => true
  | .bit => true
  | .qubit => true
  | .tensor A B => positiveRec A && positiveRec B
  | .arrow _ A B => positiveRec A && positiveRec B
  | .mu A => strictlyPositiveAt 0 A && positiveRec A

theorem positiveRec_eq_true_iff {A} :
    positiveRec A = true ↔ PositiveRec A := by
  induction A with
  | var i => simp [positiveRec, PositiveRec]
  | unit => simp [positiveRec, PositiveRec]
  | bit => simp [positiveRec, PositiveRec]
  | qubit => simp [positiveRec, PositiveRec]
  | tensor A B ihA ihB => simp [positiveRec, PositiveRec, ihA, ihB]
  | arrow κ A B ihA ihB => simp [positiveRec, PositiveRec, ihA, ihB]
  | mu A ih =>
      simp [positiveRec, PositiveRec, strictlyPositiveAt_eq_true_iff, ih]

/-- A type is admissible at depth `n` when it is scoped there and every
recursive body in it is strictly positive. -/
def AdmissibleAt (n : Nat) (A : Ty) : Prop :=
  WellScopedAt n A ∧ PositiveRec A

/-- Executable admissibility checker. -/
def admissibleAt (n : Nat) (A : Ty) : Bool :=
  wellScopedAt n A && positiveRec A

theorem admissibleAt_eq_true_iff {n A} :
    admissibleAt n A = true ↔ AdmissibleAt n A := by
  simp [admissibleAt, AdmissibleAt, wellScopedAt_eq_true_iff,
    positiveRec_eq_true_iff]

/-- Closed, admissible types. -/
abbrev Admissible (A : Ty) : Prop :=
  AdmissibleAt 0 A

/-- Check whether a type is closed and admissible. -/
def admissible (A : Ty) : Bool :=
  admissibleAt 0 A

theorem admissible_eq_true_iff {A} :
    admissible A = true ↔ Admissible A :=
  admissibleAt_eq_true_iff

/-- Proof-level counterpart of the executable duplicability checker. -/
def DuplicableAt : List Bool → Ty → Prop
  | κ, .var i => κ[i]? = some true
  | _, .unit => True
  | _, .bit => True
  | _, .qubit => False
  | κ, .tensor A B => DuplicableAt κ A ∧ DuplicableAt κ B
  | _, .arrow .lin _ _ => False
  | _, .arrow .unres _ _ => True
  | κ, .mu A => DuplicableAt (true :: κ) A

theorem duplicableAt_eq_true_iff {κ A} :
    duplicableAt κ A = true ↔ DuplicableAt κ A := by
  induction A generalizing κ with
  | var i =>
      simp only [duplicableAt, DuplicableAt]
      cases κ[i]? <;> simp
  | unit => simp [duplicableAt, DuplicableAt]
  | bit => simp [duplicableAt, DuplicableAt]
  | qubit => simp [duplicableAt, DuplicableAt]
  | tensor A B ihA ihB =>
      simp [duplicableAt, DuplicableAt, ihA, ihB]
  | arrow mode A B ihA ihB =>
      cases mode <;> simp [duplicableAt, DuplicableAt]
  | mu A ih =>
      simp [duplicableAt, DuplicableAt, ih]

/-- Closed types whose values may be copied and discarded, as a proposition. -/
abbrev Duplicable (A : Ty) : Prop :=
  DuplicableAt [] A

theorem duplicable_eq_true_iff {A} :
    duplicable A = true ↔ Duplicable A :=
  duplicableAt_eq_true_iff

instance instDecidableWellScopedAt {n A} : Decidable (WellScopedAt n A) :=
  if h : wellScopedAt n A = true then
    isTrue (wellScopedAt_eq_true_iff.mp h)
  else
    isFalse fun hA => h (wellScopedAt_eq_true_iff.mpr hA)

instance instDecidableDoesNotContainAt {target A} :
    Decidable (DoesNotContainAt target A) :=
  if h : doesNotContainAt target A = true then
    isTrue (doesNotContainAt_eq_true_iff.mp h)
  else
    isFalse fun hA => h (doesNotContainAt_eq_true_iff.mpr hA)

instance instDecidableStrictlyPositiveAt {target A} :
    Decidable (StrictlyPositiveAt target A) :=
  if h : strictlyPositiveAt target A = true then
    isTrue (strictlyPositiveAt_eq_true_iff.mp h)
  else
    isFalse fun hA => h (strictlyPositiveAt_eq_true_iff.mpr hA)

instance instDecidablePositiveRec {A} : Decidable (PositiveRec A) :=
  if h : positiveRec A = true then
    isTrue (positiveRec_eq_true_iff.mp h)
  else
    isFalse fun hA => h (positiveRec_eq_true_iff.mpr hA)

instance instDecidableAdmissibleAt {n A} : Decidable (AdmissibleAt n A) :=
  if h : admissibleAt n A = true then
    isTrue (admissibleAt_eq_true_iff.mp h)
  else
    isFalse fun hA => h (admissibleAt_eq_true_iff.mpr hA)

instance instDecidableDuplicableAt {κ A} : Decidable (DuplicableAt κ A) :=
  if h : duplicableAt κ A = true then
    isTrue (duplicableAt_eq_true_iff.mp h)
  else
    isFalse fun hA => h (duplicableAt_eq_true_iff.mpr hA)

end QLambda.Linear.Ty
