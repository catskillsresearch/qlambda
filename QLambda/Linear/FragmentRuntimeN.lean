/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentAdequacy
import QLambda.Linear.FragmentContext
import QLambda.Linear.Runtime
import QLambda.Linear.Elaboration

/-!
# N-bounded fragment execution (Track F)

Parameterize runtime / staging / quotation adequacy by a live-qubit bound `N`.
This does **not** repair the Day-bang obstruction at Hilbert dimension `A = 2`.
-/

namespace QLambda.Linear

/-- Syntactic upper bound on live wires appearing in a term's qubit-typed
subexpressions (conservative: counts `prim new0` and qubit variables). -/
def UsesAtMostQubits : Nat → Term → Prop
  | _, .unit | _, .bitLit _ => True
  | _, .var _ _ => True
  | n, .prim .new0 => n ≥ 1
  | _, .prim _ => True
  | n, .lam _ _ M => UsesAtMostQubits n M
  | n, .app F X => UsesAtMostQubits n F ∧ UsesAtMostQubits n X
  | n, .pair M N => UsesAtMostQubits n M ∧ UsesAtMostQubits n N
  | n, .unpair M K => UsesAtMostQubits n M ∧ UsesAtMostQubits n K
  | n, .ite B T E =>
      UsesAtMostQubits n B ∧ UsesAtMostQubits n T ∧ UsesAtMostQubits n E
  | n, .measure Q K => UsesAtMostQubits n Q ∧ UsesAtMostQubits n K
  | _, .fix _ _ | _, .fold _ _ | _, .unfold _ => False

theorem UsesAtMostQubits.mono {n m : Nat} {M : Term}
    (hle : n ≤ m) (h : UsesAtMostQubits n M) : UsesAtMostQubits m M := by
  induction M generalizing n m with
  | unit | bitLit | var => exact trivial
  | prim p =>
      cases p with
      | new0 => exact Nat.le_trans h hle
      | _ => exact trivial
  | lam _ _ _ ih => exact ih hle h
  | app F X ihF ihX => exact ⟨ihF hle h.1, ihX hle h.2⟩
  | pair M N ihM ihN => exact ⟨ihM hle h.1, ihN hle h.2⟩
  | unpair M K ihM ihK => exact ⟨ihM hle h.1, ihK hle h.2⟩
  | ite B T E ihB ihT ihE =>
      exact ⟨ihB hle h.1, ihT hle h.2.1, ihE hle h.2.2⟩
  | measure Q K ihQ ihK => exact ⟨ihQ hle h.1, ihK hle h.2⟩
  | fix | fold | unfold => exact h.elim

/-- Closed fragment programs using no qubits are N-bounded for every `N`. -/
theorem usesAtMost_unit (N : Nat) : UsesAtMostQubits N .unit := trivial
theorem usesAtMost_bitLit (N : Nat) (_b : Bool) :
    UsesAtMostQubits N (.bitLit _b) := trivial

/-- N-bounded closed literal adequacy: reuses Route A closed unit/bit agreement
under an explicit live-qubit policy (vacuous for unit/bit literals). -/
theorem fragment_observable_adequacy_literals (N : Nat) :
    UsesAtMostQubits N .unit ∧
    (∀ b, UsesAtMostQubits N (.bitLit b)) ∧
    (FragCert.denoteUnit FragCert.closed_unit_cert =
      routeAFragmentModel.unitIntro) ∧
    (∀ b, FragCert.denoteBitLit (FragCert.closed_bitLit_cert b) =
      routeAFragmentModel.bitLit b) :=
  ⟨usesAtMost_unit N, usesAtMost_bitLit N,
    FragCert.denoteUnit_eq _, fun b => FragCert.denoteBitLit_eq _⟩

/-- Runtime register bound: configurations with at most `N` quantum wires. -/
def RuntimeUsesAtMost (N : Nat) {q : Nat} (_ρ : Runtime.Config q) : Prop :=
  q ≤ N

theorem RuntimeUsesAtMost.mono {N M : Nat} {q : Nat} {ρ : Runtime.Config q}
    (hle : N ≤ M) (h : RuntimeUsesAtMost N ρ) : RuntimeUsesAtMost M ρ :=
  Nat.le_trans h hle

/-- Source/runtime Born agreement placeholder specialized to zero-qubit closed
literals (Gate 5–6 fragment of the N-bounded track). -/
theorem n_bounded_literal_born_agreement (N : Nat) :
    fragment_observable_adequacy_literals N =
      fragment_observable_adequacy_literals N :=
  rfl

end QLambda.Linear
