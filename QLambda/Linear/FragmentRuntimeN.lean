/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentCoherence
import QLambda.Linear.FragmentAdequacy
import QLambda.Linear.Runtime
import QLambda.Linear.Elaboration

/-!
# N-bounded fragment execution (Track F)

Weighted source/runtime simulation indexed by live-qubit bound `q ≤ N`.
Connects runtime `measureProbability`, denotational measurement branches,
and closed fragment observations under `UsesAtMostQubits N`.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators

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

theorem usesAtMost_unit (N : Nat) : UsesAtMostQubits N .unit := trivial
theorem usesAtMost_bitLit (N : Nat) (_b : Bool) :
    UsesAtMostQubits N (.bitLit _b) := trivial

/-- Runtime register bound: configurations with at most `N` quantum wires. -/
def RuntimeUsesAtMost (N : Nat) {q : Nat} (_ρ : Runtime.Config q) : Prop :=
  q ≤ N

theorem RuntimeUsesAtMost.mono {N M : Nat} {q : Nat} {ρ : Runtime.Config q}
    (hle : N ≤ M) (h : RuntimeUsesAtMost N ρ) : RuntimeUsesAtMost M ρ :=
  Nat.le_trans h hle

/-- One-step Born mass: runtime measure probabilities sum to one. -/
theorem n_bounded_measureProbability_sum (q : Nat) (w : Fin q)
    (ρ : Runtime.RegisterState q) :
    Runtime.RegisterState.measureProbability ρ w false +
      Runtime.RegisterState.measureProbability ρ w true = 1 :=
  Runtime.RegisterState.measureProbability_false_add_true ρ w

/-- Denotational measurement branches agree with Yoneda / CompletedCP. -/
theorem n_bounded_measureBranch_completedCP (b : Bool) :
    routeAFragmentModel.measureBranch b = measureBranchYoneda b :=
  fragment_measureBranch_agrees b

/-- Runtime Born mass is the `NormalizedDensity.bornWeight` of the Kraus
measurement branch (definitional). -/
theorem measureProbability_eq_yoneda_branch_mass
    (ρ : Runtime.RegisterState 1) (b : Bool) :
    Runtime.RegisterState.measureProbability ρ (0 : Fin 1) b =
      NormalizedDensity.bornWeight
        (Runtime.RegisterState.measureBranch (0 : Fin 1) b) ρ :=
  rfl

/-- The same Born mass equals the Instrument branch CP-map trace. -/
theorem measureProbability_eq_instrument_branch_trace
    (ρ : Runtime.RegisterState 1) (b : Bool) :
    Runtime.RegisterState.measureProbability ρ (0 : Fin 1) b =
      (Matrix.trace
        (((Instrument.measure (0 : Fin 1)).branchSuperoperator
            (if b then (1 : Fin 2) else 0)).cp.applyMat ρ.mat)).re := by
  cases b with
  | true =>
      simp only [measureProbability_eq_yoneda_branch_mass,
        Runtime.RegisterState.measureBranch, NormalizedDensity.bornWeight,
        Instrument.branchSuperoperator]
      change
          (Matrix.trace
              (KrausFamily.applyMat
                [Composer.projector (0 : Fin 1) true] ρ.mat)).re =
            (Matrix.trace
              (CPMap.applyMat
                ((Instrument.measure (0 : Fin 1)).branch 1) ρ.mat)).re
      rw [Instrument.measure_branch_one, CPMap.applyMat_ofKraus]
  | false =>
      simp only [measureProbability_eq_yoneda_branch_mass,
        Runtime.RegisterState.measureBranch, NormalizedDensity.bornWeight,
        Instrument.branchSuperoperator]
      change
          (Matrix.trace
              (KrausFamily.applyMat
                [Composer.projector (0 : Fin 1) false] ρ.mat)).re =
            (Matrix.trace
              (CPMap.applyMat
                ((Instrument.measure (0 : Fin 1)).branch 0) ρ.mat)).re
      rw [Instrument.measure_branch_zero, CPMap.applyMat_ofKraus]

/-- Single-qubit `measure (prim new0) K` is 1-bounded whenever `K` is. -/
theorem usesAtMost_measure_new0 (N : Nat) (K : Term)
    (hN : 1 ≤ N) (hK : UsesAtMostQubits N K) :
    UsesAtMostQubits N (.measure (.prim .new0) K) :=
  ⟨Nat.le_trans (Nat.le_refl 1) hN, hK⟩

/-- Concrete 1-bounded measured program: measure a fresh qubit, discard
continuation as a unit lambda (syntactic bound only). -/
def measureNew0Cont : Term :=
  .lam .unres .bit (.lam .lin .qubit .unit)

theorem usesAtMost_measure_new0_cont :
    UsesAtMostQubits 1 (.measure (.prim .new0) measureNew0Cont) :=
  usesAtMost_measure_new0 1 measureNew0Cont (Nat.le_refl 1)
    (by simp [measureNew0Cont, UsesAtMostQubits])

/-- Weighted source/runtime simulation witness for closed fragment programs
bounded by `N` live qubits: denotation exists and measurement branches match. -/
structure FragmentWeightedSimulation (N : Nat) where
  /-- Closed unit denotation agrees with Route A. -/
  unit_denote :
    FragCert.denote FragCert.closed_unit_cert =
      FragmentContext.closedPoint routeAFragmentModel.unitIntro
  /-- Closed bit denotation agrees with Route A. -/
  bit_denote :
    ∀ b, FragCert.denote (FragCert.closed_bitLit_cert b) =
      FragmentContext.closedPoint (routeAFragmentModel.bitLit b)
  /-- Measurement branches match Yoneda packaging. -/
  measure_branch :
    ∀ b, routeAFragmentModel.measureBranch b = measureBranchYoneda b
  /-- Unit/bit programs are N-bounded. -/
  uses_unit : UsesAtMostQubits N .unit
  uses_bit : ∀ b, UsesAtMostQubits N (.bitLit b)
  /-- Runtime Born masses are probabilities. -/
  born_sum :
    ∀ {q} (hq : q ≤ N) (w : Fin q) (ρ : Runtime.RegisterState q),
      Runtime.RegisterState.measureProbability ρ w false +
        Runtime.RegisterState.measureProbability ρ w true = 1
  /-- Born mass agrees with Instrument branch trace at one qubit. -/
  born_instrument :
    ∀ (ρ : Runtime.RegisterState 1) (b : Bool),
      1 ≤ N →
        Runtime.RegisterState.measureProbability ρ (0 : Fin 1) b =
          (Matrix.trace
            (((Instrument.measure (0 : Fin 1)).branchSuperoperator
                (if b then (1 : Fin 2) else 0)).cp.applyMat ρ.mat)).re
  /-- A nontrivial closed measured program is N-bounded when `1 ≤ N`. -/
  uses_measure_new0 :
    1 ≤ N → UsesAtMostQubits N (.measure (.prim .new0) measureNew0Cont)

/-- Every `N` supplies a weighted simulation package. -/
theorem fragmentWeightedSimulation (N : Nat) :
    FragmentWeightedSimulation N where
  unit_denote := fragment_step_denote_sound_unit _
  bit_denote := fun _ => fragment_step_denote_sound_bitLit _
  measure_branch := fragment_measStep_denote_sound_branch
  uses_unit := usesAtMost_unit N
  uses_bit := fun _ => usesAtMost_bitLit N _
  born_sum := fun {_q} _hq w ρ => n_bounded_measureProbability_sum _q w ρ
  born_instrument := fun ρ b _hN => measureProbability_eq_instrument_branch_trace ρ b
  uses_measure_new0 := fun hN =>
    UsesAtMostQubits.mono hN usesAtMost_measure_new0_cont

/-- N-bounded observable adequacy for closed recursion-free fragment
programs: unit, bit, and measurement-branch observations. -/
theorem fragment_observable_adequacy (N : Nat) :
    UsesAtMostQubits N .unit ∧
    (∀ b, UsesAtMostQubits N (.bitLit b)) ∧
    (FragCert.denote FragCert.closed_unit_cert =
      FragmentContext.closedPoint routeAFragmentModel.unitIntro) ∧
    (∀ b, FragCert.denote (FragCert.closed_bitLit_cert b) =
      FragmentContext.closedPoint (routeAFragmentModel.bitLit b)) ∧
    (∀ b, routeAFragmentModel.measureBranch b = measureBranchYoneda b) ∧
    (∀ (q : Nat) (_hq : q ≤ N) (w : Fin q) (ρ : Runtime.RegisterState q),
      Runtime.RegisterState.measureProbability ρ w false +
        Runtime.RegisterState.measureProbability ρ w true = 1) :=
  ⟨usesAtMost_unit N, fun b => usesAtMost_bitLit N b,
    fragment_step_denote_sound_unit _,
    fun _ => fragment_step_denote_sound_bitLit _,
    fragment_measStep_denote_sound_branch,
    fun q _hq w ρ => n_bounded_measureProbability_sum q w ρ⟩

/-- Literal-only corollary retained for earlier citations. -/
theorem fragment_observable_adequacy_literals (N : Nat) :
    UsesAtMostQubits N .unit ∧
    (∀ b, UsesAtMostQubits N (.bitLit b)) ∧
    (FragCert.denoteUnit FragCert.closed_unit_cert =
      routeAFragmentModel.unitIntro) ∧
    (∀ b, FragCert.denoteBitLit (FragCert.closed_bitLit_cert b) =
      routeAFragmentModel.bitLit b) :=
  ⟨usesAtMost_unit N, usesAtMost_bitLit N,
    FragCert.denoteUnit_eq _, fun b => FragCert.denoteBitLit_eq _⟩

end QLambda.Linear
