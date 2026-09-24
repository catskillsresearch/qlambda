/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentRuntimeCore
import QLambda.Linear.FragmentWeightedSimulation
import QLambda.Linear.FragmentMeasuredSimulation

/-!
# N-bounded fragment execution (Track F)

Barrel: core runtime lemmas, `FragmentWeightedSimulation`, and
`FragmentMeasuredSimulation`, plus observable-adequacy packaging.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators

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

/-- Measured-program adequacy: closed `measureNew0Program` under
`UsesAtMostQubits`, `measureElim` spine, and `|0⟩` Born masses. -/
theorem fragment_measured_observable_adequacy (N : Nat) (hN : 1 ≤ N) :
    UsesAtMostQubits N measureNew0Program ∧
    (FragCert.denote closed_measure_new0_cert =
      Hom.comp (FragCert.measureElim _)
        (Hom.comp
          (DayTensor.map
            (FragCert.denote fragCert_app_new0_unit)
            (FragCert.denote fragCert_measure_new0_cont))
          (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil))) ∧
    Runtime.RegisterState.measureProbability registerKetZero (0 : Fin 1)
        false = 1 ∧
    Runtime.RegisterState.measureProbability registerKetZero (0 : Fin 1)
        true = 0 ∧
    (∀ b, routeAFragmentModel.measureBranch b = measureBranchYoneda b) :=
  ⟨UsesAtMostQubits.mono hN usesAtMost_measure_new0_cont,
    denote_closed_measure_new0,
    measureProbability_registerKetZero_false,
    measureProbability_registerKetZero_true,
    fragment_measStep_denote_sound_branch⟩

/-- Literal-only corollary retained for earlier citations. -/
theorem fragment_observable_adequacy_literals (N : Nat) :
    UsesAtMostQubits N .unit ∧
    (∀ b, UsesAtMostQubits N (.bitLit b)) ∧
    (FragCert.denoteUnit FragCert.closed_unit_cert =
      routeAFragmentModel.unitIntro) ∧
    (∀ b, FragCert.denoteBitLit (FragCert.closed_bitLit_cert b) =
      routeAFragmentModel.bitLit b) :=
  ⟨usesAtMost_unit N, fun b => usesAtMost_bitLit N b,
    FragCert.denoteUnit_eq _, fun _ => FragCert.denoteBitLit_eq _⟩

end QLambda.Linear
