/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentRuntimeCore
import QLambda.Domain.Presheaf.SuperoperatorInstrument

/-!
# Weighted N-bounded fragment simulation
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators

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
    ∀ {q} (_hq : q ≤ N) (w : Fin q) (ρ : Runtime.RegisterState q),
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
    1 ≤ N → UsesAtMostQubits N measureNew0Program

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


end QLambda.Linear
