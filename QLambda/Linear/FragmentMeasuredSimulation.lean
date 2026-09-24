/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentWeightedSimulation

/-!
# Measured register-history simulation (F5–F6)
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators

/-- Register-history identification: closed measured `new0` program under
`UsesAtMostQubits N`, with denotational `measureElim` spine and `|0⟩` Born
masses matching Instrument/CompletedCP packaging. -/
structure FragmentMeasuredSimulation (N : Nat)
    extends FragmentWeightedSimulation N where
  /-- Closed certificate for the measured allocation program. -/
  measured_cert : FragCert.Closed measureNew0Program .qubit
  /-- The measured program is N-bounded when allocation is admitted. -/
  uses_measured : 1 ≤ N → UsesAtMostQubits N measureNew0Program
  /-- Denotation expands as `measureElim ∘ map(denote Q, denote K) ∘ split`. -/
  denote_measured :
    FragCert.denote measured_cert =
      Hom.comp (FragCert.measureElim _)
        (Hom.comp
          (DayTensor.map
            (FragCert.denote fragCert_app_new0_unit)
            (FragCert.denote fragCert_measure_new0_cont))
          (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil))
  /-- Denotational measurement branches agree with Yoneda. -/
  measure_branch_yoneda :
    ∀ b, routeAFragmentModel.measureBranch b = measureBranchYoneda b
  /-- Runtime Born masses on the prepared `|0⟩` register. -/
  born_ketZero_false :
    1 ≤ N →
      Runtime.RegisterState.measureProbability registerKetZero (0 : Fin 1)
          false = 1
  born_ketZero_true :
    1 ≤ N →
      Runtime.RegisterState.measureProbability registerKetZero (0 : Fin 1)
          true = 0
  /-- Those Born masses equal Instrument branch traces. -/
  born_ketZero_instrument :
    ∀ b, 1 ≤ N →
      Runtime.RegisterState.measureProbability registerKetZero (0 : Fin 1) b =
        (Matrix.trace
          (((Instrument.measure (0 : Fin 1)).branchSuperoperator
              (if b then (1 : Fin 2) else 0)).cp.applyMat
            registerKetZero.mat)).re

/-- Every `N` supplies a measured register-history simulation package. -/
noncomputable def fragmentMeasuredSimulation (N : Nat) :
    FragmentMeasuredSimulation N where
  toFragmentWeightedSimulation := fragmentWeightedSimulation N
  measured_cert := closed_measure_new0_cert
  uses_measured := fun hN =>
    UsesAtMostQubits.mono hN usesAtMost_measure_new0_cont
  denote_measured := denote_closed_measure_new0
  measure_branch_yoneda := fragment_measStep_denote_sound_branch
  born_ketZero_false := fun _ => measureProbability_registerKetZero_false
  born_ketZero_true := fun _ => measureProbability_registerKetZero_true
  born_ketZero_instrument := fun b _ =>
    measureProbability_eq_instrument_branch_trace registerKetZero b


end QLambda.Linear
