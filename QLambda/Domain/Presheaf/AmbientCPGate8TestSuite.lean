/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.DayBangBoundary

/-!
# Ambient-CP Gate-8 acceptance suite
-/

namespace QLambda.Domain.Presheaf.SuperoperatorModule

/-- Gate-8 acceptance suite for `AmbientCPDayBangCategory`. -/
structure AmbientCPGate8TestSuite : Prop where
  category : AmbientCPDayBangCategory
  transfer_needs_nonadditive :
    BangComultDayTransferWitness →
      ∃ L : Module.{0},
        ¬ Fiber.HasSumAdd (L.obj (tensorPowerDimension 2 1))
  cpm_pair_summable :
    ∀ (B : ℕ)
      (z₀₁ z₁₀ :
        ((cpmModule B).obj (tensorPowerDimension 2 1)).Carrier),
      ∃ Φ :
        ((cpmModule B).obj (tensorPowerDimension 2 1)).Carrier,
      ((cpmModule B).obj (tensorPowerDimension 2 1)).HasSum
        (fun i : Bool => bif i then z₀₁ else z₁₀) Φ
  raw_bound_still_fails : ¬ BangSplitEffectAdmissible 2
  le_one_components_ok :
    BangComultComponentsAdmissible 0 ∧ BangComultComponentsAdmissible 1
  transfer_implies_inadmissible :
    BangComultDayTransferWitness → ¬ BangComultComponentsAdmissible 2

theorem ambientCP_gate8_testSuite : AmbientCPGate8TestSuite where
  category := ambientCPDayBangCategory
  transfer_needs_nonadditive :=
    bangComultDayTransferWitness_requires_nonadditive_target
  cpm_pair_summable := cpm_target_cannot_supply_day_transfer_pair
  raw_bound_still_fails := day_bang_raw_global_bound_fails_at_two
  le_one_components_ok := day_bang_components_ok_zero_one
  transfer_implies_inadmissible :=
    bangComultDayTransferWitness_not_admissible

/-- L8 terminal theorem: architecture boundary plus ambient-CP Gate-8 suite. -/
theorem day_bang_l8_resolved_by_ambientCP_replacement :
    DayBangArchitectureBoundary ∧
      AmbientCPGate8TestSuite ∧
      (BangComultDayTransferWitness →
        ¬ BangComultComponentsAdmissible 2) :=
  ⟨day_bang_architecture_boundary,
    ambientCP_gate8_testSuite,
    bangComultDayTransferWitness_not_admissible⟩


end QLambda.Domain.Presheaf.SuperoperatorModule
