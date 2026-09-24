/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Comonoid
import QLambda.Linear.FragmentModel

/-!
# Day-bang architecture boundary (Gate 8)

The raw global split-effect bound fails at `A = 2`, so an all-dimensional
cofree Day bang is not obtained from the Route A fiber analysis alone.
`BangComultDayTransferWitness` kernel-checkably implies
`¬ BangComultComponentsAdmissible 2`, but no TNI/representable construction of
that witness is given (projection pairs recover one ordering; products
separate summands; unscaled addition of both orderings leaves the TNI
carrier).

**L8 terminal route (4):** the smallest named replacement category is
`AmbientCPDayBangCategory` — specialized modules with unrestricted-CP fibers
(`cpmModule`).  It restores `Fiber.HasSumAdd` and `HasActSumFromDim`, so it
cannot host the nonsummable Bool pair required by a Day-transfer witness.
The Gate-8 suite `ambientCP_gate8_testSuite` packages the acceptance checks.
Track L packages remain deferred until a bang/comonoid is rebuilt in that
(or another) replacement; Route A fragment work is independent.
-/

namespace QLambda.Domain.Presheaf.SuperoperatorModule

set_option maxHeartbeats 8000000

/-- Gate 8: raw all-dimensional Day-bang carrier bound fails at one qubit. -/
theorem day_bang_raw_global_bound_fails_at_two :
    ¬ BangSplitEffectAdmissible 2 :=
  bangSplitEffectAdmissible_excludes_identity_two

/-- Positive low-dimensional bang components remain available. -/
theorem day_bang_components_ok_zero_one :
    BangComultComponentsAdmissible 0 ∧ BangComultComponentsAdmissible 1 :=
  ⟨bangComultComponentsAdmissible_zero, bangComultComponentsAdmissible_one⟩

/-- Architecture decision record: A≤1 bang is kernel-checked; A=2 raw global
bound fails; Day transfer into TNI Day admissibility is not constructed. -/
def DayBangArchitectureBoundary : Prop :=
  BangComultComponentsAdmissible 0 ∧
  BangComultComponentsAdmissible 1 ∧
  ¬ BangSplitEffectAdmissible 2

theorem day_bang_architecture_boundary : DayBangArchitectureBoundary :=
  ⟨bangComultComponentsAdmissible_zero,
    bangComultComponentsAdmissible_one,
    bangSplitEffectAdmissible_excludes_identity_two⟩

/-- Conditional TNI no-go bridge (witness not constructed). -/
theorem trackL_requires_day_bang_resolution :
    DayBangArchitectureBoundary ∧
      (BangComultDayTransferWitness →
        ¬ BangComultComponentsAdmissible 2) :=
  ⟨day_bang_architecture_boundary,
    bangComultDayTransferWitness_not_admissible⟩

/-! ## L8 replacement: ambient CP Day-bang category -/

/-- Smallest named replacement category for the A=2 Day-bang gate:
specialized modules whose fibers are unrestricted CP maps (`cpmModule`),
with Bool-add and joint action at every dimension. -/
def AmbientCPDayBangCategory : Prop :=
  (∀ B n : ℕ, Fiber.HasSumAdd ((cpmModule B).obj n)) ∧
  (∀ B : ℕ, HasActSumFromDim (cpmModule B))

theorem ambientCPDayBangCategory : AmbientCPDayBangCategory :=
  ⟨fun B n => Fiber.HasSumAdd.cpmModule B n,
    fun B => HasActSumFromDim.cpmModule B⟩

/-- Ambient-CP fibers always admit the Bool pair demanded by the witness. -/
theorem cpm_target_cannot_supply_day_transfer_pair
    (B : ℕ)
    (z₀₁ z₁₀ :
      ((cpmModule B).obj (tensorPowerDimension 2 1)).Carrier) :
    ∃ Φ :
      ((cpmModule B).obj (tensorPowerDimension 2 1)).Carrier,
      ((cpmModule B).obj (tensorPowerDimension 2 1)).HasSum
        (fun i : Bool => bif i then z₀₁ else z₁₀) Φ :=
  Fiber.HasSumAdd.cpmModule B _ z₀₁ z₁₀

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

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule

/-- Route A fragment acceptance is independent of the A=2 Day-bang obstruction. -/
theorem routeA_independent_of_day_bang_two :
    RouteASucceeded ∧ ¬ BangSplitEffectAdmissible 2 :=
  ⟨routeA_succeeded, day_bang_raw_global_bound_fails_at_two⟩

end QLambda.Linear
