/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.AmbientCPBang
import QLambda.Linear.FragmentModel

/-!
# Day-bang architecture boundary (Gate 8 / L9)

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

**L9 (relative AmbientCP):** `AmbientCPModule` / `BangComultAmbientCPAdmissible`
in `AmbientCPBang.lean`.  Full relative admissibility is closed for `A ≤ 1`;
every dimension admits ambient-CP degree-row sums
(`bangComultAmbientCP_degree_row_hasSum`); `AmbientCPComonoid` packages
absolute `bangComonoid` for `A ≤ 1`.  A=1-style row→`ℕ×ℕ` glue is blocked by
`¬ BangDegreeUnitRectangleHasSum 2` (`day_bang_l9_ambientCP_row_glue_deferred`).
Glued `BangComultAmbientCPAdmissible 2` and L10–L12 LNL remain deferred;
absolute `BangComultComponentsAdmissible 2` is not claimed.
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


/-! ## L9: relative AmbientCP bang admissibility -/

/-- L9 acceptance (relative AmbientCP, positive): Gate-8 category, relative
admissibility for `A ≤ 1`, ambient-CP degree-row gate at `A = 2`,
`AmbientCPComonoid` packaging for `A ≤ 1`, and the precise rectangle no-go
blocking A=1-style glue at 2.  Absolute `BangComultComponentsAdmissible 2` and
glued `BangComultAmbientCPAdmissible 2` remain deferred (see
`day_bang_l9_ambientCP_row_glue_deferred`). -/
theorem day_bang_l9_ambientCP_bang_admissible :
    AmbientCPDayBangCategory ∧
      BangComultAmbientCPAdmissible 0 ∧
      BangComultAmbientCPAdmissible 1 ∧
      BangComultAmbientCPDegreeRowAdmissible 2 ∧
      ¬ BangDegreeUnitRectangleHasSum 2 ∧
      (∀ A ≤ 1, Nonempty AmbientCPComonoid) ∧
      ((BangComultDayTransferWitness →
          ¬ BangComultComponentsAdmissible 2) ∧
        (∀ A, BangComultComponentsAdmissible A →
          BangComultAmbientCPAdmissible A)) :=
  ⟨ambientCPDayBangCategory,
    bangComultAmbientCPAdmissible_zero,
    bangComultAmbientCPAdmissible_one,
    bangComultAmbientCP_degree_row_admissible_two,
    not_bangDegreeUnitRectangleHasSum_two,
    ambientCPBangComonoid_of_le_one,
    day_bang_l9_absolute_bangComult_two_not_claimed⟩

end QLambda.Domain.Presheaf.SuperoperatorModule

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule

/-- Route A fragment acceptance is independent of the A=2 Day-bang obstruction. -/
theorem routeA_independent_of_day_bang_two :
    RouteASucceeded ∧ ¬ BangSplitEffectAdmissible 2 :=
  ⟨routeA_succeeded, day_bang_raw_global_bound_fails_at_two⟩

end QLambda.Linear
