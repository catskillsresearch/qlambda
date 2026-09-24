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
cofree Day bang is not obtained from the Route A fiber analysis alone.  A
`BangComultDayTransferWitness` now kernel-checkably refutes Day component
admissibility; constructing that witness or finding a positive replacement
remains open.  Track L (`presheafQuantumLNL`, recursion, full adequacy) waits
on that resolution.
-/

namespace QLambda.Domain.Presheaf.SuperoperatorModule

/-- Gate 8: raw all-dimensional Day-bang carrier bound fails at one qubit. -/
theorem day_bang_raw_global_bound_fails_at_two :
    ¬ BangSplitEffectAdmissible 2 :=
  bangSplitEffectAdmissible_excludes_identity_two

/-- Positive low-dimensional bang components remain available. -/
theorem day_bang_components_ok_zero_one :
    BangComultComponentsAdmissible 0 ∧ BangComultComponentsAdmissible 1 :=
  ⟨bangComultComponentsAdmissible_zero, bangComultComponentsAdmissible_one⟩

/-- Architecture decision record: A≤1 bang is kernel-checked; A=2 raw global
bound fails; the Day transfer witness is the remaining bridge for a no-go or
positive repair of `BangComultComponentsAdmissible 2`. -/
def DayBangArchitectureBoundary : Prop :=
  BangComultComponentsAdmissible 0 ∧
  BangComultComponentsAdmissible 1 ∧
  ¬ BangSplitEffectAdmissible 2

theorem day_bang_architecture_boundary : DayBangArchitectureBoundary :=
  ⟨bangComultComponentsAdmissible_zero,
    bangComultComponentsAdmissible_one,
    bangSplitEffectAdmissible_excludes_identity_two⟩

/-- Track L is blocked on the A=2 Day-bang gate: without a positive
`BangComultComponentsAdmissible 2` (or a replacement category), a premise-free
`presheafQuantumLNL` cannot be assembled from the raw bang. -/
theorem trackL_requires_day_bang_resolution :
    DayBangArchitectureBoundary ∧
      (BangComultDayTransferWitness →
        ¬ BangComultComponentsAdmissible 2) :=
  ⟨day_bang_architecture_boundary,
    bangComultDayTransferWitness_not_admissible⟩

end QLambda.Domain.Presheaf.SuperoperatorModule

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule

/-- Route A fragment acceptance is independent of the A=2 Day-bang obstruction. -/
theorem routeA_independent_of_day_bang_two :
    RouteASucceeded ∧ ¬ BangSplitEffectAdmissible 2 :=
  ⟨routeA_succeeded, day_bang_raw_global_bound_fails_at_two⟩

end QLambda.Linear
