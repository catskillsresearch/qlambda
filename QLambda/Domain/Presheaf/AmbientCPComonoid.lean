/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.AmbientCPBangAdmissible

/-!
# Ambient-CP comonoid packaging (`A ≤ 1`)
-/

namespace QLambda.Domain.Presheaf.SuperoperatorModule

set_option maxHeartbeats 8000000

/-- Ambient-CP relative packaging of a Day comonoid.  `AmbientCPModule`
constrains bilinear *targets*, not the comonoid carrier; this wrapper lifts
absolute `bangComonoid` into the L9 relative interface. -/
structure AmbientCPComonoid where
  carrier : Module
  toComonoid : Comonoid
  carrier_eq : toComonoid.carrier = carrier

/-- Absolute bang comonoid for `A ≤ 1`, packaged as `AmbientCPComonoid`. -/
noncomputable def ambientCPBangComonoid (A : ℕ) (hA : A ≤ 1) :
    AmbientCPComonoid where
  carrier := bang A
  toComonoid := bangComonoid A hA
  carrier_eq := rfl

theorem ambientCPBangComonoid_of_le_one (A : ℕ) (hA : A ≤ 1) :
    Nonempty AmbientCPComonoid :=
  ⟨ambientCPBangComonoid A hA⟩

/-- Low-dimensional absolute bang comonoids remain available. -/
theorem bangComonoid_nonempty_of_le_one (A : ℕ) (hA : A ≤ 1) :
    Nonempty Comonoid :=
  ⟨bangComonoid A hA⟩

/-- L9 positive packaging: ambient-CP relative comonoids for every `A ≤ 1`. -/
theorem day_bang_l9_ambientCP_comonoid_le_one :
    (∀ A ≤ 1, Nonempty AmbientCPComonoid) ∧
      BangComultAmbientCPAdmissible 0 ∧
      BangComultAmbientCPAdmissible 1 :=
  ⟨ambientCPBangComonoid_of_le_one,
    bangComultAmbientCPAdmissible_zero,
    bangComultAmbientCPAdmissible_one⟩

/-- L9 row-glue status: degree-row gate at 2, precise rectangle no-go at 2,
`A ≤ 1` AmbientCP comonoids, absolute A=2 not claimed.  Glued
`BangComultAmbientCPAdmissible 2` remains deferred (alternative glue not
constructed). -/
theorem day_bang_l9_ambientCP_row_glue_deferred :
    BangComultAmbientCPDegreeRowAdmissible 2 ∧
      ¬ BangDegreeUnitRectangleHasSum 2 ∧
      (∀ A ≤ 1, Nonempty AmbientCPComonoid) ∧
      ((BangComultDayTransferWitness →
          ¬ BangComultComponentsAdmissible 2) ∧
        (∀ A, BangComultComponentsAdmissible A →
          BangComultAmbientCPAdmissible A)) :=
  ⟨bangComultAmbientCP_degree_row_admissible_two,
    not_bangDegreeUnitRectangleHasSum_two,
    ambientCPBangComonoid_of_le_one,
    day_bang_l9_absolute_bangComult_two_not_claimed⟩

end QLambda.Domain.Presheaf.SuperoperatorModule
