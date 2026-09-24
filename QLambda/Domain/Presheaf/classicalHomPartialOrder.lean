/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.OmegaEnriched
import QLambda.Domain.Presheaf.unitHomPartialOrder

/-!
# Instance `classicalHomPartialOrder`
-/

set_option maxHeartbeats 800000
namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-- Pointwise Choi order transported along the closed pairing. -/
def ClassicalHomLE (M : Module) (N : BiorthogonalObject)
    (f g : Hom M N.module) : Prop :=
  UnitHomLE (dayTensor M (DayNegation.neg N.module))
    (closedPairingEquiv M N f) (closedPairingEquiv M N g)

noncomputable instance classicalHomPartialOrder
    (M : Module) (N : BiorthogonalObject) :
    PartialOrder (Hom M N.module) where
  le := ClassicalHomLE M N
  le_refl f := by
    intro n x
    exact le_rfl
  le_trans f g h hfg hgh := by
    intro n x
    exact (hfg n x).trans (hgh n x)
  le_antisymm f g hfg hgf := by
    apply (closedPairingEquiv M N).injective
    apply Hom.ext
    intro n x
    change
      (show Superoperator n 1 from
        (closedPairingEquiv M N f).app n x) =
        (show Superoperator n 1 from
          (closedPairingEquiv M N g).app n x)
    exact le_antisymm (hfg n x) (hgf n x)

end SuperoperatorModule
end QLambda.Domain.Presheaf
