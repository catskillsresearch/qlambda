/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.OmegaEnriched
import QLambda.Domain.Presheaf.instPartialOrderSuperoperator

/-!
# Instance `unitHomPartialOrder`
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-- The pointwise Choi relation before it is bundled as an order. -/
def UnitHomLE (P : Module) (f g : Hom P dayTensorUnit) : Prop :=
  ∀ n x,
    (show Superoperator n 1 from f.app n x) ≤
      (show Superoperator n 1 from g.app n x)


noncomputable instance unitHomPartialOrder (P : Module) :
    PartialOrder (Hom P dayTensorUnit) where
  le := UnitHomLE P
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ hfg hgh n x := (hfg n x).trans (hgh n x)
  le_antisymm f g hfg hgf := by
    apply Hom.ext
    intro n x
    change
      (show Superoperator n 1 from f.app n x) =
        (show Superoperator n 1 from g.app n x)
    exact le_antisymm (hfg n x) (hgf n x)

end SuperoperatorModule
end QLambda.Domain.Presheaf
