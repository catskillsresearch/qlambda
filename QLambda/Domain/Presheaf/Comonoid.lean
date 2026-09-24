/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Exponential
import QLambda.Domain.Presheaf.DayCoend

/-!
# Abstract commutative Day comonoids
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

set_option maxHeartbeats 8000000

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-! ## Abstract commutative comonoids -/

/-- A commutative comonoid in specialized modules, with comultiplication
landing in the genuine Day tensor. -/
structure Comonoid where
  carrier : Module
  counit : Hom carrier dayTensorUnit
  comult : Hom carrier (dayTensor carrier carrier)
  left_counit :
    Hom.comp (DayTensor.leftUnitor carrier)
        (Hom.comp (DayTensor.map counit (Hom.id carrier)) comult) =
      Hom.id carrier
  right_counit :
    Hom.comp (DayTensor.rightUnitor carrier)
        (Hom.comp (DayTensor.map (Hom.id carrier) counit) comult) =
      Hom.id carrier
  coassociative :
    Hom.comp (DayTensor.associator carrier carrier carrier)
        (Hom.comp (DayTensor.map comult (Hom.id carrier)) comult) =
      Hom.comp (DayTensor.map (Hom.id carrier) comult) comult
  cocommutative :
    Hom.comp (DayTensor.braiding carrier carrier) comult = comult


end SuperoperatorModule

end QLambda.Domain.Presheaf
