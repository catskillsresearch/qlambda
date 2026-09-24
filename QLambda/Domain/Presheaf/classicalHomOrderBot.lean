/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.OmegaEnriched
import QLambda.Domain.Presheaf.instPartialOrderSuperoperator
import QLambda.Domain.Presheaf.instOrderBotSuperoperator
import QLambda.Domain.Presheaf.omegaComplete
import QLambda.Domain.Presheaf.unitHomPartialOrder
import QLambda.Domain.Presheaf.unitHomOrderBot
import QLambda.Domain.Presheaf.unitHomOmegaComplete
import QLambda.Domain.Presheaf.classicalHomPartialOrder

/-!
# Instance `classicalHomOrderBot`
-/

set_option maxHeartbeats 800000
namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable instance classicalHomOrderBot
    (M : Module) (N : BiorthogonalObject) :
    OrderBot (Hom M N.module) where
  bot := 0
  bot_le f := by
    intro n x
    have hz := closedPairingEquiv_zero M N
    change
      (show Superoperator n 1 from
        (closedPairingEquiv M N 0).app n x) ≤
        (show Superoperator n 1 from
          (closedPairingEquiv M N f).app n x)
    rw [hz]
    exact bot_le

end SuperoperatorModule
end QLambda.Domain.Presheaf
