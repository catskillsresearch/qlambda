/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Domain.Presheaf.OmegaEnriched
public import QLambda.Domain.Presheaf.instPartialOrderSuperoperator
public import QLambda.Domain.Presheaf.instOrderBotSuperoperator
public import QLambda.Domain.Presheaf.omegaComplete
public import QLambda.Domain.Presheaf.unitHomPartialOrder
public import QLambda.Domain.Presheaf.unitHomOrderBot
public import QLambda.Domain.Presheaf.unitHomOmegaComplete
public import QLambda.Domain.Presheaf.classicalHomPartialOrder

@[expose] public section

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
