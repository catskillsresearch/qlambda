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
public import QLambda.Domain.Presheaf.classicalHomOrderBot
public import QLambda.Domain.Presheaf.classicalHomOmegaComplete

@[expose] public section

/-!
# Instance `biorthogonalHomPartialOrder`
-/

set_option maxHeartbeats 800000
namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable instance biorthogonalHomPartialOrder
    (A B : BiorthogonalObject) :
    PartialOrder (ClassicalObject.Hom A B) :=
  classicalHomPartialOrder A.module B

end SuperoperatorModule
end QLambda.Domain.Presheaf
