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
import QLambda.Domain.Presheaf.classicalHomOrderBot
import QLambda.Domain.Presheaf.classicalHomOmegaComplete
import QLambda.Domain.Presheaf.biorthogonalHomPartialOrder
import QLambda.Domain.Presheaf.biorthogonalHomOrderBot

/-!
# Instance `biorthogonalHomOmegaComplete`
-/

set_option maxHeartbeats 800000
namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable instance biorthogonalHomOmegaComplete
    (A B : BiorthogonalObject) :
    QLambda.Domain.OmegaComplete (ClassicalObject.Hom A B) :=
  classicalHomOmegaComplete A.module B

end SuperoperatorModule
end QLambda.Domain.Presheaf
