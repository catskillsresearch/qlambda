/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.KrausFamily

/-!
# Instance `instIsPreorderResidualRefines`
-/

namespace QLambda
namespace KrausFamily

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder
variable {n m : ℕ}

instance instIsPreorderResidualRefines :
    IsPreorder (KrausFamily n m) ResidualRefines where
  refl := residualRefines_refl
  trans _ _ _ := residualRefines_trans

end KrausFamily
end QLambda
