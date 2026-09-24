/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.CPMap
import QLambda.Domain.Presheaf.instLECPMap
import QLambda.Domain.Presheaf.instPartialOrderCPMap

/-!
# Instance `instZeroCPMap`
-/

namespace QLambda.Domain.Presheaf
namespace CPMap

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder
variable {n m ℓ r : ℕ}

instance instZeroCPMap : Zero (CPMap n m) := ⟨zero⟩

@[simp]
theorem choi_zero : (0 : CPMap n m).choi = 0 := by
  exact KrausFamily.choi_nil

end CPMap
end QLambda.Domain.Presheaf
