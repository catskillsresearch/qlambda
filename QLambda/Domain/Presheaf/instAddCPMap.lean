/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.CPMap
import QLambda.Domain.Presheaf.instLECPMap
import QLambda.Domain.Presheaf.instPartialOrderCPMap
import QLambda.Domain.Presheaf.instZeroCPMap

/-!
# Instance `instAddCPMap`
-/

namespace QLambda.Domain.Presheaf
namespace CPMap

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder
variable {n m ℓ r : ℕ}

instance instAddCPMap : Add (CPMap n m) := ⟨add⟩

@[simp]
theorem choi_add (Φ Ψ : CPMap n m) :
    (Φ + Ψ).choi = Φ.choi + Ψ.choi :=
  rfl

end CPMap
end QLambda.Domain.Presheaf
