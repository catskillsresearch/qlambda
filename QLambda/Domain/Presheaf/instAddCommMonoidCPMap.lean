/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.CPMap
import QLambda.Domain.Presheaf.instLECPMap
import QLambda.Domain.Presheaf.instPartialOrderCPMap
import QLambda.Domain.Presheaf.instZeroCPMap
import QLambda.Domain.Presheaf.instAddCPMap

/-!
# Instance `instAddCommMonoidCPMap`
-/

namespace QLambda.Domain.Presheaf
namespace CPMap

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder
variable {n m ℓ r : ℕ}

instance instAddCommMonoidCPMap : AddCommMonoid (CPMap n m) where
  zero := 0
  add := (· + ·)
  zero_add Φ := ext (zero_add Φ.choi)
  add_zero Φ := ext (add_zero Φ.choi)
  add_assoc Φ Ψ Χ := ext (add_assoc Φ.choi Ψ.choi Χ.choi)
  add_comm Φ Ψ := ext (add_comm Φ.choi Ψ.choi)
  nsmul := nsmulRec

end CPMap
end QLambda.Domain.Presheaf
