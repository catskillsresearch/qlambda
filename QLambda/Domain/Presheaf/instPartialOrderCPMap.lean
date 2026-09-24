/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.CPMap
import QLambda.Domain.Presheaf.instLECPMap

/-!
# Instance `instPartialOrderCPMap`
-/

namespace QLambda.Domain.Presheaf
namespace CPMap

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder
variable {n m ℓ r : ℕ}

instance instPartialOrderCPMap : PartialOrder (CPMap n m) where
  le_refl Φ := by
    change Φ.choi ≤ Φ.choi
    exact le_rfl
  le_trans Φ Ψ Χ hΦΨ hΨΧ := by
    change Φ.choi ≤ Χ.choi
    exact le_trans hΦΨ hΨΧ
  le_antisymm Φ Ψ hΦΨ hΨΦ := by
    apply ext
    exact le_antisymm hΦΨ hΨΦ

end CPMap
end QLambda.Domain.Presheaf
