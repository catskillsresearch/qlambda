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
import QLambda.Domain.Presheaf.instAddCommMonoidCPMap

/-!
# Instance `instOrderBotCPMap`
-/

namespace QLambda.Domain.Presheaf
namespace CPMap

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder
variable {n m ℓ r : ℕ}

instance instOrderBotCPMap : OrderBot (CPMap n m) where
  bot := 0
  bot_le Φ := by
    change (0 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) ≤ Φ.choi
    rw [Matrix.le_iff]
    simpa using Φ.choi_pos

end CPMap
end QLambda.Domain.Presheaf
