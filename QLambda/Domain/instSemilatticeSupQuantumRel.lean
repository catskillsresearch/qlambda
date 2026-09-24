/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.QuantumRel
import QLambda.Domain.instLEQuantumRel
import QLambda.Domain.instPartialOrderQuantumRel
import QLambda.Domain.instBotQuantumRel
import QLambda.Domain.instTopQuantumRel
import QLambda.Domain.instInfSetQuantumRel
import QLambda.Domain.instSupSetQuantumRel
import QLambda.Domain.instSemilatticeInfQuantumRel

/-!
# Instance `instSemilatticeSupQuantumRel`
-/

namespace QLambda.Domain
namespace QuantumRel

open Matrix
variable {X Y Z W : QuantumSet}

instance instSemilatticeSupQuantumRel : SemilatticeSup (QuantumRel X Y) where
  sup R S := ⟨fun x y => R.component x y ⊔ S.component x y⟩
  le_sup_left := fun _ _ _ _ => le_sup_left
  le_sup_right := fun _ _ _ _ => le_sup_right
  sup_le := fun _ _ _ hR hS x y => sup_le (hR x y) (hS x y)

end QuantumRel
end QLambda.Domain
