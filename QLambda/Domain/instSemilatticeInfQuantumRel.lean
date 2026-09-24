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

/-!
# Instance `instSemilatticeInfQuantumRel`
-/

namespace QLambda.Domain
namespace QuantumRel

open Matrix
variable {X Y Z W : QuantumSet}

instance instSemilatticeInfQuantumRel : SemilatticeInf (QuantumRel X Y) where
  inf R S := ⟨fun x y => R.component x y ⊓ S.component x y⟩
  inf_le_left := fun _ _ _ _ => inf_le_left
  inf_le_right := fun _ _ _ _ => inf_le_right
  le_inf := fun _ _ _ hR hS x y => le_inf (hR x y) (hS x y)

end QuantumRel
end QLambda.Domain
