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
import QLambda.Domain.instSemilatticeSupQuantumRel
import QLambda.Domain.instLatticeQuantumRel

/-!
# Instance `instBoundedOrderQuantumRel`
-/

namespace QLambda.Domain
namespace QuantumRel

open Matrix
variable {X Y Z W : QuantumSet}

instance instBoundedOrderQuantumRel : BoundedOrder (QuantumRel X Y) where
  le_top := fun _ _ _ => le_top
  bot_le := fun _ _ _ => bot_le

end QuantumRel
end QLambda.Domain
