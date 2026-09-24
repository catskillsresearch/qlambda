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

/-!
# Instance `instSupSetQuantumRel`
-/

namespace QLambda.Domain
namespace QuantumRel

open Matrix
variable {X Y Z W : QuantumSet}

instance instSupSetQuantumRel : SupSet (QuantumRel X Y) where
  sSup s := ⟨fun x y => ⨆ R : s, R.1.component x y⟩

end QuantumRel
end QLambda.Domain
