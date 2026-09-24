/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.QuantumRel
import QLambda.Domain.instLEQuantumRel
import QLambda.Domain.instPartialOrderQuantumRel
import QLambda.Domain.instBotQuantumRel

/-!
# Instance `instTopQuantumRel`
-/

namespace QLambda.Domain
namespace QuantumRel

open Matrix
variable {X Y Z W : QuantumSet}

instance instTopQuantumRel : Top (QuantumRel X Y) := ⟨top⟩

end QuantumRel
end QLambda.Domain
