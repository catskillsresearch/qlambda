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

/-!
# Instance `instLatticeQuantumRel`
-/

namespace QLambda.Domain
namespace QuantumRel

open Matrix
variable {X Y Z W : QuantumSet}

instance instLatticeQuantumRel : Lattice (QuantumRel X Y) where

end QuantumRel
end QLambda.Domain
