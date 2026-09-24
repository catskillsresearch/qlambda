/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.ScottFunction
import QLambda.Domain.instCoeScottFunction

/-!
# Instance `instLEScottFunction`
-/

namespace QLambda.Domain
namespace ScottFunction

instance instLEScottFunction {P Q : QuantumCPO} : LE (ScottFunction P Q) where
  le F G := F.toQuantumFunction ≤ G.toQuantumFunction

end ScottFunction
end QLambda.Domain
