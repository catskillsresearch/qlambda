/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.ScottFunction

/-!
# Instance `instCoeScottFunction`
-/

namespace QLambda.Domain
namespace ScottFunction

instance instCoeScottFunction {P Q : QuantumCPO} : Coe (ScottFunction P Q)
    (QuantumFunction P.poset Q.poset) :=
  ⟨ScottFunction.toQuantumFunction⟩

end ScottFunction
end QLambda.Domain
