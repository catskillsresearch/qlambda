/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumFunction

/-!
# Instance `instLEQuantumFunction`
-/

namespace QLambda.Domain
namespace QuantumFunction

instance instLEQuantumFunction {P Q : QuantumPoset} : LE (QuantumFunction P Q) where
  le F G := G.rel ≤ Q.order.comp F.rel

end QuantumFunction
end QLambda.Domain
