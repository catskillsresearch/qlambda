/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.SuperoperatorInstances
import QLambda.Domain.Presheaf.instPartialOrderSuperoperator

/-!
# Instance `instOrderBotSuperoperator`
-/

namespace QLambda.Domain.Presheaf
namespace Superoperator

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

instance instOrderBotSuperoperator {n m : ℕ} : OrderBot (Superoperator n m) where
  bot := 0
  bot_le f := @bot_le (CPMap n m) _ _ f.cp

end Superoperator
end QLambda.Domain.Presheaf
