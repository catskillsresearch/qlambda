/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Finite
import QLambda.Domain.instFiniteEmpty
import QLambda.Domain.instFiniteUnit
import QLambda.Domain.instFiniteQubit
import QLambda.Domain.instFiniteBit
import QLambda.Domain.instFiniteAtomic
import QLambda.Domain.instFiniteTensor
import QLambda.Domain.instFiniteSum

/-!
# Instance `instFiniteLiftSet`
-/

set_option warn.classDefReducibility false
namespace QLambda.Domain
namespace QuantumSet

variable {X Y : QuantumSet} {α : Type} {n : ℕ}

instance instFiniteLiftSet [Fintype α] [DecidableEq α] : Finite (liftSet α) where
  fintype := inferInstanceAs (Fintype α)
  decidable := inferInstanceAs (DecidableEq α)

end QuantumSet
end QLambda.Domain
