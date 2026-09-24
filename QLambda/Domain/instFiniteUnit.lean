/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Finite
import QLambda.Domain.instFiniteEmpty

/-!
# Instance `instFiniteUnit`
-/

set_option warn.classDefReducibility false
namespace QLambda.Domain
namespace QuantumSet

variable {X Y : QuantumSet} {α : Type} {n : ℕ}

instance instFiniteUnit : Finite unit where
  fintype := inferInstanceAs (Fintype PUnit)
  decidable := inferInstanceAs (DecidableEq PUnit)

end QuantumSet
end QLambda.Domain
