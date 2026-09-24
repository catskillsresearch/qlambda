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

/-!
# Instance `instFiniteTensor`
-/

set_option warn.classDefReducibility false
namespace QLambda.Domain
namespace QuantumSet

variable {X Y : QuantumSet} {α : Type} {n : ℕ}

instance instFiniteTensor [Finite X] [Finite Y] : Finite (tensor X Y) where
  fintype := inferInstanceAs (Fintype (X.Atom × Y.Atom))
  decidable := inferInstanceAs (DecidableEq (X.Atom × Y.Atom))

end QuantumSet
end QLambda.Domain
