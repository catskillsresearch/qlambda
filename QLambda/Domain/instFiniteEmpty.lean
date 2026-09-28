/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Domain.Finite

@[expose] public section

/-!
# Instance `instFiniteEmpty`
-/

set_option warn.classDefReducibility false
namespace QLambda.Domain
namespace QuantumSet

variable {X Y : QuantumSet} {α : Type} {n : ℕ}

instance instFiniteEmpty : Finite empty where
  fintype := inferInstanceAs (Fintype Empty)
  decidable := inferInstanceAs (DecidableEq Empty)

end QuantumSet
end QLambda.Domain
