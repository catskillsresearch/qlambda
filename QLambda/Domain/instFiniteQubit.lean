/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Domain.Finite
public import QLambda.Domain.instFiniteEmpty
public import QLambda.Domain.instFiniteUnit

@[expose] public section

/-!
# Instance `instFiniteQubit`
-/

set_option warn.classDefReducibility false
namespace QLambda.Domain
namespace QuantumSet

variable {X Y : QuantumSet} {α : Type} {n : ℕ}

instance instFiniteQubit : Finite qubit where
  fintype := inferInstanceAs (Fintype PUnit)
  decidable := inferInstanceAs (DecidableEq PUnit)

end QuantumSet
end QLambda.Domain
