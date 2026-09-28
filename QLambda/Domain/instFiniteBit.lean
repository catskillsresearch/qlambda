/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Domain.Finite
public import QLambda.Domain.instFiniteEmpty
public import QLambda.Domain.instFiniteUnit
public import QLambda.Domain.instFiniteQubit

@[expose] public section

/-!
# Instance `instFiniteBit`
-/

set_option warn.classDefReducibility false
namespace QLambda.Domain
namespace QuantumSet

variable {X Y : QuantumSet} {α : Type} {n : ℕ}

instance instFiniteBit : Finite bit where
  fintype := inferInstanceAs (Fintype Bool)
  decidable := inferInstanceAs (DecidableEq Bool)

end QuantumSet
end QLambda.Domain
