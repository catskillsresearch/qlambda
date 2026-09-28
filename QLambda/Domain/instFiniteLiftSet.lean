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
public import QLambda.Domain.instFiniteBit
public import QLambda.Domain.instFiniteAtomic
public import QLambda.Domain.instFiniteTensor
public import QLambda.Domain.instFiniteSum

@[expose] public section

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
