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

@[expose] public section

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
