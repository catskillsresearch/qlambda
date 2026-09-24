/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumSet

/-!
# Finite quantum sets
-/

set_option warn.classDefReducibility false

namespace QLambda.Domain

namespace QuantumSet

variable {X Y : QuantumSet} {α : Type} {n : ℕ}

/-- A quantum set is finite when it has finitely many atoms. -/
class Finite (X : QuantumSet) where
  fintype : Fintype X.Atom
  decidable : DecidableEq X.Atom

attribute [instance, instance_reducible] Finite.fintype Finite.decidable

instance instFiniteEmpty : Finite empty where
  fintype := inferInstanceAs (Fintype Empty)
  decidable := inferInstanceAs (DecidableEq Empty)

instance instFiniteUnit : Finite unit where
  fintype := inferInstanceAs (Fintype PUnit)
  decidable := inferInstanceAs (DecidableEq PUnit)

instance instFiniteQubit : Finite qubit where
  fintype := inferInstanceAs (Fintype PUnit)
  decidable := inferInstanceAs (DecidableEq PUnit)

instance instFiniteBit : Finite bit where
  fintype := inferInstanceAs (Fintype Bool)
  decidable := inferInstanceAs (DecidableEq Bool)

instance instFiniteAtomic : Finite (atomic n) where
  fintype := inferInstanceAs (Fintype PUnit)
  decidable := inferInstanceAs (DecidableEq PUnit)

instance instFiniteTensor [Finite X] [Finite Y] : Finite (tensor X Y) where
  fintype := inferInstanceAs (Fintype (X.Atom × Y.Atom))
  decidable := inferInstanceAs (DecidableEq (X.Atom × Y.Atom))

instance instFiniteSum [Finite X] [Finite Y] : Finite (sum X Y) where
  fintype := inferInstanceAs (Fintype (X.Atom ⊕ Y.Atom))
  decidable := inferInstanceAs (DecidableEq (X.Atom ⊕ Y.Atom))

instance instFiniteLiftSet [Fintype α] [DecidableEq α] : Finite (liftSet α) where
  fintype := inferInstanceAs (Fintype α)
  decidable := inferInstanceAs (DecidableEq α)

end QuantumSet

end QLambda.Domain
