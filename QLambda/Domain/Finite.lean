/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumSetInstances

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
end QuantumSet

end QLambda.Domain
