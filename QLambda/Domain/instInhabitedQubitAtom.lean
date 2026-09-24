/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.QuantumSet
import QLambda.Domain.instInhabitedUnitAtom

/-!
# Instance `instInhabitedQubitAtom`
-/

set_option warn.classDefReducibility false
namespace QLambda.Domain
namespace QuantumSet

open Matrix
variable {X Y : QuantumSet} {α : Type} {n : ℕ}

instance instInhabitedQubitAtom : Inhabited qubit.Atom := ⟨PUnit.unit⟩

end QuantumSet
end QLambda.Domain
