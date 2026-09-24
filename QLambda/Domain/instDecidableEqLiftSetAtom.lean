/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.QuantumSet
import QLambda.Domain.instInhabitedUnitAtom
import QLambda.Domain.instInhabitedQubitAtom
import QLambda.Domain.instInhabitedAtomicAtom
import QLambda.Domain.instUniqueUnitAtom
import QLambda.Domain.instUniqueQubitAtom
import QLambda.Domain.instUniqueAtomicAtom

/-!
# Instance `instDecidableEqLiftSetAtom`
-/

set_option warn.classDefReducibility false
namespace QLambda.Domain
namespace QuantumSet

open Matrix
variable {X Y : QuantumSet} {α : Type} {n : ℕ}

instance instDecidableEqLiftSetAtom [DecidableEq α] : DecidableEq (liftSet α).Atom :=
  show DecidableEq α from inferInstance

end QuantumSet
end QLambda.Domain
