/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Domain.QuantumSet
public import QLambda.Domain.instInhabitedUnitAtom
public import QLambda.Domain.instInhabitedQubitAtom
public import QLambda.Domain.instInhabitedAtomicAtom
public import QLambda.Domain.instUniqueUnitAtom
public import QLambda.Domain.instUniqueQubitAtom
public import QLambda.Domain.instUniqueAtomicAtom
public import QLambda.Domain.instDecidableEqLiftSetAtom
public import QLambda.Domain.instFintypeLiftSetAtom
public import QLambda.Domain.instLELiftSetAtom

@[expose] public section

/-!
# Instance `instPreorderLiftSetAtom`
-/

set_option warn.classDefReducibility false
namespace QLambda.Domain
namespace QuantumSet

open Matrix
variable {X Y : QuantumSet} {α : Type} {n : ℕ}

instance instPreorderLiftSetAtom [Preorder α] : Preorder (liftSet α).Atom :=
  show Preorder α from inferInstance

end QuantumSet
end QLambda.Domain
