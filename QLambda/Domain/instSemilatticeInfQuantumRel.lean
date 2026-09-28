/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Domain.QuantumRel
public import QLambda.Domain.instLEQuantumRel
public import QLambda.Domain.instPartialOrderQuantumRel
public import QLambda.Domain.instBotQuantumRel
public import QLambda.Domain.instTopQuantumRel
public import QLambda.Domain.instInfSetQuantumRel
public import QLambda.Domain.instSupSetQuantumRel

@[expose] public section

/-!
# Instance `instSemilatticeInfQuantumRel`
-/

namespace QLambda.Domain
namespace QuantumRel

open Matrix
variable {X Y Z W : QuantumSet}

instance instSemilatticeInfQuantumRel : SemilatticeInf (QuantumRel X Y) where
  inf R S := ⟨fun x y => R.component x y ⊓ S.component x y⟩
  inf_le_left := fun _ _ _ _ => inf_le_left
  inf_le_right := fun _ _ _ _ => inf_le_right
  le_inf := fun _ _ _ hR hS x y => le_inf (hR x y) (hS x y)

end QuantumRel
end QLambda.Domain
