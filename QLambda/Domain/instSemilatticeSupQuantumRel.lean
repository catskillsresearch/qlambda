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
public import QLambda.Domain.instSemilatticeInfQuantumRel

@[expose] public section

/-!
# Instance `instSemilatticeSupQuantumRel`
-/

namespace QLambda.Domain
namespace QuantumRel

open Matrix
variable {X Y Z W : QuantumSet}

instance instSemilatticeSupQuantumRel : SemilatticeSup (QuantumRel X Y) where
  sup R S := ⟨fun x y => R.component x y ⊔ S.component x y⟩
  le_sup_left := fun _ _ _ _ => le_sup_left
  le_sup_right := fun _ _ _ _ => le_sup_right
  sup_le := fun _ _ _ hR hS x y => sup_le (hR x y) (hS x y)

end QuantumRel
end QLambda.Domain
