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
public import QLambda.Domain.instSemilatticeSupQuantumRel
public import QLambda.Domain.instLatticeQuantumRel

@[expose] public section

/-!
# Instance `instBoundedOrderQuantumRel`
-/

namespace QLambda.Domain
namespace QuantumRel

open Matrix
variable {X Y Z W : QuantumSet}

instance instBoundedOrderQuantumRel : BoundedOrder (QuantumRel X Y) where
  le_top := fun _ _ _ => le_top
  bot_le := fun _ _ _ => bot_le

end QuantumRel
end QLambda.Domain
