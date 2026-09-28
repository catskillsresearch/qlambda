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

@[expose] public section

/-!
# Instance `instSupSetQuantumRel`
-/

namespace QLambda.Domain
namespace QuantumRel

open Matrix
variable {X Y Z W : QuantumSet}

instance instSupSetQuantumRel : SupSet (QuantumRel X Y) where
  sSup s := ⟨fun x y => ⨆ R : s, R.1.component x y⟩

end QuantumRel
end QLambda.Domain
