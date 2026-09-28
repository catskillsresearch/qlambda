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

@[expose] public section

/-!
# Instance `instInfSetQuantumRel`
-/

namespace QLambda.Domain
namespace QuantumRel

open Matrix
variable {X Y Z W : QuantumSet}

instance instInfSetQuantumRel : InfSet (QuantumRel X Y) where
  sInf s := ⟨fun x y => ⨅ R : s, R.1.component x y⟩

end QuantumRel
end QLambda.Domain
