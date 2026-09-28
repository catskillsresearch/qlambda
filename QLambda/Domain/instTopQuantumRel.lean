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

@[expose] public section

/-!
# Instance `instTopQuantumRel`
-/

namespace QLambda.Domain
namespace QuantumRel

open Matrix
variable {X Y Z W : QuantumSet}

instance instTopQuantumRel : Top (QuantumRel X Y) := ⟨top⟩

end QuantumRel
end QLambda.Domain
