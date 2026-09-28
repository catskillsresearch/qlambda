/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Domain.QuantumRel
public import QLambda.Domain.instLEQuantumRel
public import QLambda.Domain.instPartialOrderQuantumRel

@[expose] public section

/-!
# Instance `instBotQuantumRel`
-/

namespace QLambda.Domain
namespace QuantumRel

open Matrix
variable {X Y Z W : QuantumSet}

instance instBotQuantumRel : Bot (QuantumRel X Y) := ⟨bot⟩

end QuantumRel
end QLambda.Domain
