/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.QuantumRel

/-!
# Instance `instLEQuantumRel`
-/

namespace QLambda.Domain
namespace QuantumRel

open Matrix
variable {X Y Z W : QuantumSet}

instance instLEQuantumRel : LE (QuantumRel X Y) where
  le R S := ∀ x y, R.component x y ≤ S.component x y

end QuantumRel
end QLambda.Domain
