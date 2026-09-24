/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.QuantumRel
import QLambda.Domain.instLEQuantumRel

/-!
# Instance `instPartialOrderQuantumRel`
-/

namespace QLambda.Domain
namespace QuantumRel

open Matrix
variable {X Y Z W : QuantumSet}

instance instPartialOrderQuantumRel : PartialOrder (QuantumRel X Y) where
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ hRS hST x y := (hRS x y).trans (hST x y)
  le_antisymm R S hRS hSR := by
    cases R
    cases S
    congr 1
    funext x y
    exact le_antisymm (hRS x y) (hSR x y)

end QuantumRel
end QLambda.Domain
