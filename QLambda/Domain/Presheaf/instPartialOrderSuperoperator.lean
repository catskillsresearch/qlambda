/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.Superoperator
import QLambda.Domain.Presheaf.CPMapInstances

/-!
# Instance `instPartialOrderSuperoperator`
-/

namespace QLambda.Domain.Presheaf
namespace Superoperator

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

instance instPartialOrderSuperoperator {n m : ℕ} : PartialOrder (Superoperator n m) where
  le f g := f.cp ≤ g.cp
  le_refl _ := le_rfl
  le_trans _ _ _ h k := h.trans k
  le_antisymm f g h k := ext (le_antisymm h k)

end Superoperator
end QLambda.Domain.Presheaf
