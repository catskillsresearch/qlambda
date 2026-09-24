/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.SymmetricElement
import QLambda.Domain.Presheaf.SuperoperatorInstances

/-!
# Instance `instZeroSymmetricElement`
-/

set_option maxHeartbeats 8000000
namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule
namespace SymmetricElement

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

instance instZeroSymmetricElement (A k n : ℕ) : Zero (SymmetricElement A k n) where
  zero :=
    { val := 0
      invariant := fun _σ => Superoperator.comp_zero_right _ }

end SymmetricElement
end SuperoperatorModule
end QLambda.Domain.Presheaf
