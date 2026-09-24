/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.SymmetricElement
import QLambda.Domain.Presheaf.instZeroSymmetricElement

/-!
# Instances from `SymmetricElement`

Barrel re-exporting `QLambda.Domain.Presheaf.SymmetricElement` and its typeclass instances.
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule
namespace SymmetricElement

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

@[simp]
theorem zero_val (A k n : ℕ) :
    (0 : SymmetricElement A k n).val = 0 :=
  rfl


end SymmetricElement
end SuperoperatorModule
end QLambda.Domain.Presheaf
