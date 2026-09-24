/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.Superoperator

/-!
# Instance `instZeroSuperoperator`
-/

namespace QLambda.Domain.Presheaf
namespace Superoperator

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder
variable {n m ℓ r : ℕ}

instance instZeroSuperoperator : Zero (Superoperator n m) := ⟨zero⟩

end Superoperator
end QLambda.Domain.Presheaf
