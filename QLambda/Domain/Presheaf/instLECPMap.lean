/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.CPMap

/-!
# Instance `instLECPMap`
-/

namespace QLambda.Domain.Presheaf
namespace CPMap

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder
variable {n m ℓ r : ℕ}

instance instLECPMap : LE (CPMap n m) :=
  ⟨fun Φ Ψ => Φ.choi ≤ Ψ.choi⟩

end CPMap
end QLambda.Domain.Presheaf
