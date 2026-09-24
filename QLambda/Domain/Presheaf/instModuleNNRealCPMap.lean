/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.CPMap
import QLambda.Domain.Presheaf.instLECPMap
import QLambda.Domain.Presheaf.instPartialOrderCPMap
import QLambda.Domain.Presheaf.instZeroCPMap
import QLambda.Domain.Presheaf.instAddCPMap
import QLambda.Domain.Presheaf.instAddCommMonoidCPMap
import QLambda.Domain.Presheaf.instOrderBotCPMap
import QLambda.Domain.Presheaf.instSMulNNRealCPMap

/-!
# Instance `instModuleNNRealCPMap`
-/

namespace QLambda.Domain.Presheaf
namespace CPMap

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder
variable {n m ℓ r : ℕ}

noncomputable instance instModuleNNRealCPMap : Module NNReal (CPMap n m) where
  one_smul Φ := by
    apply ext
    simp
  mul_smul c d Φ := by
    apply ext
    simp [mul_smul]
  smul_add c Φ Ψ := by
    apply ext
    simp [smul_add]
  smul_zero c := by
    apply ext
    simp
  add_smul c d Φ := by
    apply ext
    simp [add_smul]
  zero_smul Φ := by
    apply ext
    simp

end CPMap
end QLambda.Domain.Presheaf
