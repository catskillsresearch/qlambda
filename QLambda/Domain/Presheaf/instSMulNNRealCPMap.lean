/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Domain.Presheaf.CPMap
public import QLambda.Domain.Presheaf.instLECPMap
public import QLambda.Domain.Presheaf.instPartialOrderCPMap
public import QLambda.Domain.Presheaf.instZeroCPMap
public import QLambda.Domain.Presheaf.instAddCPMap
public import QLambda.Domain.Presheaf.instAddCommMonoidCPMap
public import QLambda.Domain.Presheaf.instOrderBotCPMap

@[expose] public section

/-!
# Instance `instSMulNNRealCPMap`
-/

namespace QLambda.Domain.Presheaf
namespace CPMap

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder
variable {n m ℓ r : ℕ}

noncomputable instance instSMulNNRealCPMap : SMul NNReal (CPMap n m) :=
  ⟨nnsmul⟩

@[simp]
theorem choi_nnsmul (c : NNReal) (Φ : CPMap n m) :
    (c • Φ).choi = (c : ℂ) • Φ.choi :=
  rfl

end CPMap
end QLambda.Domain.Presheaf
