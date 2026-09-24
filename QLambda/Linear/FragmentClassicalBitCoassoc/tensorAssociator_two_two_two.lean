/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitCoassoc.tensorAssociatorEquiv_two_two_two

/-!
# Tensor associator superoperator on `2⊗2⊗2`
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators


theorem tensorAssociator_two_two_two :
    Superoperator.tensorAssociator 2 2 2 =
      Superoperator.identity ((2 * 2) * 2) := by
  simp only [Superoperator.tensorAssociator, tensorAssociatorEquiv_two_two_two,
    Superoperator.ofEquivalence_refl]

end QLambda.Linear
