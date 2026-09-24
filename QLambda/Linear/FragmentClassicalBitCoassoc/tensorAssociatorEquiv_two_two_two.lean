/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitChannels

/-!
# Tensor associator equiv on `2⊗2⊗2`
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators


/-- The `2 ⊗ 2 ⊗ 2` associator is the identity on the shared `Fin 8` encoding. -/
theorem tensorAssociatorEquiv_two_two_two :
    Superoperator.tensorAssociatorEquiv 2 2 2 =
      Equiv.refl (Fin ((2 * 2) * 2)) := by
  ext x
  fin_cases x <;> decide

end QLambda.Linear
