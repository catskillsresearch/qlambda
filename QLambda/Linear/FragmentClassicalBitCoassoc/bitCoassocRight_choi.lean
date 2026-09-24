/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitCoassoc.bitCoassocRight_choi_collapsed
import QLambda.Linear.FragmentClassicalBitCoassoc.id_tensor_Psi_at_copy

/-!
# Right coassoc Choi (closed form)
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf

/-- Closed Choi form of the right coassociativity composite. -/
theorem bitCoassocRight_choi
    (a b : Fin 8) (i j : Fin 2) :
    bitCoassocRight.cp.choi (a, i) (b, j) =
      if i = j ∧ a.val = i.val * 7 ∧ b.val = j.val * 7 then (1 : ℂ) else 0 := by
  rw [bitCoassocRight_choi_collapsed, id_tensor_Psi_at_copy]
  rfl

end QLambda.Linear
