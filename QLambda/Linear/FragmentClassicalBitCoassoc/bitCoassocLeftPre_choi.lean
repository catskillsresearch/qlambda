/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitCoassoc.bitCoassocLeftPre_choi_collapsed
import QLambda.Linear.FragmentClassicalBitCoassoc.Psi_tensor_id_at_copy

/-!
# Left coassoc pre Choi (closed form)
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf

/-- Closed Choi form of the left coassociativity composite (sans identity associator). -/
theorem bitCoassocLeftPre_choi
    (a b : Fin 8) (i j : Fin 2) :
    bitCoassocLeftPre.cp.choi (a, i) (b, j) =
      if i = j ∧ a.val = i.val * 7 ∧ b.val = j.val * 7 then (1 : ℂ) else 0 := by
  rw [bitCoassocLeftPre_choi_collapsed, Psi_tensor_id_at_copy]
  rfl

end QLambda.Linear
