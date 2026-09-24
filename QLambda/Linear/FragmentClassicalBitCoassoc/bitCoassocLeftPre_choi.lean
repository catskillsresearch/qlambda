/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitCoassoc.bitCoassocLeftPre
import QLambda.Linear.FragmentClassicalBitCoassoc.bitCopy_comp_dephase_raw_choi_pair
import QLambda.Linear.FragmentClassicalBitCoassoc.identity_choi_pair
import QLambda.Linear.FragmentClassicalBitCoassoc.sum_fin4_coassoc

/-!
# Left coassoc pre Choi (closed form)
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000
open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators


/-- Closed Choi form of the left coassociativity composite (sans identity associator). -/
theorem bitCoassocLeftPre_choi
    (a b : Fin 8) (i j : Fin 2) :
    bitCoassocLeftPre.cp.choi (a, i) (b, j) =
      if i = j ∧ a.val = i.val * 7 ∧ b.val = j.val * 7 then (1 : ℂ) else 0 := by
  simp only [bitCoassocLeftPre, Superoperator.cp_comp, CPMap.choi_comp_apply,
    Superoperator.cp_tensor, CPMap.choi_tensor,
    Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Superoperator.identity]
  simp_rw [bitCopy_comp_dephase_raw_choi_pair, identity_choi_pair]
  simp only [bitCopySuperoperator, Superoperator.cp_ofIsometry,
    CPMap.choi_ofKraus, KrausFamily.choiTerm, classicalCopyMatrix,
    Matrix.conjTranspose_apply, CPMap.choiTensorEquiv, finProdFinEquiv,
    Fin.divNat, Fin.modNat]
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j
  all_goals
    simp [sum_fin4_coassoc, KrausFamily.choiTerm, classicalCopyMatrix,
      Matrix.conjTranspose_apply]
  all_goals norm_num

end QLambda.Linear
