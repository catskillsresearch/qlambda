/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitCoassoc.bitCopy_comp_dephase_raw_choi_pair
import QLambda.Linear.FragmentClassicalBitCoassoc.identity_choi_pair
import QLambda.Linear.FragmentClassicalBitCoassoc.copyIdx
import QLambda.Linear.FragmentClassicalBitCoassoc.tripleCopyChoi

/-!
# `(id ⊗ Ψ)` at copy indices equals the triple-copy Choi formula
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

set_option maxHeartbeats 4000000

/-- Evaluate `(id ⊗ (copy∘dephase)).choi` at `(a, 3i)` / `(b, 3j)`. -/
theorem id_tensor_Psi_at_copy
    (a b : Fin 8) (i j : Fin 2) :
    (CPMap.tensor (CPMap.identity 2)
        (bitCopySuperoperator.cp.comp bitDephaseSuperoperator.cp)).choi
      (a, copyIdx i) (b, copyIdx j) =
      tripleCopyChoi a b i j := by
  dsimp only [tripleCopyChoi]
  simp only [CPMap.choi_tensor, reindex_apply, submatrix_apply, kroneckerMap_apply]
  simp only [CPMap.choiTensorEquiv]
  simp_rw [identity_choi_pair, bitCopy_comp_dephase_raw_choi_pair]
  simp only [finProdFinEquiv, Fin.divNat, Fin.modNat, copyIdx]
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;> norm_num

end QLambda.Linear
