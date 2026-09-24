/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitCoassoc.bitCoassocRight
import QLambda.Linear.FragmentClassicalBitCoassoc.bitCopy_choi
import QLambda.Linear.FragmentClassicalBitCoassoc.copyIdx

/-!
# Right coassoc Choi collapses to a single tensor entry
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped BigOperators ComplexOrder MatrixOrder

/-- After expanding `(id ⊗ Ψ) ∘ copy` and substituting the copy Choi,
the composition sum collapses to one tensor entry at `copyIdx`. -/
theorem bitCoassocRight_choi_collapsed
    (a b : Fin 8) (i j : Fin 2) :
    bitCoassocRight.cp.choi (a, i) (b, j) =
      (CPMap.tensor (CPMap.identity 2)
          (bitCopySuperoperator.cp.comp bitDephaseSuperoperator.cp)).choi
        (a, copyIdx i) (b, copyIdx j) := by
  simp only [bitCoassocRight, Superoperator.cp_comp, CPMap.choi_comp_apply,
    Superoperator.cp_tensor, Superoperator.identity]
  simp_rw [bitCopy_choi_pair]
  exact sum_bitCopy_selector _ i j

end QLambda.Linear
