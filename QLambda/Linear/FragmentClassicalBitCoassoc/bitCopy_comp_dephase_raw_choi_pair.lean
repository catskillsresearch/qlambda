/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitCoassoc.bitCopy_comp_dephase_choi

/-!
# Copy∘dephase Choi (pair form)
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators


/-- Pair-form of the copy∘dephase Choi formula, for rewriting under tensor. -/
theorem bitCopy_comp_dephase_raw_choi_pair
    (p q : Fin 4 × Fin 2) :
    (bitCopySuperoperator.cp.comp bitDephaseSuperoperator.cp).choi p q =
      if p.2 = q.2 ∧ p.1.val = p.2.val * 3 ∧ q.1.val = q.2.val * 3 then
        (1 : ℂ) else 0 := by
  rcases p with ⟨a, i⟩
  rcases q with ⟨b, j⟩
  simpa only [← Superoperator.cp_comp] using
    bitCopy_comp_dephase_choi a b i j

end QLambda.Linear
