/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitChannels

/-!
# Classical copy Choi (closed form)
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators

/-- Choi matrix of classical copy: support on the computational copy subspace. -/
theorem bitCopy_choi (a b : Fin 4) (i j : Fin 2) :
    bitCopySuperoperator.cp.choi (a, i) (b, j) =
      if a.val = i.val * 3 ∧ b.val = j.val * 3 then (1 : ℂ) else 0 := by
  simp only [bitCopySuperoperator, Superoperator.cp_ofIsometry,
    CPMap.choi_ofKraus, KrausFamily.choi_single, KrausFamily.choiTerm,
    classicalCopyMatrix]
  split_ifs <;> simp_all [star_one, star_zero]

theorem bitCopy_choi_pair (p q : Fin 4 × Fin 2) :
    bitCopySuperoperator.cp.choi p q =
      if p.1.val = p.2.val * 3 ∧ q.1.val = q.2.val * 3 then (1 : ℂ) else 0 := by
  rcases p with ⟨a, i⟩
  rcases q with ⟨b, j⟩
  simpa using bitCopy_choi a b i j

end QLambda.Linear
