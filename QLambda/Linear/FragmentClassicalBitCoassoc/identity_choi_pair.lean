/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitChannels

/-!
# Identity channel Choi (pair form)
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators


theorem identity_choi_pair (n : ℕ) (p q : Fin n × Fin n) :
    (CPMap.identity n).choi p q =
      if p.1 = p.2 ∧ q.1 = q.2 then (1 : ℂ) else 0 := by
  rcases p with ⟨a, i⟩
  rcases q with ⟨b, j⟩
  simp [CPMap.identity, CPMap.choi_ofKraus, KrausFamily.identity,
    KrausFamily.choiTerm, Matrix.one_apply]
  split_ifs <;> simp_all

end QLambda.Linear
