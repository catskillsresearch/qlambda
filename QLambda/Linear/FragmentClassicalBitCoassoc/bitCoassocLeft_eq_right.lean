/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitCoassoc.bitCoassocLeft_eq_pre
import QLambda.Linear.FragmentClassicalBitCoassoc.bitCoassocLeftPre_choi
import QLambda.Linear.FragmentClassicalBitCoassoc.bitCoassocRight_choi

/-!
# Classical copy-after-dephase is coassociative
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators


/-- Classical copy-after-dephase is coassociative. -/
theorem bitCoassocLeft_eq_right :
    bitCoassocLeft = bitCoassocRight := by
  rw [bitCoassocLeft_eq_pre]
  apply Superoperator.ext
  apply CPMap.ext
  ext ai bj
  rcases ai with ⟨a, i⟩
  rcases bj with ⟨b, j⟩
  rw [bitCoassocLeftPre_choi, bitCoassocRight_choi]

end QLambda.Linear
