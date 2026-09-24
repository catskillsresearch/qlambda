/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Linear.TypeFormation
import QLambda.Linear.instDecidableWellScopedAt
import QLambda.Linear.instDecidableDoesNotContainAt
import QLambda.Linear.instDecidableStrictlyPositiveAt
import QLambda.Linear.instDecidablePositiveRec
import QLambda.Linear.instDecidableAdmissibleAt

/-!
# Instance `instDecidableDuplicableAt`
-/

namespace QLambda.Linear.Ty

instance instDecidableDuplicableAt {κ A} : Decidable (DuplicableAt κ A) :=
  if h : duplicableAt κ A = true then
    isTrue (duplicableAt_eq_true_iff.mp h)
  else
    isFalse fun hA => h (duplicableAt_eq_true_iff.mpr hA)

end QLambda.Linear.Ty
