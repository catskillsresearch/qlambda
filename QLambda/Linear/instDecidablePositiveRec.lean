/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Linear.TypeFormation
import QLambda.Linear.instDecidableWellScopedAt
import QLambda.Linear.instDecidableDoesNotContainAt
import QLambda.Linear.instDecidableStrictlyPositiveAt

/-!
# Instance `instDecidablePositiveRec`
-/

namespace QLambda.Linear.Ty

instance instDecidablePositiveRec {A} : Decidable (PositiveRec A) :=
  if h : positiveRec A = true then
    isTrue (positiveRec_eq_true_iff.mp h)
  else
    isFalse fun hA => h (positiveRec_eq_true_iff.mpr hA)

end QLambda.Linear.Ty
