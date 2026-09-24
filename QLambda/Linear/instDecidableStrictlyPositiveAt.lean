/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Linear.TypeFormation
import QLambda.Linear.instDecidableWellScopedAt
import QLambda.Linear.instDecidableDoesNotContainAt

/-!
# Instance `instDecidableStrictlyPositiveAt`
-/

namespace QLambda.Linear.Ty

instance instDecidableStrictlyPositiveAt {target A} :
    Decidable (StrictlyPositiveAt target A) :=
  if h : strictlyPositiveAt target A = true then
    isTrue (strictlyPositiveAt_eq_true_iff.mp h)
  else
    isFalse fun hA => h (strictlyPositiveAt_eq_true_iff.mpr hA)

end QLambda.Linear.Ty
