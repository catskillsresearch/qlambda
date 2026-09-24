/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Linear.TypeFormation
import QLambda.Linear.instDecidableWellScopedAt

/-!
# Instance `instDecidableDoesNotContainAt`
-/

namespace QLambda.Linear.Ty

instance instDecidableDoesNotContainAt {target A} :
    Decidable (DoesNotContainAt target A) :=
  if h : doesNotContainAt target A = true then
    isTrue (doesNotContainAt_eq_true_iff.mp h)
  else
    isFalse fun hA => h (doesNotContainAt_eq_true_iff.mpr hA)

end QLambda.Linear.Ty
