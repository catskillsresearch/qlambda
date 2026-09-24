/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Linear.TypeFormation

/-!
# Instance `instDecidableWellScopedAt`
-/

namespace QLambda.Linear.Ty

instance instDecidableWellScopedAt {n A} : Decidable (WellScopedAt n A) :=
  if h : wellScopedAt n A = true then
    isTrue (wellScopedAt_eq_true_iff.mp h)
  else
    isFalse fun hA => h (wellScopedAt_eq_true_iff.mpr hA)

end QLambda.Linear.Ty
