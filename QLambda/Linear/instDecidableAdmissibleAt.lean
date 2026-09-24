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

/-!
# Instance `instDecidableAdmissibleAt`
-/

namespace QLambda.Linear.Ty

instance instDecidableAdmissibleAt {n A} : Decidable (AdmissibleAt n A) :=
  if h : admissibleAt n A = true then
    isTrue (admissibleAt_eq_true_iff.mp h)
  else
    isFalse fun hA => h (admissibleAt_eq_true_iff.mpr hA)

end QLambda.Linear.Ty
