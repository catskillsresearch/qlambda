/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Linear.TypeFormation
public import QLambda.Linear.instDecidableWellScopedAt
public import QLambda.Linear.instDecidableDoesNotContainAt
public import QLambda.Linear.instDecidableStrictlyPositiveAt
public import QLambda.Linear.instDecidablePositiveRec

@[expose] public section

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
