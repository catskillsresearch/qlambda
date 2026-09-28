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
public import QLambda.Linear.instDecidableAdmissibleAt

@[expose] public section

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
