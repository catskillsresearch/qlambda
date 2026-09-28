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

@[expose] public section

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
