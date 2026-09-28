/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Linear.TypeFormation
public import QLambda.Linear.instDecidableWellScopedAt
public import QLambda.Linear.instDecidableDoesNotContainAt

@[expose] public section

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
