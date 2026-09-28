/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Linear.Denotation

@[expose] public section

/-!
# Instance `operationalSetoid`
-/

namespace QLambda.Linear

instance operationalSetoid : Setoid Term where
  r := OperationalEq
  iseqv := ⟨OperationalEq.refl, OperationalEq.symm, OperationalEq.trans⟩

end QLambda.Linear
