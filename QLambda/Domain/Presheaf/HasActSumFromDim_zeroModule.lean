/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Domain.Presheaf.ClassicalZero

@[expose] public section

/-!
# Instance `HasActSumFromDim.zeroModule`
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule

instance HasActSumFromDim.zeroModule : HasActSumFromDim zeroModule where
  act_sum_from_dim := by
    intros
    exact ⟨0, trivial⟩

end SuperoperatorModule
end QLambda.Domain.Presheaf
