/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.HasActSumFromDim

/-!
# Instance `HasActSumFromDim.cpmModule`
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

instance HasActSumFromDim.cpmModule (A : ℕ) :
    HasActSumFromDim (cpmModule A) where
  act_sum_from_dim := by
    intro ι _ m d x s f h
    obtain ⟨Χ, hΧ⟩ := SigmaMon.CPMapSum.comp_from_dim f h
    exact ⟨Χ, hΧ⟩

end SuperoperatorModule
end QLambda.Domain.Presheaf
