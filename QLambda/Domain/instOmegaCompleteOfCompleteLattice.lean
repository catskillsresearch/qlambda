/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.OmegaComplete

/-!
# Instance `instOmegaCompleteOfCompleteLattice`
-/

namespace QLambda.Domain

universe u

noncomputable instance instOmegaCompleteOfCompleteLattice (D : Type u) [CompleteLattice D] : OmegaComplete D where
  ωSup c _ := ⨆ n, c n
  le_ωSup c _ n := le_iSup c n
  ωSup_le _ _ _ h := iSup_le h

end QLambda.Domain
