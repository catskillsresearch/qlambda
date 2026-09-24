/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.AmbientCPModule

/-!
# Instance `cpmModule_ambientCP`
-/

namespace QLambda.Domain.Presheaf.SuperoperatorModule

instance cpmModule_ambientCP (B : ℕ) : AmbientCPModule (cpmModule B) where
  has_sum_add := fun n => Fiber.HasSumAdd.cpmModule B n
  has_act_sum_from_dim := HasActSumFromDim.cpmModule B

end QLambda.Domain.Presheaf.SuperoperatorModule
