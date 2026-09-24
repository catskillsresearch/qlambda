/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.SuperoperatorModule

/-!
# Ambient-CP module class (L9)
-/

namespace QLambda.Domain.Presheaf.SuperoperatorModule

/-- Fiber class restored by the L8 ambient-CP replacement: Bool-additive
fibers and joint action at every dimension. -/
class AmbientCPModule (M : Module.{0}) : Prop where
  has_sum_add : ∀ n, Fiber.HasSumAdd (M.obj n)
  has_act_sum_from_dim : HasActSumFromDim M

instance cpmModule_ambientCP (B : ℕ) : AmbientCPModule (cpmModule B) where
  has_sum_add := fun n => Fiber.HasSumAdd.cpmModule B n
  has_act_sum_from_dim := HasActSumFromDim.cpmModule B

end QLambda.Domain.Presheaf.SuperoperatorModule
