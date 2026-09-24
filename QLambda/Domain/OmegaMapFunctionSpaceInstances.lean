/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.OmegaMapFunctionSpace
import QLambda.Domain.instOmegaCompleteFunctionSpace

/-!
# Instances from `OmegaMapFunctionSpace`
-/

namespace QLambda.Domain
namespace OmegaMap

section FunctionSpace

universe u v

variable {D : Type u} {E : Type v}
  [PartialOrder D] [OmegaComplete D]
  [PartialOrder E] [OmegaComplete E]

@[simp] theorem ωSup_apply (c : ℕ → OmegaMap D E) (hc : Monotone c)
    (x : D) :
    (OmegaComplete.ωSup c hc) x =
      OmegaComplete.ωSup (fun n => c n x)
        (fun _ _ h => hc h x) :=
  rfl

end FunctionSpace
end OmegaMap
end QLambda.Domain
