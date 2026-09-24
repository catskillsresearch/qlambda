/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.OmegaMap
import QLambda.Domain.instCoeFunOmegaMap
import QLambda.Domain.instLEOmegaMap

/-!
# Instance `instOrderBotOmegaMap`
-/

namespace QLambda.Domain
namespace OmegaMap

universe u v w

variable
  {D : Type u} {E : Type v} {F : Type w} {G : Type u}
  [PartialOrder D] [OmegaComplete D]
  [PartialOrder E] [OmegaComplete E]
  [PartialOrder F] [OmegaComplete F]
  [PartialOrder G] [OmegaComplete G]

instance instOrderBotOmegaMap [OrderBot E] : OrderBot (OmegaMap D E) where
  bot :=
    { toFun := fun _ => ⊥
      monotone := fun _ _ _ => le_rfl
      map_ωSup := fun c hc => by
        apply le_antisymm
        · exact bot_le
        · exact OmegaComplete.ωSup_le (fun _ => ⊥)
            ((monotone_const).comp hc) ⊥ (fun _ => le_rfl) }
  bot_le _ _ := bot_le

end OmegaMap
end QLambda.Domain
