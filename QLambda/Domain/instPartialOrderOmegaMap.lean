/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.OmegaMap
import QLambda.Domain.instCoeFunOmegaMap
import QLambda.Domain.instLEOmegaMap
import QLambda.Domain.instOrderBotOmegaMap

/-!
# Instance `instPartialOrderOmegaMap`
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

@[ext]
theorem ext {f g : OmegaMap D E} (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  simp only [mk.injEq]
  exact funext h

instance instPartialOrderOmegaMap : PartialOrder (OmegaMap D E) where
  le_refl _ _ := le_rfl
  le_trans _ _ _ hfg hgh x := (hfg x).trans (hgh x)
  le_antisymm f g hfg hgf := by
    ext x
    exact le_antisymm (hfg x) (hgf x)

end OmegaMap
end QLambda.Domain
