/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.OmegaMap
import QLambda.Domain.instCoeFunOmegaMap

/-!
# Instance `instLEOmegaMap`
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

instance instLEOmegaMap : LE (OmegaMap D E) :=
  ⟨fun f g => ∀ x, f x ≤ g x⟩

end OmegaMap
end QLambda.Domain
