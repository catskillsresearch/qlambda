/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.OmegaMap

/-!
# Instance `instCoeFunOmegaMap`
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

instance instCoeFunOmegaMap : CoeFun (OmegaMap D E) (fun _ => D → E) :=
  ⟨OmegaMap.toFun⟩

end OmegaMap
end QLambda.Domain
