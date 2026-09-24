/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.OmegaComplete

/-!
# Scott/ω-continuous maps
-/

namespace QLambda.Domain

universe u v w

structure OmegaMap
    (D : Type u) (E : Type v)
    [PartialOrder D] [OmegaComplete D]
    [PartialOrder E] [OmegaComplete E] where
  toFun : D → E
  monotone : Monotone toFun
  map_ωSup : ∀ (c : ℕ → D) (hc : Monotone c),
    toFun (OmegaComplete.ωSup c hc) =
      OmegaComplete.ωSup (fun n => toFun (c n)) (monotone.comp hc)

end QLambda.Domain
