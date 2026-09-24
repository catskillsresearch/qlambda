/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.OmegaCategory

/-!
# ωCPO-enriched functors
-/

namespace QLambda.Domain

universe u v

namespace OmegaCategory

/-- An ωCPO-enriched functor. -/
structure Functor (C D : OmegaCategory) where
  obj : C.Obj → D.Obj
  map : {A B : C.Obj} → C.Hom A B → D.Hom (obj A) (obj B)
  map_mono : ∀ {A B : C.Obj}, Monotone (@map A B)
  map_ωSup :
    ∀ {A B : C.Obj} (c : ℕ → C.Hom A B) (hc : Monotone c),
      map (OmegaComplete.ωSup c hc) =
        OmegaComplete.ωSup (fun n => map (c n)) (map_mono.comp hc)
  map_id : ∀ {A : C.Obj}, map (@C.id A) = D.id
  map_comp :
    ∀ {A B E : C.Obj} (g : C.Hom B E) (f : C.Hom A B),
      map (C.comp g f) = D.comp (map g) (map f)

end OmegaCategory

end QLambda.Domain
