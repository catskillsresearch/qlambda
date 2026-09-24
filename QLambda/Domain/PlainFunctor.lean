/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.OmegaCategory

/-!
# Ordinary functors between underlying enriched categories
-/

namespace QLambda.Domain

universe u v

namespace OmegaCategory

/-- An ordinary functor between the underlying categories.  LNL adjunctions
need not preserve the chosen hom orders; enrichment is retained separately on
the semantic categories and on functors that genuinely preserve it. -/
structure PlainFunctor (C D : OmegaCategory) where
  obj : C.Obj → D.Obj
  map : {A B : C.Obj} → C.Hom A B → D.Hom (obj A) (obj B)
  map_id : ∀ {A : C.Obj}, map (@C.id A) = D.id
  map_comp :
    ∀ {A B E : C.Obj} (g : C.Hom B E) (f : C.Hom A B),
      map (C.comp g f) = D.comp (map g) (map f)

end OmegaCategory

end QLambda.Domain
