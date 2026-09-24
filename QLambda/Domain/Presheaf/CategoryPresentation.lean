/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Classical

/-!
# Ordinary category presentation
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u

/-- A small ordinary-category interface used for the concrete full
biorthogonal subcategory. -/
structure CategoryPresentation where
  Obj : Type (u + 1)
  hom : Obj → Obj → Type u
  id : {A : Obj} → hom A A
  comp : {A B C : Obj} → hom B C → hom A B → hom A C
  id_comp : ∀ {A B : Obj} (f : hom A B), comp id f = f
  comp_id : ∀ {A B : Obj} (f : hom A B), comp f id = f
  assoc :
    ∀ {A B C D : Obj} (h : hom C D) (g : hom B C) (f : hom A B),
      comp (comp h g) f = comp h (comp g f)

end SuperoperatorModule

end QLambda.Domain.Presheaf
