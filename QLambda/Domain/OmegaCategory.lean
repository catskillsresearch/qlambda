/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.OmegaObject

/-!
# ωCPO-enriched categories
-/

namespace QLambda.Domain

universe u v

set_option linter.checkUnivs false

/-- A small category whose homs are pointed ωCPOs and whose composition is
ω-continuous in each argument. -/
structure OmegaCategory where
  Obj : Type u
  hom : Obj → Obj → OmegaObject.{v}
  id : {A : Obj} → hom A A
  comp : {A B C : Obj} → hom B C → hom A B → hom A C
  comp_mono_left :
    ∀ {A B C : Obj} (g : hom A B), Monotone (fun f : hom B C => comp f g)
  comp_mono_right :
    ∀ {A B C : Obj} (f : hom B C), Monotone (fun g : hom A B => comp f g)
  comp_ωSup_left :
    ∀ {A B C : Obj} (c : ℕ → hom B C) (hc : Monotone c) (g : hom A B),
      comp (OmegaComplete.ωSup c hc) g =
        OmegaComplete.ωSup (fun n => comp (c n) g)
          ((comp_mono_left g).comp hc)
  comp_ωSup_right :
    ∀ {A B C : Obj} (f : hom B C) (c : ℕ → hom A B) (hc : Monotone c),
      comp f (OmegaComplete.ωSup c hc) =
        OmegaComplete.ωSup (fun n => comp f (c n))
          ((comp_mono_right f).comp hc)
  id_comp : ∀ {A B : Obj} (f : hom A B), comp id f = f
  comp_id : ∀ {A B : Obj} (f : hom A B), comp f id = f
  assoc :
    ∀ {A B C D : Obj} (h : hom C D) (g : hom B C) (f : hom A B),
      comp (comp h g) f = comp h (comp g f)

namespace OmegaCategory

abbrev Hom (C : OmegaCategory) (A B : C.Obj) : Type v :=
  C.hom A B

infixr:10 " ⟶ω " => Hom

end OmegaCategory

end QLambda.Domain
