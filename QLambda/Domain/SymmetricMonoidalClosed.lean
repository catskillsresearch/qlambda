/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Enriched

/-!
# Symmetric monoidal closed structure on an enriched category
-/

namespace QLambda.Domain

universe u v

set_option linter.checkUnivs false

open OmegaCategory

/-- Symmetric monoidal closed structure on an enriched category. -/
structure SymmetricMonoidalClosed (L : OmegaCategory.{u, v}) where
  unit : L.Obj
  tensor : L.Obj → L.Obj → L.Obj
  internalHom : L.Obj → L.Obj → L.Obj
  tensorMap :
    {A B C D : L.Obj} → L.Hom A B → L.Hom C D →
      L.Hom (tensor A C) (tensor B D)
  tensorMap_mono_left :
    ∀ {A B C D : L.Obj} (g : L.Hom C D),
      Monotone (fun f : L.Hom A B => tensorMap f g)
  tensorMap_mono_right :
    ∀ {A B C D : L.Obj} (f : L.Hom A B),
      Monotone (fun g : L.Hom C D => tensorMap f g)
  tensorMap_id :
    ∀ {A B : L.Obj}, tensorMap (@L.id A) (@L.id B) = L.id
  tensorMap_comp :
    ∀ {A B C D E F : L.Obj}
      (f₂ : L.Hom B C) (f₁ : L.Hom A B)
      (g₂ : L.Hom E F) (g₁ : L.Hom D E),
      tensorMap (L.comp f₂ f₁) (L.comp g₂ g₁) =
        L.comp (tensorMap f₂ g₂) (tensorMap f₁ g₁)
  leftUnitor : ∀ A : L.Obj, L.Iso (tensor unit A) A
  rightUnitor : ∀ A : L.Obj, L.Iso (tensor A unit) A
  associator :
    ∀ A B C : L.Obj, L.Iso (tensor (tensor A B) C) (tensor A (tensor B C))
  braiding : ∀ A B : L.Obj, L.Iso (tensor A B) (tensor B A)
  eval :
    {A B : L.Obj} → L.Hom (tensor (internalHom A B) A) B
  curry :
    {X A B : L.Obj} → L.Hom (tensor X A) B →
      L.Hom X (internalHom A B)
  uncurry :
    {X A B : L.Obj} → L.Hom X (internalHom A B) →
      L.Hom (tensor X A) B
  curry_uncurry :
    ∀ {X A B : L.Obj} (f : L.Hom X (internalHom A B)),
      curry (uncurry f) = f
  uncurry_curry :
    ∀ {X A B : L.Obj} (f : L.Hom (tensor X A) B),
      uncurry (curry f) = f
  curry_mono :
    ∀ {X A B : L.Obj}, Monotone (@curry X A B)
  curry_ωSup :
    ∀ {X A B : L.Obj} (c : ℕ → L.Hom (tensor X A) B) (hc : Monotone c),
      curry (OmegaComplete.ωSup c hc) =
        OmegaComplete.ωSup (fun n => curry (c n)) (curry_mono.comp hc)

end QLambda.Domain
