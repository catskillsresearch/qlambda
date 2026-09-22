/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Enriched

/-!
# Linear/nonlinear structure over ωCPO-enriched categories

This file records exactly the categorical data consumed by the typed
denotation.  The laws are fields, so a concrete model cannot be installed
without proving the category, closure, adjunction, and strong-monoidal laws.
-/

namespace QLambda.Domain

universe u

open OmegaCategory

/-- Cartesian closed structure on an enriched category. -/
structure CartesianClosed (C : OmegaCategory.{u}) where
  terminal : C.Obj
  product : C.Obj → C.Obj → C.Obj
  exponential : C.Obj → C.Obj → C.Obj
  terminate : {A : C.Obj} → C.Hom A terminal
  fst : {A B : C.Obj} → C.Hom (product A B) A
  snd : {A B : C.Obj} → C.Hom (product A B) B
  pair :
    {X A B : C.Obj} → C.Hom X A → C.Hom X B → C.Hom X (product A B)
  eval :
    {A B : C.Obj} → C.Hom (product (exponential A B) A) B
  curry :
    {X A B : C.Obj} → C.Hom (product X A) B → C.Hom X (exponential A B)
  terminal_unique : ∀ {A : C.Obj} (f : C.Hom A terminal), f = terminate
  fst_pair :
    ∀ {X A B : C.Obj} (f : C.Hom X A) (g : C.Hom X B),
      C.comp fst (pair f g) = f
  snd_pair :
    ∀ {X A B : C.Obj} (f : C.Hom X A) (g : C.Hom X B),
      C.comp snd (pair f g) = g
  pair_eta :
    ∀ {X A B : C.Obj} (f : C.Hom X (product A B)),
      pair (C.comp fst f) (C.comp snd f) = f
  beta :
    ∀ {X A B : C.Obj} (f : C.Hom (product X A) B),
      C.comp eval (pair (C.comp (curry f) fst) snd) = f
  curry_mono :
    ∀ {X A B : C.Obj}, Monotone (@curry X A B)
  curry_ωSup :
    ∀ {X A B : C.Obj} (c : ℕ → C.Hom (product X A) B) (hc : Monotone c),
      curry (OmegaComplete.ωSup c hc) =
        OmegaComplete.ωSup (fun n => curry (c n)) (curry_mono.comp hc)

/-- Symmetric monoidal closed structure on an enriched category. -/
structure SymmetricMonoidalClosed (L : OmegaCategory.{u}) where
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

/-- A CPO-enriched strong symmetric monoidal adjunction `F ⊣ G`. -/
structure LNLModel where
  nonlinear : OmegaCategory.{u}
  linear : OmegaCategory.{u}
  nonlinearClosed : CartesianClosed nonlinear
  linearClosed : SymmetricMonoidalClosed linear
  F : nonlinear.Functor linear
  G : linear.Functor nonlinear
  toLinear :
    {A : nonlinear.Obj} → {B : linear.Obj} →
      nonlinear.Hom A (G.obj B) → linear.Hom (F.obj A) B
  toNonlinear :
    {A : nonlinear.Obj} → {B : linear.Obj} →
      linear.Hom (F.obj A) B → nonlinear.Hom A (G.obj B)
  toLinear_toNonlinear :
    ∀ {A : nonlinear.Obj} {B : linear.Obj}
      (f : linear.Hom (F.obj A) B),
      toLinear (toNonlinear f) = f
  toNonlinear_toLinear :
    ∀ {A : nonlinear.Obj} {B : linear.Obj}
      (f : nonlinear.Hom A (G.obj B)),
      toNonlinear (toLinear f) = f
  adjunction_mono :
    ∀ {A : nonlinear.Obj} {B : linear.Obj},
      Monotone (@toLinear A B)
  F_unit : linear.Iso (F.obj nonlinearClosed.terminal) linearClosed.unit
  F_tensor :
    ∀ A B : nonlinear.Obj,
      linear.Iso (F.obj (nonlinearClosed.product A B))
        (linearClosed.tensor (F.obj A) (F.obj B))

end QLambda.Domain
