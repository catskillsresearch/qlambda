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

universe u v

set_option linter.checkUnivs false

open OmegaCategory

/-- Cartesian closed structure on an enriched category. -/
structure CartesianClosed (C : OmegaCategory.{u, v}) where
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

/-- A CPO-enriched strong symmetric monoidal adjunction `F ⊣ G`. -/
structure LNLModel where
  nonlinear : OmegaCategory.{u, v}
  linear : OmegaCategory.{u, v}
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

/-- Terminal pointed ωCPO. -/
noncomputable def omegaTerminal : OmegaObject where
  Carrier := PUnit
  partialOrder := inferInstance
  orderBot := inferInstance
  omegaComplete := inferInstance

/-- Product pointed ωCPO. -/
noncomputable def omegaProduct (A B : OmegaObject) : OmegaObject where
  Carrier := A × B
  partialOrder := inferInstance
  orderBot := inferInstance
  omegaComplete := inferInstance

/-- Pointed ωCPO of continuous maps. -/
noncomputable def omegaExponential (A B : OmegaObject) : OmegaObject where
  Carrier := OmegaMap A B
  partialOrder := inferInstance
  orderBot := inferInstance
  omegaComplete := inferInstance

attribute [reducible] omegaTerminal omegaProduct omegaExponential

/-- The ordinary category of pointed ωCPOs is Cartesian closed.  This
serves as the nonlinear side of concrete LNL models. -/
noncomputable def omegaCartesianClosed :
    CartesianClosed (omegaMapCategory.{u}) where
  terminal := omegaTerminal
  product := omegaProduct
  exponential := omegaExponential
  terminate :=
    { toFun := fun _ => PUnit.unit
      monotone := fun _ _ _ => le_rfl
      map_ωSup := fun _ _ => by
        exact (OmegaComplete.ωSup_const PUnit.unit).symm }
  fst := OmegaMap.fst
  snd := OmegaMap.snd
  pair := OmegaMap.pair
  eval := OmegaMap.eval
  curry := OmegaMap.curry
  terminal_unique := by
    intro A f
    apply OmegaMap.ext
    intro x
    exact Subsingleton.elim _ _
  fst_pair := by
    intro X A B f g
    apply OmegaMap.ext
    intro x
    rfl
  snd_pair := by
    intro X A B f g
    apply OmegaMap.ext
    intro x
    rfl
  pair_eta := by
    intro X A B f
    apply OmegaMap.ext
    intro x
    exact Prod.eta _
  beta := by
    intro X A B f
    apply OmegaMap.ext
    intro p
    cases p
    rfl
  curry_mono := by
    intro X A B f g h x a
    exact h (x, a)
  curry_ωSup := by
    intro X A B c hc
    apply OmegaMap.ext
    intro x
    apply OmegaMap.ext
    intro a
    rfl

/-- The Cartesian tensor also gives the ωCPO category a symmetric
monoidal closed structure. -/
noncomputable def omegaSymmetricMonoidalClosed :
    SymmetricMonoidalClosed (omegaMapCategory.{u}) where
  unit := omegaTerminal
  tensor := omegaProduct
  internalHom := omegaExponential
  tensorMap := fun f g =>
    OmegaMap.pair (f.comp OmegaMap.fst) (g.comp OmegaMap.snd)
  tensorMap_mono_left := by
    intro A B C D g f₁ f₂ h p
    exact ⟨h p.1, le_rfl⟩
  tensorMap_mono_right := by
    intro A B C D f g₁ g₂ h p
    exact ⟨le_rfl, h p.2⟩
  tensorMap_id := by
    intro A B
    apply OmegaMap.ext
    intro p
    exact Prod.eta _
  tensorMap_comp := by
    intro A B C D E F f₂ f₁ g₂ g₁
    apply OmegaMap.ext
    intro p
    rfl
  leftUnitor := fun A =>
    { hom := OmegaMap.snd
      inv :=
        { toFun := fun a => (PUnit.unit, a)
          monotone := fun _ _ h => ⟨le_rfl, h⟩
          map_ωSup := by
            intro c hc
            apply Prod.ext
            · exact (OmegaComplete.ωSup_const PUnit.unit).symm
            · rfl }
      hom_inv := by
        apply OmegaMap.ext
        intro a
        rfl
      inv_hom := by
        apply OmegaMap.ext
        intro p
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · rfl }
  rightUnitor := fun A =>
    { hom := OmegaMap.fst
      inv :=
        { toFun := fun a => (a, PUnit.unit)
          monotone := fun _ _ h => ⟨h, le_rfl⟩
          map_ωSup := by
            intro c hc
            apply Prod.ext
            · rfl
            · exact (OmegaComplete.ωSup_const PUnit.unit).symm }
      hom_inv := by
        apply OmegaMap.ext
        intro a
        rfl
      inv_hom := by
        apply OmegaMap.ext
        intro p
        apply Prod.ext
        · rfl
        · exact Subsingleton.elim _ _ }
  associator := fun A B C =>
    { hom :=
        { toFun := fun p => (p.1.1, (p.1.2, p.2))
          monotone := fun _ _ h =>
            ⟨h.1.1, h.1.2, h.2⟩
          map_ωSup := fun _ _ => rfl }
      inv :=
        { toFun := fun p => ((p.1, p.2.1), p.2.2)
          monotone := fun _ _ h =>
            ⟨⟨h.1, h.2.1⟩, h.2.2⟩
          map_ωSup := fun _ _ => rfl }
      hom_inv := by
        apply OmegaMap.ext
        intro p
        rcases p with ⟨a, b, c⟩
        rfl
      inv_hom := by
        apply OmegaMap.ext
        intro p
        rcases p with ⟨⟨a, b⟩, c⟩
        rfl }
  braiding := fun A B =>
    { hom := OmegaMap.pair OmegaMap.snd OmegaMap.fst
      inv := OmegaMap.pair OmegaMap.snd OmegaMap.fst
      hom_inv := by
        apply OmegaMap.ext
        intro p
        exact Prod.eta _
      inv_hom := by
        apply OmegaMap.ext
        intro p
        exact Prod.eta _ }
  eval := OmegaMap.eval
  curry := OmegaMap.curry
  uncurry := OmegaMap.uncurry
  curry_uncurry := OmegaMap.curry_uncurry
  uncurry_curry := OmegaMap.uncurry_curry
  curry_mono := by
    intro X A B f g h x a
    exact h (x, a)
  curry_ωSup := by
    intro X A B c hc
    apply OmegaMap.ext
    intro x
    apply OmegaMap.ext
    intro a
    rfl

private noncomputable def omegaIdentityFunctor :
    (omegaMapCategory.{u}).Functor omegaMapCategory where
  obj := id
  map := id
  map_mono := by
    intro A B f g h
    exact h
  map_ωSup := fun _ _ => rfl
  map_id := rfl
  map_comp := fun _ _ => rfl

/-- The identity adjunction supplies a fully concrete classical LNL
model.  The intended quantum model instead uses the published category of
pointed quantum CPOs as its linear side.  Finite CP maps and instruments embed
the circuit fragment into that category; they are not themselves asserted to
form the higher-order monoidal-closed category. -/
noncomputable def omegaIdentityLNL : LNLModel.{u + 1, u} where
  nonlinear := omegaMapCategory
  linear := omegaMapCategory
  nonlinearClosed := omegaCartesianClosed
  linearClosed := omegaSymmetricMonoidalClosed
  F := omegaIdentityFunctor
  G := omegaIdentityFunctor
  toLinear := fun f => f
  toNonlinear := fun f => f
  toLinear_toNonlinear := fun _ => rfl
  toNonlinear_toLinear := fun _ => rfl
  adjunction_mono := by
    intro A B f g h
    exact h
  F_unit :=
    { hom := OmegaMap.id
      inv := OmegaMap.id
      hom_inv := OmegaMap.id_comp _
      inv_hom := OmegaMap.id_comp _ }
  F_tensor := fun _ _ =>
    { hom := OmegaMap.id
      inv := OmegaMap.id
      hom_inv := OmegaMap.id_comp _
      inv_hom := OmegaMap.id_comp _ }

end QLambda.Domain
