/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.OmegaCPO

/-!
# Categories enriched over pointed ωCPOs

The structures in this file are proof-carrying interfaces.  In particular,
declaring an enriched category requires supplying chain suprema and proving
that composition preserves them in each argument.
-/

namespace QLambda.Domain

universe u v

set_option linter.checkUnivs false

/-- A bundled ω-complete partial order. -/
structure OmegaObject where
  Carrier : Type u
  partialOrder : PartialOrder Carrier
  omegaComplete : OmegaComplete Carrier

attribute [instance] OmegaObject.partialOrder OmegaObject.omegaComplete

namespace OmegaObject

instance : CoeSort OmegaObject (Type u) :=
  ⟨OmegaObject.Carrier⟩

end OmegaObject

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

/-- Isomorphisms in an enriched category. -/
structure Iso (C : OmegaCategory) (A B : C.Obj) where
  hom : C.Hom A B
  inv : C.Hom B A
  hom_inv : C.comp hom inv = C.id
  inv_hom : C.comp inv hom = C.id

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

/-- The canonical ωCPO-enriched category of pointed ωCPOs and
ω-continuous maps. -/
noncomputable def omegaMapCategory : OmegaCategory.{u + 1, u} where
  Obj := OmegaObject.{u}
  hom A B :=
    { Carrier := OmegaMap A B
      partialOrder := inferInstance
      omegaComplete := OmegaMap.instOmegaCompleteFunctionSpace }
  id := OmegaMap.id
  comp := OmegaMap.comp
  comp_mono_left g := by
    intro f₁ f₂ h x
    exact h (g x)
  comp_mono_right f := by
    intro g₁ g₂ h x
    exact f.monotone (h x)
  comp_ωSup_left c hc g := by
    apply OmegaMap.ext
    intro x
    rfl
  comp_ωSup_right f c hc := by
    apply OmegaMap.ext
    intro x
    exact f.map_ωSup (fun n => c n x)
      (fun _ _ h => hc h x)
  id_comp := OmegaMap.id_comp
  comp_id := OmegaMap.comp_id
  assoc := OmegaMap.comp_assoc

attribute [reducible] omegaMapCategory

end QLambda.Domain
