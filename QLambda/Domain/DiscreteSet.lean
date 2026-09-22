/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.LinearNonlinear

/-!
# Sets as a discretely CPO-enriched category

The ordinary `Set` side of the `Set ⊣ qRel` linear/nonlinear model has
discrete hom orders.  This is materially different from the pointwise order
on `OmegaMap`: graph relations are monotone for the discrete order, but not
for the pointwise order.
-/

namespace QLambda.Domain

universe u

/-- An ordinary function equipped with the discrete equality order. -/
structure SetHom (A B : Type u) where
  toFun : A → B

namespace SetHom

instance {A B : Type u} : CoeFun (SetHom A B) (fun _ => A → B) :=
  ⟨SetHom.toFun⟩

@[ext]
theorem ext {A B : Type u} {f g : SetHom A B}
    (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  congr
  exact funext h

instance {A B : Type u} : LE (SetHom A B) :=
  ⟨fun f g => f = g⟩

instance {A B : Type u} : PartialOrder (SetHom A B) where
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h

/-- An increasing chain in a discrete order is constant. -/
theorem chain_eq_zero {A B : Type u} (c : ℕ → SetHom A B)
    (hc : Monotone c) (n : ℕ) : c n = c 0 :=
  (hc (Nat.zero_le n)).symm

noncomputable instance {A B : Type u} : OmegaComplete (SetHom A B) where
  ωSup c _ := c 0
  le_ωSup c hc n := chain_eq_zero c hc n
  ωSup_le _ _ _ hx := hx 0

def id (A : Type u) : SetHom A A :=
  ⟨fun x => x⟩

def comp {A B C : Type u} (g : SetHom B C) (f : SetHom A B) :
    SetHom A C :=
  ⟨fun x => g (f x)⟩

end SetHom

/-- Ordinary sets and functions, enriched by discrete ωCPO homs. -/
noncomputable def discreteSetCategory : OmegaCategory.{u + 1, u} where
  Obj := Type u
  hom A B :=
    { Carrier := SetHom A B
      partialOrder := inferInstance
      omegaComplete := inferInstance }
  id := SetHom.id _
  comp := SetHom.comp
  comp_mono_left f := by
    intro g h hgh
    subst h
    rfl
  comp_mono_right g := by
    intro f h hfh
    subst h
    rfl
  comp_ωSup_left c hc f := by
    change SetHom.comp (c 0) f = _
    change SetHom.comp (c 0) f = SetHom.comp (c 0) f
    rfl
  comp_ωSup_right g c hc := by
    change SetHom.comp g (c 0) = _
    change SetHom.comp g (c 0) = SetHom.comp g (c 0)
    rfl
  id_comp f := by
    apply SetHom.ext
    intro x
    rfl
  comp_id f := by
    apply SetHom.ext
    intro x
    rfl
  assoc h g f := by
    apply SetHom.ext
    intro x
    rfl

attribute [reducible] discreteSetCategory

/-- The discrete enrichment leaves the ordinary Cartesian closed structure
of `Set` unchanged. -/
noncomputable def discreteSetCartesianClosed :
    CartesianClosed (discreteSetCategory.{u}) where
  terminal := PUnit
  product := Prod
  exponential := fun A B => A → B
  terminate :=
    ⟨fun _ => PUnit.unit⟩
  fst := ⟨Prod.fst⟩
  snd := ⟨Prod.snd⟩
  pair := fun f g => ⟨fun x => (f x, g x)⟩
  eval := ⟨fun p => p.1 p.2⟩
  curry := fun f => ⟨fun x a => f (x, a)⟩
  terminal_unique := by
    intro A f
    apply SetHom.ext
    intro x
    exact Subsingleton.elim _ _
  fst_pair := by
    intro X A B f g
    apply SetHom.ext
    intro x
    rfl
  snd_pair := by
    intro X A B f g
    apply SetHom.ext
    intro x
    rfl
  pair_eta := by
    intro X A B f
    apply SetHom.ext
    intro x
    exact Prod.eta _
  beta := by
    intro X A B f
    apply SetHom.ext
    intro p
    cases p
    rfl
  curry_mono := by
    intro X A B f g h
    exact congrArg (fun k : SetHom (X × A) B =>
      (⟨fun x a => k (x, a)⟩ : SetHom X (A → B))) h
  curry_ωSup := by
    intro X A B c hc
    change (⟨fun x a => c 0 (x, a)⟩ : SetHom X (A → B)) = _
    change (⟨fun x a => c 0 (x, a)⟩ : SetHom X (A → B)) =
      ⟨fun x a => c 0 (x, a)⟩
    rfl

end QLambda.Domain
