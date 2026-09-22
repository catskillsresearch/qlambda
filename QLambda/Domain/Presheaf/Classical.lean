/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.PseudoRepresentable
import QLambda.Domain.Presheaf.DayCoend

/-!
# Double-dual classical objects

The classical subcategory used by the CP-presheaf semantics consists of based
modules for which the canonical map into the second dual is an isomorphism.
This file records that criterion independently of a particular construction
of the negation module.  A later Day-closed construction must supply
`NegationData`; merely postulating a `ClassicalObject` does not produce one.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u

/-- Contravariant negation together with its canonical double-dual unit.

This is structure consumed by the definition of the classical subcategory.
The concrete instance must be constructed from Day internal hom into the
tensor unit; no instance is declared in this file. -/
structure NegationData where
  neg : Module.{u} → Module.{u}
  map :
    {M N : Module.{u}} → Hom M N → Hom (neg N) (neg M)
  map_id :
    ∀ M, map (Hom.id M) = Hom.id (neg M)
  map_comp :
    ∀ {L M N : Module.{u}} (g : Hom M N) (f : Hom L M),
      map (Hom.comp g f) = Hom.comp (map f) (map g)
  unit :
    ∀ M, Hom M (neg (neg M))
  unit_natural :
    ∀ {M N : Module.{u}} (f : Hom M N),
      Hom.comp (unit N) f =
        Hom.comp (map (map f)) (unit M)

namespace NegationData

variable (D : NegationData.{u})

/-- The second dual of a module. -/
abbrev doubleDual (M : Module.{u}) : Module.{u} :=
  D.neg (D.neg M)

end NegationData

/-! ## Concrete Day negation

The negation of `M` is the Day internal hom `[M,I]`.  The canonical map
`M → M⊥⊥` below is the transpose of evaluation after symmetry.  Nothing in
this construction says that the map is invertible: that remains the defining
property of a classical object. -/

namespace DayNegation

/-- Concrete negation by the Day internal hom into the tensor unit. -/
noncomputable abbrev neg (M : Module) : Module :=
  dayInternalHom M dayTensorUnit

/-- Precomposition of a functional by a module morphism. -/
noncomputable def mapBilinear {M N : Module} (f : Hom M N)
    (n : ℕ) (b : (neg N).obj n |>.Carrier) :
    Bilinear (representable n) M dayTensorUnit where
  app := fun x y => b.app x (f.app _ y)
  map_zero_left := fun y => b.map_zero_left (f.app _ y)
  map_zero_right := by
    intro p q x
    rw [f.map_zero]
    exact b.map_zero_right x
  map_sum_left := fun y h => b.map_sum_left (f.app _ y) h
  map_sum_right := by
    intro ι _ p q x y s h
    exact b.map_sum_right x (f.map_sum h)
  naturality := by
    intro p' p q' q x y g h
    rw [f.naturality]
    exact b.naturality x (f.app q y) g h

/-- Day negation is contravariant. -/
noncomputable def map {M N : Module} (f : Hom M N) :
    Hom (neg N) (neg M) where
  app := mapBilinear f
  map_zero := by
    intro n
    apply Bilinear.ext
    intro p q x y
    change (0 : Bilinear (representable n) N dayTensorUnit).app x
      (f.app q y) =
        (0 : Bilinear (representable n) M dayTensorUnit).app x y
    rfl
  map_sum := by
    intro ι _ n b s h p q x y
    exact h p q x (f.app q y)
  naturality := by
    intro m n b g
    apply Bilinear.ext
    intro p q x y
    simp only [mapBilinear, neg, dayInternalHom,
      DayInternalHom.module, DayInternalHom.precompose]

@[simp]
theorem map_id (M : Module) :
    map (Hom.id M) = Hom.id (neg M) := by
  apply Hom.ext
  intro n b
  apply Bilinear.ext
  intro p q x y
  exact rfl

@[simp]
theorem map_comp {L M N : Module} (g : Hom M N) (f : Hom L M) :
    map (Hom.comp g f) = Hom.comp (map f) (map g) := by
  apply Hom.ext
  intro n b
  apply Bilinear.ext
  intro p q x y
  exact rfl

/-- Evaluation after symmetry, whose transpose is the double-negation unit. -/
noncomputable def unitBilinear (M : Module) :
    Bilinear M (neg M) dayTensorUnit where
  app := fun {m n} x b =>
    dayTensorUnit.act
      (b.app (Superoperator.identity n) x)
      (Superoperator.tensorSwap m n)
  map_zero_left := by
    intro m n b
    change Bilinear (representable n) M dayTensorUnit at b
    change dayTensorUnit.act
      (b.app (show ((representable n).obj n).Carrier from
        Superoperator.identity n) 0)
      (Superoperator.tensorSwap m n) = 0
    rw [b.map_zero_right]
    exact dayTensorUnit.act_zero_element _
  map_zero_right := by
    intro m n x
    change Superoperator.comp (0 : Superoperator (n * m) 1)
      (Superoperator.tensorSwap m n) = 0
    rw [Superoperator.comp_zero_left]
  map_sum_left := by
    intro ι _ m n x s b h
    exact dayTensorUnit.act_sum_element _
      (b.map_sum_right (Superoperator.identity n) h)
  map_sum_right := by
    intro ι _ m n x b s h
    apply dayTensorUnit.act_sum_element
    exact h n m (Superoperator.identity n) x
  naturality := by
    intro m' m n' n x b f g
    change Bilinear (representable n) M dayTensorUnit at b
    change
      Superoperator.comp
          (b.app (Superoperator.comp g (Superoperator.identity n'))
            (M.act x f))
          (Superoperator.tensorSwap m' n') =
        Superoperator.comp
          (Superoperator.comp
            (b.app (Superoperator.identity n) x)
            (Superoperator.tensorSwap m n))
          (Superoperator.tensor f g)
    rw [Superoperator.comp_identity]
    have hb := b.naturality (Superoperator.identity n) x g f
    change
      b.app (Superoperator.comp (Superoperator.identity n) g)
          (M.act x f) =
        dayTensorUnit.act
          (b.app (show ((representable n).obj n).Carrier from
            Superoperator.identity n) x)
          (Superoperator.tensor g f) at hb
    rw [Superoperator.identity_comp] at hb
    let z : Superoperator (n * m) 1 :=
      show (dayTensorUnit.obj (n * m)).Carrier from
        b.app (show ((representable n).obj n).Carrier from
          Superoperator.identity n) x
    change b.app g (M.act x f) =
      Superoperator.comp z (Superoperator.tensor g f) at hb
    rw [hb]
    change
      Superoperator.comp
          (Superoperator.comp z (Superoperator.tensor g f))
          (Superoperator.tensorSwap m' n') =
        Superoperator.comp
          (Superoperator.comp z (Superoperator.tensorSwap m n))
          (Superoperator.tensor f g)
    rw [← Superoperator.comp_assoc, ← Superoperator.comp_assoc]
    congr 1
    exact (Superoperator.tensorSwap_naturality f g).symm

/-- Canonical continuation map `M → M⊥⊥`. -/
noncomputable def unit (M : Module) : Hom M (neg (neg M)) :=
  DayInternalHom.curry (unitBilinear M)

/-- Naturality of the canonical double-negation unit. -/
theorem unit_natural {M N : Module} (f : Hom M N) :
    Hom.comp (unit N) f = Hom.comp (map (map f)) (unit M) := by
  apply Hom.ext
  intro n x
  apply Bilinear.ext
  intro p q r b
  change Bilinear (representable q) N dayTensorUnit at b
  simp only [Hom.comp_app, unit, DayInternalHom.curry, unitBilinear,
    map, mapBilinear]
  exact congrArg
    (fun z => Superoperator.comp
      (b.app (show ((representable q).obj q).Carrier from
        Superoperator.identity q) z)
      (Superoperator.tensorSwap p q))
    (f.naturality x r).symm

/-- The concrete negation data supplied by Day closure. -/
noncomputable def data : NegationData where
  neg := neg
  map := map
  map_id := map_id
  map_comp := map_comp
  unit := unit
  unit_natural := unit_natural

end DayNegation

/-- A based module canonically isomorphic to its second dual. -/
structure ClassicalObject (D : NegationData.{u}) where
  module : Module.{u}
  basis : PseudoBasis module
  reflexive : Iso module (D.doubleDual module)
  canonical : reflexive.hom = D.unit module

/-- The actual biorthogonal objects for Day negation.  This is a full
subcategory selected by an exhibited inverse to the canonical continuation
map; generic continuation objects are deliberately not included. -/
abbrev BiorthogonalObject :=
  ClassicalObject (DayNegation.data)

namespace ClassicalObject

variable {D : NegationData.{u}}

/-- Morphisms in the classical subcategory are the underlying module maps;
the subcategory is full. -/
abbrev Hom (M N : ClassicalObject D) : Type u :=
  SuperoperatorModule.Hom M.module N.module

def id (M : ClassicalObject D) : Hom M M :=
  SuperoperatorModule.Hom.id M.module

def comp {L M N : ClassicalObject D}
    (g : Hom M N) (f : Hom L M) : Hom L N :=
  SuperoperatorModule.Hom.comp g f

@[simp]
theorem id_comp {M N : ClassicalObject D} (f : Hom M N) :
    comp (id N) f = f :=
  SuperoperatorModule.Hom.id_comp f

@[simp]
theorem comp_id {M N : ClassicalObject D} (f : Hom M N) :
    comp f (id M) = f :=
  SuperoperatorModule.Hom.comp_id f

theorem comp_assoc {K L M N : ClassicalObject D}
    (h : Hom M N) (g : Hom L M) (f : Hom K L) :
    comp h (comp g f) = comp (comp h g) f :=
  SuperoperatorModule.Hom.comp_assoc h g f

end ClassicalObject

end SuperoperatorModule

end QLambda.Domain.Presheaf
