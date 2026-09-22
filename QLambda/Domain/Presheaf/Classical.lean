/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.PseudoRepresentable

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

/-- A based module canonically isomorphic to its second dual. -/
structure ClassicalObject (D : NegationData.{u}) where
  module : Module.{u}
  basis : PseudoBasis module
  reflexive : Iso module (D.doubleDual module)
  canonical : reflexive.hom = D.unit module

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
