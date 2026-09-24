/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.DayNegation

/-!
# Classical (biorthogonal) objects
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u

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
