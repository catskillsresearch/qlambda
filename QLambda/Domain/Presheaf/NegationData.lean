/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.SuperoperatorModule

/-!
# Negation data for double-dual classical objects
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

end SuperoperatorModule

end QLambda.Domain.Presheaf
