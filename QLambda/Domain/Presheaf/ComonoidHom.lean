/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Comonoid

/-!
# Morphisms of commutative Day comonoids
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

set_option maxHeartbeats 8000000

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-- Morphisms of commutative comonoids: underlying module maps preserving
counit and comultiplication. -/
structure ComonoidHom (C D : Comonoid) where
  hom : Hom C.carrier D.carrier
  preserves_counit :
    Hom.comp D.counit hom = C.counit
  preserves_comult :
    Hom.comp D.comult hom =
      Hom.comp (DayTensor.map hom hom) C.comult

namespace ComonoidHom

@[ext]
theorem ext {C D : Comonoid} {f g : ComonoidHom C D}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (C : Comonoid) : ComonoidHom C C where
  hom := Hom.id C.carrier
  preserves_counit := by simp
  preserves_comult := by simp [DayTensor.map_id]

def comp {C D E : Comonoid}
    (g : ComonoidHom D E) (f : ComonoidHom C D) :
    ComonoidHom C E where
  hom := Hom.comp g.hom f.hom
  preserves_counit := by
    rw [Hom.comp_assoc, g.preserves_counit, f.preserves_counit]
  preserves_comult := by
    rw [Hom.comp_assoc, g.preserves_comult, ← Hom.comp_assoc,
      f.preserves_comult, Hom.comp_assoc, DayTensor.map_comp]

@[simp]
theorem id_hom (C : Comonoid) : (id C).hom = Hom.id C.carrier :=
  rfl

@[simp]
theorem comp_hom {C D E : Comonoid}
    (g : ComonoidHom D E) (f : ComonoidHom C D) :
    (comp g f).hom = Hom.comp g.hom f.hom :=
  rfl

end ComonoidHom

end SuperoperatorModule

end QLambda.Domain.Presheaf
