/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.CategoryPresentation
import QLambda.Domain.Presheaf.ClassicalZeroInstances

/-!
# Full category of Day-biorthogonal objects
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u

/-- The mathematically valid full category of Day-biorthogonal objects.
Objects contain a pseudo-basis and an inverse to the canonical unit. -/
noncomputable def biorthogonalCategory : CategoryPresentation where
  Obj := ClassicalObject (DayNegation.data)
  hom := ClassicalObject.Hom
  id := ClassicalObject.id _
  comp := ClassicalObject.comp
  id_comp := ClassicalObject.id_comp
  comp_id := ClassicalObject.comp_id
  assoc := fun h g f => (ClassicalObject.comp_assoc h g f).symm


end SuperoperatorModule

end QLambda.Domain.Presheaf
