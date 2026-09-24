/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.HomInstances

/-!
# Isomorphisms of specialized superoperator modules
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SuperoperatorModule

universe u v

/-- A module isomorphism, used without importing a second categorical
interface. -/
structure Iso (M : Module.{u}) (N : Module.{v}) where
  hom : Hom M N
  inv : Hom N M
  hom_inv : Hom.comp hom inv = Hom.id N
  inv_hom : Hom.comp inv hom = Hom.id M


end SuperoperatorModule

end QLambda.Domain.Presheaf
