/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.ClosedCoefficient

/-!
# Closed bases over closed coefficient codes
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

/-- A countably based module whose coefficient objects all belong to the
concretely closed coefficient fragment. -/
structure ClosedBasis (M : Module) where
  Index : Type
  countableIndex : Countable Index
  coeff : Index → ClosedCoefficient
  ket : ∀ i, Hom (coeff i).toModule M
  bra : ∀ i, Hom M (coeff i).toModule
  resolves :
    Hom.HasSum
      (fun i : Index => Hom.comp (ket i) (bra i))
      (Hom.id M)

attribute [instance] ClosedBasis.countableIndex

end SuperoperatorModule

end QLambda.Domain.Presheaf
