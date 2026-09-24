/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentModel
import QLambda.Linear.FragmentContext
import QLambda.Domain.Presheaf.AdditiveProduct

/-!
# Explicit fragment `ite` branching interface
-/

namespace QLambda.Linear

open Domain.Presheaf
open Domain.Presheaf.SuperoperatorModule

/-- The sole effect not supplied by symmetric monoidal closed structure:
selection between two already-denoted branches.  Keeping this interface
explicit prevents a zero/fallback map from masquerading as `ite` semantics. -/
structure FragmentBranching where
  iteElim :
    ∀ {A : Ty}, Ty.SemanticFragment A →
      Hom
        (dayTensor (fragmentModule .bit)
          (additiveProduct (fragmentModule A) (fragmentModule A)))
        (fragmentModule A)


end QLambda.Linear
