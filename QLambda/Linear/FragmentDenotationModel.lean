/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentDenotation

/-!
# Full compositional fragment denotation model
-/

namespace QLambda.Linear

open Domain.Presheaf
open Domain.Presheaf.SuperoperatorModule

/-- Operations required for full compositional fragment denotation. -/
structure FragmentDenotationModel where
  /-- Open-term denotation on combined contexts. -/
  denote :
    ∀ {Γ Δ M A}, FragCert Γ Δ M A →
      Hom (FragmentContext.combined Γ Δ) (fragmentModule A)
  /-- Closed unit agrees with Route A. -/
  denote_unit :
    ∀ (c : FragCert.Closed .unit .unit),
      denote c =
        FragmentContext.closedPoint routeAFragmentModel.unitIntro
  /-- Closed bit literals agree with Route A. -/
  denote_bitLit :
    ∀ (b : Bool) (c : FragCert.Closed (.bitLit b) .bit),
      denote c =
        FragmentContext.closedPoint (routeAFragmentModel.bitLit b)


end QLambda.Linear
