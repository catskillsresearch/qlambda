/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.ProjectionChain
import QLambda.Domain.Enriched

/-!
# Recursive objects (fold/unfold solutions)
-/

namespace QLambda.Domain

/-- A fold/unfold solution of a locally continuous recursive-object
equation.  Concrete models construct this record from a projection
chain; clients consume the proved isomorphism rather than an axiom. -/
structure RecursiveObject (C : OmegaCategory) (F : C.Functor C) where
  carrier : C.Obj
  fold : C.Hom (F.obj carrier) carrier
  unfold : C.Hom carrier (F.obj carrier)
  fold_unfold : C.comp fold unfold = C.id
  unfold_fold : C.comp unfold fold = C.id


end QLambda.Domain
