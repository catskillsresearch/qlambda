/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Classical

/-!
# Canonical reflexivity (double-dual invertibility)
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u

/-- Exact, non-idempotence-assuming witness that the canonical continuation
map of one module is invertible. -/
structure CanonicalReflexivity (M : Module) where
  inv : Hom (DayNegation.neg (DayNegation.neg M)) M
  hom_inv :
    Hom.comp (DayNegation.unit M) inv =
      Hom.id (DayNegation.neg (DayNegation.neg M))
  inv_hom :
    Hom.comp inv (DayNegation.unit M) = Hom.id M

/-- Package a canonical-reflexivity witness as an isomorphism. -/
noncomputable def CanonicalReflexivity.iso {M : Module}
    (h : CanonicalReflexivity M) :
    Iso M (DayNegation.neg (DayNegation.neg M)) where
  hom := DayNegation.unit M
  inv := h.inv
  hom_inv := h.hom_inv
  inv_hom := h.inv_hom

/-- The exact finite-dimensional biorthogonality statement still required
to put a representable in the classical category. -/
abbrev RepresentableReflexivity (A : ℕ) :=
  CanonicalReflexivity (representable A)

end SuperoperatorModule

end QLambda.Domain.Presheaf
