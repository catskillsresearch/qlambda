/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.PseudoBasis

/-!
# Orthogonal pseudo-representable bases
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped ComplexOrder MatrixOrder

namespace SuperoperatorModule

universe u

/-- Orthogonality is an optional strengthening of a pseudo-representable
basis; it does not imply diagonal normalization. -/
structure OrthogonalPseudoBasis (M : Module.{u}) where
  basis : PseudoBasis M
  orthogonal :
    ∀ i j, i ≠ j →
      Hom.comp (basis.bra i) (basis.ket j) = 0

end SuperoperatorModule

end QLambda.Domain.Presheaf
