/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.DayTensorPresentation

/-!
# Interface for general Day monoidal closure
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

/-- Exact interface for general Day monoidal closure.

The representable results above instantiate each field on the elementary
fragment.  `DayCoend.lean` constructs the general enriched coend quotient and
provides a concrete value of this structure. -/
structure DayClosedPresentation where
  tensor :
    (M N : Module) → DayTensorPresentation M N
  internalHom :
    Module → Module → Module
  closed :
    ∀ (X A N : Module),
      Hom (tensor X A).object N ≃ Hom X (internalHom A N)

end SuperoperatorModule

end QLambda.Domain.Presheaf
