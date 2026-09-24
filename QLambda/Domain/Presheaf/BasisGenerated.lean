/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Basis

/-!
# Basis-generated specialized modules
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u

/-- A specialized module together with an exhibited generalized countable
basis.  This data is useful for coefficient calculations but is not by itself
a generated-subcategory predicate. -/
structure BasisGenerated where
  module : Module.{u}
  basis : Basis module

/-- A representable as a basis-generated object. -/
noncomputable def generatedRepresentable (A : ℕ) :
    BasisGenerated.{0} where
  module := representable A
  basis := representableBasis A

end SuperoperatorModule

end QLambda.Domain.Presheaf
