/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.OmegaCPO

/-!
# Bundled pointed ωCPO
-/

namespace QLambda.Domain

universe u

set_option linter.checkUnivs false

/-- A bundled ω-complete partial order. -/
structure OmegaObject where
  Carrier : Type u
  partialOrder : PartialOrder Carrier
  omegaComplete : OmegaComplete Carrier

attribute [instance] OmegaObject.partialOrder OmegaObject.omegaComplete

namespace OmegaObject

instance instCoeSortOmegaObject : CoeSort OmegaObject (Type u) :=
  ⟨OmegaObject.Carrier⟩

end OmegaObject

end QLambda.Domain
