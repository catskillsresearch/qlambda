/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.ModuleChoiSum

/-!
# Fiber of a specialized superoperator module
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SuperoperatorModule

universe u

/-- A carrier equipped with a relational partial countable sum. -/
structure Fiber where
  Carrier : Type u
  zero : Carrier
  summation : @SigmaMon.PartialCountableSum Carrier ⟨zero⟩

end SuperoperatorModule

end QLambda.Domain.Presheaf
