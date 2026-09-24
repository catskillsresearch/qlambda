/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Order.Antisymmetrization
import QLambda.QuantumInstruments
import QLambda.Composer.MatrixSemantics

/-!
# Presentation-independent finite-dimensional CP maps (`CompletedCP`)
-/

namespace QLambda.Domain

open scoped BigOperators ComplexConjugate MatrixOrder

/-- Finite Kraus presentation of a CP map. -/
structure CPPresentation (n m : ℕ) where
  kraus : KrausFamily n m

end QLambda.Domain

