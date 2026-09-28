/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import Mathlib.Order.Antisymmetrization
public import QLambda.QuantumInstruments
public import QLambda.Composer.MatrixSemantics

@[expose] public section

/-!
# Presentation-independent finite-dimensional CP maps (`CompletedCP`)
-/

namespace QLambda.Domain

open scoped BigOperators ComplexConjugate MatrixOrder

/-- Finite Kraus presentation of a CP map. -/
structure CPPresentation (n m : ℕ) where
  kraus : KrausFamily n m

end QLambda.Domain

