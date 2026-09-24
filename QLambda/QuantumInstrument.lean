/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.QuantumOperation

/-!
# Finite quantum instruments
-/

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace QLambda

/-- A finite quantum instrument. Each outcome is CP, while trace
non-increase is required of the sum over all outcomes. -/
structure QuantumInstrument (n m outcomes : ℕ) where
  branch : Fin outcomes → KrausFamily n m
  trace_nonincreasing :
    ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (∑ i, (Matrix.trace (KrausFamily.applyMat (branch i) ρ)).re) ≤
        (Matrix.trace ρ).re

namespace QuantumInstrument

/-- Regard a quantum operation as a one-outcome instrument. -/
def singleton {n m : ℕ} (Φ : QuantumOperation n m) :
    QuantumInstrument n m 1 where
  branch := fun _ => Φ.kraus
  trace_nonincreasing := by
    intro ρ hρ
    simpa using Φ.trace_nonincreasing ρ hρ

end QuantumInstrument

end QLambda
