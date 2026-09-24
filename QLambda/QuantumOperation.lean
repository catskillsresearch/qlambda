/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.KrausFamilyInstances

/-!
# Trace-nonincreasing quantum operations
-/

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace QLambda

/-- A trace-nonincreasing completely positive map, represented by
finitely many Kraus operators. -/
structure QuantumOperation (n m : ℕ) where
  kraus : KrausFamily n m
  trace_nonincreasing :
    ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (KrausFamily.applyMat kraus ρ)).re ≤
        (Matrix.trace ρ).re

namespace QuantumOperation

/-- The identity quantum operation. -/
def identity (n : ℕ) : QuantumOperation n n where
  kraus := KrausFamily.identity n
  trace_nonincreasing := by
    intro ρ _
    rw [KrausFamily.applyMat_identity]

/-- The zero (completely forgetful) operation. -/
def zero (n m : ℕ) : QuantumOperation n m where
  kraus := KrausFamily.zero
  trace_nonincreasing := by
    intro ρ hρ
    have htr : 0 ≤ Matrix.trace ρ := PosSemidef.trace_nonneg hρ
    rw [KrausFamily.applyMat_zero, Matrix.trace_zero, Complex.zero_re]
    exact (RCLike.nonneg_iff (K := ℂ).mp htr).1

/-- Sequential composition of trace-nonincreasing CP maps. -/
def comp {n m ℓ : ℕ} (Ψ : QuantumOperation m ℓ) (Φ : QuantumOperation n m) :
    QuantumOperation n ℓ where
  kraus := KrausFamily.comp Ψ.kraus Φ.kraus
  trace_nonincreasing := by
    intro ρ hρ
    rw [KrausFamily.applyMat_comp]
    exact (Ψ.trace_nonincreasing _ (KrausFamily.applyMat_posSemidef Φ.kraus hρ)).trans
      (Φ.trace_nonincreasing ρ hρ)

/-- Action on a sub-normalized density. -/
def apply {n m : ℕ} (Φ : QuantumOperation n m) (ρ : SubNormalizedDensity n) :
    SubNormalizedDensity m where
  mat := KrausFamily.applyMat Φ.kraus ρ.mat
  posSemidef := KrausFamily.applyMat_posSemidef Φ.kraus ρ.posSemidef
  trace_le_one :=
    (Φ.trace_nonincreasing ρ.mat ρ.posSemidef).trans ρ.trace_le_one

/-- One-element family of an isometry is a quantum operation. -/
def ofIsometry {n m : ℕ} (A : KrausOperator n m) (hA : Aᴴ * A = 1) :
    QuantumOperation n m where
  kraus := [A]
  trace_nonincreasing := by
    intro ρ _
    rw [KrausFamily.trace_applyMat_isometry A hA]

end QuantumOperation

end QLambda
