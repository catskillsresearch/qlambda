/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.QuantumInstruments

/-!
# Normalized runtime density states
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QLambda

/-- A normalized finite-dimensional density matrix. -/
structure NormalizedDensity (n : ℕ) where
  mat : Matrix (Fin n) (Fin n) ℂ
  posSemidef : mat.PosSemidef
  trace_eq_one : Matrix.trace mat = 1

namespace NormalizedDensity

variable {n m : ℕ}

@[ext]
theorem ext {ρ σ : NormalizedDensity n} (h : ρ.mat = σ.mat) : ρ = σ := by
  cases ρ
  cases σ
  congr

/-- Born weight of a Kraus branch on a normalized state. -/
def bornWeight (K : KrausFamily n m) (ρ : NormalizedDensity n) : ℝ :=
  (Matrix.trace (KrausFamily.applyMat K ρ.mat)).re

theorem bornWeight_nonneg (K : KrausFamily n m) (ρ : NormalizedDensity n) :
    0 ≤ bornWeight K ρ := by
  have hpos := KrausFamily.applyMat_posSemidef K ρ.posSemidef
  simpa [bornWeight, Matrix.trace] using
    (Finset.sum_nonneg fun (i : Fin m) (_ : i ∈ Finset.univ) =>
      (Complex.nonneg_iff.mp hpos.diag_nonneg).1)

/-- Normalize a positive Kraus branch. -/
noncomputable def normalizeBranch (K : KrausFamily n m)
    (ρ : NormalizedDensity n) (h : 0 < bornWeight K ρ) :
    NormalizedDensity m where
  mat := (bornWeight K ρ)⁻¹ • KrausFamily.applyMat K ρ.mat
  posSemidef :=
    (KrausFamily.applyMat_posSemidef K ρ.posSemidef).smul
      (inv_nonneg.mpr (le_of_lt h))
  trace_eq_one := by
    rw [Matrix.trace_smul]
    have hpos := KrausFamily.applyMat_posSemidef K ρ.posSemidef
    have him :
        (Matrix.trace (KrausFamily.applyMat K ρ.mat)).im = 0 := by
      simpa [Matrix.trace] using
        (Finset.sum_eq_zero fun (i : Fin m) (_ : i ∈ Finset.univ) =>
          (Complex.nonneg_iff.mp hpos.diag_nonneg).2.symm)
    have htrace :
        Matrix.trace (KrausFamily.applyMat K ρ.mat) =
          (bornWeight K ρ : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using him
    rw [htrace]
    simp [ne_of_gt h]

@[simp] theorem normalizeBranch_mat (K : KrausFamily n m)
    (ρ : NormalizedDensity n) (h : 0 < bornWeight K ρ) :
    (normalizeBranch K ρ h).mat =
      (bornWeight K ρ)⁻¹ • KrausFamily.applyMat K ρ.mat :=
  rfl

end NormalizedDensity

end QLambda
