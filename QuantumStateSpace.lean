/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Sub-normalized density operators (Loewner order)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

/-- Sub-normalized density operator on `M_n(ℂ)`: positive semidefinite
with real trace at most one. -/
structure SubNormalizedDensity (n : ℕ) where
  mat : Matrix (Fin n) (Fin n) ℂ
  posSemidef : mat.PosSemidef
  trace_le_one : (Matrix.trace mat).re ≤ 1

namespace SubNormalizedDensity

variable {n : ℕ}

@[ext]
theorem ext {ρ σ : SubNormalizedDensity n} (h : ρ.mat = σ.mat) : ρ = σ := by
  cases ρ; cases σ; congr

/-- Loewner order: `ρ ≤ σ` iff `σ − ρ` is positive semidefinite. -/
instance : PartialOrder (SubNormalizedDensity n) where
  le ρ σ := ρ.mat ≤ σ.mat
  le_refl ρ := le_refl ρ.mat
  le_trans ρ σ τ := le_trans
  le_antisymm ρ σ hρσ hσρ := ext (le_antisymm hρσ hσρ)

theorem le_def {ρ σ : SubNormalizedDensity n} :
    ρ ≤ σ ↔ ρ.mat ≤ σ.mat :=
  Iff.rfl

theorem le_iff {ρ σ : SubNormalizedDensity n} :
    ρ ≤ σ ↔ (σ.mat - ρ.mat).PosSemidef :=
  Iff.rfl

/-- If `A` and `-A` are both positive semidefinite, then `A = 0`. -/
theorem le_antisymm_of_posSemidef_neg {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hneg : (-A).PosSemidef) : A = 0 := by
  have h₁ : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ A := by
    simpa [nonneg_iff_posSemidef] using hA
  have h₂ : A ≤ (0 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Matrix.le_iff, zero_sub]
    exact hneg
  exact le_antisymm h₂ h₁

theorem re_trace_nonneg (ρ : SubNormalizedDensity n) :
    0 ≤ (Matrix.trace ρ.mat).re := by
  have hsum : (Matrix.trace ρ.mat).re = ∑ i : Fin n, (ρ.mat i i).re := by
    simp [Matrix.trace]
  rw [hsum]
  exact Finset.sum_nonneg fun i _ =>
    (RCLike.nonneg_iff (K := ℂ).mp (ρ.posSemidef.diag_nonneg (i := i))).1

instance : OrderBot (SubNormalizedDensity n) where
  bot := ⟨0, PosSemidef.zero, by simp [Matrix.trace_zero]⟩
  bot_le ρ := by
    change (ρ.mat - 0).PosSemidef
    simpa using ρ.posSemidef

theorem mat_bot : (⊥ : SubNormalizedDensity n).mat = 0 := rfl

noncomputable def spectralScale (t : ℝ) : ℝ := Real.exp (-max t 0)

theorem spectralScale_nonneg (t : ℝ) : 0 ≤ spectralScale t :=
  Real.exp_nonneg _

theorem spectralScale_le_one (t : ℝ) : spectralScale t ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_right t 0))

theorem spectralScale_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    spectralScale t = Real.exp (-t) := by
  simp [spectralScale, ht]

/-- Spectral depletion flow: `Φ_t(ρ) = e^{-max(t,0)} ρ`. -/
noncomputable def spectralErode (t : ℝ) (ρ : SubNormalizedDensity n) :
    SubNormalizedDensity n where
  mat := spectralScale t • ρ.mat
  posSemidef := ρ.posSemidef.smul (spectralScale_nonneg t)
  trace_le_one := by
    have hre := ρ.re_trace_nonneg
    calc
      (Matrix.trace (spectralScale t • ρ.mat)).re
          = spectralScale t * (Matrix.trace ρ.mat).re := by
            simp [Matrix.trace_smul]
      _ ≤ 1 * (Matrix.trace ρ.mat).re :=
            mul_le_mul_of_nonneg_right (spectralScale_le_one t) hre
      _ = (Matrix.trace ρ.mat).re := one_mul _
      _ ≤ 1 := ρ.trace_le_one

theorem spectralErode_mat (t : ℝ) (ρ : SubNormalizedDensity n) :
    (spectralErode t ρ).mat = spectralScale t • ρ.mat := rfl

theorem spectralErode_mono {t : ℝ} (_ht : 0 ≤ t) {ρ σ : SubNormalizedDensity n}
    (h : ρ ≤ σ) : spectralErode t ρ ≤ spectralErode t σ := by
  change ((spectralErode t σ).mat - (spectralErode t ρ).mat).PosSemidef
  have : (spectralErode t σ).mat - (spectralErode t ρ).mat =
      spectralScale t • (σ.mat - ρ.mat) := by
    simp [spectralErode_mat, smul_sub]
  rw [this]
  exact (le_iff.mp h).smul (spectralScale_nonneg t)

end SubNormalizedDensity
