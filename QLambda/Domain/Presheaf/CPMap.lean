/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.CompletedCP

/-!
# Intrinsic finite-dimensional completely positive maps

`CPMap n m` is a positive semidefinite Choi matrix, rather than a quotient or
a chosen Kraus presentation.  A Kraus family can always be recovered
noncomputably in finite dimensions; this is used to transport composition and
positivity results from the existing operator-sum development.
-/

namespace QLambda

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder NNReal

namespace KrausFamily

variable {n m : ℕ}

/-- The input effect `∑ᵢ Aᵢ† Aᵢ` of a Kraus family. -/
def effect (K : KrausFamily n m) : Matrix (Fin n) (Fin n) ℂ :=
  (K.map fun A => Aᴴ * A).sum

private theorem trace_mul_vecMulVec
    (E : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    Matrix.trace (E * Matrix.vecMulVec x (star x)) =
      star x ⬝ᵥ E *ᵥ x := by
  change (∑ i, ∑ j, E i j * (x j * star (x i))) =
    ∑ i, star (x i) * ∑ j, E i j * x j
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem trace_vecMulVec_self (x : Fin n → ℂ) :
    Matrix.trace (Matrix.vecMulVec x (star x)) = star x ⬝ᵥ x := by
  rw [Matrix.trace_vecMulVec]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem quad_sub_one
    (E : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    star x ⬝ᵥ (1 - E) *ᵥ x =
      Matrix.trace (Matrix.vecMulVec x (star x)) -
        Matrix.trace (E * Matrix.vecMulVec x (star x)) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    trace_mul_vecMulVec, trace_vecMulVec_self]

/-- Trace of a Kraus action is pairing with its input effect. -/
theorem trace_applyMat_eq_effect (K : KrausFamily n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (applyMat K ρ) = Matrix.trace (effect K * ρ) := by
  induction K with
  | nil => simp [applyMat, effect]
  | cons A K ih =>
    rw [applyMat_cons, Matrix.trace_add, ih]
    rw [Matrix.trace_mul_comm (A * ρ) Aᴴ, ← Matrix.mul_assoc]
    simp [effect, Matrix.add_mul, Matrix.trace_add]

theorem effect_posSemidef (K : KrausFamily n m) :
    (effect K).PosSemidef := by
  induction K with
  | nil =>
    simpa [effect] using
      (Matrix.PosSemidef.zero :
        (0 : Matrix (Fin n) (Fin n) ℂ).PosSemidef)
  | cons A K ih =>
    simp only [effect, List.map_cons, List.sum_cons]
    exact (Matrix.posSemidef_conjTranspose_mul_self A).add ih

/-- Testing TNI on all positive inputs forces the input effect below identity. -/
theorem effect_le_one_of_trace_nonincreasing (K : KrausFamily n m)
    (hK : ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (applyMat K ρ)).re ≤ (Matrix.trace ρ).re) :
    effect K ≤ 1 := by
  rw [Matrix.le_iff]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.IsHermitian.sub Matrix.isHermitian_one
      (effect_posSemidef K).isHermitian
  · intro x
    let ρ := Matrix.vecMulVec x (star x)
    have hρ : ρ.PosSemidef :=
      Matrix.posSemidef_vecMulVec_self_star x
    have hout : 0 ≤ Matrix.trace (applyMat K ρ) :=
      (applyMat_posSemidef K hρ).trace_nonneg
    have hin : 0 ≤ Matrix.trace ρ := hρ.trace_nonneg
    have hle : Matrix.trace (applyMat K ρ) ≤ Matrix.trace ρ := by
      rw [Complex.le_def]
      exact
        ⟨hK ρ hρ,
          (Complex.nonneg_iff.mp hout).2.symm.trans
            (Complex.nonneg_iff.mp hin).2⟩
    rw [quad_sub_one, ← trace_applyMat_eq_effect]
    exact sub_nonneg.mpr hle

private theorem trace_mul_nonneg_of_posSemidef
    {A ρ : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hρ : ρ.PosSemidef) :
    0 ≤ Matrix.trace (A * ρ) := by
  obtain ⟨k, v, rfl⟩ :=
    Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hρ
  rw [Matrix.mul_sum, Matrix.trace_sum]
  exact Finset.sum_nonneg fun i _ => by
    rw [trace_mul_vecMulVec]
    exact hA.dotProduct_mulVec_nonneg (v i)

/-- The effect bound implies trace non-increase on every positive input. -/
theorem trace_nonincreasing_of_effect_le_one (K : KrausFamily n m)
    (hK : effect K ≤ 1) :
    ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (applyMat K ρ)).re ≤ (Matrix.trace ρ).re := by
  intro ρ hρ
  have hdiff : (1 - effect K).PosSemidef := Matrix.le_iff.mp hK
  have htr := trace_mul_nonneg_of_posSemidef hdiff hρ
  have hre := (Complex.nonneg_iff.mp htr).1
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at hre
  rw [trace_applyMat_eq_effect]
  exact sub_nonneg.mp hre

end KrausFamily

end QLambda

namespace QLambda.Domain.Presheaf

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder

/-- An intrinsic completely positive map, represented by its positive
semidefinite Choi matrix. -/
structure CPMap (n m : ℕ) where
  choi : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ
  choi_pos : choi.PosSemidef

namespace CPMap

variable {n m ℓ r : ℕ}

@[ext]
theorem ext {Φ Ψ : CPMap n m} (h : Φ.choi = Ψ.choi) : Φ = Ψ := by
  cases Φ
  cases Ψ
  cases h
  rfl

/-- A finite Kraus presentation determines an intrinsic CP map. -/
def ofKraus (K : KrausFamily n m) : CPMap n m where
  choi := KrausFamily.choi K
  choi_pos := KrausFamily.choi_posSemidef K

@[simp]
theorem choi_ofKraus (K : KrausFamily n m) :
    (ofKraus K).choi = KrausFamily.choi K :=
  rfl

/-- Every intrinsic finite-dimensional CP map has a finite Kraus
presentation.  No choice of presentation is exposed as semantic data. -/
noncomputable def toKraus (Φ : CPMap n m) : KrausFamily n m :=
  Classical.choose (KrausFamily.exists_krausFamily_choi_eq Φ.choi_pos)

@[simp]
theorem choi_toKraus (Φ : CPMap n m) :
    KrausFamily.choi (toKraus Φ) = Φ.choi :=
  Classical.choose_spec
    (KrausFamily.exists_krausFamily_choi_eq Φ.choi_pos)

@[simp]
theorem ofKraus_toKraus (Φ : CPMap n m) : ofKraus (toKraus Φ) = Φ :=
  ext (choi_toKraus Φ)

theorem ofKraus_eq_iff (K L : KrausFamily n m) :
    ofKraus K = ofKraus L ↔ KrausFamily.SemEq K L := by
  rw [KrausFamily.semEq_iff_choi_eq]
  exact ⟨fun h => congrArg choi h, fun h => ext h⟩

/-- Application to an arbitrary matrix. -/
noncomputable def applyMat (Φ : CPMap n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  KrausFamily.applyMat (toKraus Φ) ρ

@[simp]
theorem applyMat_ofKraus (K : KrausFamily n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat (ofKraus K) ρ = KrausFamily.applyMat K ρ := by
  apply KrausFamily.semEq_of_choi_eq
  simp

theorem ext_apply {Φ Ψ : CPMap n m}
    (h : ∀ ρ, applyMat Φ ρ = applyMat Ψ ρ) : Φ = Ψ := by
  apply ext
  rw [← choi_toKraus Φ, ← choi_toKraus Ψ]
  exact KrausFamily.choi_eq_of_semEq h

theorem applyMat_posSemidef (Φ : CPMap n m)
    {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.PosSemidef) :
    (applyMat Φ ρ).PosSemidef :=
  KrausFamily.applyMat_posSemidef (toKraus Φ) hρ

theorem applyMat_add (Φ : CPMap n m)
    (ρ σ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat Φ (ρ + σ) = applyMat Φ ρ + applyMat Φ σ :=
  KrausFamily.applyMat_add (toKraus Φ) ρ σ

theorem applyMat_smul (Φ : CPMap n m) (c : ℂ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat Φ (c • ρ) = c • applyMat Φ ρ :=
  KrausFamily.applyMat_smul (toKraus Φ) c ρ

/-- The intrinsic input effect, obtained by tracing the Choi matrix over its
output coordinate.  The transposed input coordinates agree with `∑ᵢ Aᵢ†Aᵢ`. -/
def effect (Φ : CPMap n m) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ∑ a, Φ.choi (a, j) (a, i)

@[simp]
theorem effect_ofKraus (K : KrausFamily n m) :
    effect (ofKraus K) = KrausFamily.effect K := by
  ext i j
  induction K with
  | nil => simp [effect, KrausFamily.effect, KrausFamily.choi]
  | cons A K ih =>
    simp only [effect, choi_ofKraus, KrausFamily.choi_cons,
      Matrix.add_apply, Finset.sum_add_distrib, KrausFamily.effect,
      List.map_cons, List.sum_cons]
    change (∑ a, KrausFamily.choiTerm A (a, j) (a, i)) +
      effect (ofKraus K) i j =
        (Aᴴ * A) i j + KrausFamily.effect K i j
    rw [ih]
    apply congrArg (· + KrausFamily.effect K i j)
    simp only [KrausFamily.choiTerm, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro a _
    ring

theorem effect_posSemidef (Φ : CPMap n m) :
    Φ.effect.PosSemidef := by
  rw [← ofKraus_toKraus Φ, effect_ofKraus]
  exact KrausFamily.effect_posSemidef _

/-- Trace of an intrinsic CP action is pairing with its input effect. -/
theorem trace_applyMat_eq_effect (Φ : CPMap n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (applyMat Φ ρ) = Matrix.trace (Φ.effect * ρ) := by
  rw [← ofKraus_toKraus Φ, applyMat_ofKraus, effect_ofKraus]
  exact KrausFamily.trace_applyMat_eq_effect _ _

/-- Intrinsic finite-dimensional TNI is equivalent to the Choi partial trace
being below identity. -/
theorem effect_le_one_of_trace_nonincreasing (Φ : CPMap n m)
    (hΦ : ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (applyMat Φ ρ)).re ≤ (Matrix.trace ρ).re) :
    Φ.effect ≤ 1 := by
  let K := toKraus Φ
  have hK : ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (KrausFamily.applyMat K ρ)).re ≤
        (Matrix.trace ρ).re := by
    intro ρ hρ
    rw [← applyMat_ofKraus]
    simpa [K] using hΦ ρ hρ
  calc
    Φ.effect = effect (ofKraus K) := by
      change Φ.effect = effect (ofKraus (toKraus Φ))
      rw [ofKraus_toKraus]
    _ = KrausFamily.effect K := effect_ofKraus K
    _ ≤ 1 := KrausFamily.effect_le_one_of_trace_nonincreasing K hK

theorem trace_nonincreasing_of_effect_le_one (Φ : CPMap n m)
    (hΦ : Φ.effect ≤ 1) :
    ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (applyMat Φ ρ)).re ≤ (Matrix.trace ρ).re := by
  let K := toKraus Φ
  have hK : KrausFamily.effect K ≤ 1 := by
    rw [← effect_ofKraus]
    simpa [K] using hΦ
  intro ρ hρ
  rw [show applyMat Φ ρ = KrausFamily.applyMat K ρ by
    rw [← applyMat_ofKraus]
    simp [K]]
  exact KrausFamily.trace_nonincreasing_of_effect_le_one K hK ρ hρ

/-- The zero CP map. -/
def zero : CPMap n m :=
  ofKraus KrausFamily.zero

/-- Addition of CP maps is addition of their Choi matrices. -/
def add (Φ Ψ : CPMap n m) : CPMap n m where
  choi := Φ.choi + Ψ.choi
  choi_pos := Φ.choi_pos.add Ψ.choi_pos

noncomputable def scaleNonneg
    (c : ℝ) (hc : 0 ≤ c) (Φ : CPMap n m) : CPMap n m where
  choi := c • Φ.choi
  choi_pos := Φ.choi_pos.smul hc

/-- Canonical nonnegative-real scalar multiplication on intrinsic CP maps. -/
noncomputable def nnsmul (c : NNReal) (Φ : CPMap n m) : CPMap n m where
  choi := (c : ℂ) • Φ.choi
  choi_pos :=
    Φ.choi_pos.smul
      (Complex.nonneg_iff.mpr ⟨c.property, by simp⟩)

end CPMap

end QLambda.Domain.Presheaf
