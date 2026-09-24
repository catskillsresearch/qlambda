/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.RepresentableBipolar.BornHomogeneity

/-!
# Polarization and density recovery

Parallelogram, polar sesquilinearity, Loewner extension, and spectral expansion.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder InnerProductSpace Kronecker

universe u

/-! ### Parallelogram / polarization recovery of the density -/

theorem smul_le_smul_one_of_le_one {A : ℕ} (E : Matrix (Fin A) (Fin A) ℂ)
    (_hE : E.PosSemidef) (hE1 : E ≤ 1) (c : ℝ) (hc0 : 0 ≤ c) :
    (c • E) ≤ (c • (1 : Matrix (Fin A) (Fin A) ℂ)) := by
  rw [Matrix.le_iff]
  have : c • (1 : Matrix (Fin A) (Fin A) ℂ) - c • E = c • (1 - E) := by
    ext; simp [Matrix.sub_apply, Matrix.smul_apply]; ring
  rw [this]
  exact (Matrix.le_iff.mp hE1).smul hc0

/-- Rank-one Loewner bound `|v⟩⟨v| ≤ ‖v‖² • I`. -/
theorem vecMulVec_le_normSq_smul_one {A : ℕ} (v : Fin A → ℂ) :
    Matrix.vecMulVec v (star v) ≤
      (((star v ⬝ᵥ v).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ)) := by
  classical
  by_cases hv : star v ⬝ᵥ v = 0
  · have hv0 : v = 0 := (dotProduct_star_self_eq_zero).1 hv
    have hre0 : (star v ⬝ᵥ v).re = 0 := by simp [hv]
    rw [show Matrix.vecMulVec v (star v) = 0 by simp [hv0],
      show (((star v ⬝ᵥ v).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ)) = 0 by
        simp [hre0]]
  · set û := normalizeVec v hv
    have hre := (star_dotProduct_self_nonneg_real v).1
    have him := (star_dotProduct_self_nonneg_real v).2
    set s : ℂ := ↑(Real.sqrt (star v ⬝ᵥ v).re)
    have hv_eq : v = s • û := by
      simp only [û, normalizeVec, s]
      ext i
      have hs_ne : s ≠ 0 := by
        intro hs0
        exact hv (Complex.ext
          ((Real.sqrt_eq_zero hre).1 (by simpa [s] using congrArg Complex.re hs0))
          him)
      change v i = s * (s⁻¹ * v i)
      field_simp [hs_ne]
    have hstar_s : star s = s := by simp [s, Complex.conj_ofReal]
    have hnrm_sq : star v ⬝ᵥ v = s * s := by
      apply Complex.ext
      · simpa [Complex.mul_re, s, Complex.ofReal_re] using
          (Real.mul_self_sqrt hre).symm
      · simpa [Complex.mul_im, s] using him
    have hmat : Matrix.vecMulVec v (star v) =
        (star v ⬝ᵥ v) • Matrix.vecMulVec û (star û) := by
      calc Matrix.vecMulVec v (star v)
          = Matrix.vecMulVec (s • û) (star (s • û)) := by rw [hv_eq]
        _ = (s * star s) • Matrix.vecMulVec û (star û) := vecMulVec_smul_star s û
        _ = (s * s) • Matrix.vecMulVec û (star û) := by rw [hstar_s]
        _ = (star v ⬝ᵥ v) • Matrix.vecMulVec û (star û) := by rw [← hnrm_sq]
    have hsmul_eq :
        ((star v ⬝ᵥ v).re : ℝ) • Matrix.vecMulVec û (star û) =
          (star v ⬝ᵥ v) • Matrix.vecMulVec û (star û) := by
      ext i j
      simp [Matrix.smul_apply, smul_eq_mul, ofReal_re_of_im_zero _ him]
    rw [hmat, ← hsmul_eq]
    exact smul_le_smul_one_of_le_one _
      (Matrix.posSemidef_vecMulVec_self_star û)
      (vecMulVec_unit_le_one û (normalizeVec_norm v hv)) _ hre

theorem vecMulVec_le_one_of_normSq_le {A : ℕ} (v : Fin A → ℂ)
    (hle : (star v ⬝ᵥ v).re ≤ 1) :
    Matrix.vecMulVec v (star v) ≤ (1 : Matrix (Fin A) (Fin A) ℂ) :=
  (vecMulVec_le_normSq_smul_one v).trans <|
    smul_le_one_of_le_one (1 : Matrix (Fin A) (Fin A) ℂ)
      PosSemidef.one le_rfl _ (star_dotProduct_self_nonneg_real v).1 hle

theorem star_dot_add_self {A : ℕ} (x y : Fin A → ℂ) :
    star (x + y) ⬝ᵥ (x + y) + star (x - y) ⬝ᵥ (x - y) =
      (2 : ℂ) * (star x ⬝ᵥ x + star y ⬝ᵥ y) := by
  simp only [dotProduct, Pi.add_apply, Pi.sub_apply, Pi.star_apply]
  have hterm : ∀ i,
      star (x i + y i) * (x i + y i) + star (x i - y i) * (x i - y i) =
        2 * (star (x i) * x i + star (y i) * y i) := by
    intro i; simp [star_add, star_sub]; ring
  calc ∑ i, star (x i + y i) * (x i + y i) +
        ∑ i, star (x i - y i) * (x i - y i)
      = ∑ i, (star (x i + y i) * (x i + y i) +
          star (x i - y i) * (x i - y i)) :=
        (Finset.sum_add_distrib).symm
    _ = ∑ i, (2 * (star (x i) * x i + star (y i) * y i)) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = 2 * ∑ i, (star (x i) * x i + star (y i) * y i) := by
        rw [← Finset.mul_sum]
    _ = 2 * (∑ i, star (x i) * x i + ∑ i, star (y i) * y i) := by
        simp [Finset.sum_add_distrib]

theorem star_dot_add_re_le {A : ℕ} (x y : Fin A → ℂ) :
    (star (x + y) ⬝ᵥ (x + y)).re ≤
      2 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) := by
  have hx := star_dotProduct_self_nonneg_real x
  have hy := star_dotProduct_self_nonneg_real y
  have hxy := (star_dotProduct_self_nonneg_real (x - y)).1
  have h := congrArg Complex.re (star_dot_add_self x y)
  simp only [Complex.add_re, Complex.mul_re, Complex.add_im, hx.2, hy.2,
    mul_zero, sub_zero, add_zero] at h
  have hsum :
      (star (x + y) ⬝ᵥ (x + y)).re + (star (x - y) ⬝ᵥ (x - y)).re =
        2 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) := by
    simpa [two_mul] using h
  linarith

theorem ofReal_smul_normSq {A : ℕ} (t : ℝ) (v : Fin A → ℂ) :
    (star ((t : ℂ) • v) ⬝ᵥ ((t : ℂ) • v)).re =
      t ^ 2 * (star v ⬝ᵥ v).re := by
  have him := (star_dotProduct_self_nonneg_real v).2
  have hstar : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  rw [star_dotProduct_smul_self, hstar]
  have hmul : ((t : ℂ) * (t : ℂ)).re = t ^ 2 := by simp [pow_two]
  have himt : ((t : ℂ) * (t : ℂ)).im = 0 := by simp
  simp [Complex.mul_re, him, himt, hmul]

theorem two_smul_vecMulVec_add_le_one {A : ℕ} (x y : Fin A → ℂ)
    (h : 2 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) ≤ 1) :
    (2 : ℝ) • Matrix.vecMulVec x (star x) +
      (2 : ℝ) • Matrix.vecMulVec y (star y) ≤
        (1 : Matrix (Fin A) (Fin A) ℂ) := by
  have hx := vecMulVec_le_normSq_smul_one x
  have hy := vecMulVec_le_normSq_smul_one y
  have hx2 : (2 : ℝ) • Matrix.vecMulVec x (star x) ≤
      (2 * (star x ⬝ᵥ x).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) := by
    rw [Matrix.le_iff]
    have : (2 * (star x ⬝ᵥ x).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) -
        (2 : ℝ) • Matrix.vecMulVec x (star x) =
        (2 : ℝ) • (((star x ⬝ᵥ x).re : ℝ) • 1 -
          Matrix.vecMulVec x (star x)) := by
      ext; simp [Matrix.sub_apply, Matrix.smul_apply]; ring
    rw [this]
    exact (Matrix.le_iff.mp hx).smul (by norm_num)
  have hy2 : (2 : ℝ) • Matrix.vecMulVec y (star y) ≤
      (2 * (star y ⬝ᵥ y).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) := by
    rw [Matrix.le_iff]
    have : (2 * (star y ⬝ᵥ y).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) -
        (2 : ℝ) • Matrix.vecMulVec y (star y) =
        (2 : ℝ) • (((star y ⬝ᵥ y).re : ℝ) • 1 -
          Matrix.vecMulVec y (star y)) := by
      ext; simp [Matrix.sub_apply, Matrix.smul_apply]; ring
    rw [this]
    exact (Matrix.le_iff.mp hy).smul (by norm_num)
  refine (add_le_add hx2 hy2).trans ?_
  have hsum :
      (2 * (star x ⬝ᵥ x).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) +
        (2 * (star y ⬝ᵥ y).re : ℝ) • 1 =
      (2 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) : ℝ) • 1 := by
    ext; simp [Matrix.add_apply, Matrix.smul_apply]; ring
  rw [hsum]
  exact smul_le_one_of_le_one (1 : Matrix (Fin A) (Fin A) ℂ)
    PosSemidef.one le_rfl _
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (add_nonneg (star_dotProduct_self_nonneg_real x).1
        (star_dotProduct_self_nonneg_real y).1)) h

/-- Scaling factor making `2(|tx⟩⟨tx|+|ty⟩⟨ty|) ≤ I`. -/
noncomputable def parallelScaleR {A : ℕ} (x y : Fin A → ℂ) : ℝ :=
  let N := (star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re
  Real.sqrt (1 / (2 * (N + 1)))

theorem parallelScaleR_pos {A : ℕ} (x y : Fin A → ℂ) :
    0 < parallelScaleR x y := by
  set N := (star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re
  have hN0 : 0 ≤ N :=
    add_nonneg (star_dotProduct_self_nonneg_real x).1
      (star_dotProduct_self_nonneg_real y).1
  have hden : 0 < 2 * (N + 1) := by
    nlinarith
  exact Real.sqrt_pos.2 (div_pos (by norm_num) hden)

theorem parallelScaleR_bound {A : ℕ} (x y : Fin A → ℂ) :
    2 * (parallelScaleR x y) ^ 2 *
      ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) ≤ 1 := by
  set N := (star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re
  have hN0 : 0 ≤ N :=
    add_nonneg (star_dotProduct_self_nonneg_real x).1
      (star_dotProduct_self_nonneg_real y).1
  have hden : 0 < 2 * (N + 1) := by nlinarith
  have hsq : (parallelScaleR x y) ^ 2 = 1 / (2 * (N + 1)) := by
    simp only [parallelScaleR, N]
    exact Real.sq_sqrt (div_nonneg (by norm_num) (le_of_lt hden))
  rw [hsq]
  have : 2 * (1 / (2 * (N + 1))) * N = N / (N + 1) := by
    field_simp [hden.ne']
  rw [this]
  exact div_le_one_of_le₀ (by linarith) (add_nonneg hN0 zero_le_one)

/-- Parallelogram identity for the double-dual Born quadratic form. -/
theorem effectPairingQuad_parallelogram {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y : Fin A → ℂ) :
    effectPairingQuad (doubleDualEffectPairing F) (x + y) +
      effectPairingQuad (doubleDualEffectPairing F) (x - y) =
      2 * effectPairingQuad (doubleDualEffectPairing F) x +
        2 * effectPairingQuad (doubleDualEffectPairing F) y := by
  set α := doubleDualEffectPairing F
  set t := parallelScaleR x y
  have ht0 : 0 < t := parallelScaleR_pos x y
  set x' : Fin A → ℂ := (t : ℂ) • x
  set y' : Fin A → ℂ := (t : ℂ) • y
  have hxN : (star x' ⬝ᵥ x').re = t ^ 2 * (star x ⬝ᵥ x).re := by
    simpa [x'] using ofReal_smul_normSq t x
  have hyN : (star y' ⬝ᵥ y').re = t ^ 2 * (star y ⬝ᵥ y).re := by
    simpa [y'] using ofReal_smul_normSq t y
  have hsumN : 2 * ((star x' ⬝ᵥ x').re + (star y' ⬝ᵥ y').re) ≤ 1 := by
    simp only [hxN, hyN]
    convert parallelScaleR_bound x y using 1
    ring
  have hx1 : Matrix.vecMulVec x' (star x') ≤ 1 :=
    vecMulVec_le_one_of_normSq_le _
      (by linarith [(star_dotProduct_self_nonneg_real y').1])
  have hy1 : Matrix.vecMulVec y' (star y') ≤ 1 :=
    vecMulVec_le_one_of_normSq_le _
      (by linarith [(star_dotProduct_self_nonneg_real x').1])
  have hxp_re : (star (x' + y') ⬝ᵥ (x' + y')).re ≤ 1 := by
    linarith [star_dot_add_re_le x' y']
  have hxm_re : (star (x' - y') ⬝ᵥ (x' - y')).re ≤ 1 := by
    have hx := star_dotProduct_self_nonneg_real x'
    have hy := star_dotProduct_self_nonneg_real y'
    have h := congrArg Complex.re (star_dot_add_self x' y')
    simp only [Complex.add_re, Complex.mul_re, Complex.add_im, hx.2, hy.2,
      mul_zero, sub_zero, add_zero] at h
    have hsum :
        (star (x' + y') ⬝ᵥ (x' + y')).re + (star (x' - y') ⬝ᵥ (x' - y')).re =
          2 * ((star x' ⬝ᵥ x').re + (star y' ⬝ᵥ y').re) := by
      simpa [two_mul] using h
    linarith [(star_dotProduct_self_nonneg_real (x' + y')).1]
  have hxp1 : Matrix.vecMulVec (x' + y') (star (x' + y')) ≤ 1 :=
    vecMulVec_le_one_of_normSq_le _ hxp_re
  have hxm1 : Matrix.vecMulVec (x' - y') (star (x' - y')) ≤ 1 :=
    vecMulVec_le_one_of_normSq_le _ hxm_re
  have hq_xp := effectPairingQuad_eq_expectation F (x' + y') hxp1
  have hq_xm := effectPairingQuad_eq_expectation F (x' - y') hxm1
  have hq_x := effectPairingQuad_eq_expectation F x' hx1
  have hq_y := effectPairingQuad_eq_expectation F y' hy1
  set Pxp := Matrix.vecMulVec (x' + y') (star (x' + y'))
  set Pxm := Matrix.vecMulVec (x' - y') (star (x' - y'))
  set Px := Matrix.vecMulVec x' (star x')
  set Py := Matrix.vecMulVec y' (star y')
  have hPxp1 : Pxp ≤ 1 := hxp1
  have hPxm1 : Pxm ≤ 1 := hxm1
  have hPx1 : Px ≤ 1 := hx1
  have hPy1 : Py ≤ 1 := hy1
  have hmatR : Pxp + Pxm = (2 : ℝ) • Px + (2 : ℝ) • Py := by
    have hmat := vecMulVec_parallelogram x' y'
    simp only [Pxp, Pxm, Px, Py]
    rw [hmat]
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply, two_smul]
  have h2le : (2 : ℝ) • Px + (2 : ℝ) • Py ≤ 1 := by
    simpa [Px, Py] using two_smul_vecMulVec_add_le_one x' y' hsumN
  have hsum_le : Pxp + Pxm ≤ 1 := by rwa [hmatR]
  have hsum_psd : (Pxp + Pxm).PosSemidef :=
    (Matrix.posSemidef_vecMulVec_self_star (x' + y')).add
      (Matrix.posSemidef_vecMulVec_self_star (x' - y'))
  have hadd_xp_xm :=
    effectExpectation_add_doubleDual F Pxp Pxm
      (Matrix.posSemidef_vecMulVec_self_star (x' + y'))
      (Matrix.posSemidef_vecMulVec_self_star (x' - y'))
      hPxp1 hPxm1 hsum_le
  have hA_eq : (2 : ℝ) • Px + (2 : ℝ) • Py = (2 : ℝ) • (Px + Py) := by
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply, two_smul]
  have h2A' : (2 : ℝ) • (Px + Py) ≤ 1 := by rwa [← hA_eq]
  have hA_le : Px + Py ≤ 1 := by
    have hhalf : Px + Py =
        ((2 : ℝ)⁻¹) • ((2 : ℝ) • (Px + Py)) := by
      ext i j
      simp [Matrix.add_apply, Matrix.smul_apply, two_smul]
      ring
    rw [hhalf]
    refine (smul_le_smul_one_of_le_one _
      (((Matrix.posSemidef_vecMulVec_self_star x').add
          (Matrix.posSemidef_vecMulVec_self_star y')).smul
        (by norm_num : (0 : ℝ) ≤ 2))
      h2A' _ (by norm_num)).trans ?_
    exact smul_le_one_of_le_one (1 : Matrix (Fin A) (Fin A) ℂ)
      PosSemidef.one le_rfl _ (by norm_num) (by norm_num)
  have hadd_xy :=
    effectExpectation_add_doubleDual F Px Py
      (Matrix.posSemidef_vecMulVec_self_star x')
      (Matrix.posSemidef_vecMulVec_self_star y')
      hPx1 hPy1 hA_le
  have hβ2 :=
    effectExpectation_nsmul_doubleDual F 2 (Px + Py)
      ((Matrix.posSemidef_vecMulVec_self_star x').add
        (Matrix.posSemidef_vecMulVec_self_star y'))
      hA_le h2A'
  have hβ_sum :
      effectExpectation α Pxp
          (Matrix.posSemidef_vecMulVec_self_star (x' + y')) hPxp1 +
        effectExpectation α Pxm
          (Matrix.posSemidef_vecMulVec_self_star (x' - y')) hPxm1 =
      (2 : ℂ) *
        (effectExpectation α Px
            (Matrix.posSemidef_vecMulVec_self_star x') hPx1 +
          effectExpectation α Py
            (Matrix.posSemidef_vecMulVec_self_star y') hPy1) := by
    have h1 :
        effectExpectation α Pxp
            (Matrix.posSemidef_vecMulVec_self_star (x' + y')) hPxp1 +
          effectExpectation α Pxm
            (Matrix.posSemidef_vecMulVec_self_star (x' - y')) hPxm1 =
        effectExpectation α (Pxp + Pxm) hsum_psd hsum_le :=
      hadd_xp_xm.symm
    have h2 :
        effectExpectation α (Pxp + Pxm) hsum_psd hsum_le =
        effectExpectation α ((2 : ℝ) • (Px + Py))
          (((Matrix.posSemidef_vecMulVec_self_star x').add
              (Matrix.posSemidef_vecMulVec_self_star y')).smul
            (by norm_num)) h2A' := by
      simp only [effectExpectation, α, hmatR, hA_eq]
    have h3 :
        effectExpectation α ((2 : ℝ) • (Px + Py))
          (((Matrix.posSemidef_vecMulVec_self_star x').add
              (Matrix.posSemidef_vecMulVec_self_star y')).smul
            (by norm_num)) h2A' =
        (2 : ℂ) * effectExpectation α (Px + Py)
          ((Matrix.posSemidef_vecMulVec_self_star x').add
            (Matrix.posSemidef_vecMulVec_self_star y')) hA_le := by
      simpa [α, Nat.cast_ofNat] using hβ2
    have h4 :
        effectExpectation α (Px + Py)
          ((Matrix.posSemidef_vecMulVec_self_star x').add
            (Matrix.posSemidef_vecMulVec_self_star y')) hA_le =
        effectExpectation α Px
            (Matrix.posSemidef_vecMulVec_self_star x') hPx1 +
          effectExpectation α Py
            (Matrix.posSemidef_vecMulVec_self_star y') hPy1 :=
      hadd_xy
    rw [h1, h2, h3, h4]
  have hq' :
      effectPairingQuad α (x' + y') + effectPairingQuad α (x' - y') =
        2 * effectPairingQuad α x' + 2 * effectPairingQuad α y' := by
    rw [hq_xp, hq_xm, hq_x, hq_y]
    simpa [α, Pxp, Pxm, Px, Py, two_mul, mul_add] using hβ_sum
  have htstar : star (t : ℂ) * (t : ℂ) = ↑(t ^ 2) := by
    simp [Complex.conj_ofReal, pow_two]
  have hxpy : x' + y' = (t : ℂ) • (x + y) := by
    ext i; simp [x', y', smul_add, mul_add]
  have hxmy : x' - y' = (t : ℂ) • (x - y) := by
    ext i; simp [x', y', smul_sub, mul_sub]
  rw [hxpy, hxmy] at hq'
  rw [effectPairingQuad_smul α (t : ℂ) (x + y),
    effectPairingQuad_smul α (t : ℂ) (x - y),
    effectPairingQuad_smul α (t : ℂ) x,
    effectPairingQuad_smul α (t : ℂ) y, htstar] at hq'
  -- hq' : ↑(t²)*q(x+y) + ↑(t²)*q(x-y) = 2*(↑(t²)*qx) + 2*(↑(t²)*qy)
  have hcoef : (↑(t ^ 2) : ℂ) ≠ 0 :=
    mod_cast (pow_ne_zero 2 ht0.ne')
  have hq'' :
      (↑(t ^ 2) : ℂ) *
          (effectPairingQuad α (x + y) + effectPairingQuad α (x - y)) =
        (↑(t ^ 2) : ℂ) *
          (2 * effectPairingQuad α x + 2 * effectPairingQuad α y) := by
    convert hq' using 1 <;> ring
  exact mul_left_cancel₀ hcoef hq''

/-- Parallelogram with `I • y` (uses `|I|² = 1`). -/
theorem effectPairingQuad_parallelogram_I {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y : Fin A → ℂ) :
    effectPairingQuad (doubleDualEffectPairing F) (x + Complex.I • y) +
      effectPairingQuad (doubleDualEffectPairing F) (x - Complex.I • y) =
      2 * effectPairingQuad (doubleDualEffectPairing F) x +
        2 * effectPairingQuad (doubleDualEffectPairing F) y := by
  have h := effectPairingQuad_parallelogram F x (Complex.I • y)
  have hI : effectPairingQuad (doubleDualEffectPairing F) (Complex.I • y) =
      effectPairingQuad (doubleDualEffectPairing F) y := by
    rw [effectPairingQuad_smul]
    have : star Complex.I * Complex.I = 1 := by
      simp [Complex.star_def, Complex.conj_I, neg_mul, Complex.I_mul_I]
    rw [this, one_mul]
  rw [hI] at h
  exact h

theorem q_phase_I {A : ℕ}
    (α : Superoperator A 1 → Superoperator 1 1) (v : Fin A → ℂ) :
    effectPairingQuad α (Complex.I • v) = effectPairingQuad α v := by
  rw [effectPairingQuad_smul]
  have : star Complex.I * Complex.I = 1 := by
    simp [Complex.conj_I, neg_mul, Complex.I_mul_I]
  rw [this, one_mul]

/-- Our polar equals the OfNorm-style polarization formula. -/
theorem effectPairingPolar_eq_ofNorm {A : ℕ}
    (α : Superoperator A 1 → Superoperator 1 1) (x y : Fin A → ℂ) :
    effectPairingPolar α x y =
      (effectPairingQuad α (x + y) - effectPairingQuad α (x - y) +
        Complex.I * effectPairingQuad α (Complex.I • x + y) -
        Complex.I * effectPairingQuad α (Complex.I • x - y)) / 4 := by
  have h1 : effectPairingQuad α (x + Complex.I • y) =
      effectPairingQuad α (Complex.I • x - y) := by
    have hmul : Complex.I • (x + Complex.I • y) = Complex.I • x - y := by
      ext i
      simp [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
      ring_nf; rw [Complex.I_sq]; ring
    calc effectPairingQuad α (x + Complex.I • y)
        = effectPairingQuad α (Complex.I • (x + Complex.I • y)) :=
          (q_phase_I α _).symm
      _ = effectPairingQuad α (Complex.I • x - y) := by rw [hmul]
  have h2 : effectPairingQuad α (x - Complex.I • y) =
      effectPairingQuad α (Complex.I • x + y) := by
    have hmul : Complex.I • (x - Complex.I • y) = Complex.I • x + y := by
      ext i
      simp [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      ring_nf; rw [Complex.I_sq]; ring
    calc effectPairingQuad α (x - Complex.I • y)
        = effectPairingQuad α (Complex.I • (x - Complex.I • y)) :=
          (q_phase_I α _).symm
      _ = effectPairingQuad α (Complex.I • x + y) := by rw [hmul]
  simp only [effectPairingPolar, h1, h2]
  ring

/-- Left additivity of the polarized form (Jordan–von Neumann / OfNorm). -/
theorem effectPairingPolar_add_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y z : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) (x + y) z =
      effectPairingPolar (doubleDualEffectPairing F) x z +
        effectPairingPolar (doubleDualEffectPairing F) y z := by
  set α := doubleDualEffectPairing F
  rw [effectPairingPolar_eq_ofNorm α (x + y) z,
    effectPairingPolar_eq_ofNorm α x z,
    effectPairingPolar_eq_ofNorm α y z]
  have H1 := effectPairingQuad_parallelogram F (x + y + z) (x - z)
  have H2 := effectPairingQuad_parallelogram F (x + y - z) (x + z)
  have H3 := effectPairingQuad_parallelogram F (y + z) z
  have H4 := effectPairingQuad_parallelogram F (y - z) z
  have H5 := effectPairingQuad_parallelogram F
    (Complex.I • (x + y) + z) (Complex.I • x - z)
  have H6 := effectPairingQuad_parallelogram F
    (Complex.I • (x + y) - z) (Complex.I • x + z)
  have H7 := effectPairingQuad_parallelogram F (Complex.I • y + z) z
  have H8 := effectPairingQuad_parallelogram F (Complex.I • y - z) z
  have s1 : x + y + z + (x - z) = (2 : ℂ) • x + y := by
    ext i; simp [two_smul]; ring
  have s1' : x + y + z - (x - z) = y + (2 : ℂ) • z := by
    ext i; simp [two_smul]; ring
  have s2 : x + y - z + (x + z) = (2 : ℂ) • x + y := by
    ext i; simp [two_smul]; ring
  have s2' : x + y - z - (x + z) = y - (2 : ℂ) • z := by
    ext i; simp [two_smul]; ring
  have s3 : (y + z) + z = y + (2 : ℂ) • z := by
    ext i; simp [two_smul]; ring
  have s3' : (y + z) - z = y := add_sub_cancel_right y z
  have s4 : (y - z) + z = y := sub_add_cancel y z
  have s4' : (y - z) - z = y - (2 : ℂ) • z := by
    ext i; simp [two_smul]; ring
  rw [s1, s1'] at H1; rw [s2, s2'] at H2
  rw [s3, s3'] at H3; rw [s4, s4'] at H4
  have t5 : Complex.I • (x + y) + z + (Complex.I • x - z) =
      Complex.I • ((2 : ℂ) • x + y) := by
    ext i; simp [two_smul, smul_add, Pi.smul_apply, smul_eq_mul]; ring
  have t5' : Complex.I • (x + y) + z - (Complex.I • x - z) =
      Complex.I • y + (2 : ℂ) • z := by
    ext i; simp [two_smul, smul_add, Pi.smul_apply, smul_eq_mul]; ring
  have t6 : Complex.I • (x + y) - z + (Complex.I • x + z) =
      Complex.I • ((2 : ℂ) • x + y) := by
    ext i; simp [two_smul, smul_add, Pi.smul_apply, smul_eq_mul]; ring
  have t6' : Complex.I • (x + y) - z - (Complex.I • x + z) =
      Complex.I • y - (2 : ℂ) • z := by
    ext i; simp [two_smul, smul_add, Pi.smul_apply, smul_eq_mul]; ring
  have t7 : Complex.I • y + z + z = Complex.I • y + (2 : ℂ) • z := by
    ext i; simp [two_smul]; ring
  have t7' : Complex.I • y + z - z = Complex.I • y :=
    add_sub_cancel_right _ _
  have t8 : Complex.I • y - z + z = Complex.I • y := sub_add_cancel _ _
  have t8' : Complex.I • y - z - z = Complex.I • y - (2 : ℂ) • z := by
    ext i; simp [two_smul]; ring
  rw [t5, t5'] at H5; rw [t6, t6'] at H6
  rw [t7, t7'] at H7; rw [t8, t8'] at H8
  have pI2 := q_phase_I α ((2 : ℂ) • x + y)
  have pIy := q_phase_I α y
  simp only [α] at H1 H2 H3 H4 H5 H6 H7 H8 pI2 pIy ⊢
  rw [pI2] at H5 H6
  rw [pIy] at H7 H8
  rw [← add_div]
  refine congrArg (fun t : ℂ => t / 4) ?_
  linear_combination
    (-H1 + H2 + H3 - H4 + Complex.I * (-H5 + H6 + H7 - H8)) / 2

theorem effectPairingPolar_zero_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) 0 y = 0 := by
  have h := effectPairingPolar_add_left F 0 0 y
  simp only [zero_add] at h
  exact (add_eq_left.mp h.symm)

theorem effectPairingPolar_nsmul_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (n : ℕ) (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) (n • x) y =
      (n : ℂ) * effectPairingPolar (doubleDualEffectPairing F) x y := by
  induction n with
  | zero => simp [effectPairingPolar_zero_left]
  | succ n ih =>
    rw [succ_nsmul, effectPairingPolar_add_left, ih]
    push_cast
    ring


/-! ### Polar sesquilinearity, density recovery, PSD, trace -/

theorem q_neg {A : ℕ} (α : Superoperator A 1 → Superoperator 1 1)
    (v : Fin A → ℂ) :
    effectPairingQuad α (-v) = effectPairingQuad α v := by
  have hv : -v = (-1 : ℂ) • v := by ext i; simp
  rw [hv, effectPairingQuad_smul]
  norm_num

theorem effectPairingQuad_star {A : ℕ}
    (α : Superoperator A 1 → Superoperator 1 1) (v : Fin A → ℂ) :
    star (effectPairingQuad α v) = effectPairingQuad α v := by
  have him := (effectPairingQuad_nonneg α v).2
  apply Complex.ext
  · simp [Complex.conj_re]
  · simp [Complex.conj_im, him]

theorem effectPairingPolar_conj_symm {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y : Fin A → ℂ) :
    star (effectPairingPolar (doubleDualEffectPairing F) y x) =
      effectPairingPolar (doubleDualEffectPairing F) x y := by
  set α := doubleDualEffectPairing F
  set Q := effectPairingQuad α
  simp only [effectPairingPolar]
  have hQ : ∀ v, star (Q v) = Q v := fun v => by
    simpa [Q] using effectPairingQuad_star α v
  have hyx : y + x = x + y := add_comm _ _
  have hyxm : Q (y - x) = Q (x - y) := by
    have : y - x = -(x - y) := by
      ext i; simp [Pi.sub_apply, Pi.neg_apply, sub_eq_add_neg]
    rw [this]; simpa [Q] using q_neg α (x - y)
  have h1 : Q (y + Complex.I • x) = Q (x - Complex.I • y) := by
    have hmul : Complex.I • (x - Complex.I • y) = Complex.I • x + y := by
      ext i; simp [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply]
      ring_nf; rw [Complex.I_sq]; ring
    have hcomm : y + Complex.I • x = Complex.I • x + y := add_comm _ _
    calc Q (y + Complex.I • x)
        = Q (Complex.I • x + y) := by rw [hcomm]
      _ = Q (Complex.I • (x - Complex.I • y)) := by rw [← hmul]
      _ = Q (x - Complex.I • y) := by simpa [Q] using q_phase_I α _
  have h2 : Q (y - Complex.I • x) = Q (x + Complex.I • y) := by
    have hmul : (-Complex.I) • (x + Complex.I • y) = y - Complex.I • x := by
      ext i; simp [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply]
      ring_nf; rw [Complex.I_sq]; ring
    have hphase : Q ((-Complex.I) • (x + Complex.I • y)) =
        Q (x + Complex.I • y) := by
      simp only [Q]
      rw [effectPairingQuad_smul]
      have : star (-(Complex.I : ℂ)) * (-Complex.I) = 1 := by
        apply Complex.ext <;> simp [Complex.conj_I, Complex.I_mul_I]
      rw [this, one_mul]
    calc Q (y - Complex.I • x)
        = Q ((-Complex.I) • (x + Complex.I • y)) := by rw [← hmul]
      _ = Q (x + Complex.I • y) := hphase
  have hstarI : star (Complex.I : ℂ) = -Complex.I := Complex.conj_I
  have hnum :
      star (Q (y + x) - Q (y - x) -
          Complex.I * Q (y + Complex.I • x) +
          Complex.I * Q (y - Complex.I • x)) =
        Q (x + y) - Q (x - y) -
          Complex.I * Q (x + Complex.I • y) +
          Complex.I * Q (x - Complex.I • y) := by
    simp only [star_sub, star_add, star_mul, hQ, hyx, hyxm, h1, h2, hstarI]
    ring
  have hdiv : star ((Q (y + x) - Q (y - x) -
      Complex.I * Q (y + Complex.I • x) +
      Complex.I * Q (y - Complex.I • x)) / 4) =
      star (Q (y + x) - Q (y - x) -
          Complex.I * Q (y + Complex.I • x) +
          Complex.I * Q (y - Complex.I • x)) / 4 := by
    rw [star_div₀]
    simp [star_ofNat]
  rw [hdiv, hnum]

theorem effectPairingPolar_add_right {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y z : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) x (y + z) =
      effectPairingPolar (doubleDualEffectPairing F) x y +
        effectPairingPolar (doubleDualEffectPairing F) x z := by
  -- conj_symm: star B(b,a) = B(a,b)
  have hyx := effectPairingPolar_conj_symm F x y
  have hzx := effectPairingPolar_conj_symm F x z
  have hyzx := effectPairingPolar_conj_symm F x (y + z)
  calc effectPairingPolar (doubleDualEffectPairing F) x (y + z)
      = star (effectPairingPolar (doubleDualEffectPairing F) (y + z) x) := hyzx.symm
    _ = star (effectPairingPolar (doubleDualEffectPairing F) y x +
          effectPairingPolar (doubleDualEffectPairing F) z x) := by
            rw [effectPairingPolar_add_left]
    _ = star (effectPairingPolar (doubleDualEffectPairing F) y x) +
          star (effectPairingPolar (doubleDualEffectPairing F) z x) := star_add _ _
    _ = effectPairingPolar (doubleDualEffectPairing F) x y +
          effectPairingPolar (doubleDualEffectPairing F) x z := by
            rw [hyx, hzx]


/-! ### Extension of Born reading off the Loewner interval -/

theorem PosSemidef.trace_mul_nonneg {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    0 ≤ Matrix.trace (X * Y) := by
  classical
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.nonneg
  rw [hC, hD]
  change 0 ≤ Matrix.trace (Cᴴ * C * (Dᴴ * D))
  have hcycle : Matrix.trace (Cᴴ * C * (Dᴴ * D)) =
      Matrix.trace ((D * Cᴴ)ᴴ * (D * Cᴴ)) := by
    simp only [Matrix.mul_assoc]
    rw [trace_mul_comm Cᴴ (C * (Dᴴ * D))]
    simp [conjTranspose_mul, Matrix.mul_assoc]
  rw [hcycle]
  exact (posSemidef_conjTranspose_mul_self (D * Cᴴ)).trace_nonneg

theorem PosSemidef.le_re_trace_smul_one {A : ℕ}
    (E : Matrix (Fin A) (Fin A) ℂ) (hE : E.PosSemidef) :
    E ≤ ((Matrix.trace E).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) := by
  rw [Matrix.le_iff]
  have h1 : IsHermitian (1 : Matrix (Fin A) (Fin A) ℂ) := isHermitian_one
  have hc : IsSelfAdjoint ((Matrix.trace E).re : ℂ) := by
    simp [IsSelfAdjoint, Complex.conj_ofReal]
  have hherm := (IsHermitian.smul h1 hc).sub hE.1
  refine PosSemidef.of_dotProduct_mulVec_nonneg hherm fun v => ?_
  have hn := star_dotProduct_self_nonneg_real v
  have hcalc :
      star v ⬝ᵥ ((((Matrix.trace E).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) - E) *ᵥ v) =
        ↑(Matrix.trace E).re * (star v ⬝ᵥ v) - star v ⬝ᵥ E *ᵥ v := by
    simp [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub]
  rw [hcalc]
  by_cases hv : star v ⬝ᵥ v = 0
  · have : v = 0 := (dotProduct_star_self_eq_zero).1 hv
    simp [this]
  · set û := normalizeVec v hv
    have hre := hn.1
    have him := hn.2
    set s : ℂ := ↑(Real.sqrt (star v ⬝ᵥ v).re)
    have hv_eq : v = s • û := by
      simp only [û, normalizeVec, s]
      ext i
      have hs_ne : s ≠ 0 := by
        intro hs0
        have : (star v ⬝ᵥ v).re = 0 :=
          (Real.sqrt_eq_zero hre).1 (by simpa [s] using congrArg Complex.re hs0)
        exact hv (Complex.ext this him)
      change v i = s * (s⁻¹ * v i)
      field_simp [hs_ne]
    have hstar_s : star s = s := by simp [s, Complex.conj_ofReal]
    have hnrm : star v ⬝ᵥ v = s * s := by
      apply Complex.ext
      · have : (star v ⬝ᵥ v).re = s.re * s.re := by
          simpa [s, Complex.ofReal_re] using (Real.mul_self_sqrt hre).symm
        simpa [Complex.mul_re, s] using this
      · simpa [Complex.mul_im, s] using him
    have hEv' : star v ⬝ᵥ E *ᵥ v = (s * s) * (star û ⬝ᵥ E *ᵥ û) := by
      calc star v ⬝ᵥ E *ᵥ v
          = star (s • û) ⬝ᵥ E *ᵥ (s • û) := by rw [hv_eq]
        _ = star s * s * (star û ⬝ᵥ E *ᵥ û) := quad_smul E s û
        _ = (s * s) * (star û ⬝ᵥ E *ᵥ û) := by rw [hstar_s]
    have hû1 : star û ⬝ᵥ û = 1 := normalizeVec_norm v hv
    have hP : Matrix.vecMulVec û (star û) ≤ 1 := vecMulVec_unit_le_one û hû1
    have hIPpsd : ((1 : Matrix (Fin A) (Fin A) ℂ) -
        Matrix.vecMulVec û (star û)).PosSemidef := Matrix.le_iff.mp hP
    have htr_split :
        Matrix.trace E =
          Matrix.trace (E * Matrix.vecMulVec û (star û)) +
            Matrix.trace (E * (1 - Matrix.vecMulVec û (star û))) := by
      have : Matrix.vecMulVec û (star û) + (1 - Matrix.vecMulVec û (star û)) = 1 := by abel
      rw [← Matrix.trace_add, ← Matrix.mul_add, this, Matrix.mul_one]
    have htrIP_nonneg :
        0 ≤ Matrix.trace (E * (1 - Matrix.vecMulVec û (star û))) :=
      PosSemidef.trace_mul_nonneg E _ hE hIPpsd
    have htrP :
        Matrix.trace (E * Matrix.vecMulVec û (star û)) = star û ⬝ᵥ E *ᵥ û := by
      simp only [Matrix.trace, diag_apply, mul_apply, vecMulVec_apply, dotProduct, mulVec]
      refine Finset.sum_congr rfl fun i _ => ?_
      calc ∑ j, E i j * (û j * star (û i))
          = ∑ j, star (û i) * (E i j * û j) :=
            Finset.sum_congr rfl fun j _ => by ring
        _ = star (û i) * ∑ j, E i j * û j := (Finset.mul_sum _ _ _).symm
    have himÛ : (star û ⬝ᵥ E *ᵥ û).im = 0 :=
      (Complex.nonneg_iff.mp (hE.dotProduct_mulVec_nonneg û)).2.symm
    have hre_bound : (star û ⬝ᵥ E *ᵥ û).re ≤ (Matrix.trace E).re := by
      have hsplit_re := congrArg Complex.re htr_split
      simp only [Complex.add_re] at hsplit_re
      have hnn := (Complex.nonneg_iff.mp htrIP_nonneg).1
      have : (Matrix.trace (E * Matrix.vecMulVec û (star û))).re ≤ (Matrix.trace E).re := by
        linarith
      simpa [htrP] using this
    have hss_im : (s * s).im = 0 := by simpa [← hnrm] using him
    refine Complex.nonneg_iff.mpr ⟨?_, ?_⟩
    · rw [hEv', hnrm]
      have hex :
          (((Matrix.trace E).re : ℂ) * (s * s) - (s * s) * (star û ⬝ᵥ E *ᵥ û)).re =
            (s * s).re * ((Matrix.trace E).re - (star û ⬝ᵥ E *ᵥ û).re) := by
        simp [Complex.sub_re, Complex.mul_re, hss_im, himÛ, Complex.ofReal_im]; ring
      rw [hex]
      have hss_re0 : 0 ≤ (s * s).re := by
        have : s * s = star v ⬝ᵥ v := hnrm.symm
        simpa [← this] using hre
      nlinarith [hre_bound]
    · rw [hEv', hnrm]
      simp [Complex.sub_im, Complex.mul_im, hss_im, himÛ, Complex.ofReal_re, Complex.ofReal_im]

theorem inv_smul_le_one_of_le_trace_smul {A : ℕ}
    (E : Matrix (Fin A) (Fin A) ℂ) (hE : E.PosSemidef) (c : ℝ)
    (hc : max (Matrix.trace E).re 1 ≤ c) (hc0 : 0 < c) :
    ((c⁻¹ : ℝ) • E) ≤ (1 : Matrix (Fin A) (Fin A) ℂ) := by
  have hE_le := PosSemidef.le_re_trace_smul_one E hE
  have ht_le : (Matrix.trace E).re ≤ c := (le_max_left _ _).trans hc
  have hE_le' : E ≤ (c : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) := by
    refine hE_le.trans ?_
    rw [Matrix.le_iff]
    have : (c : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) -
        ((Matrix.trace E).re : ℝ) • 1 = (c - (Matrix.trace E).re) • 1 := by
      ext; simp [Matrix.sub_apply, Matrix.smul_apply]; ring
    rw [this]
    exact (PosSemidef.one).smul (sub_nonneg.mpr ht_le)
  rw [Matrix.le_iff] at hE_le' ⊢
  have : (1 : Matrix (Fin A) (Fin A) ℂ) - (c⁻¹ : ℝ) • E =
      (c⁻¹ : ℝ) • (c • 1 - E) := by
    ext i j
    have hc0' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> field_simp [hc0'] <;> ring
  rw [this]
  exact hE_le'.smul (inv_nonneg.mpr hc0.le)

noncomputable def effectExpectationExt {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E : Matrix (Fin A) (Fin A) ℂ) (hE : E.PosSemidef) : ℂ :=
  let c : ℝ := max (Matrix.trace E).re 1
  (c : ℂ) *
    effectExpectation (doubleDualEffectPairing F)
      ((c⁻¹ : ℝ) • E)
      (hE.smul (inv_nonneg.mpr (le_trans zero_le_one (le_max_right _ _))))
      (inv_smul_le_one_of_le_trace_smul E hE c le_rfl
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)))

theorem effectExpectation_smul_nonneg_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (r : ℝ) (hr0 : 0 ≤ r)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1) (hrE : (r • E) ≤ 1) :
    effectExpectation (doubleDualEffectPairing F) (r • E) (hE.smul hr0) hrE =
      (r : ℂ) * effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  by_cases hr1 : r ≤ 1
  · exact effectExpectation_smul_doubleDual F r hr0 hr1 E hE hE1
  · have hr1' : 1 < r := not_le.mp hr1
    have hrpos : 0 < r := lt_trans (by norm_num) hr1'
    have hinv0 : 0 ≤ (r⁻¹ : ℝ) := inv_nonneg.mpr hr0
    have hinv1 : (r⁻¹ : ℝ) ≤ 1 := inv_le_one_of_one_le₀ (le_of_lt hr1')
    have hRE_psd : (r • E).PosSemidef := hE.smul hr0
    have hsmul :=
      effectExpectation_smul_doubleDual F r⁻¹ hinv0 hinv1 (r • E) hRE_psd hrE
    have hE_eq : (r⁻¹ : ℝ) • (r • E) = E := by
      ext i j; simp [Matrix.smul_apply]; field_simp [hrpos.ne']
    have hr_ne : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have hβE :
        effectExpectation (doubleDualEffectPairing F) E hE hE1 =
          (r : ℂ)⁻¹ *
            effectExpectation (doubleDualEffectPairing F) (r • E) hRE_psd hrE := by
      have : effectExpectation (doubleDualEffectPairing F) E hE hE1 =
          effectExpectation (doubleDualEffectPairing F)
            ((r⁻¹ : ℝ) • (r • E)) ((hE.smul hr0).smul hinv0)
            (smul_le_one_of_le_one (r • E) hRE_psd hrE r⁻¹ hinv0 hinv1) := by
        simp only [effectExpectation, hE_eq]
      rw [this, ← Complex.ofReal_inv]
      exact hsmul
    calc effectExpectation (doubleDualEffectPairing F) (r • E) (hE.smul hr0) hrE
        = (r : ℂ) * ((r : ℂ)⁻¹ *
            effectExpectation (doubleDualEffectPairing F) (r • E) hRE_psd hrE) := by
            rw [← mul_assoc, mul_inv_cancel₀ hr_ne, one_mul]
      _ = (r : ℂ) * effectExpectation (doubleDualEffectPairing F) E hE hE1 := by rw [← hβE]

/-- Ext(E) = t * β(t⁻¹ • E) for any sufficiently large t. -/
theorem effectExpectationExt_eq_of_scale {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E : Matrix (Fin A) (Fin A) ℂ) (hE : E.PosSemidef) (t : ℝ)
    (ht : max (Matrix.trace E).re 1 ≤ t) (ht0 : 0 < t) :
    effectExpectationExt F E hE =
      (t : ℂ) * effectExpectation (doubleDualEffectPairing F) ((t⁻¹ : ℝ) • E)
        (hE.smul (inv_nonneg.mpr ht0.le))
        (inv_smul_le_one_of_le_trace_smul E hE t ht ht0) := by
  set c : ℝ := max (Matrix.trace E).re 1
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  have hle : c ≤ t := ht
  -- Ext = c β(c⁻¹ E); want t β(t⁻¹ E)
  -- t⁻¹ E = (c/t) • (c⁻¹ E)
  have hmat : (t⁻¹ : ℝ) • E = ((c / t) : ℝ) • ((c⁻¹ : ℝ) • E) := by
    ext; simp [Matrix.smul_apply]; field_simp [ht0.ne', hc0.ne']
  have hratio0 : 0 ≤ c / t := div_nonneg hc0.le ht0.le
  have hratio1 : c / t ≤ 1 := (div_le_one ht0).mpr hle
  have hE0_psd : ((c⁻¹ : ℝ) • E).PosSemidef := hE.smul (inv_nonneg.mpr hc0.le)
  have hE0_le : ((c⁻¹ : ℝ) • E) ≤ 1 :=
    inv_smul_le_one_of_le_trace_smul E hE c le_rfl hc0
  have hsmul :=
    effectExpectation_smul_nonneg_doubleDual F (c / t) hratio0
      ((c⁻¹ : ℝ) • E) hE0_psd hE0_le (by
        simpa [← hmat] using inv_smul_le_one_of_le_trace_smul E hE t ht ht0)
  have hc_ne : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have ht_ne : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  simp only [effectExpectationExt]
  have hβ :
      effectExpectation (doubleDualEffectPairing F) ((t⁻¹ : ℝ) • E)
          (hE.smul (inv_nonneg.mpr ht0.le))
          (inv_smul_le_one_of_le_trace_smul E hE t ht ht0) =
        (c / t : ℂ) *
          effectExpectation (doubleDualEffectPairing F) ((c⁻¹ : ℝ) • E)
            hE0_psd hE0_le := by
    simpa [hmat, effectExpectation, Complex.ofReal_div] using hsmul
  calc (c : ℂ) *
        effectExpectation (doubleDualEffectPairing F) ((c⁻¹ : ℝ) • E)
          (hE.smul (inv_nonneg.mpr (le_trans zero_le_one (le_max_right _ _))))
          (inv_smul_le_one_of_le_trace_smul E hE c le_rfl
            (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _))) =
      (c : ℂ) * effectExpectation (doubleDualEffectPairing F) ((c⁻¹ : ℝ) • E)
          hE0_psd hE0_le := by simp only [effectExpectation]
    _ = (t : ℂ) * ((c / t : ℂ) *
          effectExpectation (doubleDualEffectPairing F) ((c⁻¹ : ℝ) • E)
            hE0_psd hE0_le) := by field_simp [hc_ne, ht_ne]
    _ = (t : ℂ) * effectExpectation (doubleDualEffectPairing F) ((t⁻¹ : ℝ) • E)
          (hE.smul (inv_nonneg.mpr ht0.le))
          (inv_smul_le_one_of_le_trace_smul E hE t ht ht0) := by rw [← hβ]

theorem effectExpectationExt_smul {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (r : ℝ) (hr0 : 0 ≤ r)
    (E : Matrix (Fin A) (Fin A) ℂ) (hE : E.PosSemidef) :
    effectExpectationExt F (r • E) (hE.smul hr0) =
      (r : ℂ) * effectExpectationExt F E hE := by
  by_cases hr : r = 0
  · subst hr
    simp only [zero_smul, Complex.ofReal_zero, zero_mul]
    simp only [effectExpectationExt, Matrix.trace_zero, Complex.zero_re, max_eq_right zero_le_one]
    have h0 : ((1⁻¹ : ℝ) • (0 : Matrix (Fin A) (Fin A) ℂ)) = 0 := by ext; simp
    simpa [effectExpectation, h0] using effectExpectation_zero_doubleDual (A := A) F
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    set D : ℝ := max (Matrix.trace E).re 1
    have hD0 : 0 < D := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
    -- Choose U = max(D, c/r) where c = max(Tr(rE),1); equivalently U = max(D, max(Tr(rE),1)/r)
    have htr : Matrix.trace (r • E) = (r : ℂ) * Matrix.trace E := by
      simp [Matrix.trace, Finset.mul_sum, Matrix.smul_apply]
    have himE : (Matrix.trace E).im = 0 :=
      (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_nonneg hE)).2.symm
    have htRE : (Matrix.trace (r • E)).re = r * (Matrix.trace E).re := by
      have := congrArg Complex.re htr
      simpa [Complex.mul_re, himE, Complex.ofReal_re] using this
    set cRE : ℝ := max (Matrix.trace (r • E)).re 1
    have hcRE0 : 0 < cRE := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
    set U : ℝ := max D (cRE / r)
    have hU0 : 0 < U := lt_of_lt_of_le hD0 (le_max_left _ _)
    have hU_ge_D : D ≤ U := le_max_left _ _
    have hU_ge_c : cRE / r ≤ U := le_max_right _ _
    have hU_ge_E : max (Matrix.trace E).re 1 ≤ U := hU_ge_D
    have hUr_ge_RE : max (Matrix.trace (r • E)).re 1 ≤ r * U := by
      have : cRE ≤ r * U := by
        have h := (div_le_iff₀ hrpos).mp hU_ge_c
        rwa [mul_comm] at h
      simpa [cRE] using this
    have hE_eq := effectExpectationExt_eq_of_scale F E hE U hU_ge_E hU0
    have hRE_eq :=
      effectExpectationExt_eq_of_scale F (r • E) (hE.smul hr0) (r * U) hUr_ge_RE (mul_pos hrpos hU0)
    have hmat : ((r * U)⁻¹ : ℝ) • (r • E) = (U⁻¹ : ℝ) • E := by
      ext; simp [Matrix.smul_apply]; field_simp [hrpos.ne', hU0.ne']
    calc effectExpectationExt F (r • E) (hE.smul hr0)
        = (↑(r * U) : ℂ) *
            effectExpectation (doubleDualEffectPairing F) (((r * U)⁻¹ : ℝ) • (r • E))
              ((hE.smul hr0).smul (inv_nonneg.mpr (mul_pos hrpos hU0).le))
              (inv_smul_le_one_of_le_trace_smul (r • E) (hE.smul hr0) (r * U)
                hUr_ge_RE (mul_pos hrpos hU0)) := hRE_eq
      _ = (r : ℂ) * (U : ℂ) *
            effectExpectation (doubleDualEffectPairing F) ((U⁻¹ : ℝ) • E)
              (hE.smul (inv_nonneg.mpr hU0.le))
              (inv_smul_le_one_of_le_trace_smul E hE U hU_ge_E hU0) := by
            simp only [effectExpectation, hmat]; push_cast; ring
      _ = (r : ℂ) * effectExpectationExt F E hE := by
            rw [hE_eq]; ring


theorem effectExpectationExt_of_le_one {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E : Matrix (Fin A) (Fin A) ℂ) (hE : E.PosSemidef) (hE1 : E ≤ 1) :
    effectExpectationExt F E hE =
      effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  have h := effectExpectationExt_eq_of_scale F E hE
    (max (Matrix.trace E).re 1) le_rfl
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _))
  simp only [effectExpectationExt] at h ⊢
  set c : ℝ := max (Matrix.trace E).re 1
  have hc0 : 0 ≤ c := le_trans zero_le_one (le_max_right _ _)
  have hc1 : 1 ≤ c := le_max_right _ _
  have hinv0 : 0 ≤ (c⁻¹ : ℝ) := inv_nonneg.mpr hc0
  have hinv1 : (c⁻¹ : ℝ) ≤ 1 := inv_le_one_of_one_le₀ hc1
  have hsmul := effectExpectation_smul_doubleDual F c⁻¹ hinv0 hinv1 E hE hE1
  have hc_ne : (c : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hc1)
  calc (c : ℂ) *
        effectExpectation (doubleDualEffectPairing F) ((c⁻¹ : ℝ) • E)
          (hE.smul (inv_nonneg.mpr (le_trans zero_le_one (le_max_right _ _))))
          (inv_smul_le_one_of_le_trace_smul E hE c le_rfl
            (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _))) =
      (c : ℂ) *
        effectExpectation (doubleDualEffectPairing F) ((c⁻¹ : ℝ) • E)
          (hE.smul hinv0) (smul_le_one_of_le_one E hE hE1 c⁻¹ hinv0 hinv1) := by
            simp only [effectExpectation]
    _ = (c : ℂ) * ((c⁻¹ : ℂ) *
          effectExpectation (doubleDualEffectPairing F) E hE hE1) := by
            rw [hsmul]; simp [Complex.ofReal_inv]
    _ = effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
            field_simp [hc_ne]

theorem effectExpectationExt_add {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E G : Matrix (Fin A) (Fin A) ℂ) (hE : E.PosSemidef) (hG : G.PosSemidef) :
    effectExpectationExt F (E + G) (hE.add hG) =
      effectExpectationExt F E hE + effectExpectationExt F G hG := by
  set cE : ℝ := max (Matrix.trace E).re 1
  set cG : ℝ := max (Matrix.trace G).re 1
  set t : ℝ := cE + cG
  have hcE0 : 0 < cE := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  have hcG0 : 0 < cG := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  have ht0 : 0 < t := add_pos hcE0 hcG0
  have himE : (Matrix.trace E).im = 0 :=
    (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_nonneg hE)).2.symm
  have himG : (Matrix.trace G).im = 0 :=
    (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_nonneg hG)).2.symm
  have htSum : (Matrix.trace (E + G)).re =
      (Matrix.trace E).re + (Matrix.trace G).re := by
    simp [Matrix.trace_add, Complex.add_re]
  have ht_ge_sum : max (Matrix.trace (E + G)).re 1 ≤ t := by
    rw [htSum]
    refine max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) ?_
    · calc (1 : ℝ) ≤ cE := le_max_right _ _
        _ ≤ cE + cG := le_add_of_nonneg_right hcG0.le
  have ht_ge_E : max (Matrix.trace E).re 1 ≤ t :=
    le_add_of_nonneg_right hcG0.le
  have ht_ge_G : max (Matrix.trace G).re 1 ≤ t :=
    le_add_of_nonneg_left hcE0.le
  have hE_eq := effectExpectationExt_eq_of_scale F E hE t ht_ge_E ht0
  have hG_eq := effectExpectationExt_eq_of_scale F G hG t ht_ge_G ht0
  have hSum_eq :=
    effectExpectationExt_eq_of_scale F (E + G) (hE.add hG) t ht_ge_sum ht0
  have hmat : (t⁻¹ : ℝ) • (E + G) = (t⁻¹ : ℝ) • E + (t⁻¹ : ℝ) • G := smul_add _ _ _
  have hE1 : ((t⁻¹ : ℝ) • E) ≤ 1 :=
    inv_smul_le_one_of_le_trace_smul E hE t ht_ge_E ht0
  have hG1 : ((t⁻¹ : ℝ) • G) ≤ 1 :=
    inv_smul_le_one_of_le_trace_smul G hG t ht_ge_G ht0
  have hSum1 : ((t⁻¹ : ℝ) • (E + G)) ≤ 1 :=
    inv_smul_le_one_of_le_trace_smul (E + G) (hE.add hG) t ht_ge_sum ht0
  have hEG1 : ((t⁻¹ : ℝ) • E + (t⁻¹ : ℝ) • G) ≤ 1 := by
    convert hSum1 using 1
    exact hmat.symm
  have hadd :=
    effectExpectation_add_doubleDual F ((t⁻¹ : ℝ) • E) ((t⁻¹ : ℝ) • G)
      (hE.smul (inv_nonneg.mpr ht0.le)) (hG.smul (inv_nonneg.mpr ht0.le))
      hE1 hG1 hEG1
  have hSum_β :
      effectExpectation (doubleDualEffectPairing F) ((t⁻¹ : ℝ) • (E + G))
          ((hE.add hG).smul (inv_nonneg.mpr ht0.le)) hSum1 =
        effectExpectation (doubleDualEffectPairing F)
          ((t⁻¹ : ℝ) • E + (t⁻¹ : ℝ) • G)
          ((hE.smul (inv_nonneg.mpr ht0.le)).add (hG.smul (inv_nonneg.mpr ht0.le)))
          hEG1 := by
    simp only [effectExpectation, hmat]
  calc effectExpectationExt F (E + G) (hE.add hG)
      = (t : ℂ) * effectExpectation (doubleDualEffectPairing F) ((t⁻¹ : ℝ) • (E + G))
          ((hE.add hG).smul (inv_nonneg.mpr ht0.le)) hSum1 := hSum_eq
    _ = (t : ℂ) * effectExpectation (doubleDualEffectPairing F)
          ((t⁻¹ : ℝ) • E + (t⁻¹ : ℝ) • G)
          ((hE.smul (inv_nonneg.mpr ht0.le)).add (hG.smul (inv_nonneg.mpr ht0.le)))
          hEG1 := by rw [hSum_β]
    _ = (t : ℂ) * (effectExpectation (doubleDualEffectPairing F) ((t⁻¹ : ℝ) • E)
          (hE.smul (inv_nonneg.mpr ht0.le)) hE1 +
        effectExpectation (doubleDualEffectPairing F) ((t⁻¹ : ℝ) • G)
          (hG.smul (inv_nonneg.mpr ht0.le)) hG1) := by rw [hadd]
    _ = effectExpectationExt F E hE + effectExpectationExt F G hG := by
          rw [mul_add, ← hE_eq, ← hG_eq]

theorem effectPairingQuad_eq_ext {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (v : Fin A → ℂ) :
    effectPairingQuad (doubleDualEffectPairing F) v =
      effectExpectationExt F (Matrix.vecMulVec v (star v))
        (Matrix.posSemidef_vecMulVec_self_star v) := by
  by_cases hle : Matrix.vecMulVec v (star v) ≤ (1 : Matrix (Fin A) (Fin A) ℂ)
  · rw [effectPairingQuad_eq_expectation F v hle, effectExpectationExt_of_le_one]
  · have hv : star v ⬝ᵥ v ≠ 0 := by
      intro hv0
      have : v = 0 := (dotProduct_star_self_eq_zero).1 hv0
      have hmat0 : Matrix.vecMulVec v (star v) = 0 := by simp [this]
      have h0le : (0 : Matrix (Fin A) (Fin A) ℂ) ≤ 1 := by
        rw [Matrix.le_iff, sub_zero]; exact PosSemidef.one
      exact hle (by simpa [hmat0] using h0le)
    set û := normalizeVec v hv
    have hre := (star_dotProduct_self_nonneg_real v).1
    have him := (star_dotProduct_self_nonneg_real v).2
    set s : ℂ := ↑(Real.sqrt (star v ⬝ᵥ v).re)
    have hv_eq : v = s • û := by
      simp only [û, normalizeVec, s]
      ext i
      have hs_ne : s ≠ 0 := by
        intro hs0
        have : (star v ⬝ᵥ v).re = 0 :=
          (Real.sqrt_eq_zero hre).1 (by simpa [s] using congrArg Complex.re hs0)
        exact hv (Complex.ext this him)
      change v i = s * (s⁻¹ * v i)
      field_simp [hs_ne]
    have hstar_s : star s = s := by simp [s, Complex.conj_ofReal]
    have hnrm_sq : star v ⬝ᵥ v = s * s := by
      apply Complex.ext
      · have : (star v ⬝ᵥ v).re = s.re * s.re := by
          simpa [s, Complex.ofReal_re] using (Real.mul_self_sqrt hre).symm
        simpa [Complex.mul_re, s] using this
      · simpa [Complex.mul_im, s] using him
    have hmat : Matrix.vecMulVec v (star v) =
        ((star v ⬝ᵥ v).re : ℝ) • Matrix.vecMulVec û (star û) := by
      have hnrm_ofReal : (↑((star v ⬝ᵥ v).re) : ℂ) = star v ⬝ᵥ v :=
        ofReal_re_of_im_zero _ him
      have hsmul_eq :
          ((star v ⬝ᵥ v).re : ℝ) • Matrix.vecMulVec û (star û) =
            (star v ⬝ᵥ v) • Matrix.vecMulVec û (star û) := by
        ext i j; simp [Matrix.smul_apply, smul_eq_mul, hnrm_ofReal]
      calc Matrix.vecMulVec v (star v)
          = Matrix.vecMulVec (s • û) (star (s • û)) := by rw [hv_eq]
        _ = (s * star s) • Matrix.vecMulVec û (star û) := vecMulVec_smul_star s û
        _ = (s * s) • Matrix.vecMulVec û (star û) := by rw [hstar_s]
        _ = (star v ⬝ᵥ v) • Matrix.vecMulVec û (star û) := by rw [← hnrm_sq]
        _ = ((star v ⬝ᵥ v).re : ℝ) • Matrix.vecMulVec û (star û) := by rw [← hsmul_eq]
    have hû_le : Matrix.vecMulVec û (star û) ≤ 1 :=
      vecMulVec_unit_le_one û (normalizeVec_norm v hv)
    have hs0 : 0 ≤ (star v ⬝ᵥ v).re := hre
    set r : ℝ := (star v ⬝ᵥ v).re
    have hnrm_ofReal : (r : ℂ) = star v ⬝ᵥ v := ofReal_re_of_im_zero _ him
    have hQ : effectPairingQuad (doubleDualEffectPairing F) v =
        (r : ℂ) *
          effectExpectation (doubleDualEffectPairing F)
            (Matrix.vecMulVec û (star û))
            (Matrix.posSemidef_vecMulVec_self_star û) hû_le := by
      calc effectPairingQuad (doubleDualEffectPairing F) v
          = effectPairingQuad (doubleDualEffectPairing F) (s • û) := by rw [hv_eq]
        _ = (star s * s) * effectPairingQuad (doubleDualEffectPairing F) û :=
              effectPairingQuad_smul _ _ _
        _ = (s * s) * effectPairingQuad (doubleDualEffectPairing F) û := by rw [hstar_s]
        _ = (star v ⬝ᵥ v) * effectPairingQuad (doubleDualEffectPairing F) û := by
              rw [← hnrm_sq]
        _ = (r : ℂ) * effectPairingQuad (doubleDualEffectPairing F) û := by rw [← hnrm_ofReal]
        _ = (r : ℂ) *
              effectExpectation (doubleDualEffectPairing F)
                (Matrix.vecMulVec û (star û))
                (Matrix.posSemidef_vecMulVec_self_star û) hû_le := by
              rw [effectPairingQuad_eq_expectation F û hû_le]
    have hExt :=
      effectExpectationExt_smul F r hs0
        (Matrix.vecMulVec û (star û)) (Matrix.posSemidef_vecMulVec_self_star û)
    have hû_ext :=
      effectExpectationExt_of_le_one F (Matrix.vecMulVec û (star û))
        (Matrix.posSemidef_vecMulVec_self_star û) hû_le
    have hmat' : Matrix.vecMulVec v (star v) =
        (r : ℝ) • Matrix.vecMulVec û (star û) := hmat
    calc effectPairingQuad (doubleDualEffectPairing F) v
        = (r : ℂ) *
            effectExpectation (doubleDualEffectPairing F)
              (Matrix.vecMulVec û (star û))
              (Matrix.posSemidef_vecMulVec_self_star û) hû_le := hQ
      _ = (r : ℂ) *
            effectExpectationExt F (Matrix.vecMulVec û (star û))
              (Matrix.posSemidef_vecMulVec_self_star û) := by rw [← hû_ext]
      _ = effectExpectationExt F ((r : ℝ) • Matrix.vecMulVec û (star û))
            ((Matrix.posSemidef_vecMulVec_self_star û).smul hs0) := hExt.symm
      _ = effectExpectationExt F (Matrix.vecMulVec v (star v))
            (Matrix.posSemidef_vecMulVec_self_star v) := by
            simp only [effectExpectationExt, hmat']


/-! ### Polar ℂ-sesquilinearity -/

theorem effectPairingPolar_neg_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) (-x) y =
      -effectPairingPolar (doubleDualEffectPairing F) x y := by
  have h := effectPairingPolar_add_left F x (-x) y
  simp only [add_neg_cancel, effectPairingPolar_zero_left] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem effectPairingPolar_natCast_smul_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (k : ℕ) (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) ((k : ℂ) • x) y =
      (k : ℂ) * effectPairingPolar (doubleDualEffectPairing F) x y := by
  have : (k : ℂ) • x = k • x := by ext i; simp [nsmul_eq_mul]
  rw [this, effectPairingPolar_nsmul_left]

theorem effectPairingPolar_zsmul_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (n : ℤ) (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) ((n : ℂ) • x) y =
      (n : ℂ) * effectPairingPolar (doubleDualEffectPairing F) x y := by
  cases n with
  | ofNat k => simpa using effectPairingPolar_natCast_smul_left F k x y
  | negSucc k =>
    simp only [Int.cast_negSucc]
    have hk := effectPairingPolar_natCast_smul_left F (k + 1) x y
    have hneg : ∀ z : ℂ, (-z) • x = -(z • x) := fun z => by ext; rw [neg_smul]
    rw [hneg, effectPairingPolar_neg_left, hk]; ring

theorem effectPairingPolar_qsmul_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (q : ℚ) (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) ((q : ℂ) • x) y =
      (q : ℂ) * effectPairingPolar (doubleDualEffectPairing F) x y := by
  let hom : ℂ →+ ℂ := AddMonoidHom.mk'
    (fun c => effectPairingPolar (doubleDualEffectPairing F) (c • x) y)
    (fun a b => by
      simpa [add_smul] using
        effectPairingPolar_add_left F (a • x) (b • x) y)
  let lhom : ℂ →ₗ[ℚ] ℂ := AddMonoidHom.toRatLinearMap hom
  simpa [lhom, hom, Rat.smul_def, one_smul] using lhom.map_smul q (1 : ℂ)

theorem effectPairingPolar_I_smul_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) (Complex.I • x) y =
      -Complex.I * effectPairingPolar (doubleDualEffectPairing F) x y := by
  set α := doubleDualEffectPairing F
  rw [effectPairingPolar_eq_ofNorm α (Complex.I • x) y,
    effectPairingPolar_eq_ofNorm α x y]
  have hII : Complex.I • (Complex.I • x) = (-1 : ℂ) • x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  have hII' : (-1 : ℂ) • x = -x := by ext; simp
  have h3 : effectPairingQuad α (Complex.I • (Complex.I • x) + y) =
      effectPairingQuad α (x - y) := by
    rw [hII, hII']
    have : -x + y = -(x - y) := by ext; simp [sub_eq_add_neg]; abel
    rw [this, q_neg]
  have h4 : effectPairingQuad α (Complex.I • (Complex.I • x) - y) =
      effectPairingQuad α (x + y) := by
    rw [hII, hII']
    have : -x - y = -(x + y) := by ext; simp [sub_eq_add_neg]; abel
    rw [this, q_neg]
  rw [h3, h4]; ring_nf; rw [Complex.I_sq]; ring


theorem effectPairingQuad_norm_le {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (v : Fin A → ℂ) :
    ‖effectPairingQuad (doubleDualEffectPairing F) v‖ ≤ (star v ⬝ᵥ v).re := by
  have hn := star_dotProduct_self_nonneg_real v
  have hq := effectPairingQuad_nonneg (doubleDualEffectPairing F) v
  have hnorm : ‖effectPairingQuad (doubleDualEffectPairing F) v‖ =
      |(effectPairingQuad (doubleDualEffectPairing F) v).re| :=
    (Complex.abs_re_eq_norm.mpr hq.2).symm
  rw [hnorm, abs_of_nonneg hq.1]
  simp only [effectPairingQuad]
  split_ifs with h
  · exact hn.1
  · have hb := bornScalar_nonneg
      (doubleDualEffectPairing F
        (ofEffect (Matrix.vecMulVec (normalizeVec v h) (star (normalizeVec v h)))
          (Matrix.posSemidef_vecMulVec_self_star _)
          (vecMulVec_unit_le_one _ (normalizeVec_norm v h))))
    set β := bornScalar (doubleDualEffectPairing F
      (ofEffect (Matrix.vecMulVec (normalizeVec v h) (star (normalizeVec v h)))
        (Matrix.posSemidef_vecMulVec_self_star _)
        (vecMulVec_unit_le_one _ (normalizeVec_norm v h))))
    have hre : ((star v ⬝ᵥ v) * β).re = (star v ⬝ᵥ v).re * β.re := by
      simp [Complex.mul_re, hn.2, hb.2.1]
    change ((star v ⬝ᵥ v) * β).re ≤ (star v ⬝ᵥ v).re
    rw [hre]; nlinarith [hn.1, hb.2.2]

theorem re_star_dot_eq_sum_normSq {A : ℕ}
    (v : Fin A → ℂ) :
    (star v ⬝ᵥ v).re = ∑ i : Fin A, Complex.normSq (v i) := by
  simp only [dotProduct, Pi.star_apply]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : star (v i) * v i = (Complex.normSq (v i) : ℂ) := by
    simpa [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := v i)).symm
  rw [this, Complex.ofReal_re]

theorem normSq_add_le_two (z w : ℂ) :
    Complex.normSq (z + w) ≤ 2 * (Complex.normSq z + Complex.normSq w) := by
  have h := Complex.normSq_add z w
  have hsub := Complex.normSq_sub z w
  have : Complex.normSq (z + w) + Complex.normSq (z - w) =
      2 * (Complex.normSq z + Complex.normSq w) := by
    rw [h, hsub]; ring
  linarith [Complex.normSq_nonneg (z - w)]

theorem re_norm_smul_add_le {A : ℕ}
    (r : ℝ) (hr : |r| ≤ 1) (x z : Fin A → ℂ) :
    (star ((r : ℂ) • x + z) ⬝ᵥ ((r : ℂ) • x + z)).re ≤
      2 * ((star x ⬝ᵥ x).re + (star z ⬝ᵥ z).re) := by
  rw [re_star_dot_eq_sum_normSq, re_star_dot_eq_sum_normSq x, re_star_dot_eq_sum_normSq z]
  calc ∑ i : Fin A, Complex.normSq (((r : ℂ) • x + z) i)
      = ∑ i, Complex.normSq ((r : ℂ) * x i + z i) := by
          simp [Pi.add_apply, Pi.smul_apply]
    _ ≤ ∑ i, 2 * (Complex.normSq ((r : ℂ) * x i) + Complex.normSq (z i)) :=
          Finset.sum_le_sum fun i _ => normSq_add_le_two _ _
    _ = 2 * (∑ i, Complex.normSq ((r : ℂ) * x i) + ∑ i, Complex.normSq (z i)) := by
          rw [← Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 2 * (r ^ 2 * ∑ i, Complex.normSq (x i) + ∑ i, Complex.normSq (z i)) := by
          have : ∀ i, Complex.normSq ((r : ℂ) * x i) = r ^ 2 * Complex.normSq (x i) := by
            intro i; simp [Complex.normSq_mul, Complex.normSq_ofReal, sq]
          simp_rw [this, ← Finset.mul_sum]
    _ ≤ 2 * (∑ i, Complex.normSq (x i) + ∑ i, Complex.normSq (z i)) := by
          have hr2 : r ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one r).2 hr
          nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin A))) =>
            Complex.normSq_nonneg (x i))]

noncomputable def effectPairingPolarRealHom {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y : Fin A → ℂ) : ℝ →+ ℂ :=
  AddMonoidHom.mk'
    (fun r => effectPairingPolar (doubleDualEffectPairing F) ((r : ℂ) • x) y)
    (fun a b => by
      have : ((a + b : ℝ) : ℂ) • x = (a : ℂ) • x + (b : ℂ) • x := by
        ext i; simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
      rw [this, effectPairingPolar_add_left])

theorem effectPairingPolarRealHom_continuous {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y : Fin A → ℂ) : Continuous (effectPairingPolarRealHom F x y) := by
  have hs : Metric.ball (0 : ℝ) 1 ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
  refine (effectPairingPolarRealHom F x y).continuous_of_isBounded_nhds_zero hs ?_
  rw [isBounded_iff_forall_norm_le]
  refine ⟨8 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re + 1), ?_⟩
  intro z hz
  obtain ⟨r, hrMem, rfl⟩ := (Set.mem_image _ _ _).1 hz
  have hrle : |r| ≤ 1 := le_of_lt (by
    simpa [Real.dist_eq, sub_zero] using Metric.mem_ball.mp hrMem)
  simp only [effectPairingPolarRealHom, AddMonoidHom.mk'_apply, effectPairingPolar]
  set Q := effectPairingQuad (doubleDualEffectPairing F)
  have bound (w : Fin A → ℂ) :
      ‖Q ((r : ℂ) • x + w)‖ ≤ 2 * ((star x ⬝ᵥ x).re + (star w ⬝ᵥ w).re) :=
    le_trans (effectPairingQuad_norm_le F _) (re_norm_smul_add_le r hrle x w)
  have hyI : (star (Complex.I • y) ⬝ᵥ (Complex.I • y)).re = (star y ⬝ᵥ y).re := by
    have h : star Complex.I * Complex.I = 1 := by simp [Complex.conj_I, Complex.I_mul_I]
    rw [star_dotProduct_smul_self, h, one_mul]
  have hneg (w : Fin A → ℂ) : (star (-w) ⬝ᵥ (-w)).re = (star w ⬝ᵥ w).re := by
    have : -w = (-1 : ℂ) • w := by ext; simp
    rw [this, star_dotProduct_smul_self]; simp
  have hsub (w : Fin A → ℂ) : (r : ℂ) • x - w = (r : ℂ) • x + (-w) := by
    ext; simp [sub_eq_add_neg]
  have htri :
      ‖(Q ((r:ℂ)•x+y) - Q ((r:ℂ)•x-y) - Complex.I*Q ((r:ℂ)•x+Complex.I•y) +
          Complex.I*Q ((r:ℂ)•x-Complex.I•y)) / 4‖ ≤
        ‖Q ((r:ℂ)•x+y)‖ + ‖Q ((r:ℂ)•x-y)‖ + ‖Q ((r:ℂ)•x+Complex.I•y)‖ +
          ‖Q ((r:ℂ)•x-Complex.I•y)‖ := by
    have hdiv (a : ℂ) : ‖a / 4‖ ≤ ‖a‖ := by
      rw [norm_div]
      have : ‖(4 : ℂ)‖ = 4 := by norm_num
      rw [this]; exact div_le_self (norm_nonneg _) (by norm_num)
    refine le_trans (hdiv _) ?_
    set a := Q ((r:ℂ)•x+y)
    set b := Q ((r:ℂ)•x-y)
    set c := Q ((r:ℂ)•x+Complex.I•y)
    set d := Q ((r:ℂ)•x-Complex.I•y)
    have : a - b - Complex.I * c + Complex.I * d = a + (-b) + (-(Complex.I * c)) + Complex.I * d := by
      ring
    rw [this]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
    refine le_trans (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) ?_
    simp only [norm_neg, norm_mul, Complex.norm_I, one_mul]
    exact le_rfl
  have Nx := (star_dotProduct_self_nonneg_real x).1
  have Ny := (star_dotProduct_self_nonneg_real y).1
  have b1 := bound y
  have b2 : ‖Q ((r:ℂ)•x-y)‖ ≤ 2 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) := by
    rw [hsub y]; refine le_trans (bound (-y)) ?_; rw [hneg y]
  have b3 : ‖Q ((r:ℂ)•x+Complex.I•y)‖ ≤ 2 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) := by
    refine le_trans (bound (Complex.I • y)) ?_; rw [hyI]
  have b4 : ‖Q ((r:ℂ)•x-Complex.I•y)‖ ≤ 2 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) := by
    rw [hsub (Complex.I • y)]; refine le_trans (bound (-(Complex.I • y))) ?_
    rw [hneg (Complex.I • y), hyI]
  refine le_trans htri ?_
  nlinarith [b1, b2, b3, b4, Nx, Ny]

theorem effectPairingPolar_ofReal_smul_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (r : ℝ) (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) ((r : ℂ) • x) y =
      (r : ℂ) * effectPairingPolar (doubleDualEffectPairing F) x y := by
  have h := map_real_smul (effectPairingPolarRealHom F x y) (effectPairingPolarRealHom_continuous F x y) r (1 : ℝ)
  simpa [effectPairingPolarRealHom, AddMonoidHom.mk'_apply, one_smul] using h

theorem effectPairingPolar_smul_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (c : ℂ) (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) (c • x) y =
      star c * effectPairingPolar (doubleDualEffectPairing F) x y := by
  have hre := effectPairingPolar_ofReal_smul_left F c.re x y
  have him := effectPairingPolar_ofReal_smul_left F c.im (Complex.I • x) y
  have hI := effectPairingPolar_I_smul_left F x y
  have hc : c • x = (c.re : ℂ) • x + (c.im : ℂ) • (Complex.I • x) := by
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    -- RHS = c.re * xi + c.im * (I * xi) = (c.re + c.im * I) * xi = c * xi
    trans ((c.re : ℂ) + (c.im : ℂ) * Complex.I) * x i
    · exact (Complex.re_add_im c).symm ▸ rfl
    · ring
  rw [hc, effectPairingPolar_add_left, hre, him, hI]
  have hstar : star c = (c.re : ℂ) + (c.im : ℂ) * (-Complex.I) := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  rw [hstar]; ring






theorem effectPairingPolar_smul_right {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (c : ℂ) (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) x (c • y) =
      c * effectPairingPolar (doubleDualEffectPairing F) x y := by
  have h1 := effectPairingPolar_conj_symm F x (c • y)
  have h2 := effectPairingPolar_smul_left F c y x
  have h3 := effectPairingPolar_conj_symm F x y
  calc effectPairingPolar (doubleDualEffectPairing F) x (c • y)
      = star (effectPairingPolar (doubleDualEffectPairing F) (c • y) x) := h1.symm
    _ = star (star c * effectPairingPolar (doubleDualEffectPairing F) y x) := by rw [h2]
    _ = star (effectPairingPolar (doubleDualEffectPairing F) y x) * star (star c) := by
          rw [star_mul]
    _ = star (effectPairingPolar (doubleDualEffectPairing F) y x) * c := by
          rw [star_star]
    _ = c * star (effectPairingPolar (doubleDualEffectPairing F) y x) := mul_comm _ _
    _ = c * effectPairingPolar (doubleDualEffectPairing F) x y := by rw [h3]

theorem effectPairingPolar_zero_right {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) x 0 = 0 := by
  have h := effectPairingPolar_conj_symm F 0 x
  have h0 := effectPairingPolar_zero_left F x
  have : star (effectPairingPolar (doubleDualEffectPairing F) x 0) = 0 := by
    rw [h, h0]
  exact (star_eq_zero.mp this)

theorem effectPairingPolar_sum_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (s : Finset (Fin A)) (v : Fin A → ℂ) (y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F)
        (∑ i ∈ s, v i • Pi.single i (1 : ℂ)) y =
      ∑ i ∈ s, star (v i) * effectPairingPolar (doubleDualEffectPairing F)
        (Pi.single i (1 : ℂ)) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [effectPairingPolar_zero_left]
  | insert i s hs ih =>
    simp only [Finset.sum_insert hs]
    rw [effectPairingPolar_add_left, effectPairingPolar_smul_left, ih]

theorem effectPairingPolar_sum_right {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (s : Finset (Fin A)) (x : Fin A → ℂ) (w : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) x
        (∑ j ∈ s, w j • Pi.single j (1 : ℂ)) =
      ∑ j ∈ s, w j * effectPairingPolar (doubleDualEffectPairing F) x
        (Pi.single j (1 : ℂ)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [effectPairingPolar_zero_right]
  | insert j s hs ih =>
    simp only [Finset.sum_insert hs]
    rw [effectPairingPolar_add_right, effectPairingPolar_smul_right, ih]

theorem eq_sum_single {A : ℕ}
    (v : Fin A → ℂ) :
    v = ∑ i : Fin A, v i • Pi.single i (1 : ℂ) := by
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  classical
  -- goal: v j = ∑ i, v i * (if j = i then 1 else 0)
  symm
  calc ∑ i : Fin A, v i * (if j = i then (1 : ℂ) else 0)
      = ∑ i : Fin A, if j = i then v i else 0 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs <;> simp
    _ = v j := by simp [Finset.sum_ite_eq]


theorem sum_psd_matrix {A : ℕ} {ι : Type*}
    (s : Finset ι) (M : ι → Matrix (Fin A) (Fin A) ℂ)
    (h : ∀ i ∈ s, (M i).PosSemidef) :
    (∑ i ∈ s, M i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact PosSemidef.zero
  | insert i s hs ih =>
    rw [Finset.sum_insert hs]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem le_one_of_add_le_one_of_posSemidef {A : ℕ}
    (P S : Matrix (Fin A) (Fin A) ℂ) (hP : P.PosSemidef) (hle : P + S ≤ 1) :
    S ≤ 1 := by
  rw [Matrix.le_iff] at hle ⊢
  have : (1 : Matrix (Fin A) (Fin A) ℂ) - S = (1 - (P + S)) + P := by
    abel
  rw [this]
  exact hle.add hP

theorem sum_rankOne_eq_one {A : ℕ} :
    (∑ i : Fin A, Matrix.vecMulVec (Pi.single i (1 : ℂ))
      (star (Pi.single i (1 : ℂ)))) = (1 : Matrix (Fin A) (Fin A) ℂ) := by
  ext a b
  simp only [Matrix.one_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Pi.single_apply]
  classical
  by_cases hab : a = b
  · subst hab
    have : ∀ i, (if a = i then (1 : ℂ) else 0) * star (if a = i then (1 : ℂ) else 0) =
        if a = i then 1 else 0 := by
      intro i; split_ifs <;> simp
    simp_rw [this, Finset.sum_ite_eq]
    simp
  · have h : ∀ i, (if a = i then (1 : ℂ) else 0) * star (if b = i then (1 : ℂ) else 0) = 0 := by
      intro i
      by_cases hai : a = i
      · have hbi : b ≠ i := fun h => hab (hai.trans h.symm)
        simp [hai, hbi]
      · simp [hai]
    simp_rw [h, Finset.sum_const_zero]
    simp [hab]

theorem single_normSq_one {A : ℕ} (i : Fin A) :
    star (Pi.single i (1 : ℂ)) ⬝ᵥ Pi.single i (1 : ℂ) = 1 := by
  simp only [dotProduct, Pi.single_apply, Pi.star_apply]
  classical
  calc ∑ x : Fin A, star (if x = i then (1 : ℂ) else 0) * (if x = i then 1 else 0)
      = ∑ x : Fin A, if x = i then (1 : ℂ) else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          split_ifs <;> simp
    _ = 1 := by simp

theorem effectExpectation_sum_rankOne {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier) :
    (∑ i : Fin A, effectExpectation (doubleDualEffectPairing F)
        (Matrix.vecMulVec (Pi.single i (1 : ℂ)) (star (Pi.single i (1 : ℂ))))
        (Matrix.posSemidef_vecMulVec_self_star _)
        (vecMulVec_unit_le_one _ (single_normSq_one i))) =
      effectExpectation (doubleDualEffectPairing F)
        (1 : Matrix (Fin A) (Fin A) ℂ) PosSemidef.one le_rfl := by
  classical
  have hadd : ∀ (s : Finset (Fin A))
      (hle : (∑ i ∈ s, Matrix.vecMulVec (Pi.single i (1 : ℂ))
            (star (Pi.single i (1 : ℂ)))) ≤ (1 : Matrix (Fin A) (Fin A) ℂ)),
      effectExpectation (doubleDualEffectPairing F)
          (∑ i ∈ s, Matrix.vecMulVec (Pi.single i (1 : ℂ))
            (star (Pi.single i (1 : ℂ))))
          (sum_psd_matrix s _ (fun i _ => Matrix.posSemidef_vecMulVec_self_star _))
          hle =
        ∑ i ∈ s, effectExpectation (doubleDualEffectPairing F)
          (Matrix.vecMulVec (Pi.single i (1 : ℂ)) (star (Pi.single i (1 : ℂ))))
          (Matrix.posSemidef_vecMulVec_self_star _)
          (vecMulVec_unit_le_one _ (single_normSq_one i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro hle
      simp only [Finset.sum_empty]
      exact effectExpectation_zero_doubleDual F
    | insert i s hs ih =>
      intro hle
      simp only [Finset.sum_insert hs] at hle ⊢
      have hE := Matrix.posSemidef_vecMulVec_self_star (Pi.single i (1 : ℂ))
      have hS := sum_psd_matrix s (fun j => Matrix.vecMulVec (Pi.single j (1 : ℂ))
          (star (Pi.single j (1 : ℂ))))
        (fun j _ => Matrix.posSemidef_vecMulVec_self_star _)
      have hEle : Matrix.vecMulVec (Pi.single i (1 : ℂ))
          (star (Pi.single i (1 : ℂ))) ≤ (1 : Matrix (Fin A) (Fin A) ℂ) :=
        vecMulVec_unit_le_one _ (single_normSq_one i)
      have hSle := le_one_of_add_le_one_of_posSemidef _ _ hE hle
      rw [effectExpectation_add_doubleDual F _ _ hE hS hEle hSle hle, ih hSle]
  have huniv_le : (∑ i : Fin A, Matrix.vecMulVec (Pi.single i (1 : ℂ))
      (star (Pi.single i (1 : ℂ)))) ≤ (1 : Matrix (Fin A) (Fin A) ℂ) := by
    rw [sum_rankOne_eq_one]
  have h := hadd Finset.univ huniv_le
  have hβ :
      effectExpectation (doubleDualEffectPairing F)
          (∑ i : Fin A, Matrix.vecMulVec (Pi.single i (1 : ℂ))
            (star (Pi.single i (1 : ℂ))))
          (sum_psd_matrix Finset.univ _ (fun i _ => Matrix.posSemidef_vecMulVec_self_star _))
          huniv_le =
        effectExpectation (doubleDualEffectPairing F)
          (1 : Matrix (Fin A) (Fin A) ℂ) PosSemidef.one le_rfl := by
    simp only [effectExpectation, sum_rankOne_eq_one]
  exact hβ ▸ h.symm

theorem trace_density_le_one {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier) :
    (Matrix.trace (densityFromEffectPairing (doubleDualEffectPairing F))).re ≤ 1 := by
  set ρ := densityFromEffectPairing (doubleDualEffectPairing F)
  have htr : Matrix.trace ρ =
      ∑ i : Fin A, effectPairingQuad (doubleDualEffectPairing F)
        (Pi.single i (1 : ℂ)) := by
    change ∑ i, ρ i i = ∑ i, effectPairingQuad (doubleDualEffectPairing F) (Pi.single i 1)
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ρ, densityFromEffectPairing]
    exact effectPairingPolar_self (doubleDualEffectPairing F) (Pi.single i 1)
  have hQ : ∀ i, effectPairingQuad (doubleDualEffectPairing F) (Pi.single i (1 : ℂ)) =
      effectExpectation (doubleDualEffectPairing F)
        (Matrix.vecMulVec (Pi.single i (1 : ℂ)) (star (Pi.single i (1 : ℂ))))
        (Matrix.posSemidef_vecMulVec_self_star _)
        (vecMulVec_unit_le_one _ (single_normSq_one i)) := by
    intro i
    exact effectPairingQuad_eq_expectation F (Pi.single i (1 : ℂ))
      (vecMulVec_unit_le_one _ (single_normSq_one i))
  have hsum := effectExpectation_sum_rankOne F
  have hborn := bornScalar_nonneg
    (doubleDualEffectPairing F (ofEffect (1 : Matrix (Fin A) (Fin A) ℂ)
      PosSemidef.one le_rfl))
  calc (Matrix.trace ρ).re
      = (∑ i, effectPairingQuad (doubleDualEffectPairing F)
          (Pi.single i (1 : ℂ))).re := by rw [htr]
    _ = (effectExpectation (doubleDualEffectPairing F) 1 PosSemidef.one le_rfl).re := by
          simp_rw [hQ]; exact congrArg Complex.re hsum
    _ ≤ 1 := by simpa [effectExpectation] using hborn.2.2


theorem effectPairingPolar_basis_expansion {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (v w : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) v w =
      ∑ i : Fin A, ∑ j : Fin A,
        star (v i) * effectPairingPolar (doubleDualEffectPairing F)
          (Pi.single i (1 : ℂ)) (Pi.single j (1 : ℂ)) * w j := by
  have step1 : effectPairingPolar (doubleDualEffectPairing F) v w =
      ∑ i : Fin A, star (v i) *
        effectPairingPolar (doubleDualEffectPairing F) (Pi.single i (1 : ℂ)) w := by
    conv_lhs => rw [eq_sum_single v]
    exact effectPairingPolar_sum_left F Finset.univ v w
  have step2 : effectPairingPolar (doubleDualEffectPairing F) v w =
      ∑ i : Fin A, star (v i) *
        (∑ j : Fin A, w j *
          effectPairingPolar (doubleDualEffectPairing F)
            (Pi.single i (1 : ℂ)) (Pi.single j (1 : ℂ))) := by
    rw [step1]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [eq_sum_single w]
    rw [effectPairingPolar_sum_right]
  rw [step2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, mul_right_comm (star (v i)) (w j)]

theorem density_quad_eq {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (v : Fin A → ℂ) :
    star v ⬝ᵥ (densityFromEffectPairing (doubleDualEffectPairing F)) *ᵥ v =
      effectPairingQuad (doubleDualEffectPairing F) v := by
  set ρ := densityFromEffectPairing (doubleDualEffectPairing F)
  have hdot : star v ⬝ᵥ ρ *ᵥ v =
      ∑ i : Fin A, ∑ j : Fin A, star (v i) * ρ i j * v j := by
    simp only [dotProduct, mulVec, Pi.star_apply]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _) ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc]
  rw [hdot, ← effectPairingPolar_self (doubleDualEffectPairing F) v,
    effectPairingPolar_basis_expansion]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [ρ, densityFromEffectPairing]

theorem densityFromDoubleDual_isHermitian {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier) :
    (densityFromEffectPairing (doubleDualEffectPairing F)).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, densityFromEffectPairing]
  exact effectPairingPolar_conj_symm F (Pi.single i (1 : ℂ)) (Pi.single j (1 : ℂ))

theorem densityFromDoubleDual_posSemidef {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier) :
    (densityFromEffectPairing (doubleDualEffectPairing F)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (densityFromDoubleDual_isHermitian F) ?_
  intro v
  have hq := effectPairingQuad_nonneg (doubleDualEffectPairing F) v
  rw [density_quad_eq F v]
  exact Complex.nonneg_iff.mpr ⟨hq.1, hq.2.symm⟩


/-! ### Spectral expansion for Born match -/

theorem diagonal_eq_sum_single {n : Type*} [Fintype n] [DecidableEq n] (f : n → ℂ) :
    diagonal f = ∑ i : n, f i • Matrix.single i i (1 : ℂ) := by
  ext a b
  classical
  simp only [diagonal, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.single, Matrix.of_apply]
  refine Eq.symm ?_
  by_cases hab : a = b
  · rw [if_pos hab]
    cases hab
    have hterm : ∀ i, f i * (if i = a ∧ i = a then (1 : ℂ) else 0) =
        if i = a then f a else 0 := by
      intro i; split_ifs <;> simp_all
    simp_rw [hterm]
    simpa using Finset.sum_ite_eq' (s := Finset.univ) (a := a) (f := fun _ => f a)
  · rw [if_neg hab]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ¬(i = a ∧ i = b) := fun ⟨ha, hb⟩ => hab (ha.symm.trans hb)
    simp [this]

theorem entry_mul_single {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (i : n) (a j : n) :
    (U * Matrix.single i i (1 : ℂ)) a j = if j = i then U a i else 0 := by
  classical
  simp only [Matrix.mul_apply, Matrix.single, Matrix.of_apply]
  split_ifs with hj
  · have hif : ∀ k, (i = k ∧ i = j) ↔ k = i := by
      intro k; constructor
      · intro ⟨h1, _⟩; exact h1.symm
      · intro hk; exact ⟨hk.symm, hj.symm⟩
    simp_rw [hif]
    have hterm : ∀ k, U a k * (if k = i then (1 : ℂ) else 0) =
        if k = i then U a i else 0 := by
      intro k; split_ifs <;> simp_all
    simp_rw [hterm]
    simpa using Finset.sum_ite_eq' (s := Finset.univ) (a := i) (f := fun _ => U a i)
  · refine Finset.sum_eq_zero fun k _ => ?_
    have : ¬(i = k ∧ i = j) := fun ⟨_, h2⟩ => hj h2.symm
    simp [this]

theorem mul_single_mul_star {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (i : n) :
    U * Matrix.single i i (1 : ℂ) * star U =
      Matrix.vecMulVec (fun a => U a i) (fun b => star (U b i)) := by
  classical
  set M := U * Matrix.single i i (1 : ℂ)
  have hM (a j : n) : M a j = if j = i then U a i else 0 := entry_mul_single U i a j
  ext a b
  simp only [Matrix.vecMulVec_apply, Matrix.mul_apply, star_apply]
  have hterm : ∀ j, M a j * star (U b j) =
      if j = i then U a i * star (U b i) else 0 := by
    intro j
    rw [hM]
    split_ifs with hj <;> simp [hj]
  simp_rw [hterm]
  simpa using Finset.sum_ite_eq' (s := Finset.univ) (a := i)
    (f := fun _ => U a i * star (U b i))

theorem isHermitian_eq_sum_eigenprojectors {n : Type*} [Fintype n] [DecidableEq n]
    (E : Matrix n n ℂ) (hE : E.IsHermitian) :
    E = ∑ i : n, (hE.eigenvalues i : ℂ) •
      Matrix.vecMulVec
        (fun a => (↑hE.eigenvectorUnitary : Matrix n n ℂ) a i)
        (fun b => star ((↑hE.eigenvectorUnitary : Matrix n n ℂ) b i)) := by
  set U : Matrix n n ℂ := ↑hE.eigenvectorUnitary
  have hEUD : E = U * diagonal (RCLike.ofReal ∘ hE.eigenvalues) * star U := by
    simpa [U, Unitary.conjStarAlgAut_apply] using hE.spectral_theorem
  have heq : (RCLike.ofReal ∘ hE.eigenvalues : n → ℂ) = fun i => (hE.eigenvalues i : ℂ) := by
    ext i; simp [Function.comp]
  have hD : diagonal (RCLike.ofReal ∘ hE.eigenvalues) =
      ∑ i : n, (hE.eigenvalues i : ℂ) • Matrix.single i i (1 : ℂ) := by
    rw [heq]; exact diagonal_eq_sum_single _
  calc E
      = U * diagonal (RCLike.ofReal ∘ hE.eigenvalues) * star U := hEUD
    _ = U * (∑ i : n, (hE.eigenvalues i : ℂ) • Matrix.single i i (1 : ℂ)) * star U := by
          rw [hD]
    _ = ∑ i : n, (U * ((hE.eigenvalues i : ℂ) • Matrix.single i i (1 : ℂ))) * star U := by
          rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i : n, (((hE.eigenvalues i : ℂ) • (U * Matrix.single i i (1 : ℂ))) * star U) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.mul_smul]
    _ = ∑ i : n, (hE.eigenvalues i : ℂ) • ((U * Matrix.single i i (1 : ℂ)) * star U) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.smul_mul]
    _ = ∑ i : n, (hE.eigenvalues i : ℂ) • (U * Matrix.single i i (1 : ℂ) * star U) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [Matrix.mul_assoc]
    _ = ∑ i : n, (hE.eigenvalues i : ℂ) •
          Matrix.vecMulVec (fun a => U a i) (fun b => star (U b i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_single_mul_star]

theorem eigenvectorUnitary_col_normSq {n : Type*} [Fintype n] [DecidableEq n]
    (E : Matrix n n ℂ) (hE : E.IsHermitian) (i : n) :
    star (fun a => (↑hE.eigenvectorUnitary : Matrix n n ℂ) a i) ⬝ᵥ
      (fun a => (↑hE.eigenvectorUnitary : Matrix n n ℂ) a i) = 1 := by
  have hstar : star (↑hE.eigenvectorUnitary : Matrix n n ℂ) *
      (↑hE.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
    simpa using (Unitary.coe_star_mul_self hE.eigenvectorUnitary)
  have hii : (star (↑hE.eigenvectorUnitary : Matrix n n ℂ) *
      (↑hE.eigenvectorUnitary : Matrix n n ℂ)) i i = 1 := by
    simp [hstar]
  simpa [Matrix.mul_apply, star_apply, dotProduct] using hii


end SuperoperatorModule

end QLambda.Domain.Presheaf
