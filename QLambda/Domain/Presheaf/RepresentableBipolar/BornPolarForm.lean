/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.RepresentableBipolar.BornHomogeneity

/-!
# Parallelogram and Born polarization

Loewner bounds, parallelogram identity, and polar sesquilinearity of the double-dual Born form.
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

end SuperoperatorModule

end QLambda.Domain.Presheaf
