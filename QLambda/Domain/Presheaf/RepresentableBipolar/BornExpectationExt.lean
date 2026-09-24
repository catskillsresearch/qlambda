/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.RepresentableBipolar.BornPolarForm

/-!
# Born reading off the Loewner interval

Positive-homogeneous extension `effectExpectationExt` and polar homogeneity/continuity lemmas.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder InnerProductSpace Kronecker

universe u

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
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> (field_simp [hc0']; try ring)
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
      simp [Complex.mul_re, himE, Complex.ofReal_re] at this ⊢
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
      exact hle (by simp [hmat0])
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

end SuperoperatorModule

end QLambda.Domain.Presheaf
