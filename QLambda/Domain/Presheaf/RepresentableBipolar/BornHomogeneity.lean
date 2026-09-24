/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.RepresentableBipolar.EffectFamily

/-!
# Double-dual Born homogeneity (n = 1)

Additive / monotone / half / dyadic Born reading on Loewner effects.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder InnerProductSpace Kronecker

universe u

/-! ### Double-dual Born calculus (n=1) -/

/-- Born scalars of `1→1` maps are real and lie in `[0,1]`. -/
theorem bornScalar_nonneg (χ : Superoperator 1 1) :
    0 ≤ (bornScalar χ).re ∧ (bornScalar χ).im = 0 ∧ (bornScalar χ).re ≤ 1 := by
  have hpsd := CPMap.applyMat_posSemidef χ.cp Matrix.PosSemidef.one
  have htr :=
    χ.trace_nonincreasing (1 : Matrix (Fin 1) (Fin 1) ℂ) Matrix.PosSemidef.one
  have ht1 : (Matrix.trace (1 : Matrix (Fin 1) (Fin 1) ℂ)).re = 1 := by
    simp [Matrix.trace_one]
  have heq : bornScalar χ = Matrix.trace (χ.cp.applyMat 1) := by
    simp [bornScalar, Matrix.trace, Fin.default_eq_zero]
  have hnn := Matrix.PosSemidef.trace_nonneg hpsd
  rw [heq]
  exact ⟨(Complex.nonneg_iff.mp hnn).1, (Complex.nonneg_iff.mp hnn).2.symm,
    by simpa [ht1] using htr⟩

theorem bornScalar_eq_choi (ψ : Superoperator 1 1) :
    bornScalar ψ = ψ.cp.choi (0, 0) (0, 0) := by
  have h := KrausFamily.applyMat_apply (CPMap.toKraus ψ.cp) 1 0 0
  simp only [bornScalar]
  change KrausFamily.applyMat (CPMap.toKraus ψ.cp) 1 0 0 =
    ψ.cp.choi (0, 0) (0, 0)
  rw [h, CPMap.choi_toKraus]
  simp [Matrix.one_apply]

theorem bornScalar_hasSum {ι : Type} [Countable ι]
    {f : ι → Superoperator 1 1} {χ : Superoperator 1 1}
    (h : SigmaMon.ChoiSum.HasSum f χ) :
    HasSum (fun i => bornScalar (f i)) (bornScalar χ) := by
  simpa only [bornScalar_eq_choi] using
    (Pi.hasSum.mp (Pi.hasSum.mp h ⟨0, 0⟩) ⟨0, 0⟩)

theorem ofEffect_hasSum_add {A : ℕ}
    (E F : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hF : F.PosSemidef)
    (hE1 : E ≤ 1) (hF1 : F ≤ 1) (hEF : E + F ≤ 1) :
    SigmaMon.ChoiSum.HasSum
      (fun i : Bool => if i then ofEffect E hE hE1 else ofEffect F hF hF1)
      (ofEffect (E + F) (hE.add hF) hEF) := by
  let fChoi : Bool → Matrix (Fin 1 × Fin A) (Fin 1 × Fin A) ℂ :=
    fun i => (if i then ofEffect E hE hE1 else ofEffect F hF hF1).cp.choi
  have hsum : HasSum fChoi (∑ i : Bool, fChoi i) :=
    hasSum_sum_of_ne_finset_zero (s := Finset.univ)
      (fun i hi => (hi (Finset.mem_univ i)).elim)
  have hchoi := ofEffect_add_choi E F hE hF hEF hE1 hF1
  have htotal : ∑ i : Bool, fChoi i =
      (ofEffect (E + F) (hE.add hF) hEF).cp.choi := by
    simp only [fChoi, Fintype.sum_bool, ↓reduceIte]
    exact (congrArg CPMap.choi hchoi).symm
  change HasSum fChoi _
  rwa [← htotal]

theorem effectPack_hasSum_add {A : ℕ}
    (E F : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hF : F.PosSemidef)
    (hE1 : E ≤ 1) (hF1 : F ≤ 1) (hEF : E + F ≤ 1) :
    ((DayNegation.neg (representable A)).obj 1).HasSum
      (fun i : Bool =>
        effectPack A (if i then ofEffect E hE hE1 else ofEffect F hF hF1))
      (effectPack A (ofEffect (E + F) (hE.add hF) hEF)) := by
  have hχ :=
    SigmaMon.ChoiSum.comp_right (Superoperator.tensorLeftUnitor A)
      (ofEffect_hasSum_add E F hE hF hE1 hF1 hEF)
  simpa [effectPack, dualFiberBilinear] using
    (dayInternalHomRepresentableIso A dayTensorUnit).inv.map_sum hχ

/-- Double-dual Born reading is additive on Loewner-summable effects. -/
theorem effectExpectation_add_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E G : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hG : G.PosSemidef)
    (hE1 : E ≤ 1) (hG1 : G ≤ 1) (hEG : E + G ≤ 1) :
    effectExpectation (doubleDualEffectPairing F) (E + G) (hE.add hG) hEG =
      effectExpectation (doubleDualEffectPairing F) E hE hE1 +
        effectExpectation (doubleDualEffectPairing F) G hG hG1 := by
  simp only [effectExpectation]
  set α := doubleDualEffectPairing F
  have hF :=
    F.map_sum_right (Superoperator.identity 1)
      (effectPack_hasSum_add E G hE hG hE1 hG1 hEG)
  have hα :
      SigmaMon.ChoiSum.HasSum
        (fun i : Bool =>
          α (if i then ofEffect E hE hE1 else ofEffect G hG hG1))
        (α (ofEffect (E + G) (hE.add hG) hEG)) := by
    simp only [α, doubleDualEffectPairing]
    exact SigmaMon.ChoiSum.comp_right _
      (SigmaMon.ChoiSum.comp_right _ hF)
  have ht := (bornScalar_hasSum hα).tsum_eq
  rw [tsum_bool] at ht
  simpa [add_comm] using ht.symm

theorem effectExpectation_nonneg_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1) :
    0 ≤ (effectExpectation (doubleDualEffectPairing F) E hE hE1).re ∧
      (effectExpectation (doubleDualEffectPairing F) E hE hE1).im = 0 := by
  have h :=
    bornScalar_nonneg (doubleDualEffectPairing F (ofEffect E hE hE1))
  exact ⟨h.1, h.2.1⟩

/-- Monotonicity of the double-dual Born reading on the Loewner order. -/
theorem effectExpectation_mono_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E G : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hG : G.PosSemidef)
    (hE1 : E ≤ 1) (hG1 : G ≤ 1) (hle : E ≤ G) :
    (effectExpectation (doubleDualEffectPairing F) E hE hE1).re ≤
      (effectExpectation (doubleDualEffectPairing F) G hG hG1).re := by
  have hdiff : (G - E).PosSemidef := Matrix.le_iff.mp hle
  have hLE_diff_G : G - E ≤ G := by
    rw [Matrix.le_iff, sub_sub_cancel]
    exact hE
  have hdiff_le : G - E ≤ 1 := hLE_diff_G.trans hG1
  have hsum_eq : E + (G - E) = G := add_sub_cancel _ _
  have hEG : E + (G - E) ≤ 1 := by simpa [hsum_eq] using hG1
  have hadd :=
    effectExpectation_add_doubleDual F E (G - E) hE hdiff hE1 hdiff_le hEG
  have hn :=
    effectExpectation_nonneg_doubleDual F (G - E) hdiff hdiff_le
  have hβG :
      effectExpectation (doubleDualEffectPairing F)
          (E + (G - E)) (hE.add hdiff) hEG =
        effectExpectation (doubleDualEffectPairing F) G hG hG1 := by
    simp only [effectExpectation, hsum_eq]
  have hre := congrArg Complex.re (hβG.symm.trans hadd)
  simp only [Complex.add_re] at hre
  linarith [hn.1]


/-- Halving homogeneity of the double-dual Born reading. -/
theorem effectExpectation_half_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1) :
    effectExpectation (doubleDualEffectPairing F) E hE hE1 =
      (2 : ℂ) *
        effectExpectation (doubleDualEffectPairing F)
          (((2 : ℝ)⁻¹) • E)
          (hE.smul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹))
          (by
            have hhalf : ((2 : ℝ)⁻¹) • E ≤ E := by
              rw [Matrix.le_iff]
              have :
                  E - ((2 : ℝ)⁻¹) • E = ((1 : ℝ) - (2 : ℝ)⁻¹) • E := by
                ext i j
                simp [Matrix.sub_apply, Matrix.smul_apply]
                ring
              rw [this]
              exact hE.smul
                (by norm_num : (0 : ℝ) ≤ (1 : ℝ) - (2 : ℝ)⁻¹)
            exact hhalf.trans hE1) := by
  set E2 : Matrix (Fin A) (Fin A) ℂ := ((2 : ℝ)⁻¹) • E
  have hE2psd : E2.PosSemidef :=
    hE.smul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
  have hE2le : E2 ≤ 1 := by
    have hhalf : E2 ≤ E := by
      rw [Matrix.le_iff]
      have : E - E2 = ((1 : ℝ) - (2 : ℝ)⁻¹) • E := by
        ext
        simp [E2, Matrix.sub_apply, Matrix.smul_apply]
        ring
      rw [this]
      exact hE.smul (by norm_num : (0 : ℝ) ≤ (1 : ℝ) - (2 : ℝ)⁻¹)
    exact hhalf.trans hE1
  have hsum : E2 + E2 = E := by
    ext
    simp [E2, Matrix.add_apply, Matrix.smul_apply]
    ring
  have hE2E2 : E2 + E2 ≤ 1 := by simpa [hsum] using hE1
  have hadd :=
    effectExpectation_add_doubleDual F E2 E2 hE2psd hE2psd hE2le hE2le hE2E2
  have hcongr :
      effectExpectation (doubleDualEffectPairing F) (E2 + E2)
          (hE2psd.add hE2psd) hE2E2 =
        effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
    simp only [effectExpectation, hsum]
  rw [← hcongr, hadd]
  ring

theorem ofEffect_proof_irrel {A : ℕ} (E : Matrix (Fin A) (Fin A) ℂ)
    (h1 h1' : E.PosSemidef) (h2 h2' : E ≤ 1) :
    ofEffect E h1 h2 = ofEffect E h1' h2' := by
  apply Superoperator.ext
  apply CPMap.ext
  rfl

theorem smul_le_self_of_le_one {A : ℕ} (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (c : ℝ) (_hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (c • E) ≤ E := by
  rw [Matrix.le_iff]
  have : E - c • E = (1 - c) • E := by
    ext
    simp [Matrix.sub_apply, Matrix.smul_apply]
    ring
  rw [this]
  exact hE.smul (sub_nonneg.mpr hc1)

theorem smul_le_one_of_le_one {A : ℕ} (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (c • E) ≤ (1 : Matrix (Fin A) (Fin A) ℂ) :=
  (smul_le_self_of_le_one E hE c hc0 hc1).trans hE1

theorem two_pow_inv_nonneg (k : ℕ) : (0 : ℝ) ≤ ((2 : ℝ) ^ k)⁻¹ :=
  inv_nonneg.mpr (pow_nonneg (by norm_num) k)

theorem two_pow_inv_le_one (k : ℕ) : ((2 : ℝ) ^ k)⁻¹ ≤ (1 : ℝ) :=
  inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

/-- β(0) = 0 from additivity. -/
theorem effectExpectation_zero_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier) :
    effectExpectation (doubleDualEffectPairing F)
        (0 : Matrix (Fin A) (Fin A) ℂ) PosSemidef.zero
        (by rw [Matrix.le_iff, sub_zero]; exact PosSemidef.one) = 0 := by
  set z : Matrix (Fin A) (Fin A) ℂ := 0
  have hzpsd : z.PosSemidef := PosSemidef.zero
  have hzle : z ≤ 1 := by rw [Matrix.le_iff, sub_zero]; exact PosSemidef.one
  have hz2 : z + z = z := by simp [z]
  have hz2le : z + z ≤ 1 := by simpa [hz2] using hzle
  have hadd :=
    effectExpectation_add_doubleDual F z z hzpsd hzpsd hzle hzle hz2le
  have hcongr :
      effectExpectation (doubleDualEffectPairing F) (z + z)
          (hzpsd.add hzpsd) hz2le =
        effectExpectation (doubleDualEffectPairing F) z hzpsd hzle := by
    simp only [effectExpectation, hz2]
  have heq :
      effectExpectation (doubleDualEffectPairing F) z hzpsd hzle =
        effectExpectation (doubleDualEffectPairing F) z hzpsd hzle +
          effectExpectation (doubleDualEffectPairing F) z hzpsd hzle :=
    hcongr.symm.trans hadd
  have him := (effectExpectation_nonneg_doubleDual F z hzpsd hzle).2
  have hre0 : (effectExpectation (doubleDualEffectPairing F) z hzpsd hzle).re = 0 := by
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re] at hre
    linarith
  have hβ0 : effectExpectation (doubleDualEffectPairing F) z hzpsd hzle = 0 :=
    Complex.ext hre0 him
  simpa [z, effectExpectation] using hβ0

/-- ℕ-homogeneity of the double-dual Born reading. -/
theorem effectExpectation_nsmul_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (n : ℕ) (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1)
    (hn : ((n : ℝ) • E) ≤ 1) :
    effectExpectation (doubleDualEffectPairing F)
        ((n : ℝ) • E) (hE.smul (Nat.cast_nonneg n)) hn =
      (n : ℂ) *
        effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  induction n with
  | zero =>
    have hmat : ((0 : ℕ) : ℝ) • E = (0 : Matrix (Fin A) (Fin A) ℂ) := by simp
    have hL :
        effectExpectation (doubleDualEffectPairing F)
          (((0 : ℕ) : ℝ) • E) (hE.smul (Nat.cast_nonneg 0)) hn =
        effectExpectation (doubleDualEffectPairing F)
          (0 : Matrix (Fin A) (Fin A) ℂ) PosSemidef.zero
          (by rw [Matrix.le_iff, sub_zero]; exact PosSemidef.one) := by
      simp only [effectExpectation, hmat]
    rw [hL, effectExpectation_zero_doubleDual F]
    simp
  | succ n ih =>
    have hnE : ((n : ℝ) • E) ≤ ((n + 1 : ℕ) : ℝ) • E := by
      rw [Matrix.le_iff]
      have : ((n + 1 : ℕ) : ℝ) • E - (n : ℝ) • E = E := by
        ext
        simp [Matrix.sub_apply, Matrix.smul_apply, Nat.cast_succ]
        ring
      rw [this]
      exact hE
    have hn_le : ((n : ℝ) • E) ≤ 1 := hnE.trans hn
    have hsum : ((n : ℝ) • E) + E = (((n + 1 : ℕ) : ℝ) • E) := by
      ext
      simp [Matrix.add_apply, Matrix.smul_apply, Nat.cast_succ]
      ring
    have hsum_le : ((n : ℝ) • E) + E ≤ 1 := by simpa [hsum] using hn
    have hadd :=
      effectExpectation_add_doubleDual F ((n : ℝ) • E) E
        (hE.smul (Nat.cast_nonneg n)) hE hn_le hE1 hsum_le
    have ih' := ih hn_le
    calc
      effectExpectation (doubleDualEffectPairing F)
          (((n + 1 : ℕ) : ℝ) • E) (hE.smul (Nat.cast_nonneg _)) hn =
        effectExpectation (doubleDualEffectPairing F)
          (((n : ℝ) • E) + E)
          ((hE.smul (Nat.cast_nonneg n)).add hE) hsum_le := by
        simp only [effectExpectation, hsum]
      _ = effectExpectation (doubleDualEffectPairing F)
            ((n : ℝ) • E) (hE.smul (Nat.cast_nonneg n)) hn_le +
          effectExpectation (doubleDualEffectPairing F) E hE hE1 := hadd
      _ = (n : ℂ) * effectExpectation (doubleDualEffectPairing F) E hE hE1 +
          effectExpectation (doubleDualEffectPairing F) E hE hE1 := by rw [ih']
      _ = ((n + 1 : ℕ) : ℂ) *
          effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
        simp [Nat.cast_succ]
        ring

/-- Invert the half-homogeneity identity. -/
theorem effectExpectation_of_half {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1) :
    effectExpectation (doubleDualEffectPairing F)
        (((2 : ℝ)⁻¹) • E)
        (hE.smul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹))
        (smul_le_one_of_le_one E hE hE1 (2 : ℝ)⁻¹ (by norm_num) (by norm_num)) =
      (2 : ℂ)⁻¹ *
        effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  have h := effectExpectation_half_doubleDual F E hE hE1
  apply_fun (fun z : ℂ => (2 : ℂ)⁻¹ * z) at h
  convert h.symm using 1
  ring

/-- Dyadic power-of-two homogeneity: β(E/2^k) = β(E)/2^k. -/
theorem effectExpectation_div_pow_two {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (k : ℕ) (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1) :
    effectExpectation (doubleDualEffectPairing F)
        (((2 : ℝ) ^ k)⁻¹ • E)
        (hE.smul (two_pow_inv_nonneg k))
        (smul_le_one_of_le_one E hE hE1 _ (two_pow_inv_nonneg k) (two_pow_inv_le_one k)) =
      ((2 : ℂ) ^ k)⁻¹ *
        effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  induction k with
  | zero => simp [pow_zero, inv_one, one_smul]
  | succ k ih =>
    have hE_k_psd : (((2 : ℝ) ^ k)⁻¹ • E).PosSemidef :=
      hE.smul (two_pow_inv_nonneg k)
    have hE_k_le : ((2 : ℝ) ^ k)⁻¹ • E ≤ 1 :=
      smul_le_one_of_le_one E hE hE1 _ (two_pow_inv_nonneg k) (two_pow_inv_le_one k)
    have hmat : ((2 : ℝ) ^ (k + 1))⁻¹ • E =
        ((2 : ℝ)⁻¹) • (((2 : ℝ) ^ k)⁻¹ • E) := by
      have : ((2 : ℝ) ^ (k + 1))⁻¹ = (2 : ℝ)⁻¹ * ((2 : ℝ) ^ k)⁻¹ := by
        rw [pow_succ, mul_inv]
        ring
      rw [this, mul_smul]
    calc
      effectExpectation (doubleDualEffectPairing F)
          (((2 : ℝ) ^ (k + 1))⁻¹ • E)
          (hE.smul (two_pow_inv_nonneg (k + 1)))
          (smul_le_one_of_le_one E hE hE1 _ (two_pow_inv_nonneg (k + 1))
            (two_pow_inv_le_one (k + 1))) =
        effectExpectation (doubleDualEffectPairing F)
          (((2 : ℝ)⁻¹) • (((2 : ℝ) ^ k)⁻¹ • E))
          (hE_k_psd.smul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹))
          (smul_le_one_of_le_one _ hE_k_psd hE_k_le (2 : ℝ)⁻¹
            (by norm_num) (by norm_num)) := by
        simp only [effectExpectation, hmat]
      _ = (2 : ℂ)⁻¹ *
          effectExpectation (doubleDualEffectPairing F)
            (((2 : ℝ) ^ k)⁻¹ • E) hE_k_psd hE_k_le :=
        effectExpectation_of_half F _ hE_k_psd hE_k_le
      _ = (2 : ℂ)⁻¹ *
          (((2 : ℂ) ^ k)⁻¹ *
            effectExpectation (doubleDualEffectPairing F) E hE hE1) := by
        rw [ih]
      _ = ((2 : ℂ) ^ (k + 1))⁻¹ *
          effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
        simp only [pow_succ, mul_inv]
        ring

/-- Dyadic rational homogeneity: β((m/2^k)•E) = (m/2^k)·β(E) when scaled ≤ I. -/
theorem effectExpectation_dyadic_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (m k : ℕ) (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1)
    (hm : (((m : ℝ) / (2 : ℝ) ^ k) • E) ≤ 1) :
    effectExpectation (doubleDualEffectPairing F)
        (((m : ℝ) / (2 : ℝ) ^ k) • E)
        (hE.smul (div_nonneg (Nat.cast_nonneg m) (pow_nonneg (by norm_num) k)))
        hm =
      ((m : ℂ) / (2 : ℂ) ^ k) *
        effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  have hmat : ((m : ℝ) / (2 : ℝ) ^ k) • E =
      (m : ℝ) • (((2 : ℝ) ^ k)⁻¹ • E) := by
    rw [div_eq_mul_inv, mul_smul]
  have hEk_psd : (((2 : ℝ) ^ k)⁻¹ • E).PosSemidef :=
    hE.smul (two_pow_inv_nonneg k)
  have hEk_le : ((2 : ℝ) ^ k)⁻¹ • E ≤ 1 :=
    smul_le_one_of_le_one E hE hE1 _ (two_pow_inv_nonneg k) (two_pow_inv_le_one k)
  have hm' : ((m : ℝ) • (((2 : ℝ) ^ k)⁻¹ • E)) ≤ 1 := by simpa [hmat] using hm
  have hβ_half := effectExpectation_div_pow_two F k E hE hE1
  have hβ_n :=
    effectExpectation_nsmul_doubleDual F m (((2 : ℝ) ^ k)⁻¹ • E) hEk_psd hEk_le hm'
  calc
    effectExpectation (doubleDualEffectPairing F)
        (((m : ℝ) / (2 : ℝ) ^ k) • E)
        (hE.smul (div_nonneg (Nat.cast_nonneg m) (pow_nonneg (by norm_num) k))) hm =
      effectExpectation (doubleDualEffectPairing F)
        ((m : ℝ) • (((2 : ℝ) ^ k)⁻¹ • E))
        (hEk_psd.smul (Nat.cast_nonneg m)) hm' := by
      simp only [effectExpectation, hmat]
    _ = (m : ℂ) *
        effectExpectation (doubleDualEffectPairing F)
          (((2 : ℝ) ^ k)⁻¹ • E) hEk_psd hEk_le := hβ_n
    _ = (m : ℂ) *
        (((2 : ℂ) ^ k)⁻¹ *
          effectExpectation (doubleDualEffectPairing F) E hE hE1) := by
      rw [hβ_half]
    _ = ((m : ℂ) / (2 : ℂ) ^ k) *
        effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
      rw [div_eq_mul_inv]
      ring

theorem smul_le_smul_of_le {A : ℕ} (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) {c d : ℝ} (_hc : 0 ≤ c) (hcd : c ≤ d) :
    (c • E) ≤ (d • E) := by
  rw [Matrix.le_iff]
  have : d • E - c • E = (d - c) • E := by
    ext; simp [Matrix.sub_apply, Matrix.smul_apply]; ring
  rw [this]
  exact hE.smul (sub_nonneg.mpr hcd)

theorem abs_le_inv_pow_two_eq_zero (x : ℝ)
    (h : ∀ k : ℕ, |x| ≤ ((2 : ℝ) ^ k)⁻¹) : x = 0 := by
  by_contra hx
  have hxpos : 0 < |x| := abs_pos.mpr hx
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 : ℝ) / |x| < (2 : ℝ) ^ k :=
    pow_unbounded_of_one_lt (1 / |x|) (by norm_num : (1 : ℝ) < 2)
  have hlt : ((2 : ℝ) ^ k)⁻¹ < |x| := by
    have hpos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
    rw [inv_lt_comm₀ hpos hxpos]
    simpa [one_div] using hk
  exact lt_irrefl _ (hlt.trans_le (h k))

theorem floor_dyadic_le (t : ℝ) (ht0 : 0 ≤ t) (k : ℕ) :
    ((Nat.floor (t * (2 : ℝ) ^ k) : ℕ) : ℝ) / (2 : ℝ) ^ k ≤ t := by
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) k
  have hm : ((Nat.floor (t * (2 : ℝ) ^ k) : ℕ) : ℝ) ≤ t * (2 : ℝ) ^ k :=
    Nat.floor_le (mul_nonneg ht0 (le_of_lt hpow_pos))
  calc ((Nat.floor (t * (2 : ℝ) ^ k) : ℕ) : ℝ) / (2 : ℝ) ^ k
      ≤ (t * (2 : ℝ) ^ k) / (2 : ℝ) ^ k :=
        div_le_div_of_nonneg_right hm (le_of_lt hpow_pos)
    _ = t := by field_simp [hpow_pos.ne']

theorem floor_dyadic_gt (t : ℝ) (k : ℕ) :
    t ≤ (((Nat.floor (t * (2 : ℝ) ^ k) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k) := by
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) k
  set m := Nat.floor (t * (2 : ℝ) ^ k)
  have hm : t * (2 : ℝ) ^ k < (m : ℝ) + 1 := by
    simpa [m, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (t * (2 : ℝ) ^ k)
  have : t < ((m : ℝ) + 1) / (2 : ℝ) ^ k :=
    (lt_div_iff₀ hpow_pos).mpr (by linarith)
  exact le_of_lt (by simpa [Nat.cast_add, Nat.cast_one] using this)

theorem effectExpectation_one_smul_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1) :
    effectExpectation (doubleDualEffectPairing F) ((1 : ℝ) • E)
        (hE.smul zero_le_one) (by simpa [one_smul] using hE1) =
      effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  simp only [effectExpectation, one_smul]

theorem dyadic_gap (m k : ℕ) :
    (((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k) - ((m : ℝ) / (2 : ℝ) ^ k) =
      ((2 : ℝ) ^ k)⁻¹ := by
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) k
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by simp
  rw [hcast]
  field_simp [hpow_pos.ne']
  ring

/-- Homogeneity at a concrete dyadic rational written as `c = m/2^k`. -/
theorem effectExpectation_ofReal_dyadic {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (m k : ℕ) (c : ℝ) (hc : c = (m : ℝ) / (2 : ℝ) ^ k)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1)
    (hc0 : 0 ≤ c) (_hc1 : c ≤ 1)
    (hm : (c • E) ≤ 1) :
    effectExpectation (doubleDualEffectPairing F) (c • E) (hE.smul hc0) hm =
      (c : ℂ) * effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  have hm' : (((m : ℝ) / (2 : ℝ) ^ k) • E) ≤ 1 := by simpa [hc] using hm
  have hdy := effectExpectation_dyadic_doubleDual F m k E hE hE1 hm'
  have hL :
      effectExpectation (doubleDualEffectPairing F) (c • E) (hE.smul hc0) hm =
      effectExpectation (doubleDualEffectPairing F)
        (((m : ℝ) / (2 : ℝ) ^ k) • E)
        (hE.smul (div_nonneg (Nat.cast_nonneg m) (pow_nonneg (by norm_num) k)))
        hm' := by
    simp only [effectExpectation, hc]
  rw [hL, hdy, hc]
  simp [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_pow]

theorem effectExpectation_smul_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1) :
    effectExpectation (doubleDualEffectPairing F) (t • E)
        (hE.smul ht0) (smul_le_one_of_le_one E hE hE1 t ht0 ht1) =
      (t : ℂ) * effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  set βE := effectExpectation (doubleDualEffectPairing F) E hE hE1 with hβE_def
  have hEt_psd : (t • E).PosSemidef := hE.smul ht0
  have hEt_le : t • E ≤ 1 := smul_le_one_of_le_one E hE hE1 t ht0 ht1
  set βt := effectExpectation (doubleDualEffectPairing F) (t • E) hEt_psd hEt_le
  have himE : βE.im = 0 := by
    simpa [βE] using (effectExpectation_nonneg_doubleDual F E hE hE1).2
  have himt : βt.im = 0 := by
    simpa [βt] using (effectExpectation_nonneg_doubleDual F (t • E) hEt_psd hEt_le).2
  have hreE_nn : 0 ≤ βE.re := by
    simpa [βE] using (effectExpectation_nonneg_doubleDual F E hE hE1).1
  have hβE_re_le1 : βE.re ≤ 1 := by
    simpa [βE, effectExpectation] using
      (bornScalar_nonneg (doubleDualEffectPairing F (ofEffect E hE hE1))).2.2
  have hclose : ∀ k : ℕ, |βt.re - t * βE.re| ≤ ((2 : ℝ) ^ k)⁻¹ := by
    intro k
    set m := Nat.floor (t * (2 : ℝ) ^ k)
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) k
    have hpow_nn : (0 : ℝ) ≤ (2 : ℝ) ^ k := le_of_lt hpow_pos
    set r : ℝ := (m : ℝ) / (2 : ℝ) ^ k
    set s0 : ℝ := ((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k
    set s : ℝ := min s0 1
    have hr_le_t : r ≤ t := by simpa [r, m] using floor_dyadic_le t ht0 k
    have ht_le_s0 : t ≤ s0 := by simpa [s0, m] using floor_dyadic_gt t k
    have ht_le_s : t ≤ s := le_min ht_le_s0 ht1
    have hr0 : 0 ≤ r := div_nonneg (Nat.cast_nonneg m) hpow_nn
    have hr1 : r ≤ 1 := by
      have hm_le : (m : ℝ) ≤ t * (2 : ℝ) ^ k :=
        Nat.floor_le (mul_nonneg ht0 hpow_nn)
      exact (div_le_one hpow_pos).mpr (hm_le.trans (by nlinarith [ht1]))
    have hs0nn : 0 ≤ s :=
      le_min (div_nonneg (Nat.cast_nonneg (m + 1)) hpow_nn) zero_le_one
    have hs1 : s ≤ 1 := min_le_right _ _
    have hgap : s - r ≤ ((2 : ℝ) ^ k)⁻¹ := by
      have hs0r : s0 - r = ((2 : ℝ) ^ k)⁻¹ := by
        simpa [r, s0] using dyadic_gap m k
      cases le_total s0 1 with
      | inl h => have := min_eq_left h; linarith
      | inr h =>
        have hs_eq : s = 1 := min_eq_right h
        have : 1 - r ≤ ((2 : ℝ) ^ k)⁻¹ := by
          have : 1 - r ≤ s0 - r := sub_le_sub_right h _
          linarith
        simpa [hs_eq] using this
    have hrE_le : (r • E) ≤ t • E := smul_le_smul_of_le E hE hr0 hr_le_t
    have htE_le : t • E ≤ s • E := smul_le_smul_of_le E hE ht0 ht_le_s
    have hsE_le1 : (s • E) ≤ 1 := smul_le_one_of_le_one E hE hE1 s hs0nn hs1
    have hrE_le1 : (r • E) ≤ 1 := smul_le_one_of_le_one E hE hE1 r hr0 hr1
    have hβr :
        effectExpectation (doubleDualEffectPairing F) (r • E) (hE.smul hr0) hrE_le1 =
          (r : ℂ) * βE := by
      simpa [βE] using
        effectExpectation_ofReal_dyadic F m k r rfl E hE hE1 hr0 hr1 hrE_le1
    have hβs :
        effectExpectation (doubleDualEffectPairing F) (s • E) (hE.smul hs0nn) hsE_le1 =
          (s : ℂ) * βE := by
      cases le_total s0 1 with
      | inl h =>
        have hs_eq : s = s0 := min_eq_left h
        -- s = (m+1)/2^k
        have hs_dy : s = ((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k := hs_eq
        simpa [βE] using
          effectExpectation_ofReal_dyadic F (m + 1) k s hs_dy E hE hE1 hs0nn hs1 hsE_le1
      | inr h =>
        have hs_eq : s = (1 : ℝ) := min_eq_right h
        -- β(s•E) = β(1•E) = β(E) = 1*βE = s*βE
        have hL :
            effectExpectation (doubleDualEffectPairing F) (s • E)
              (hE.smul hs0nn) hsE_le1 =
            effectExpectation (doubleDualEffectPairing F) ((1 : ℝ) • E)
              (hE.smul zero_le_one) (by simpa [one_smul] using hE1) := by
          simp only [effectExpectation, hs_eq]
        rw [hL, effectExpectation_one_smul_doubleDual F E hE hE1, hs_eq, hβE_def]
        simp [Complex.ofReal_one]
    have hmono_r :=
      effectExpectation_mono_doubleDual F (r • E) (t • E) (hE.smul hr0) hEt_psd
        hrE_le1 hEt_le hrE_le
    have hmono_s :=
      effectExpectation_mono_doubleDual F (t • E) (s • E) hEt_psd (hE.smul hs0nn)
        hEt_le hsE_le1 htE_le
    have hβr_re :
        (effectExpectation (doubleDualEffectPairing F) (r • E)
          (hE.smul hr0) hrE_le1).re = r * βE.re := by
      rw [hβr]; simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, himE]
    have hβs_re :
        (effectExpectation (doubleDualEffectPairing F) (s • E)
          (hE.smul hs0nn) hsE_le1).re = s * βE.re := by
      rw [hβs]; simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, himE]
    have hlow : r * βE.re ≤ βt.re := by simpa [βt, hβr_re] using hmono_r
    have hhigh : βt.re ≤ s * βE.re := by simpa [βt, hβs_re] using hmono_s
    have habs : |βt.re - t * βE.re| ≤ (s - r) * βE.re := by
      rw [abs_sub_le_iff]; constructor <;> nlinarith
    have hgapβ : (s - r) * βE.re ≤ ((2 : ℝ) ^ k)⁻¹ := by
      have h1 := mul_le_mul_of_nonneg_right hgap hreE_nn
      have h2 := mul_le_mul_of_nonneg_left hβE_re_le1 (inv_nonneg.mpr hpow_nn)
      nlinarith
    exact habs.trans hgapβ
  have hre_eq : βt.re = t * βE.re := by
    have hx := abs_le_inv_pow_two_eq_zero (βt.re - t * βE.re) fun k => by
      simpa [sub_eq_add_neg] using hclose k
    linarith
  refine Complex.ext ?_ ?_
  · have hL :
        (effectExpectation (doubleDualEffectPairing F) (t • E)
          (hE.smul ht0) (smul_le_one_of_le_one E hE hE1 t ht0 ht1)).re = βt.re := by
      simp only [βt, effectExpectation]
    rw [hL, hre_eq]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, himE, βE]
  · have hL :
        (effectExpectation (doubleDualEffectPairing F) (t • E)
          (hE.smul ht0) (smul_le_one_of_le_one E hE hE1 t ht0 ht1)).im = βt.im := by
      simp only [βt, effectExpectation]
    rw [hL]
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, himE, himt, βE]


theorem conj_mul_self_eq_normSq (c : ℂ) :
    star c * c = ↑(Complex.normSq c) := by
  simpa using (Complex.normSq_eq_conj_mul_self (z := c)).symm

theorem conj_mul_self_re (c : ℂ) : (star c * c).re = Complex.normSq c := by
  rw [conj_mul_self_eq_normSq]; simp

theorem conj_mul_self_im (c : ℂ) : (star c * c).im = 0 := by
  rw [conj_mul_self_eq_normSq]; simp

theorem vecMulVec_smul_star {ι : Type*} [Fintype ι]
    (a : ℂ) (v : ι → ℂ) :
    Matrix.vecMulVec (a • v) (star (a • v)) =
      (a * star a) • Matrix.vecMulVec v (star v) := by
  ext i j
  simp [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem ofReal_sqrt_sq (x : ℝ) (hx : 0 ≤ x) :
    (↑(Real.sqrt x) : ℂ) * ↑(Real.sqrt x) = ↑x := by
  norm_cast; exact Real.mul_self_sqrt hx

theorem normalizeVec_smul_projector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (v : ι → ℂ) (_hc : c ≠ 0)
    (hv : star v ⬝ᵥ v ≠ 0) (hcv : star (c • v) ⬝ᵥ (c • v) ≠ 0) :
    Matrix.vecMulVec (normalizeVec (c • v) hcv) (star (normalizeVec (c • v) hcv)) =
      Matrix.vecMulVec (normalizeVec v hv) (star (normalizeVec v hv)) := by
  have hre_v := (star_dotProduct_self_nonneg_real v).1
  have him_v := (star_dotProduct_self_nonneg_real v).2
  have hre_cv := (star_dotProduct_self_nonneg_real (c • v)).1
  have hnrm_re : (star (c • v) ⬝ᵥ (c • v)).re =
      Complex.normSq c * (star v ⬝ᵥ v).re := by
    rw [star_dotProduct_smul_self, Complex.mul_re, conj_mul_self_im, him_v,
      conj_mul_self_re]; ring
  set svR : ℝ := Real.sqrt (star v ⬝ᵥ v).re
  set scvR : ℝ := Real.sqrt (star (c • v) ⬝ᵥ (c • v)).re
  set sv : ℂ := ↑svR
  set scv : ℂ := ↑scvR
  have hsv_ne : sv ≠ 0 := by
    intro h
    have : (star v ⬝ᵥ v).re = 0 :=
      (Real.sqrt_eq_zero hre_v).1 (by simpa [sv, svR] using congrArg Complex.re h)
    exact hv (Complex.ext this him_v)
  have hscv_ne : scv ≠ 0 := by
    intro h
    have him_cv := (star_dotProduct_self_nonneg_real (c • v)).2
    have : (star (c • v) ⬝ᵥ (c • v)).re = 0 :=
      (Real.sqrt_eq_zero hre_cv).1 (by simpa [scv, scvR] using congrArg Complex.re h)
    exact hcv (Complex.ext this him_cv)
  have hcv_proj :
      Matrix.vecMulVec (normalizeVec (c • v) hcv) (star (normalizeVec (c • v) hcv)) =
        (scv⁻¹ * star scv⁻¹) • Matrix.vecMulVec (c • v) (star (c • v)) := by
    unfold normalizeVec
    change Matrix.vecMulVec (scv⁻¹ • (c • v)) (star (scv⁻¹ • (c • v))) = _
    exact vecMulVec_smul_star scv⁻¹ (c • v)
  have hv_proj :
      Matrix.vecMulVec (normalizeVec v hv) (star (normalizeVec v hv)) =
        (sv⁻¹ * star sv⁻¹) • Matrix.vecMulVec v (star v) := by
    unfold normalizeVec
    change Matrix.vecMulVec (sv⁻¹ • v) (star (sv⁻¹ • v)) = _
    exact vecMulVec_smul_star sv⁻¹ v
  have hcv_expand :
      Matrix.vecMulVec (normalizeVec (c • v) hcv) (star (normalizeVec (c • v) hcv)) =
        ((scv⁻¹ * star scv⁻¹) * (c * star c)) • Matrix.vecMulVec v (star v) := by
    rw [hcv_proj, vecMulVec_smul_star c v, smul_smul]
  have hcoef : (scv⁻¹ * star scv⁻¹) * (c * star c) = sv⁻¹ * star sv⁻¹ := by
    have hcstar : c * star c = ↑(Complex.normSq c) := by
      simpa using Complex.mul_conj c
    have hsv_star : star sv = sv := by simp [sv, Complex.conj_ofReal]
    have hscv_star : star scv = scv := by simp [scv, Complex.conj_ofReal]
    have hsv_sq : sv * sv = ↑((star v ⬝ᵥ v).re) := by
      simp [sv, svR]; exact ofReal_sqrt_sq _ hre_v
    have hscv_sq : scv * scv = ↑(Complex.normSq c) * ↑((star v ⬝ᵥ v).re) := by
      have h := ofReal_sqrt_sq (star (c • v) ⬝ᵥ (c • v)).re hre_cv
      have hscv_def : scv = ↑(Real.sqrt (star (c • v) ⬝ᵥ (c • v)).re) := by
        simp [scv, scvR]
      rw [← hscv_def, hnrm_re] at h
      simpa [Complex.ofReal_mul] using h
    rw [hcstar, star_inv₀, star_inv₀, hsv_star, hscv_star]
    field_simp [hsv_ne, hscv_ne]
    simp only [pow_two, hsv_sq, hscv_sq]
  rw [hcv_expand, hcoef, hv_proj]

theorem effectPairingQuad_smul {A : ℕ}
    (α : Superoperator A 1 → Superoperator 1 1) (c : ℂ) (v : Fin A → ℂ) :
    effectPairingQuad α (c • v) =
      (star c * c) * effectPairingQuad α v := by
  simp only [effectPairingQuad]
  by_cases hv : star v ⬝ᵥ v = 0
  · simp [hv]
  · by_cases hcv : star (c • v) ⬝ᵥ (c • v) = 0
    · have : (star c * c) * (star v ⬝ᵥ v) = 0 := by
        simpa [star_dotProduct_smul_self] using hcv
      have hc0 : star c * c = 0 := (mul_eq_zero.mp this).resolve_right hv
      rw [dif_pos hcv, dif_neg hv, hc0, zero_mul]
    · have hc0 : c ≠ 0 := fun hc => by
        simp [hc, zero_smul] at hcv
      have hproj := normalizeVec_smul_projector c v hc0 hv hcv
      rw [dif_neg hcv, dif_neg hv, star_dotProduct_smul_self]
      have hof :
          ofEffect
              (Matrix.vecMulVec (normalizeVec (c • v) hcv)
                (star (normalizeVec (c • v) hcv)))
              (Matrix.posSemidef_vecMulVec_self_star _)
              (vecMulVec_unit_le_one _ (normalizeVec_norm (c • v) hcv)) =
            ofEffect
              (Matrix.vecMulVec (normalizeVec v hv)
                (star (normalizeVec v hv)))
              (Matrix.posSemidef_vecMulVec_self_star _)
              (vecMulVec_unit_le_one _ (normalizeVec_norm v hv)) := by
        simp only [hproj]
      rw [hof]
      ring

theorem effectPairingPolar_self {A : ℕ}
    (α : Superoperator A 1 → Superoperator 1 1) (v : Fin A → ℂ) :
    effectPairingPolar α v v = effectPairingQuad α v := by
  simp only [effectPairingPolar]
  have hv2 : v + v = (2 : ℂ) • v := by ext; simp; ring
  have hvpi : v + Complex.I • v = (1 + Complex.I) • v := by ext; simp; ring
  have hvmi : v - Complex.I • v = (1 - Complex.I) • v := by ext; simp; ring
  have hq0 : effectPairingQuad α (v - v) = 0 := by
    simp [sub_self, effectPairingQuad]
  have hq2 := effectPairingQuad_smul α (2 : ℂ) v
  have hqpi := effectPairingQuad_smul α (1 + Complex.I) v
  have hqmi := effectPairingQuad_smul α (1 - Complex.I) v
  have h2 : star (2 : ℂ) * (2 : ℂ) = 4 := by norm_num
  have hpi : star (1 + Complex.I) * (1 + Complex.I) = 2 := by
    simp [star_add]; ring_nf; norm_num
  have hmi : star (1 - Complex.I) * (1 - Complex.I) = 2 := by
    simp [star_sub]; ring_nf; norm_num
  simp only [hv2, hvpi, hvmi]
  rw [hq2, hq0, hqpi, hqmi, h2, hpi, hmi]
  ring


theorem vecMulVec_parallelogram {ι : Type*} [Fintype ι]
    (x y : ι → ℂ) :
    Matrix.vecMulVec (x + y) (star (x + y)) +
      Matrix.vecMulVec (x - y) (star (x - y)) =
      (2 : ℂ) • Matrix.vecMulVec x (star x) +
        (2 : ℂ) • Matrix.vecMulVec y (star y) := by
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply,
    Pi.sub_apply, Pi.star_apply, smul_eq_mul, star_add, star_sub]
  ring

theorem vecMulVec_parallelogram_I {ι : Type*} [Fintype ι]
    (x y : ι → ℂ) :
    Matrix.vecMulVec (x + Complex.I • y) (star (x + Complex.I • y)) +
      Matrix.vecMulVec (x - Complex.I • y) (star (x - Complex.I • y)) =
      (2 : ℂ) • Matrix.vecMulVec x (star x) +
        (2 : ℂ) • Matrix.vecMulVec y (star y) := by
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply,
    Pi.sub_apply, Pi.star_apply, smul_eq_mul, star_add, star_sub, star_smul]
  ring_nf
  -- goal has -I^2; rewrite I^2 = -1
  rw [Complex.I_sq]
  ring

theorem vecMulVec_mulVec_self {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    (Matrix.vecMulVec v (star v)) *ᵥ v = (star v ⬝ᵥ v) • v := by
  ext i
  simp only [mulVec, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, dotProduct]
  calc ∑ j, v i * star (v j) * v j
      = ∑ j, (star (v j) * v j) * v i :=
        Finset.sum_congr rfl fun j _ => by ring
    _ = (∑ j, star (v j) * v j) * v i := (Finset.sum_mul _ _ _).symm

theorem ofReal_re_of_im_zero (z : ℂ) (him : z.im = 0) : (↑z.re : ℂ) = z := by
  apply Complex.ext
  · simp
  · simpa using him.symm

theorem star_dot_smul {A : ℕ} (c : ℂ) (v w : Fin A → ℂ) :
    star v ⬝ᵥ (c • w) = c * (star v ⬝ᵥ w) := by
  simp [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

theorem vecMulVec_le_one_normSq_le_one {A : ℕ}
    (v : Fin A → ℂ)
    (hle : Matrix.vecMulVec v (star v) ≤ (1 : Matrix (Fin A) (Fin A) ℂ)) :
    (star v ⬝ᵥ v).re ≤ 1 := by
  have him := (star_dotProduct_self_nonneg_real v).2
  set nrm := star v ⬝ᵥ v
  have hdiff : ((1 : Matrix (Fin A) (Fin A) ℂ) -
      Matrix.vecMulVec v (star v)).PosSemidef := Matrix.le_iff.mp hle
  have hpos := Matrix.PosSemidef.dotProduct_mulVec_nonneg hdiff v
  have hI : star v ⬝ᵥ (1 : Matrix (Fin A) (Fin A) ℂ) *ᵥ v = nrm := by simp [nrm]
  have hP : star v ⬝ᵥ (Matrix.vecMulVec v (star v)) *ᵥ v = nrm * nrm := by
    rw [vecMulVec_mulVec_self, star_dot_smul]
  have hsub : star v ⬝ᵥ ((1 : Matrix (Fin A) (Fin A) ℂ) -
      Matrix.vecMulVec v (star v)) *ᵥ v = nrm - nrm * nrm := by
    rw [sub_mulVec, dotProduct_sub, hI, hP]
  have hnn : 0 ≤ (nrm - nrm * nrm).re := by
    have := hpos; rw [hsub] at this
    exact (Complex.nonneg_iff.mp this).1
  have : (nrm - nrm * nrm).re = nrm.re - nrm.re * nrm.re := by
    simp [Complex.sub_re, Complex.mul_re, him]
  rw [this] at hnn
  nlinarith

theorem effectPairingQuad_eq_expectation {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (v : Fin A → ℂ)
    (hle : Matrix.vecMulVec v (star v) ≤ (1 : Matrix (Fin A) (Fin A) ℂ)) :
    effectPairingQuad (doubleDualEffectPairing F) v =
      effectExpectation (doubleDualEffectPairing F)
        (Matrix.vecMulVec v (star v))
        (Matrix.posSemidef_vecMulVec_self_star v) hle := by
  simp only [effectPairingQuad]
  by_cases hv : star v ⬝ᵥ v = 0
  · have hmat : Matrix.vecMulVec v (star v) = 0 := by
      have : v = 0 := (dotProduct_star_self_eq_zero).1 hv
      simp [this]
    have h0 := effectExpectation_zero_doubleDual (A := A) F
    simp only [effectExpectation, hv, hmat] at h0 ⊢
    simpa using h0.symm
  · set û := normalizeVec v hv
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
        (star v ⬝ᵥ v) • Matrix.vecMulVec û (star û) := by
      calc Matrix.vecMulVec v (star v)
          = Matrix.vecMulVec (s • û) (star (s • û)) := by rw [hv_eq]
        _ = (s * star s) • Matrix.vecMulVec û (star û) := vecMulVec_smul_star s û
        _ = (s * s) • Matrix.vecMulVec û (star û) := by rw [hstar_s]
        _ = (star v ⬝ᵥ v) • Matrix.vecMulVec û (star û) := by rw [← hnrm_sq]
    have ht0 : (0 : ℝ) ≤ (star v ⬝ᵥ v).re := hre
    have ht1 : (star v ⬝ᵥ v).re ≤ 1 := vecMulVec_le_one_normSq_le_one v hle
    have hû_le : Matrix.vecMulVec û (star û) ≤ 1 :=
      vecMulVec_unit_le_one û (normalizeVec_norm v hv)
    have hnrm_ofReal : (↑((star v ⬝ᵥ v).re) : ℂ) = star v ⬝ᵥ v :=
      ofReal_re_of_im_zero _ him
    have hsmul_eq :
        ((star v ⬝ᵥ v).re : ℝ) • Matrix.vecMulVec û (star û) =
          (star v ⬝ᵥ v) • Matrix.vecMulVec û (star û) := by
      ext i j
      simp [Matrix.smul_apply, smul_eq_mul, hnrm_ofReal]
    have hmat' : Matrix.vecMulVec v (star v) =
        ((star v ⬝ᵥ v).re : ℝ) • Matrix.vecMulVec û (star û) := by
      rw [hmat, ← hsmul_eq]
    have hβ :=
      effectExpectation_smul_doubleDual F (star v ⬝ᵥ v).re ht0 ht1
        (Matrix.vecMulVec û (star û))
        (Matrix.posSemidef_vecMulVec_self_star û) hû_le
    rw [dif_neg hv]
    have hR :
        effectExpectation (doubleDualEffectPairing F)
          (Matrix.vecMulVec v (star v))
          (Matrix.posSemidef_vecMulVec_self_star v) hle =
        (↑((star v ⬝ᵥ v).re) : ℂ) *
          effectExpectation (doubleDualEffectPairing F)
            (Matrix.vecMulVec û (star û))
            (Matrix.posSemidef_vecMulVec_self_star û) hû_le := by
      have hL :
          effectExpectation (doubleDualEffectPairing F)
            (Matrix.vecMulVec v (star v))
            (Matrix.posSemidef_vecMulVec_self_star v) hle =
          effectExpectation (doubleDualEffectPairing F)
            (((star v ⬝ᵥ v).re : ℝ) • Matrix.vecMulVec û (star û))
            ((Matrix.posSemidef_vecMulVec_self_star û).smul ht0)
            (smul_le_one_of_le_one _ (Matrix.posSemidef_vecMulVec_self_star û)
              hû_le _ ht0 ht1) := by
        simp only [effectExpectation, hmat']
      rw [hL, hβ]
    have hborn :
        bornScalar (doubleDualEffectPairing F
          (ofEffect (Matrix.vecMulVec (normalizeVec v hv)
            (star (normalizeVec v hv)))
            (Matrix.posSemidef_vecMulVec_self_star _)
            (vecMulVec_unit_le_one _ (normalizeVec_norm v hv)))) =
        effectExpectation (doubleDualEffectPairing F)
          (Matrix.vecMulVec û (star û))
          (Matrix.posSemidef_vecMulVec_self_star û) hû_le := by
      simp only [effectExpectation, û]
    rw [hborn, ← hnrm_ofReal, hR]


theorem effectPairingQuad_nonneg {A : ℕ}
    (α : Superoperator A 1 → Superoperator 1 1) (v : Fin A → ℂ) :
    0 ≤ (effectPairingQuad α v).re ∧ (effectPairingQuad α v).im = 0 := by
  simp only [effectPairingQuad]
  split_ifs with h
  · simp
  · have hb :=
      bornScalar_nonneg
        (α (ofEffect
          (Matrix.vecMulVec (normalizeVec v h) (star (normalizeVec v h)))
          (Matrix.posSemidef_vecMulVec_self_star _)
          (vecMulVec_unit_le_one _ (normalizeVec_norm v h))))
    have hnrm := star_dotProduct_self_nonneg_real v
    constructor
    · simp only [Complex.mul_re, hnrm.2, hb.2.1, mul_zero, sub_zero]
      nlinarith [hnrm.1, hb.1]
    · simp [Complex.mul_im, hnrm.2, hb.2.1]


end SuperoperatorModule

end QLambda.Domain.Presheaf
