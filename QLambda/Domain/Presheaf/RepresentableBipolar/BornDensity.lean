/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.RepresentableBipolar.BornExpectationExt

/-!
# Density recovery from the polarized Born form

Spectral / rank-one expansion and `densityFromDoubleDual` positivity.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder InnerProductSpace Kronecker

universe u

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
