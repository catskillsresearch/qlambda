/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.RepresentableBipolar.BornPolarDensity

/-!
# Born match and n = 1 preparation

`born_match_density` and the preparation gate used by surjectivity.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder InnerProductSpace Kronecker

universe u

/-! ### Born match and n=1 preparation -/

/-- On every Loewner effect, the double-dual Born pairing matches the density
recovered by polarization: `β(E) = Tr(E ρ)`. -/
theorem born_match_density {A : ℕ} (_hA : 0 < A)
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E : Matrix (Fin A) (Fin A) ℂ) (hpsd : E.PosSemidef) (hle : E ≤ 1) :
    effectExpectation (doubleDualEffectPairing F) E hpsd hle =
      Matrix.trace (E * densityFromEffectPairing (doubleDualEffectPairing F)) := by
  classical
  set ρ := densityFromEffectPairing (doubleDualEffectPairing F)
  have hHerm := hpsd.isHermitian
  set U : Matrix (Fin A) (Fin A) ℂ := ↑hHerm.eigenvectorUnitary
  set u : Fin A → (Fin A → ℂ) := fun i a => U a i
  set P : Fin A → Matrix (Fin A) (Fin A) ℂ := fun i =>
    Matrix.vecMulVec (fun a => U a i) (fun b => star (U b i))
  have hPu (i : Fin A) : P i = Matrix.vecMulVec (u i) (star (u i)) := by
    simp only [P, u]; congr 1
  have hPpsd : ∀ i, (P i).PosSemidef := fun i => by
    rw [hPu]; exact Matrix.posSemidef_vecMulVec_self_star (u i)
  have hLam0 : ∀ i, 0 ≤ hHerm.eigenvalues i :=
    fun i => PosSemidef.eigenvalues_nonneg hpsd i
  have hexp : E = ∑ i : Fin A, (hHerm.eigenvalues i : ℂ) • P i := by
    simpa [P, U] using isHermitian_eq_sum_eigenprojectors E hHerm
  have hexpR : E = ∑ i : Fin A, (hHerm.eigenvalues i : ℝ) • P i := by
    convert hexp using 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ext a b
    simp [Matrix.smul_apply, smul_eq_mul]
  have hExtβ : effectExpectationExt F E hpsd =
      effectExpectation (doubleDualEffectPairing F) E hpsd hle :=
    effectExpectationExt_of_le_one F E hpsd hle
  have hExtP (i : Fin A) :
      effectExpectationExt F (P i) (hPpsd i) =
        Matrix.trace (P i * ρ) := by
    have hq := effectPairingQuad_eq_ext F (u i)
    have hd := density_quad_eq F (u i)
    have htr := trace_vecMulVec_mul ρ (u i)
    have hL : effectExpectationExt F (P i) (hPpsd i) =
        effectExpectationExt F (Matrix.vecMulVec (u i) (star (u i)))
          (Matrix.posSemidef_vecMulVec_self_star (u i)) := by
      simp only [effectExpectationExt, hPu]
    have hR : Matrix.trace (P i * ρ) =
        Matrix.trace (Matrix.vecMulVec (u i) (star (u i)) * ρ) := by
      rw [hPu]
    rw [hL, hR]
    calc effectExpectationExt F (Matrix.vecMulVec (u i) (star (u i))) _
          = effectPairingQuad (doubleDualEffectPairing F) (u i) := hq.symm
      _ = star (u i) ⬝ᵥ ρ *ᵥ u i := hd.symm
      _ = Matrix.trace (Matrix.vecMulVec (u i) (star (u i)) * ρ) := htr.symm
  have hExtLamP (i : Fin A) :
      effectExpectationExt F ((hHerm.eigenvalues i : ℝ) • P i)
          ((hPpsd i).smul (hLam0 i)) =
        (hHerm.eigenvalues i : ℂ) * effectExpectationExt F (P i) (hPpsd i) :=
    effectExpectationExt_smul F (hHerm.eigenvalues i) (hLam0 i) (P i) (hPpsd i)
  have hExtSum : effectExpectationExt F E hpsd =
      ∑ i : Fin A, effectExpectationExt F ((hHerm.eigenvalues i : ℝ) • P i)
        ((hPpsd i).smul (hLam0 i)) := by
    have hadd : ∀ (s : Finset (Fin A)),
        effectExpectationExt F
            (∑ i ∈ s, (hHerm.eigenvalues i : ℝ) • P i)
            (sum_psd_matrix s (fun i => (hHerm.eigenvalues i : ℝ) • P i)
              (fun i _ => (hPpsd i).smul (hLam0 i))) =
          ∑ i ∈ s, effectExpectationExt F ((hHerm.eigenvalues i : ℝ) • P i)
            ((hPpsd i).smul (hLam0 i)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        have h0 : effectExpectationExt F (0 : Matrix (Fin A) (Fin A) ℂ)
            PosSemidef.zero = 0 := by
          simp only [effectExpectationExt, Matrix.trace_zero, Complex.zero_re,
            max_eq_right zero_le_one]
          have hz : ((1⁻¹ : ℝ) • (0 : Matrix (Fin A) (Fin A) ℂ)) = 0 := by
            ext; simp
          simpa [effectExpectation, hz] using
            effectExpectation_zero_doubleDual (A := A) F
        convert h0 <;> simp
      | insert i s hs ih =>
        simp only [Finset.sum_insert hs]
        have hE := (hPpsd i).smul (hLam0 i)
        have hS := sum_psd_matrix s (fun j => (hHerm.eigenvalues j : ℝ) • P j)
          (fun j _ => (hPpsd j).smul (hLam0 j))
        rw [effectExpectationExt_add F _ _ hE hS, ih]
    have h := hadd Finset.univ
    have hL : effectExpectationExt F
        (∑ i : Fin A, (hHerm.eigenvalues i : ℝ) • P i)
        (sum_psd_matrix Finset.univ (fun i => (hHerm.eigenvalues i : ℝ) • P i)
          (fun i _ => (hPpsd i).smul (hLam0 i))) =
      effectExpectationExt F E hpsd := by
      simp only [effectExpectationExt, ← hexpR]
    exact hL ▸ h
  calc effectExpectation (doubleDualEffectPairing F) E hpsd hle
      = effectExpectationExt F E hpsd := hExtβ.symm
    _ = ∑ i, effectExpectationExt F ((hHerm.eigenvalues i : ℝ) • P i)
          ((hPpsd i).smul (hLam0 i)) := hExtSum
    _ = ∑ i, (hHerm.eigenvalues i : ℂ) *
          effectExpectationExt F (P i) (hPpsd i) := by
          refine Finset.sum_congr rfl fun i _ => hExtLamP i
    _ = ∑ i, (hHerm.eigenvalues i : ℂ) * Matrix.trace (P i * ρ) := by
          refine Finset.sum_congr rfl fun i _ => by rw [hExtP]
    _ = ∑ i, Matrix.trace (((hHerm.eigenvalues i : ℂ) • P i) * ρ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hsm : ((hHerm.eigenvalues i : ℂ) • P i) * ρ =
              (hHerm.eigenvalues i : ℂ) • (P i * ρ) := Matrix.smul_mul _ _ _
          rw [hsm, Matrix.trace_smul, smul_eq_mul]
    _ = Matrix.trace ((∑ i, (hHerm.eigenvalues i : ℂ) • P i) * ρ) := by
          simp [Finset.sum_mul, Matrix.trace_sum]
    _ = Matrix.trace (E * ρ) := by rw [← hexp]

/-- From Born match: a double-dual fiber at `n = 1` yields a preparation `Φ`
with `e ∘ Φ = doubleDualEffectPairing F e` for every effect `e`. -/
theorem exists_preparation_of_doubleDual {A : ℕ} (hA : 0 < A)
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier) :
    ∃ Φ : Superoperator 1 A,
      ∀ e : Superoperator A 1,
        effectPrecompose Φ e = doubleDualEffectPairing F e := by
  set ρ := densityFromEffectPairing (doubleDualEffectPairing F)
  refine exists_superoperator_of_effect_pairing
    (doubleDualEffectPairing F) ρ
    (densityFromDoubleDual_posSemidef F)
    (trace_density_le_one F) ?_
  intro E hpsd hle
  simpa [effectExpectation] using born_match_density hA F E hpsd hle

end SuperoperatorModule

end QLambda.Domain.Presheaf
