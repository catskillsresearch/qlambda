/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.PhysicalTheory

/-!
# Choi observations do not characterize TT refinement

This file gives a rational, two-dimensional counterexample.  The classical
output is the four-element diamond `Bool × Bool`.  A bottom branch completes
each instrument to a trace-preserving one; every proper upper observation
therefore sees exactly the three branches responsible for the counterexample.
-/

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace QLambda.RefinementCounterexample

abbrev Diamond := Bool × Bool

local instance diamondPreorder : Preorder Diamond where
  le x y := x.1 ≤ y.1 ∧ x.2 ≤ y.2
  lt x y := (x.1 ≤ y.1 ∧ x.2 ≤ y.2) ∧
    ¬(y.1 ≤ x.1 ∧ y.2 ≤ x.2)
  le_refl := by
    rintro ⟨a, b⟩
    cases a <;> cases b <;> simp
  le_trans := by
    rintro ⟨a₀, a₁⟩ ⟨b₀, b₁⟩ ⟨c₀, c₁⟩ hab hbc
    cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;>
      cases c₀ <;> cases c₁ <;> simp_all
  lt_iff_le_not_ge := by intros; rfl

private noncomputable def quarter : ℂ := ⟨1 / 4, 0⟩

private noncomputable def k (x y : ℂ) : KrausOperator 2 2 :=
  fun i j => if i = 0 then if j = 0 then x * quarter else y * quarter else 0

private def l (x y : ℂ) : KrausOperator 2 2 :=
  fun i j => if j = 0 then if i = 0 then x else y else 0

private def copies (n : ℕ) (A : KrausOperator 2 2) : KrausFamily 2 2 :=
  List.replicate n A

private noncomputable def muBranch : Diamond → KrausFamily 2 2
  | (false, false) => copies 9 (k 1 0) ++ copies 9 (k 0 1)
  | (true, false) => copies 2 (k 1 0) ++ copies 2 (k 0 1)
  | (false, true) => copies 5 (k 1 0) ++ copies 5 (k 0 1)
  | (true, true) => []

private noncomputable def nuBranch : Diamond → KrausFamily 2 2
  | (false, false) =>
      copies 2 (k 1 (-1)) ++ copies 3 (k 1 0) ++ copies 6 (k 0 1)
  | (true, false) => copies 2 (k 1 1) ++ [k 0 1]
  | (false, true) => copies 2 (k 1 (-1)) ++ copies 3 (k 1 0)
  | (true, true) => copies 2 (k 1 1) ++ copies 2 (k 1 0) ++ [k 0 1]

private theorem mu_trace (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ o : Diamond,
        (Matrix.trace (KrausFamily.applyMat (muBranch o) ρ)).re =
      (Matrix.trace ρ).re := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  simp [muBranch, copies, k, quarter, KrausFamily.applyMat, Matrix.mul_apply,
    Matrix.trace, conjTranspose]
  norm_num
  ring

private theorem nu_trace (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ o : Diamond,
        (Matrix.trace (KrausFamily.applyMat (nuBranch o) ρ)).re =
      (Matrix.trace ρ).re := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  simp [nuBranch, copies, k, quarter, KrausFamily.applyMat, Matrix.mul_apply,
    Matrix.trace, conjTranspose]
  norm_num
  ring

private noncomputable def mu : FiniteInstrumentComp 2 Diamond where
  Outcome := Diamond
  branch := muBranch
  value := id
  trace_nonincreasing := fun ρ _ => (mu_trace ρ).le

private noncomputable def nu : FiniteInstrumentComp 2 Diamond where
  Outcome := Diamond
  branch := nuBranch
  value := id
  trace_nonincreasing := fun ρ _ => (nu_trace ρ).le

private theorem observed_top :
    KrausFamily.choi (nuBranch (true, true)) -
        KrausFamily.choi (muBranch (true, true)) =
      KrausFamily.choi (nuBranch (true, true)) := by
  simp [muBranch]

private theorem observed_a_top :
    (KrausFamily.choi (nuBranch (true, true)) +
        KrausFamily.choi (nuBranch (true, false))) -
      (KrausFamily.choi (muBranch (true, true)) +
        KrausFamily.choi (muBranch (true, false))) =
      KrausFamily.choi [k 2 2] := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [muBranch, nuBranch, copies, k, quarter, KrausFamily.choi,
      KrausFamily.choiTerm] <;> ring

private theorem observed_c_top :
    (KrausFamily.choi (nuBranch (true, true)) +
        KrausFamily.choi (nuBranch (false, true))) -
      (KrausFamily.choi (muBranch (true, true)) +
        KrausFamily.choi (muBranch (false, true))) =
      KrausFamily.choi [k 2 0] := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [muBranch, nuBranch, copies, k, quarter, KrausFamily.choi,
      KrausFamily.choiTerm] <;> ring

private theorem observed_nonbottom :
    (KrausFamily.choi (nuBranch (true, true)) +
        KrausFamily.choi (nuBranch (true, false)) +
        KrausFamily.choi (nuBranch (false, true))) -
      (KrausFamily.choi (muBranch (true, true)) +
        KrausFamily.choi (muBranch (true, false)) +
        KrausFamily.choi (muBranch (false, true))) =
      KrausFamily.choi [k 2 1] := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [muBranch, nuBranch, copies, k, quarter, KrausFamily.choi,
      KrausFamily.choiTerm] <;> ring

private theorem observed_all :
    (∑ o : Diamond, KrausFamily.choi (muBranch o)) =
      ∑ o : Diamond, KrausFamily.choi (nuBranch o) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  ext ⟨i, j⟩ ⟨i', j'⟩
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [muBranch, nuBranch, copies, k, quarter, KrausFamily.choi,
      KrausFamily.choiTerm] <;> ring

private theorem observation_refines :
    FiniteInstrumentComp.ObservationRefines mu nu := by
  classical
  intro U
  rw [FiniteInstrumentComp.observationChoi_eq_testChoi,
    FiniteInstrumentComp.observationChoi_eq_testChoi]
  unfold FiniteInstrumentComp.testChoi
  simp only [mu, nu]
  change
    (∑ o : Diamond, if o ∈ (U : Set Diamond) then
        KrausFamily.choi (muBranch o) else 0) ≤
      ∑ o : Diamond, if o ∈ (U : Set Diamond) then
        KrausFamily.choi (nuBranch o) else 0
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  by_cases hb : (false, false) ∈ (U : Set Diamond)
  · have hall : ∀ d : Diamond, d ∈ (U : Set Diamond) :=
      fun d => U.isScottOpen.1 (bot_le : (false, false) ≤ d) hb
    simp [hall]
    simpa [Fintype.sum_prod_type, Fintype.sum_bool] using observed_all.le
  · by_cases ha : (true, false) ∈ (U : Set Diamond)
    · have ht : (true, true) ∈ (U : Set Diamond) :=
        U.isScottOpen.1 (by simp) ha
      by_cases hc : (false, true) ∈ (U : Set Diamond)
      · simp [hb, ha, hc, ht]
        rw [Matrix.le_iff, observed_nonbottom]
        exact KrausFamily.choi_posSemidef _
      · simp [hb, ha, hc, ht]
        rw [Matrix.le_iff, observed_a_top]
        exact KrausFamily.choi_posSemidef _
    · by_cases hc : (false, true) ∈ (U : Set Diamond)
      · have ht : (true, true) ∈ (U : Set Diamond) :=
          U.isScottOpen.1 (by simp) hc
        simp [hb, ha, hc, ht]
        rw [Matrix.le_iff, observed_c_top]
        exact KrausFamily.choi_posSemidef _
      · by_cases ht : (true, true) ∈ (U : Set Diamond)
        · simp [hb, ha, hc, ht]
          rw [Matrix.le_iff, observed_top]
          exact KrausFamily.choi_posSemidef _
        · simp [hb, ha, hc, ht]

private def postPred : Diamond → KrausFamily 2 2
  | (false, false) => []
  | (true, false) => [l 1 0, l 1 0]
  | (false, true) => [l 1 1]
  | (true, true) => [l 1 0, l 1 0, l 0 1, l 0 1]

private theorem plus_residual (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    KrausFamily.applyMat (postPred (true, true)) ρ =
      KrausFamily.applyMat (postPred (false, true) ++ [l 1 (-1)]) ρ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [postPred, l, KrausFamily.applyMat, Matrix.mul_apply, conjTranspose]

private theorem bottom_refines (d : Diamond) :
    KrausFamily.Refines (postPred (false, false)) (postPred d) := by
  refine ⟨postPred d, fun ρ => ?_⟩
  simp [postPred, KrausFamily.applyMat]

private theorem a_refines_top :
    KrausFamily.Refines (postPred (true, false)) (postPred (true, true)) := by
  refine ⟨[l 0 1, l 0 1], fun ρ => ?_⟩
  rfl

private theorem c_refines_top :
    KrausFamily.Refines (postPred (false, true)) (postPred (true, true)) :=
  ⟨[l 1 (-1)], plus_residual⟩

private noncomputable def post : FiniteInstrumentComp.KrausPost 2 Diamond where
  pred := postPred
  mono := by
    rintro ⟨d₀, d₁⟩ ⟨e₀, e₁⟩ h
    change d₀ ≤ e₀ ∧ d₁ ≤ e₁ at h
    rcases h with ⟨h₀, h₁⟩
    fin_cases d₀ <;> fin_cases d₁ <;> fin_cases e₀ <;> fin_cases e₁
    all_goals
      try
        have hfalse : ¬(true : Bool) ≤ false := by decide
        contradiction
    all_goals
      first
      | exact KrausFamily.residualRefines_refl _
      | exact bottom_refines _
      | exact a_refines_top
      | exact c_refines_top

private def witness : (Fin 2 × Fin 2) → ℂ
  | (0, 0) => -1
  | (0, 1) => 2
  | (1, 0) => 0
  | (1, 1) => 1

private theorem choi_wp_eq_sum (ξ : FiniteInstrumentComp 2 Diamond)
    (P : Diamond → KrausFamily 2 2) :
    KrausFamily.choi (ξ.wpKraus P) =
      ∑ o : ξ.Outcome,
        KrausFamily.choi (KrausFamily.comp (P (ξ.value o)) (ξ.branch o)) := by
  classical
  unfold FiniteInstrumentComp.wpKraus
  rw [FiniteInstrumentComp.choi_flatMap]
  rw [← List.sum_toFinset
    (fun o : ξ.Outcome =>
      KrausFamily.choi (KrausFamily.comp (P (ξ.value o)) (ξ.branch o)))
    (Finset.nodup_toList Finset.univ)]
  simp

private theorem witness_negative :
    star witness ⬝ᵥ
        ((KrausFamily.choi (nu.wpKraus post) -
          KrausFamily.choi (mu.wpKraus post)).mulVec witness) =
      (-1 / 16 : ℂ) := by
  rw [choi_wp_eq_sum, choi_wp_eq_sum]
  change
    star witness ⬝ᵥ
        (((∑ o : Diamond,
            KrausFamily.choi
              (KrausFamily.comp (postPred o) (nuBranch o))) -
          (∑ o : Diamond,
            KrausFamily.choi
              (KrausFamily.comp (postPred o) (muBranch o)))).mulVec witness) =
      (-1 / 16 : ℂ)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [dotProduct, Matrix.mulVec]
  simp_rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Fin.sum_univ_two]
  simp [postPred, muBranch, nuBranch, copies, k, quarter, l, witness,
    KrausFamily.comp, KrausFamily.choi, KrausFamily.choiTerm,
    Matrix.mul_apply]
  apply Complex.ext <;> norm_num

private theorem not_refines :
    ¬ FiniteInstrumentComp.Refines mu nu := by
  intro h
  have hchoi :=
    KrausFamily.choiRefines_of_residualRefines (h post)
  rw [KrausFamily.ChoiRefines, Matrix.le_iff] at hchoi
  have hnonneg :=
    hchoi.dotProduct_mulVec_nonneg witness
  rw [witness_negative] at hnonneg
  rw [RCLike.nonneg_iff] at hnonneg
  norm_num at hnonneg

/-- On a qubit and the four-element diamond, pointwise Choi refinement
of all Scott-open observations is strictly weaker than TT refinement. -/
theorem exists_observationRefines_not_refines :
    ∃ μ ν : FiniteInstrumentComp 2 (Bool × Bool),
      FiniteInstrumentComp.ObservationRefines μ ν ∧
        ¬ FiniteInstrumentComp.Refines μ ν :=
  ⟨mu, nu, observation_refines, not_refines⟩

end QLambda.RefinementCounterexample
