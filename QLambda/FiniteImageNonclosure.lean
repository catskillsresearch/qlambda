/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.TTPhysicalEmbedding

/-!
# A finite-coordinate criterion for non-closure of the physical image

A finite instrument can exhibit only finitely many different Choi matrices
when tested by the coordinate opens `{A : Set ℕ | j ∈ A}`.  Consequently, any
continuation with injectively many recovered coordinate observations cannot
be a finite physical embedding.
-/

namespace QLambda

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open Scott1972.ContinuousLattice

namespace TTPhysicalEmbedding

/-- The upper Scott-open coordinate predicate on the powerset domain. -/
def coordinateSet (j : ℕ) : Set (Set ℕ) :=
  {A | j ∈ A}

/-! ## A concrete dyadic prefix chain -/

/-- The nested classical value returned by the `i`th dyadic branch. -/
def dyadicPrefix (i : ℕ) : Set ℕ :=
  Set.Iic i

/-- The probability carried by the `i`th branch. -/
noncomputable def dyadicWeight (i : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (i + 1)

/-- A one-dimensional Kraus branch with Choi weight `2⁻⁽ⁱ⁺¹⁾`. -/
noncomputable def dyadicBranch (i : ℕ) : KrausFamily 1 1 :=
  KrausFamily.scale (Real.sqrt (dyadicWeight i))
    (KrausFamily.identity 1)

theorem dyadicWeight_nonneg (i : ℕ) : 0 ≤ dyadicWeight i := by
  unfold dyadicWeight
  positivity

theorem dyadicWeight_pos (i : ℕ) : 0 < dyadicWeight i := by
  unfold dyadicWeight
  positivity

theorem dyadicBranch_applyMat
    (i : ℕ) (ρ : Matrix (Fin 1) (Fin 1) ℂ) :
    KrausFamily.applyMat (dyadicBranch i) ρ =
      (dyadicWeight i : ℂ) • ρ := by
  rw [dyadicBranch, KrausFamily.applyMat_scale,
    KrausFamily.applyMat_identity]
  have hsqrt :
      (Real.sqrt (dyadicWeight i) : ℂ) *
          star (Real.sqrt (dyadicWeight i) : ℂ) =
        dyadicWeight i := by
    simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    norm_cast
    simpa [pow_two] using Real.sq_sqrt (dyadicWeight_nonneg i)
  rw [hsqrt]

theorem sum_dyadicWeight (m : ℕ) :
    (∑ i : Fin (m + 1), dyadicWeight i) =
      1 - (1 / 2 : ℝ) ^ (m + 1) := by
  rw [← Finset.sum_range]
  simp only [dyadicWeight, pow_succ']
  rw [← Finset.mul_sum, geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
  field_simp
  ring

/-- The first `m+1` branches of the countably supported dyadic instrument. -/
noncomputable def dyadicStage (m : ℕ) :
    FiniteInstrumentComp 1 (Set ℕ) where
  Outcome := Fin (m + 1)
  branch := fun i => dyadicBranch i
  value := fun i => dyadicPrefix i
  trace_nonincreasing := by
    intro ρ hρ
    simp_rw [dyadicBranch_applyMat, Matrix.trace_smul]
    have hre (x : ℝ) :
        (((x : ℂ) • Matrix.trace ρ).re) =
          x * (Matrix.trace ρ).re := by
      rw [smul_eq_mul, Complex.mul_re]
      simp
    simp_rw [hre]
    rw [← Finset.sum_mul, sum_dyadicWeight]
    have htrace : 0 ≤ (Matrix.trace ρ).re := by
      simpa [Matrix.trace] using
        (Finset.sum_nonneg fun (j : Fin 1) (_ : j ∈ Finset.univ) =>
          (Complex.nonneg_iff.mp hρ.diag_nonneg).1)
    nlinarith [show 0 ≤ (1 / 2 : ℝ) ^ (m + 1) by positivity]

private theorem choi_wpKraus_eq_sum
    (μ : FiniteInstrumentComp 1 (Set ℕ))
    (P : Set ℕ → KrausFamily 1 1) :
    KrausFamily.choi (μ.wpKraus P) =
      ∑ o : μ.Outcome,
        KrausFamily.choi
          (KrausFamily.comp (P (μ.value o)) (μ.branch o)) := by
  classical
  unfold FiniteInstrumentComp.wpKraus
  rw [FiniteInstrumentComp.choi_flatMap]
  simp

theorem dyadicStage_wpKraus_refines
    (m : ℕ) (P : Set ℕ → KrausFamily 1 1) :
    KrausFamily.Refines
      ((dyadicStage m).wpKraus P)
      ((dyadicStage (m + 1)).wpKraus P) := by
  apply KrausFamily.residualRefines_of_choiRefines
  rw [KrausFamily.ChoiRefines, choi_wpKraus_eq_sum,
    choi_wpKraus_eq_sum]
  change
    (∑ i : Fin (m + 1),
      KrausFamily.choi
        (KrausFamily.comp (P (dyadicPrefix i)) (dyadicBranch i))) ≤
    ∑ i : Fin (m + 2),
      KrausFamily.choi
        (KrausFamily.comp (P (dyadicPrefix i)) (dyadicBranch i))
  conv_rhs => rw [Fin.sum_univ_castSucc]
  apply le_add_of_nonneg_right
  exact KrausFamily.choi_nonneg _

theorem dyadicStage_bind_finitaryTTRefines
    (m : ℕ) (ξ : Set ℕ → FiniteInstrumentComp 1 PUnit.{1}) :
    FiniteInstrumentComp.FinitaryTTRefines
      TTContinuation.resultCode
      ((dyadicStage m).bind ξ) ((dyadicStage (m + 1)).bind ξ) := by
  intro c
  exact KrausFamily.residualRefines_trans
    (KrausFamily.residualRefines_of_semEq
      (FiniteInstrumentComp.wpKraus_bind_semEq
        (dyadicStage m) ξ (c.decode TTContinuation.resultCode)))
    (KrausFamily.residualRefines_trans
      (dyadicStage_wpKraus_refines m
        (fun d => (ξ d).wpKraus (c.decode TTContinuation.resultCode)))
      (KrausFamily.residualRefines_of_semEq
        (KrausFamily.applySemEq_symm
          (FiniteInstrumentComp.wpKraus_bind_semEq
            (dyadicStage (m + 1)) ξ
            (c.decode TTContinuation.resultCode)))))

/-- Each dyadic stage embeds below its successor. -/
theorem embed_dyadicStage_le_succ (m : ℕ) :
    embed (dyadicStage m) ≤ embed (dyadicStage (m + 1)) := by
  let injectOutcome : (dyadicStage m).Outcome →
      (dyadicStage (m + 1)).Outcome :=
    Fin.castSucc
  let retract : (dyadicStage (m + 1)).Outcome →
      (dyadicStage m).Outcome :=
    Fin.lastCases (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) id
  apply embed_le_of_outcome_retract
    (dyadicStage m) (dyadicStage (m + 1))
    injectOutcome retract
  · intro o
    exact Fin.lastCases_castSucc o
  · intro o
    rfl
  · intro q
    refine Fin.lastCases ?_ (fun i => ?_) q
    · simp only [retract, Fin.lastCases_last, dyadicStage]
      change dyadicPrefix 0 ⊆ dyadicPrefix (m + 1)
      intro x hx
      change x ≤ 0 at hx
      change x ≤ m + 1
      omega
    · simp only [retract, Fin.lastCases_castSucc, dyadicStage]
      change dyadicPrefix i ⊆ dyadicPrefix i
      exact le_rfl
  · exact dyadicStage_bind_finitaryTTRefines m

/-- The range of the concrete stage embeddings is directed. -/
theorem directedOn_range_embed_dyadicStage :
    DirectedOn (· ≤ ·) (Set.range fun m => embed (dyadicStage m)) := by
  rw [directedOn_range]
  intro i j
  refine ⟨max i j, ?_, ?_⟩
  · exact monotone_nat_of_le_succ
      embed_dyadicStage_le_succ (le_max_left i j)
  · exact monotone_nat_of_le_succ
      embed_dyadicStage_le_succ (le_max_right i j)

/-! ## Rational coordinate posts -/

/-- The coordinate predicate as a Scott-open output observation. -/
def coordinateOpen (j : ℕ) : OutputObservation (Set ℕ) where
  carrier := coordinateSet j
  isScottOpen := by
    constructor
    · intro A B hAB hj
      exact hAB hj
    · intro S hS _hdir hj
      change j ∈ ⋃₀ S at hj
      obtain ⟨A, hAS, hjA⟩ := Set.mem_sUnion.mp hj
      exact ⟨A, hAS, hjA⟩

/-- The natural-number code of coordinate Scott opens. -/
def coordinateCode : OutputCode ℕ (Set ℕ) :=
  ⟨coordinateOpen⟩

/-- The rational zero TNI Choi code. -/
noncomputable def rationalZero (n : ℕ) : RatTNICPMatrix n where
  cp := {
    matrix := 0
    posSemidef := by
      convert (Matrix.PosSemidef.zero :
        (0 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ).PosSemidef) using 1
      ext p q
      simp [RatChoiMatrix.toComplex] }
  trace_nonincreasing := by
    intro ρ hρ
    have hz :
        KrausFamily.SemEq
          (RatCPMatrix.realize {
            matrix := 0
            posSemidef := by
              convert (Matrix.PosSemidef.zero :
                (0 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ).PosSemidef) using 1
              ext p q
              simp [RatChoiMatrix.toComplex] })
          (KrausFamily.zero : KrausFamily n n) := by
      apply KrausFamily.semEq_of_choi_eq
      rw [RatCPMatrix.choi_realize]
      change
        (RatChoiMatrix.toComplex (0 : RatChoiMatrix n)) =
          (0 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
      ext p q
      simp [RatChoiMatrix.toComplex]
    rw [hz, KrausFamily.applyMat_zero, Matrix.trace_zero, Complex.zero_re]
    simpa [Matrix.trace] using
      (Finset.sum_nonneg fun (j : Fin n) (_ : j ∈ Finset.univ) =>
        (Complex.nonneg_iff.mp hρ.diag_nonneg).1)

@[simp]
theorem rationalZero_toComplex (n : ℕ) :
    (rationalZero n).toComplex = 0 := by
  ext p q
  simp [rationalZero, RatTNICPMatrix.toComplex, RatCPMatrix.toComplex,
    RatChoiMatrix.toComplex]

theorem rationalZero_realize_semEq_zero (n : ℕ) :
    KrausFamily.SemEq (rationalZero n).realize
      (KrausFamily.zero : KrausFamily n n) := by
  apply KrausFamily.semEq_of_choi_eq
  rw [RatTNICPMatrix.choi_realize, rationalZero_toComplex,
    show KrausFamily.choi
        (KrausFamily.zero : KrausFamily n n) = 0 by
      exact KrausFamily.choi_nil]

/-- The rational identity/zero post selected by membership in coordinate `j`. -/
noncomputable def coordinatePost (j : ℕ) : RatStepPostCode 1 where
  arity := 1
  opens := fun _ => j
  table := fun s =>
    if s 0 then RatTNICPMatrix.identity 1 else rationalZero 1
  table_mono := by
    intro s t hst
    cases hs : s 0 <;> cases ht : t 0
    · simp
    · simp
      rw [Matrix.le_iff]
      simpa using RatTNICPMatrix.toComplex_posSemidef
        (RatTNICPMatrix.identity 1)
    · have h := hst 0
      exfalso
      exact (by decide : ¬ (true ≤ false)) (by simpa [hs, ht] using h)
    · simp

/-- The operation selected by one coordinate membership bit. -/
noncomputable def coordinateTNI (j : ℕ) (A : Set ℕ) : RatTNICPMatrix 1 := by
  classical
  exact if j ∈ A then RatTNICPMatrix.identity 1 else rationalZero 1

theorem coordinatePost_decodedTNI (j : ℕ) (A : Set ℕ) :
    (coordinatePost j).decodedTNI coordinateCode A =
      coordinateTNI j A := by
  classical
  unfold RatStepPostCode.decodedTNI
  change
    (if (if j ∈ A then true else false) then
        RatTNICPMatrix.identity 1 else rationalZero 1) = _
  by_cases h : j ∈ A
  · simp [coordinateTNI, h]
  · simp [coordinateTNI, h]

theorem coordinatePost_decode_apply (j : ℕ) (A : Set ℕ) :
    (coordinatePost j).decode coordinateCode A =
      (coordinateTNI j A).realize := by
  change (coordinatePost j).decodedKraus coordinateCode A =
    (coordinateTNI j A).realize
  change
    ((coordinatePost j).decodedTNI coordinateCode A).realize =
      (coordinateTNI j A).realize
  rw [coordinatePost_decodedTNI]

/-- The finite result operation representing one coordinate indicator. -/
noncomputable def coordinateResult (j : ℕ) (A : Set ℕ) :
    FiniteInstrumentComp 1 PUnit.{1} :=
  codedResult coordinateCode (coordinatePost j) A

theorem coordinateResult_eq_of_mem_iff
    {j k : ℕ} {A : Set ℕ} (h : j ∈ A ↔ k ∈ A) :
    coordinateResult j A = coordinateResult k A := by
  unfold coordinateResult codedResult RatStepPostCode.decodedOperation
  rw [coordinatePost_decodedTNI, coordinatePost_decodedTNI]
  classical
  simp only [coordinateTNI]
  rw [if_congr h rfl rfl]

/-- Select a Kraus branch exactly when coordinate `j` is present. -/
noncomputable def coordinateSelected
    (j : ℕ) (A : Set ℕ) (K : KrausFamily 1 1) : KrausFamily 1 1 := by
  classical
  exact if j ∈ A then K else KrausFamily.zero

theorem coordinatePost_comp_semEq
    (j : ℕ) (A : Set ℕ) (K : KrausFamily 1 1) :
    KrausFamily.SemEq
      (KrausFamily.comp ((coordinatePost j).decode coordinateCode A) K)
      (coordinateSelected j A K) := by
  classical
  rw [coordinatePost_decode_apply]
  by_cases h : j ∈ A
  · simp only [coordinateTNI, coordinateSelected, h, ↓reduceIte]
    intro ρ
    rw [KrausFamily.applyMat_comp,
      RatTNICPMatrix.realize_identity_semEq,
      KrausFamily.applyMat_identity]
  · simp only [coordinateTNI, coordinateSelected, h, ↓reduceIte]
    intro ρ
    rw [KrausFamily.applyMat_comp,
      rationalZero_realize_semEq_zero,
      KrausFamily.applyMat_zero, KrausFamily.applyMat_zero]

theorem dyadicBranch_choi_entry (i : ℕ) :
    (KrausFamily.choi (dyadicBranch i)
      ((0, 0) : Fin 1 × Fin 1) ((0, 0) : Fin 1 × Fin 1)).re =
      dyadicWeight i := by
  rw [← KrausFamily.applyMat_matrixUnit (dyadicBranch i)
    ((0, 0) : Fin 1 × Fin 1) ((0, 0) : Fin 1 × Fin 1),
    dyadicBranch_applyMat]
  simp [KrausFamily.matrixUnit]

theorem dyadicStage_coordinateChoi_entry (m j : ℕ) :
    (KrausFamily.choi
      ((dyadicStage m).wpKraus
        ((coordinatePost j).decode coordinateCode))
      ((0, 0) : Fin 1 × Fin 1) ((0, 0) : Fin 1 × Fin 1)).re =
      ∑ i : Fin (m + 1),
        if j ≤ i then dyadicWeight i else 0 := by
  rw [choi_wpKraus_eq_sum]
  rw [Matrix.sum_apply]
  change Complex.reCLM _ = _
  rw [map_sum]
  simp only [dyadicStage]
  apply Fintype.sum_congr
  intro i
  have hsem := coordinatePost_comp_semEq j (dyadicPrefix i)
    (dyadicBranch i)
  have hchoi := KrausFamily.choi_eq_of_semEq hsem
  by_cases hji : j ≤ i
  · have hmem : j ∈ dyadicPrefix i := hji
    simp only [coordinateSelected, hmem, ↓reduceIte] at hchoi
    rw [hchoi, if_pos hji]
    change
      (KrausFamily.choi (dyadicBranch i)
        ((0, 0) : Fin 1 × Fin 1) ((0, 0) : Fin 1 × Fin 1)).re =
        dyadicWeight i
    exact dyadicBranch_choi_entry i
  · have hmem : j ∉ dyadicPrefix i := hji
    simp only [coordinateSelected, hmem, ↓reduceIte] at hchoi
    rw [hchoi, if_neg hji]
    change
      (KrausFamily.choi (KrausFamily.zero : KrausFamily 1 1)
        ((0, 0) : Fin 1 × Fin 1) ((0, 0) : Fin 1 × Fin 1)).re = 0
    rw [show KrausFamily.choi
        (KrausFamily.zero : KrausFamily 1 1) = 0 by
      exact KrausFamily.choi_nil]
    rfl

theorem sum_dyadicCoordinate (m j : ℕ) :
    (∑ i : Fin (m + 1),
      if j ≤ i then dyadicWeight i else 0) =
      if j ≤ m then
        (1 / 2 : ℝ) ^ j - (1 / 2 : ℝ) ^ (m + 1)
      else 0 := by
  induction m with
  | zero =>
      by_cases hj : j = 0
      · subst j
        simp [dyadicWeight]
        norm_num
      · have hj0 : ¬ j ≤ 0 := by omega
        simp [hj0]
  | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ih]
      by_cases hjm : j ≤ m
      · have hjm' : j ≤ m + 1 := hjm.trans (Nat.le_succ m)
        simp only [hjm, hjm', ↓reduceIte, dyadicWeight]
        rw [pow_succ (1 / 2 : ℝ) (m + 1)]
        ring
      · by_cases hj : j = m + 1
        · subst j
          have hnot : ¬ m + 1 ≤ m := by omega
          simp only [hnot, le_rfl, ↓reduceIte, dyadicWeight]
          rw [pow_succ (1 / 2 : ℝ) (m + 1)]
          ring
        · have hnot' : ¬ j ≤ m + 1 := by omega
          simp [hjm, hnot']

/-- The dyadic rational used as a strict coordinate threshold. -/
def dyadicThreshold (k : ℕ) : NonnegRat :=
  ⟨(1 / 2 : ℚ) ^ k, by positivity⟩

/-- A singleton result atom testing whether scalar Choi weight exceeds `2⁻ᵏ`. -/
noncomputable def dyadicProbe (k : ℕ) : TTObservationAtom 1 :=
  ⟨RatStepPostCode.identity 1,
    (RatChoiVec.single (finProdFinEquiv ((0, 0) : Fin 1 × Fin 1)),
      dyadicThreshold k)⟩

theorem dyadicProbe_holds_stage_iff (m j k : ℕ) :
    TTObservationAtom.Holds TTContinuation.resultCode (dyadicProbe k)
        ((dyadicStage m).bind (coordinateResult j)) ↔
      (1 / 2 : ℝ) ^ k <
        ∑ i : Fin (m + 1),
          if j ≤ i then dyadicWeight i else 0 := by
  have hsem :=
    (codedTestRepresentation coordinateCode (coordinatePost j)).wp_semEq
      (dyadicStage m)
  have hchoi := KrausFamily.choi_eq_of_semEq hsem
  have hchoi' :
      KrausFamily.choi
          (((dyadicStage m).bind (coordinateResult j)).wpKraus
            ((RatStepPostCode.identity 1).decode
              TTContinuation.resultCode)) =
        KrausFamily.choi
          ((dyadicStage m).wpKraus
            ((coordinatePost j).decode coordinateCode)) := by
    unfold coordinateResult
    simpa [codedTestRepresentation] using hchoi
  change
    ((dyadicThreshold k).1 : ℝ) <
      ChoiTest.eval
        (RatChoiVec.single (finProdFinEquiv ((0, 0) : Fin 1 × Fin 1)),
          dyadicThreshold k)
        (KrausFamily.choi
          (((dyadicStage m).bind (coordinateResult j)).wpKraus
            ((RatStepPostCode.identity 1).decode
              TTContinuation.resultCode))) ↔ _
  rw [hchoi']
  have heval :
      ChoiTest.eval
          (RatChoiVec.single (finProdFinEquiv ((0, 0) : Fin 1 × Fin 1)),
            dyadicThreshold k)
          (KrausFamily.choi
            ((dyadicStage m).wpKraus
              ((coordinatePost j).decode coordinateCode))) =
        (KrausFamily.choi
          ((dyadicStage m).wpKraus
            ((coordinatePost j).decode coordinateCode))
          ((0, 0) : Fin 1 × Fin 1) ((0, 0) : Fin 1 × Fin 1)).re := by
    change
      ChoiTest.eval
          (RatChoiVec.single (finProdFinEquiv ((0, 0) : Fin 1 × Fin 1)),
            ⟨0, le_rfl⟩)
          (KrausFamily.choi
            ((dyadicStage m).wpKraus
              ((coordinatePost j).decode coordinateCode))) = _
    exact ChoiTest.eval_single _ ((0, 0) : Fin 1 × Fin 1)
  rw [heval, dyadicStage_coordinateChoi_entry]
  norm_num [dyadicThreshold]

theorem dyadicProbe_holds_cross {j k : ℕ} (hjk : j < k) :
    TTObservationAtom.Holds TTContinuation.resultCode (dyadicProbe k)
      ((dyadicStage k).bind (coordinateResult j)) := by
  rw [dyadicProbe_holds_stage_iff, sum_dyadicCoordinate, if_pos hjk.le]
  have hpow :
      (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ (j + 1) := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Nat.succ_le_iff.mpr hjk)
  rw [pow_succ (1 / 2 : ℝ) j] at hpow
  rw [pow_succ (1 / 2 : ℝ) k]
  have hkpos : 0 < (1 / 2 : ℝ) ^ k := by positivity
  nlinarith

theorem dyadicProbe_not_holds_diagonal (m k : ℕ) :
    ¬ TTObservationAtom.Holds TTContinuation.resultCode (dyadicProbe k)
      ((dyadicStage m).bind (coordinateResult k)) := by
  rw [dyadicProbe_holds_stage_iff, sum_dyadicCoordinate]
  by_cases hkm : k ≤ m
  · simp only [hkm, ↓reduceIte]
    have hpos : 0 < (1 / 2 : ℝ) ^ (m + 1) := by positivity
    linarith
  · simp only [hkm, ↓reduceIte]
    exact not_lt_of_ge (by positivity)

/-- The represented result continuation selecting coordinate `j`. -/
noncomputable def coordinateContinuation (j : ℕ) :
    ScottMap (Set ℕ) (TTContinuation.TTResult 1) :=
  codedPost coordinateCode (coordinatePost j)

theorem embed_dyadicStage_coordinate (m j : ℕ) :
    embed (dyadicStage m) (coordinateContinuation j) =
      ((dyadicStage m).bind (coordinateResult j)).satisfiedTTTheory
        TTContinuation.resultCode := by
  apply embed_satisfied
  intro o
  exact codedPost_apply coordinateCode (coordinatePost j)
    ((dyadicStage m).value o)

theorem dyadicProbe_mem_cross {j k : ℕ} (hjk : j < k) :
    [dyadicProbe k] ∈
      embed (dyadicStage k) (coordinateContinuation j) := by
  rw [embed_dyadicStage_coordinate,
    FiniteInstrumentComp.mem_satisfiedTTTheory]
  intro a ha
  have ha' : a = dyadicProbe k := List.mem_singleton.mp ha
  subst a
  exact dyadicProbe_holds_cross hjk

theorem dyadicProbe_not_mem_diagonal (m k : ℕ) :
    [dyadicProbe k] ∉
      embed (dyadicStage m) (coordinateContinuation k) := by
  rw [embed_dyadicStage_coordinate,
    FiniteInstrumentComp.mem_satisfiedTTTheory]
  intro h
  exact dyadicProbe_not_holds_diagonal m k
    (h (dyadicProbe k) (by simp))

/-- The directed supremum of the finite dyadic prefix embeddings. -/
noncomputable def dyadicLimit :
    TTContinuation.TTContinuationPower 1 (Set ℕ) :=
  sSup (Set.range fun m => embed (dyadicStage m))

theorem dyadicProbe_mem_limit_cross {j k : ℕ} (hjk : j < k) :
    [dyadicProbe k] ∈ dyadicLimit (coordinateContinuation j) := by
  have hstage :
      embed (dyadicStage k) ≤ dyadicLimit := by
    exact le_sSup ⟨k, rfl⟩
  exact hstage (coordinateContinuation j) (dyadicProbe_mem_cross hjk)

theorem dyadicProbe_not_mem_limit_diagonal (k : ℕ) :
    [dyadicProbe k] ∉ dyadicLimit (coordinateContinuation k) := by
  intro h
  change [dyadicProbe k] ∈
    (sSup (Set.range fun m => embed (dyadicStage m)))
      (coordinateContinuation k) at h
  rw [ScottMap.sSup_apply, RoundedTheory.mem_sSup] at h
  obtain ⟨T, ⟨q, ⟨m, rfl⟩, rfl⟩, hT⟩ := h
  exact dyadicProbe_not_mem_diagonal m k hT

theorem exists_coordinate_collision
    (μ : FiniteInstrumentComp 1 (Set ℕ)) :
    ∃ j k, j < k ∧
      ∀ o : μ.Outcome, (j ∈ μ.value o ↔ k ∈ μ.value o) := by
  classical
  let selected : ℕ → Finset μ.Outcome :=
    fun j => Finset.univ.filter fun o => j ∈ μ.value o
  have hnot : ¬ Function.Injective selected := by
    intro hinj
    exact Set.infinite_range_of_injective hinj
      (Set.toFinite (Set.range selected))
  obtain ⟨j, k, heq, hne⟩ :=
    Function.not_injective_iff.mp hnot
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · refine ⟨j, k, hjk, ?_⟩
    intro o
    have hmem := Finset.ext_iff.mp heq o
    simpa [selected] using hmem
  · refine ⟨k, j, hkj, ?_⟩
    intro o
    have hmem := Finset.ext_iff.mp heq.symm o
    simpa [selected] using hmem

/-- The directed dyadic limit is not represented by any finite instrument. -/
theorem dyadicLimit_not_mem_range :
    dyadicLimit ∉
      Set.range (embed (n := 1) (D := Set ℕ)) := by
  rintro ⟨μ, hμ⟩
  obtain ⟨j, k, hjk, hcollision⟩ :=
    exists_coordinate_collision μ
  have hbind :
      (μ.bind (coordinateResult j)).satisfiedTTTheory
          TTContinuation.resultCode =
        (μ.bind (coordinateResult k)).satisfiedTTTheory
          TTContinuation.resultCode := by
    apply TTTokenTheory.bindPresented_eq_of_values
    intro o
    exact coordinateResult_eq_of_mem_iff (hcollision o)
  have hembed :
      embed μ (coordinateContinuation j) =
        embed μ (coordinateContinuation k) := by
    calc
      embed μ (coordinateContinuation j) =
          (μ.bind (coordinateResult j)).satisfiedTTTheory
            TTContinuation.resultCode := by
        apply embed_satisfied
        intro o
        exact codedPost_apply coordinateCode (coordinatePost j) (μ.value o)
      _ = (μ.bind (coordinateResult k)).satisfiedTTTheory
            TTContinuation.resultCode := hbind
      _ = embed μ (coordinateContinuation k) := by
        symm
        apply embed_satisfied
        intro o
        exact codedPost_apply coordinateCode (coordinatePost k) (μ.value o)
  have hlimit :
      dyadicLimit (coordinateContinuation j) =
        dyadicLimit (coordinateContinuation k) := by
    calc
      dyadicLimit (coordinateContinuation j) =
          embed μ (coordinateContinuation j) :=
        congrArg (fun q => q (coordinateContinuation j)) hμ.symm
      _ = embed μ (coordinateContinuation k) := hembed
      _ = dyadicLimit (coordinateContinuation k) :=
        congrArg (fun q => q (coordinateContinuation k)) hμ
  have hmem := dyadicProbe_mem_limit_cross hjk
  rw [hlimit] at hmem
  exact dyadicProbe_not_mem_limit_diagonal k hmem

/-- The concrete finite-image range is directed but its supremum leaves the
finite physical image. -/
theorem range_embed_dyadicStage_directed_nonclosed :
    DirectedOn (· ≤ ·) (Set.range fun m => embed (dyadicStage m)) ∧
      sSup (Set.range fun m => embed (dyadicStage m)) ∉
        Set.range (embed (n := 1) (D := Set ℕ)) := by
  exact ⟨directedOn_range_embed_dyadicStage, dyadicLimit_not_mem_range⟩

/-- Unconditional failure of a Scott retraction onto the finite physical
image, witnessed by the one-dimensional dyadic prefix chain. -/
theorem no_finiteImageScottRetraction_dyadic :
    FiniteImageScottRetraction 1 (Set ℕ) → False := by
  apply no_finiteImageScottRetraction_of_directedSup_not_finite
    (S := Set.range fun m => embed (dyadicStage m))
  · exact Set.range_nonempty _
  · exact directedOn_range_embed_dyadicStage
  · rintro q ⟨m, rfl⟩
    exact ⟨dyadicStage m, rfl⟩
  · exact dyadicLimit_not_mem_range

/-- Coordinate Choi observations of a finite instrument have finite range. -/
theorem finite_coordinateChoi_range
    (μ : FiniteInstrumentComp n (Set ℕ)) :
    (Set.range fun j => μ.testChoi (coordinateSet j)).Finite := by
  classical
  let selected : ℕ → Finset μ.Outcome :=
    fun j => Finset.univ.filter fun o => j ∈ μ.value o
  let choiSum : Finset μ.Outcome →
      Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
    fun s => ∑ o ∈ s, KrausFamily.choi (μ.branch o)
  have hfactor (j : ℕ) :
      μ.testChoi (coordinateSet j) = choiSum (selected j) := by
    simp only [FiniteInstrumentComp.testChoi, coordinateSet, Set.mem_ofPred_eq,
      selected, choiSum, Finset.sum_filter]
    rfl
  apply Set.Finite.subset (Set.finite_range choiSum)
  rintro M ⟨j, rfl⟩
  exact ⟨selected j, (hfactor j).symm⟩

/-- An ambient coordinate observation which agrees with branch selection on
every finite physical embedding. -/
structure CoordinateObservation (n : ℕ) where
  observe :
    TTContinuation.TTContinuationPower n (Set ℕ) → ℕ →
      Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ
  observe_embed :
    ∀ (μ : FiniteInstrumentComp n (Set ℕ)) (j : ℕ),
      observe (embed μ) j = μ.testChoi (coordinateSet j)

/-- Injectively many recovered coordinate matrices exclude finite
representability. -/
theorem not_mem_finiteImage_of_coordinate_injective
    (O : CoordinateObservation n)
    (q : TTContinuation.TTContinuationPower n (Set ℕ))
    (hinj : Function.Injective (O.observe q)) :
    q ∉ Set.range (embed (n := n) (D := Set ℕ)) := by
  rintro ⟨μ, rfl⟩
  have hfinite :
      (Set.range fun j => O.observe (embed μ) j).Finite := by
    simpa only [O.observe_embed] using finite_coordinateChoi_range μ
  exact Set.infinite_range_of_injective hinj hfinite

/-- A directed family of finite embeddings with injective coordinate
observations at its supremum rules out a finite-image Scott retraction. -/
theorem no_finiteImageScottRetraction_of_coordinate_witness
    (O : CoordinateObservation n)
    (stage : ℕ → FiniteInstrumentComp n (Set ℕ))
    (hdir : DirectedOn (· ≤ ·) (Set.range fun k => embed (stage k)))
    (hinj : Function.Injective
      (O.observe (sSup (Set.range fun k => embed (stage k))))) :
    FiniteImageScottRetraction n (Set ℕ) → False := by
  apply no_finiteImageScottRetraction_of_directedSup_not_finite
    (S := Set.range fun k => embed (stage k))
  · exact Set.range_nonempty _
  · exact hdir
  · rintro q ⟨k, rfl⟩
    exact ⟨stage k, rfl⟩
  · exact not_mem_finiteImage_of_coordinate_injective O _ hinj

end TTPhysicalEmbedding

end QLambda
