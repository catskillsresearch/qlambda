import QLambda.TTContinuationMonad
import QLambda.TTRefinement

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace QLambda

namespace KrausFamily

variable {n m ℓ : ℕ}

theorem semEq_identity_comp (K : KrausFamily n m) :
    SemEq (comp (identity m) K) K := by
  rw [identity_comp]
  exact applySemEq_refl K

theorem semEq_comp_identity (K : KrausFamily n m) :
    SemEq (comp K (identity n)) K := by
  rw [comp_identity]
  exact applySemEq_refl K

theorem semEq_comp_append_left (L₁ L₂ : KrausFamily m ℓ)
    (K : KrausFamily n m) :
    SemEq (comp (L₁ ++ L₂) K) (comp L₁ K ++ comp L₂ K) := by
  rw [comp_append]
  exact applySemEq_refl _

theorem semEq_comp_append_right (L : KrausFamily m ℓ)
    (K₁ K₂ : KrausFamily n m) :
    SemEq (comp L (K₁ ++ K₂)) (comp L K₁ ++ comp L K₂) := by
  intro ρ
  simp only [applyMat_comp, applyMat_append]
  exact applyMat_add L _ _

theorem semEq_comp_assoc (M : KrausFamily ℓ r) (L : KrausFamily m ℓ)
    (K : KrausFamily n m) :
    SemEq (comp M (comp L K)) (comp (comp M L) K) := by
  rw [comp_assoc]
  exact applySemEq_refl _

end KrausFamily

namespace FiniteInstrumentComp

variable {n : ℕ}

noncomputable def totalKraus (μ : FiniteInstrumentComp n PUnit.{1}) :
    KrausFamily n n := by
  classical
  exact Finset.univ.toList.flatMap μ.branch

theorem applyMat_totalKraus (μ : FiniteInstrumentComp n PUnit.{1})
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    KrausFamily.applyMat μ.totalKraus ρ =
      ∑ o : μ.Outcome, KrausFamily.applyMat (μ.branch o) ρ := by
  classical
  unfold totalKraus
  rw [KrausFamily.applyMat_flatMap]
  simp

theorem choi_totalKraus (μ : FiniteInstrumentComp n PUnit.{1}) :
    KrausFamily.choi μ.totalKraus =
      ∑ o : μ.Outcome, KrausFamily.choi (μ.branch o) := by
  classical
  unfold totalKraus
  rw [FiniteInstrumentComp.choi_flatMap]
  simp

theorem totalKraus_trace_nonincreasing
    (μ : FiniteInstrumentComp n PUnit.{1})
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosSemidef) :
    (Matrix.trace (KrausFamily.applyMat μ.totalKraus ρ)).re ≤
      (Matrix.trace ρ).re := by
  rw [applyMat_totalKraus]
  simpa using μ.trace_nonincreasing ρ hρ

noncomputable def totalOperation (μ : FiniteInstrumentComp n PUnit.{1}) :
    QuantumOperation n n where
  kraus := μ.totalKraus
  trace_nonincreasing := μ.totalKraus_trace_nonincreasing

@[simp] theorem totalOperation_kraus
    (μ : FiniteInstrumentComp n PUnit.{1}) :
    μ.totalOperation.kraus = μ.totalKraus :=
  rfl

theorem applyMat_totalOperation (μ : FiniteInstrumentComp n PUnit.{1})
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    KrausFamily.applyMat μ.totalOperation.kraus ρ =
      ∑ o : μ.Outcome, KrausFamily.applyMat (μ.branch o) ρ :=
  μ.applyMat_totalKraus ρ

theorem choi_totalOperation (μ : FiniteInstrumentComp n PUnit.{1}) :
    KrausFamily.choi μ.totalOperation.kraus =
      ∑ o : μ.Outcome, KrausFamily.choi (μ.branch o) :=
  μ.choi_totalKraus

end FiniteInstrumentComp

namespace RatStepPostCode

variable {n : ℕ}

theorem signature_resultCode (c : RatStepPostCode n) (d : PUnit.{1}) :
    c.signature TTContinuation.resultCode d = fun _ => true := by
  classical
  funext i
  unfold signature
  have hd : d ∈ TTContinuation.resultCode.observe (c.opens i) := by
    change d ∈ (Set.univ : Set PUnit.{1})
    simp
  rw [if_pos hd]

theorem signature_resultCode_eq (c : RatStepPostCode n)
    (d e : PUnit.{1}) :
    c.signature TTContinuation.resultCode d =
      c.signature TTContinuation.resultCode e := by
  exact (signature_resultCode c d).trans (signature_resultCode c e).symm

noncomputable def resultMatrix (c : RatStepPostCode n) : RatCPMatrix n :=
  c.decodedMatrix TTContinuation.resultCode PUnit.unit

noncomputable def resultOperation (c : RatStepPostCode n) :
    QuantumOperation n n :=
  c.decodedOperation TTContinuation.resultCode PUnit.unit

theorem decodedMatrix_resultCode (c : RatStepPostCode n) (d : PUnit.{1}) :
    c.decodedMatrix TTContinuation.resultCode d = c.resultMatrix := by
  unfold resultMatrix decodedMatrix decodedTNI
  rw [signature_resultCode_eq c d PUnit.unit]

theorem decodedOperation_resultCode (c : RatStepPostCode n)
    (d : PUnit.{1}) :
    c.decodedOperation TTContinuation.resultCode d = c.resultOperation := by
  unfold resultOperation decodedOperation decodedTNI
  rw [signature_resultCode_eq c d PUnit.unit]

theorem decodedKraus_resultCode (c : RatStepPostCode n) (d : PUnit.{1}) :
    c.decodedKraus TTContinuation.resultCode d = c.resultOperation.kraus := by
  unfold decodedKraus
  rw [decodedOperation_resultCode]

end RatStepPostCode

namespace FiniteInstrumentComp

variable {n : ℕ}

private theorem applyMat_sum (K : KrausFamily n n)
    {α : Type*} [Fintype α]
    (f : α → Matrix (Fin n) (Fin n) ℂ) :
    KrausFamily.applyMat K (∑ a, f a) =
      ∑ a, KrausFamily.applyMat K (f a) := by
  classical
  induction (Finset.univ : Finset α) using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      induction K with
      | nil => simp
      | cons A K ih =>
          rw [KrausFamily.applyMat_cons, ih]
          simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, KrausFamily.applyMat_add, ih]

theorem wpKraus_result_semEq
    (μ : FiniteInstrumentComp n PUnit.{1}) (c : RatStepPostCode n) :
    KrausFamily.SemEq
      (μ.wpKraus (c.decode TTContinuation.resultCode))
      (KrausFamily.comp c.resultOperation.kraus μ.totalOperation.kraus) := by
  intro ρ
  rw [applyMat_wpKraus, KrausFamily.applyMat_comp,
    totalOperation_kraus, applyMat_totalKraus,
    applyMat_sum]
  apply Finset.sum_congr rfl
  intro o _
  rw [KrausFamily.applyMat_comp]
  change
    KrausFamily.applyMat
        (c.decodedKraus TTContinuation.resultCode (μ.value o))
        (KrausFamily.applyMat (μ.branch o) ρ) =
      KrausFamily.applyMat c.resultOperation.kraus
        (KrausFamily.applyMat (μ.branch o) ρ)
  rw [c.decodedKraus_resultCode (μ.value o)]

theorem wpKraus_result_trace_nonincreasing
    (μ : FiniteInstrumentComp n PUnit.{1}) (c : RatStepPostCode n)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosSemidef) :
    (Matrix.trace
      (KrausFamily.applyMat
        (μ.wpKraus (c.decode TTContinuation.resultCode)) ρ)).re ≤
      (Matrix.trace ρ).re := by
  rw [wpKraus_result_semEq μ c ρ]
  exact
    (QuantumOperation.comp c.resultOperation μ.totalOperation).trace_nonincreasing
      ρ hρ

noncomputable def wpResultOperation
    (μ : FiniteInstrumentComp n PUnit.{1}) (c : RatStepPostCode n) :
    QuantumOperation n n where
  kraus := μ.wpKraus (c.decode TTContinuation.resultCode)
  trace_nonincreasing := μ.wpKraus_result_trace_nonincreasing c

@[simp] theorem wpResultOperation_kraus
    (μ : FiniteInstrumentComp n PUnit.{1}) (c : RatStepPostCode n) :
    (μ.wpResultOperation c).kraus =
      μ.wpKraus (c.decode TTContinuation.resultCode) :=
  rfl

theorem wpResultOperation_semEq_comp
    (μ : FiniteInstrumentComp n PUnit.{1}) (c : RatStepPostCode n) :
    KrausFamily.SemEq (μ.wpResultOperation c).kraus
      (QuantumOperation.comp c.resultOperation μ.totalOperation).kraus :=
  μ.wpKraus_result_semEq c

end FiniteInstrumentComp

universe u

variable {n : ℕ} {D : Type u} [CompleteLattice D]

namespace FiniteInstrumentComp

theorem wpKraus_mono_pred_on_values
    (μ : FiniteInstrumentComp n D) (P : PUnit.{1} → KrausFamily n n)
    {ν₁ ν₂ : D → FiniteInstrumentComp n PUnit.{1}}
    (h : ∀ o : μ.Outcome,
      KrausFamily.Refines
        ((ν₁ (μ.value o)).wpKraus P) ((ν₂ (μ.value o)).wpKraus P)) :
    KrausFamily.Refines
      (μ.wpKraus fun d => (ν₁ d).wpKraus P)
      (μ.wpKraus fun d => (ν₂ d).wpKraus P) := by
  unfold wpKraus
  apply KrausFamily.residualRefines_flatMap
  intro o _
  exact KrausFamily.residualRefines_comp_right (μ.branch o) (h o)

theorem finitaryTTRefines_bind_result_values
    (μ : FiniteInstrumentComp n D)
    {ν₁ ν₂ : D → FiniteInstrumentComp n PUnit.{1}}
    (h : ∀ o : μ.Outcome,
      FinitaryTTRefines TTContinuation.resultCode
        (ν₁ (μ.value o)) (ν₂ (μ.value o))) :
    FinitaryTTRefines TTContinuation.resultCode (μ.bind ν₁) (μ.bind ν₂) := by
  letI : Preorder D := ChainCompletePartialOrder.instOfCompleteLattice.toPreorder
  letI : Preorder PUnit := ChainCompletePartialOrder.instOfCompleteLattice.toPreorder
  rw [finitaryTTRefines_iff_choi TTContinuation.resultCode]
  intro c
  let pred := (RatStepPostCode.decode TTContinuation.resultCode c).pred
  have hchoi₁ :=
    KrausFamily.choi_eq_of_semEq (wpKraus_bind_semEq μ ν₁ pred)
  have hchoi₂ :=
    KrausFamily.choi_eq_of_semEq (wpKraus_bind_semEq μ ν₂ pred)
  have hle :=
    KrausFamily.choiRefines_of_residualRefines <|
      wpKraus_mono_pred_on_values μ pred fun o =>
        KrausFamily.residualRefines_of_choiRefines
          ((finitaryTTRefines_iff_choi TTContinuation.resultCode).1 (h o) c)
  exact (le_of_eq hchoi₁).trans (hle.trans (le_of_eq hchoi₂.symm))

theorem bindPresented_eq_of_values
    (μ : FiniteInstrumentComp n D)
    {ν₁ ν₂ : D → FiniteInstrumentComp n PUnit.{1}}
    (h : ∀ o : μ.Outcome, ν₁ (μ.value o) = ν₂ (μ.value o)) :
    (μ.bind ν₁).satisfiedTTTheory TTContinuation.resultCode =
      (μ.bind ν₂).satisfiedTTTheory TTContinuation.resultCode := by
  apply (satisfiedTTTheory_eq_iff_mutual_finitaryTTRefines
    TTContinuation.resultCode).2
  constructor
  · exact finitaryTTRefines_bind_result_values μ fun o => by
      rw [h o]
      exact finitaryTTRefines_refl _ _
  · exact finitaryTTRefines_bind_result_values μ fun o => by
      rw [← h o]
      exact finitaryTTRefines_refl _ _

theorem satisfiedTTTheory_bind_mono_values
    (μ : FiniteInstrumentComp n D)
    {ν₁ ν₂ : D → FiniteInstrumentComp n PUnit.{1}}
    (h : ∀ o : μ.Outcome,
      (ν₁ (μ.value o)).satisfiedTTTheory TTContinuation.resultCode ≤
        (ν₂ (μ.value o)).satisfiedTTTheory TTContinuation.resultCode) :
    (μ.bind ν₁).satisfiedTTTheory TTContinuation.resultCode ≤
      (μ.bind ν₂).satisfiedTTTheory TTContinuation.resultCode :=
  (satisfiedTTTheory_le_iff_finitaryTTRefines
    TTContinuation.resultCode).2
    (finitaryTTRefines_bind_result_values μ fun o =>
      (satisfiedTTTheory_le_iff_finitaryTTRefines
        TTContinuation.resultCode).1 (h o))

end FiniteInstrumentComp

end QLambda
