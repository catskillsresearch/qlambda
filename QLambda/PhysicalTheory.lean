/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.RoundedTheory

/-!
# Physical instruments as rounded token theories

Finite instruments determine theories of all strict coded observations
they satisfy.  Rational density supplies the strict rounding witness.
-/

namespace QLambda

open Scott1972.ContinuousLattice

universe u v

namespace FiniteInstrumentComp.KrausPost

variable {n : ℕ} {D : Type u} [CompleteLattice D]

/-- The quantum indicator of a Scott-open output observation. -/
noncomputable def indicator (U : OutputObservation D) : KrausPost n D := by
  classical
  exact
    { pred := fun d =>
        if d ∈ U then KrausFamily.identity n else KrausFamily.zero
      mono := by
        intro d e hde
        by_cases hd : d ∈ U
        · have he : e ∈ U := U.isScottOpen.1 hde hd
          simp [hd, he, KrausFamily.residualRefines_refl]
        · by_cases he : e ∈ U
          · simp only [hd, he, ↓reduceIte]
            refine ⟨KrausFamily.identity n, ?_⟩
            intro ρ
            simp [KrausFamily.zero]
          · simp [hd, he, KrausFamily.residualRefines_refl] }

end FiniteInstrumentComp.KrausPost

namespace CodedAtom

variable {n : ℕ} {ι : Type v} {D : Type u} [CompleteLattice D]

/-- Every satisfied strict rational atom has a strictly stronger
rational threshold which is still satisfied. -/
theorem exists_stronglyBelow_holds (C : OutputCode ι D)
    (μ : FiniteInstrumentComp n D) {a : CodedAtom n ι}
    (ha : Holds C a μ) :
    ∃ b, StronglyBelow a b ∧ Holds C b μ := by
  have hlt :
      (a.1.2.1 : ℝ) <
        a.1.eval (μ.observationChoi (C.observe a.2)) := by
    exact ha
  obtain ⟨q, haq, hqeval⟩ := exists_rat_btwn hlt
  have hq0 : 0 ≤ q := by
    have ha0 : (0 : ℝ) ≤ (a.1.2.1 : ℝ) := by
      exact_mod_cast a.1.2.2
    have hq0r : (0 : ℝ) ≤ (q : ℝ) := ha0.trans haq.le
    exact_mod_cast hq0r
  let b : CodedAtom n ι := ((a.1.1, ⟨q, hq0⟩), a.2)
  refine ⟨b, ?_, ?_⟩
  · exact ⟨rfl, rfl, by
      dsimp [b]
      exact_mod_cast haq⟩
  · change (q : ℝ) <
      a.1.eval (μ.observationChoi (C.observe a.2))
    exact hqeval

end CodedAtom

namespace CodedToken

variable {n : ℕ} {ι : Type v} {D : Type u} [CompleteLattice D]

/-- Strictly strengthen all conjuncts of a satisfied finite token. -/
theorem exists_stronglyBelow_holds (C : OutputCode ι D)
    (μ : FiniteInstrumentComp n D) {t : CodedToken n ι}
    (ht : Holds C t μ) :
    ∃ s, StronglyBelow t s ∧ Holds C s μ := by
  induction t with
  | nil =>
      exact ⟨[], by simp [StronglyBelow], by
        rw [holds_iff]
        simp⟩
  | cons a t ih =>
      have htc : ∀ x ∈ a :: t, CodedAtom.Holds C x μ :=
        (holds_iff C (a :: t) μ).mp ht
      have ha : CodedAtom.Holds C a μ := by
        exact htc a (by simp)
      have ht' : Holds C t μ := by
        rw [holds_iff]
        intro x hx
        exact htc x (by simp [hx])
      obtain ⟨b, hab, hb⟩ := CodedAtom.exists_stronglyBelow_holds C μ ha
      obtain ⟨s, hts, hs⟩ := ih ht'
      refine ⟨b :: s, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨b, by simp, hab⟩
        · obtain ⟨y, hy, hxy⟩ := hts x hx
          exact ⟨y, by simp [hy], hxy⟩
      · rw [holds_iff]
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hb
        · rw [holds_iff] at hs
          exact hs y hy

end CodedToken

namespace FiniteInstrumentComp

variable {n : ℕ} {D : Type u} [CompleteLattice D]
variable {ι : Type v}

/-- The weakest precondition against a Scott-open indicator has exactly
the Choi denotation selected by that observation. -/
theorem choi_wpKraus_indicator (μ : FiniteInstrumentComp n D)
    (U : OutputObservation D) :
    KrausFamily.choi (μ.wpKraus (KrausPost.indicator U)) =
      μ.observationChoi U := by
  classical
  rw [observationChoi_eq_testChoi]
  unfold wpKraus testChoi KrausPost.indicator
  rw [choi_flatMap]
  rw [← List.sum_toFinset
    (fun o : μ.Outcome =>
      KrausFamily.choi
        (KrausFamily.comp
          (if μ.value o ∈ U then KrausFamily.identity n else KrausFamily.zero)
          (μ.branch o)))
    (Finset.nodup_toList Finset.univ)]
  have huniv : (Finset.univ.toList.toFinset : Finset μ.Outcome) =
      Finset.univ := by
    ext o
    simp
  rw [huniv]
  apply Finset.sum_congr rfl
  intro o ho
  by_cases hU : μ.value o ∈ U
  · simp [hU]
  · simp [hU, KrausFamily.zero, KrausFamily.comp]

/-- TT refinement implies pointwise Choi observational refinement. -/
theorem observationRefines_of_refines {μ ν : FiniteInstrumentComp n D}
    (hμν : Refines μ ν) : ObservationRefines μ ν := by
  intro U
  have hwp := hμν (KrausPost.indicator U)
  have hchoi := KrausFamily.choiRefines_of_residualRefines hwp
  rw [KrausFamily.ChoiRefines, choi_wpKraus_indicator,
    choi_wpKraus_indicator] at hchoi
  exact hchoi

/-- The rounded theory of all coded strict observations satisfied by a
finite physical instrument. -/
def satisfiedTheory (C : OutputCode ι D) (μ : FiniteInstrumentComp n D) :
    TokenTheory n C where
  carrier := {t | CodedToken.Holds C t μ}
  rounded := by
    apply Set.Subset.antisymm
    · rintro t ⟨s, hs, hts⟩
      exact CodedToken.roundedBelow_entails C hts μ hs
    · intro t ht
      obtain ⟨s, hts, hs⟩ :=
        CodedToken.exists_stronglyBelow_holds C μ ht
      exact ⟨s, hs, ⟨t, CodedToken.entails_refl C t, hts⟩⟩

@[simp]
theorem mem_satisfiedTheory (C : OutputCode ι D)
    (μ : FiniteInstrumentComp n D) (t : CodedToken n ι) :
    t ∈ μ.satisfiedTheory C ↔ CodedToken.Holds C t μ :=
  Iff.rfl

/-- Pointwise Choi refinement preserves every coded strict token and
therefore induces inclusion of satisfied theories. -/
theorem observationRefines_satisfiedTheory_le
    (C : OutputCode ι D) {μ ν : FiniteInstrumentComp n D}
    (hμν : ObservationRefines μ ν) :
    μ.satisfiedTheory C ≤ ν.satisfiedTheory C := by
  intro t ht
  change CodedToken.Holds C t ν
  exact hμν.token_holds ht

/-- TT refinement therefore implies inclusion of every satisfied token
theory. -/
theorem satisfiedTheory_le_of_refines
    (C : OutputCode ι D) {μ ν : FiniteInstrumentComp n D}
    (hμν : Refines μ ν) :
    μ.satisfiedTheory C ≤ ν.satisfiedTheory C :=
  observationRefines_satisfiedTheory_le C
    (observationRefines_of_refines hμν)

/-- Inclusion of satisfied theories over the finite-union output basis
recovers pointwise Choi refinement. -/
theorem observationRefines_of_satisfiedTheory_le [IsOmegaQVA D]
    {μ ν : FiniteInstrumentComp n D}
    (h :
      μ.satisfiedTheory
          (CountableOutputBasis.ofOmegaQVAFiniteUnion (D := D)).code ≤
        ν.satisfiedTheory
          (CountableOutputBasis.ofOmegaQVAFiniteUnion (D := D)).code) :
    ObservationRefines μ ν := by
  intro U
  obtain ⟨k, hkU, hμ, hν⟩ :=
    exists_pair_coded_observationChoi_eq μ ν U
  rw [← hμ, ← hν]
  let C := (CountableOutputBasis.ofOmegaQVAFiniteUnion (D := D)).code
  let V := C.observe k
  apply ChoiTest.le_of_rational_quadratic_le
    (μ.observationChoi_posSemidef V).1
    (ν.observationChoi_posSemidef V).1
  intro v
  by_contra hle
  have hlt :
      ChoiTest.eval (v, ⟨0, le_rfl⟩) (ν.observationChoi V) <
        ChoiTest.eval (v, ⟨0, le_rfl⟩) (μ.observationChoi V) :=
    lt_of_not_ge hle
  obtain ⟨q, hνq, hqμ⟩ := exists_rat_btwn hlt
  have hq0 : 0 ≤ q := by
    have hν0 :
        0 ≤ ChoiTest.eval (v, ⟨0, le_rfl⟩)
          (ν.observationChoi V) :=
      ChoiTest.eval_nonneg _ (ν.observationChoi_posSemidef V)
    have hq0r : (0 : ℝ) ≤ (q : ℝ) := hν0.trans hνq.le
    exact_mod_cast hq0r
  let a : CodedAtom n ℕ := ((v, ⟨q, hq0⟩), k)
  have hμa : CodedToken.Holds C [a] μ := by
    rw [CodedToken.holds_iff]
    intro b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact hqμ
  have hνa : CodedToken.Holds C [a] ν := by
    exact h hμa
  rw [CodedToken.holds_iff] at hνa
  have := hνa a (by simp)
  exact (not_lt_of_ge hνq.le) this

theorem satisfiedTheory_le_iff_observationRefines [IsOmegaQVA D]
    {μ ν : FiniteInstrumentComp n D} :
    μ.satisfiedTheory
          (CountableOutputBasis.ofOmegaQVAFiniteUnion (D := D)).code ≤
        ν.satisfiedTheory
          (CountableOutputBasis.ofOmegaQVAFiniteUnion (D := D)).code ↔
      ObservationRefines μ ν := by
  constructor
  · exact observationRefines_of_satisfiedTheory_le
  · intro h
    exact observationRefines_satisfiedTheory_le _ h

/-- Equality in the physical embedding is exactly mutual pointwise Choi
refinement. -/
theorem satisfiedTheory_eq_iff_observationEquivalent [IsOmegaQVA D]
    {μ ν : FiniteInstrumentComp n D} :
    μ.satisfiedTheory
          (CountableOutputBasis.ofOmegaQVAFiniteUnion (D := D)).code =
        ν.satisfiedTheory
          (CountableOutputBasis.ofOmegaQVAFiniteUnion (D := D)).code ↔
      ObservationRefines μ ν ∧ ObservationRefines ν μ := by
  constructor
  · intro h
    constructor
    · apply observationRefines_of_satisfiedTheory_le
      exact h.le
    · apply observationRefines_of_satisfiedTheory_le
      exact h.ge
  · rintro ⟨hμν, hνμ⟩
    apply le_antisymm
    · exact observationRefines_satisfiedTheory_le _ hμν
    · exact observationRefines_satisfiedTheory_le _ hνμ

end FiniteInstrumentComp

end QLambda
