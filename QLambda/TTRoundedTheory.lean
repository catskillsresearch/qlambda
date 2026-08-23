/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.RoundedTheoryOmega
import QLambda.TTRefinement

open Set

namespace QLambda

open Scott1972.ContinuousLattice

universe u

namespace TTObservationAtom

variable {n : ℕ}

/-- Strict strengthening of a TT atom: the postcondition code and rational
vector are unchanged while the threshold strictly increases. -/
def StronglyBelow (a b : TTObservationAtom n) : Prop :=
  a.post = b.post ∧ a.choi.1 = b.choi.1 ∧ a.choi.2.1 < b.choi.2.1

theorem stronglyBelow_trans {a b c : TTObservationAtom n}
    (hab : StronglyBelow a b) (hbc : StronglyBelow b c) :
    StronglyBelow a c :=
  ⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1,
    hab.2.2.trans hbc.2.2⟩

theorem stronglyBelow_interpolate {a c : TTObservationAtom n}
    (hac : StronglyBelow a c) :
    ∃ b, StronglyBelow a b ∧ StronglyBelow b c := by
  let q : ℚ := (a.choi.2.1 + c.choi.2.1) / 2
  have hq0 : 0 ≤ q := by
    have ha0 := a.choi.2.2
    have hc0 := c.choi.2.2
    dsimp [q]
    linarith
  let b : TTObservationAtom n :=
    ⟨a.post, (a.choi.1, ⟨q, hq0⟩)⟩
  refine ⟨b, ?_, ?_⟩
  · exact ⟨rfl, rfl, by dsimp [b, q]; linarith [hac.2.2]⟩
  · exact ⟨hac.1, hac.2.1, by dsimp [b, q]; linarith [hac.2.2]⟩

theorem stronglyBelow_holds {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) {a b : TTObservationAtom n}
    (hab : StronglyBelow a b) {μ : FiniteInstrumentComp n D}
    (hb : Holds C b μ) : Holds C a μ := by
  apply holds_of_threshold_le C hab.1 hab.2.1
  · change (a.choi.2.1 : ℝ) ≤ (b.choi.2.1 : ℝ)
    exact_mod_cast hab.2.2.le
  · exact hb

end TTObservationAtom

namespace TTObservationToken

variable {n : ℕ}

/-- Pointwise strict strengthening of every TT conjunct. -/
def StronglyBelow (t s : TTObservationToken n) : Prop :=
  ∀ a ∈ t, ∃ b ∈ s, TTObservationAtom.StronglyBelow a b

theorem stronglyBelow_trans {t s r : TTObservationToken n}
    (hts : StronglyBelow t s) (hsr : StronglyBelow s r) :
    StronglyBelow t r := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := hts a ha
  obtain ⟨c, hc, hbc⟩ := hsr b hb
  exact ⟨c, hc, TTObservationAtom.stronglyBelow_trans hab hbc⟩

theorem stronglyBelow_interpolate {t r : TTObservationToken n}
    (htr : StronglyBelow t r) :
    ∃ s, StronglyBelow t s ∧ StronglyBelow s r := by
  induction t with
  | nil =>
      exact ⟨[], by simp [StronglyBelow], by simp [StronglyBelow]⟩
  | cons a t ih =>
      obtain ⟨c, hc, hac⟩ := htr a (by simp)
      obtain ⟨b, hab, hbc⟩ :=
        TTObservationAtom.stronglyBelow_interpolate hac
      have htr' : StronglyBelow t r := by
        intro x hx
        exact htr x (by simp [hx])
      obtain ⟨s, hts, hsr⟩ := ih htr'
      refine ⟨b :: s, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨b, by simp, hab⟩
        · obtain ⟨y, hy, hxy⟩ := hts x hx
          exact ⟨y, by simp [hy], hxy⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨c, hc, hbc⟩
        · exact hsr x hx

/-- Semantic entailment between TT observation tokens. -/
def Entails {D : Type u} [CompleteLattice D] (C : OutputCode ℕ D)
    (t s : TTObservationToken n) : Prop :=
  ∀ μ : FiniteInstrumentComp n D, Holds C s μ → Holds C t μ

theorem entails_refl {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) (t : TTObservationToken n) :
    Entails C t t :=
  fun _ h => h

theorem entails_trans {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) {t s r : TTObservationToken n}
    (hts : Entails C t s) (hsr : Entails C s r) :
    Entails C t r :=
  fun μ hr => hts μ (hsr μ hr)

theorem stronglyBelow_entails {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) {t s : TTObservationToken n}
    (hts : StronglyBelow t s) : Entails C t s := by
  intro μ hs a ha
  obtain ⟨b, hb, hab⟩ := hts a ha
  exact TTObservationAtom.stronglyBelow_holds C hab (hs b hb)

/-- Semantic weakening followed by strict rational strengthening. -/
def RoundedBelow {D : Type u} [CompleteLattice D] (C : OutputCode ℕ D)
    (t s : TTObservationToken n) : Prop :=
  ∃ u, Entails C t u ∧ StronglyBelow u s

theorem roundedBelow_entails {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) {t s : TTObservationToken n}
    (hts : RoundedBelow C t s) : Entails C t s := by
  obtain ⟨u, htu, hus⟩ := hts
  exact entails_trans C htu (stronglyBelow_entails C hus)

theorem roundedBelow_trans {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) {t s r : TTObservationToken n}
    (hts : RoundedBelow C t s) (hsr : RoundedBelow C s r) :
    RoundedBelow C t r := by
  obtain ⟨v, hsv, hvr⟩ := hsr
  exact ⟨v, entails_trans C (roundedBelow_entails C hts) hsv, hvr⟩

theorem roundedBelow_interpolate {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) {t r : TTObservationToken n}
    (htr : RoundedBelow C t r) :
    ∃ s, RoundedBelow C t s ∧ RoundedBelow C s r := by
  obtain ⟨u, htu, hur⟩ := htr
  obtain ⟨s, hus, hsr⟩ := stronglyBelow_interpolate hur
  refine ⟨s, ⟨u, htu, hus⟩, ?_⟩
  exact ⟨s, entails_refl C s, hsr⟩

/-- The interpolative basis of TT observation tokens. -/
def roundedBasis {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) : AbstractBasis (TTObservationToken n) where
  below := RoundedBelow C
  trans := roundedBelow_trans C
  interpolate := roundedBelow_interpolate C

end TTObservationToken

/-- The saturated rounded-theory completion of TT observation tokens. -/
abbrev TTTokenTheory (n : ℕ) {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) :=
  RoundedTheory.Carrier (TTObservationToken.roundedBasis (n := n) C)

/-- The TT token-theory completion is a continuous lattice. -/
theorem ttTokenTheory_isContinuousLattice
    (n : ℕ) {D : Type u} [CompleteLattice D] (C : OutputCode ℕ D) :
    IsContinuousLattice (TTTokenTheory n C) :=
  RoundedTheory.isContinuousLattice
    (TTObservationToken.roundedBasis (n := n) C)

/-- TT token theories form an `ωQVA`. -/
@[instance_reducible] noncomputable def ttTokenTheory_isOmegaQVA
    (n : ℕ) {D : Type u} [CompleteLattice D] (C : OutputCode ℕ D) :
    IsOmegaQVA (TTTokenTheory n C) :=
  RoundedTheory.isOmegaQVA
    (TTObservationToken.roundedBasis (n := n) C)

noncomputable instance TTTokenTheory.instIsOmegaQVA
    (n : ℕ) {D : Type u} [CompleteLattice D] (C : OutputCode ℕ D) :
    IsOmegaQVA (TTTokenTheory n C) :=
  ttTokenTheory_isOmegaQVA n C

namespace TTObservationAtom

variable {n : ℕ} {D : Type u} [CompleteLattice D]

/-- Every satisfied TT atom has a strict rational strengthening which is
still satisfied. -/
theorem exists_stronglyBelow_holds (C : OutputCode ℕ D)
    (μ : FiniteInstrumentComp n D) {a : TTObservationAtom n}
    (ha : Holds C a μ) :
    ∃ b, StronglyBelow a b ∧ Holds C b μ := by
  have hlt :
      (a.choi.threshold : ℝ) <
        a.choi.eval (KrausFamily.choi (μ.wpKraus (a.post.decode C))) :=
    ha
  obtain ⟨q, haq, hqeval⟩ := exists_rat_btwn hlt
  have hq0 : 0 ≤ q := by
    have ha0 : (0 : ℝ) ≤ (a.choi.2.1 : ℝ) := by
      exact_mod_cast a.choi.2.2
    have hq0r : (0 : ℝ) ≤ (q : ℝ) := ha0.trans haq.le
    exact_mod_cast hq0r
  let b : TTObservationAtom n :=
    ⟨a.post, (a.choi.1, ⟨q, hq0⟩)⟩
  refine ⟨b, ?_, ?_⟩
  · exact ⟨rfl, rfl, by
      dsimp [b]
      change (a.choi.2.1 : ℝ) < (q : ℝ) at haq
      have haqrat : a.choi.2.1 < q := by
        exact_mod_cast haq
      exact haqrat⟩
  · change (q : ℝ) <
      a.choi.eval (KrausFamily.choi (μ.wpKraus (a.post.decode C)))
    exact hqeval

end TTObservationAtom

namespace TTObservationToken

variable {n : ℕ} {D : Type u} [CompleteLattice D]

/-- Strictly strengthen every conjunct of a satisfied TT token. -/
theorem exists_stronglyBelow_holds (C : OutputCode ℕ D)
    (μ : FiniteInstrumentComp n D) {t : TTObservationToken n}
    (ht : Holds C t μ) :
    ∃ s, StronglyBelow t s ∧ Holds C s μ := by
  induction t with
  | nil =>
      exact ⟨[], by simp [StronglyBelow], nil_holds C μ⟩
  | cons a t ih =>
      have ha : a.Holds C μ := ht a (by simp)
      have ht' : Holds C t μ := by
        intro x hx
        exact ht x (by simp [hx])
      obtain ⟨b, hab, hb⟩ :=
        TTObservationAtom.exists_stronglyBelow_holds C μ ha
      obtain ⟨s, hts, hs⟩ := ih ht'
      refine ⟨b :: s, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨b, by simp, hab⟩
        · obtain ⟨y, hy, hxy⟩ := hts x hx
          exact ⟨y, by simp [hy], hxy⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hb
        · exact hs y hy

end TTObservationToken

namespace FiniteInstrumentComp

variable {n : ℕ} {D : Type u} [CompleteLattice D]

/-- The rounded theory of all TT observation tokens satisfied by a finite
instrument. -/
def satisfiedTTTheory (C : OutputCode ℕ D) (μ : FiniteInstrumentComp n D) :
    TTTokenTheory n C where
  carrier := {t | TTObservationToken.Holds C t μ}
  rounded := by
    apply Set.Subset.antisymm
    · rintro t ⟨s, hs, hts⟩
      exact TTObservationToken.roundedBelow_entails C hts μ hs
    · intro t ht
      obtain ⟨s, hts, hs⟩ :=
        TTObservationToken.exists_stronglyBelow_holds C μ ht
      exact ⟨s, hs, ⟨t, TTObservationToken.entails_refl C t, hts⟩⟩

@[simp]
theorem mem_satisfiedTTTheory (C : OutputCode ℕ D)
    (μ : FiniteInstrumentComp n D) (t : TTObservationToken n) :
    t ∈ μ.satisfiedTTTheory C ↔ TTObservationToken.Holds C t μ :=
  Iff.rfl

/-- Theory inclusion is exactly finitary TT refinement. -/
theorem satisfiedTTTheory_le_iff_finitaryTTRefines
    (C : OutputCode ℕ D) {μ ν : FiniteInstrumentComp n D} :
    μ.satisfiedTTTheory C ≤ ν.satisfiedTTTheory C ↔
      FinitaryTTRefines C μ ν := by
  rw [finitaryTTRefines_iff_token_holds]
  rfl

/-- Equality of satisfied TT theories is exactly mutual finitary TT
refinement. -/
theorem satisfiedTTTheory_eq_iff_mutual_finitaryTTRefines
    (C : OutputCode ℕ D) {μ ν : FiniteInstrumentComp n D} :
    μ.satisfiedTTTheory C = ν.satisfiedTTTheory C ↔
      FinitaryTTRefines C μ ν ∧ FinitaryTTRefines C ν μ := by
  constructor
  · intro h
    constructor
    · rw [← satisfiedTTTheory_le_iff_finitaryTTRefines C]
      exact h.le
    · rw [← satisfiedTTTheory_le_iff_finitaryTTRefines C]
      exact h.ge
  · rintro ⟨hμν, hνμ⟩
    apply le_antisymm
    · exact (satisfiedTTTheory_le_iff_finitaryTTRefines C).2 hμν
    · exact (satisfiedTTTheory_le_iff_finitaryTTRefines C).2 hνμ

end FiniteInstrumentComp

end QLambda
