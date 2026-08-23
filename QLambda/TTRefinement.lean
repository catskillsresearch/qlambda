/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.TTObservationBasis

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QLambda

open Scott1972.ContinuousLattice

universe u

namespace FiniteInstrumentComp

variable {n : ℕ} {D : Type u} [CompleteLattice D]

/-- Refinement tested by all finite rational step postconditions. -/
def FinitaryTTRefines (C : OutputCode ℕ D)
    (μ ν : FiniteInstrumentComp n D) : Prop :=
  ∀ c : RatStepPostCode n,
    KrausFamily.Refines (μ.wpKraus (c.decode C)) (ν.wpKraus (c.decode C))

theorem finitaryTTRefines_refl (C : OutputCode ℕ D)
    (μ : FiniteInstrumentComp n D) :
    FinitaryTTRefines C μ μ :=
  fun _ => KrausFamily.residualRefines_refl _

theorem finitaryTTRefines_trans (C : OutputCode ℕ D)
    {μ ν ξ : FiniteInstrumentComp n D}
    (hμν : FinitaryTTRefines C μ ν)
    (hνξ : FinitaryTTRefines C ν ξ) :
    FinitaryTTRefines C μ ξ :=
  fun c => KrausFamily.residualRefines_trans (hμν c) (hνξ c)

instance instIsPreorderFinitaryTTRefines (C : OutputCode ℕ D) :
    IsPreorder (FiniteInstrumentComp n D) (FinitaryTTRefines C) where
  refl := finitaryTTRefines_refl C
  trans _ _ _ := finitaryTTRefines_trans C

/-- Full monotone-postcondition TT refinement implies its rational
finite-step restriction. -/
theorem finitaryTTRefines_of_refines (C : OutputCode ℕ D)
    {μ ν : FiniteInstrumentComp n D} (hμν : Refines μ ν) :
    FinitaryTTRefines C μ ν :=
  fun c => hμν (c.decode C)

/-- Residual and Choi formulations of finitary TT refinement coincide. -/
theorem finitaryTTRefines_iff_choi (C : OutputCode ℕ D)
    {μ ν : FiniteInstrumentComp n D} :
    FinitaryTTRefines C μ ν ↔
      ∀ c : RatStepPostCode n,
        KrausFamily.choi (μ.wpKraus (c.decode C)) ≤
          KrausFamily.choi (ν.wpKraus (c.decode C)) := by
  constructor
  · intro h c
    exact KrausFamily.choiRefines_of_residualRefines (h c)
  · intro h c
    exact KrausFamily.residualRefines_of_choiRefines (h c)

/-- Finitary TT refinement is exactly preservation of every strict
rational quadratic atom. -/
theorem finitaryTTRefines_iff_atom_holds (C : OutputCode ℕ D)
    {μ ν : FiniteInstrumentComp n D} :
    FinitaryTTRefines C μ ν ↔
      ∀ a : TTObservationAtom n, a.Holds C μ → a.Holds C ν := by
  constructor
  · intro h a ha
    apply ha.trans_le
    exact a.choi.eval_mono
      (KrausFamily.choiRefines_of_residualRefines (h a.post))
  · intro h
    rw [finitaryTTRefines_iff_choi]
    intro c
    apply ChoiTest.le_of_rational_quadratic_le
      (KrausFamily.choi_posSemidef _).1
      (KrausFamily.choi_posSemidef _).1
    intro v
    by_contra hle
    have hlt :
        ChoiTest.eval (v, ⟨0, le_rfl⟩)
            (KrausFamily.choi (ν.wpKraus (c.decode C))) <
          ChoiTest.eval (v, ⟨0, le_rfl⟩)
            (KrausFamily.choi (μ.wpKraus (c.decode C))) :=
      lt_of_not_ge hle
    obtain ⟨q, hνq, hqμ⟩ := exists_rat_btwn hlt
    have hq0 : 0 ≤ q := by
      have hν0 :
          0 ≤ ChoiTest.eval (v, ⟨0, le_rfl⟩)
            (KrausFamily.choi (ν.wpKraus (c.decode C))) :=
        ChoiTest.eval_nonneg _ (KrausFamily.choi_posSemidef _)
      have hq0r : (0 : ℝ) ≤ (q : ℝ) := hν0.trans hνq.le
      exact_mod_cast hq0r
    let a : TTObservationAtom n := ⟨c, (v, ⟨q, hq0⟩)⟩
    have hμa : a.Holds C μ := by
      exact hqμ
    have hνa : a.Holds C ν := h a hμa
    exact (not_lt_of_ge hνq.le) hνa

/-- Finite conjunctions add no separating power beyond singleton atoms. -/
theorem finitaryTTRefines_iff_token_holds (C : OutputCode ℕ D)
    {μ ν : FiniteInstrumentComp n D} :
    FinitaryTTRefines C μ ν ↔
      ∀ t : TTObservationToken n, t.Holds C μ → t.Holds C ν := by
  rw [finitaryTTRefines_iff_atom_holds]
  constructor
  · intro h t ht a ha
    exact h a (ht a ha)
  · intro h a ha
    have hs : TTObservationToken.Holds C [a] μ := by
      intro b hb
      have hba : b = a := List.mem_singleton.mp hb
      subst b
      exact ha
    have ht := h [a] hs
    exact ht a (by simp)

end FiniteInstrumentComp

namespace RatStepPostCode

variable {n : ℕ} {D : Type u} [CompleteLattice D]

/-- Every finite signature at a directed supremum is already attained
at one member of the directed set. -/
theorem exists_signature_eq_of_directed
    (C : OutputCode ℕ D) (c : RatStepPostCode n)
    {S : Set D} (hS : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S) :
    ∃ d ∈ S, c.signature C d = c.signature C (sSup S) := by
  classical
  have hfinite :
      ∀ I : Finset (Fin c.arity),
        ∃ d ∈ S, ∀ i ∈ I,
          c.signature C d i = c.signature C (sSup S) i := by
    intro I
    induction I using Finset.induction_on with
    | empty =>
        obtain ⟨d, hd⟩ := hS
        exact ⟨d, hd, by simp⟩
    | @insert i I hi ih =>
        obtain ⟨d, hdS, hd⟩ := ih
        by_cases hsup : sSup S ∈ C.observe (c.opens i)
        · obtain ⟨e, heS, he⟩ :=
            (C.observe (c.opens i)).isScottOpen.2 hS hdir hsup
          obtain ⟨z, hzS, hdz, hez⟩ := hdir d hdS e heS
          refine ⟨z, hzS, ?_⟩
          intro j hj
          rw [Finset.mem_insert] at hj
          rcases hj with hji | hj
          · have hsupj : sSup S ∈ C.observe (c.opens j) := by
              simpa [hji] using hsup
            have hej : e ∈ C.observe (c.opens j) := by
              simpa [hji] using he
            have hzj := (C.observe (c.opens j)).isScottOpen.1 hez hej
            have hzj' : z ∈ C.observe (c.opens j) := by
              change z ∈ (C.observe (c.opens j)).carrier
              exact hzj
            simp [signature, hsupj, hzj']
          · have hdj := hd j hj
            unfold signature at hdj ⊢
            by_cases hsupj : sSup S ∈ C.observe (c.opens j)
            · have hdmem : d ∈ C.observe (c.opens j) := by
                simpa [hsupj] using hdj
              have hzmem :=
                (C.observe (c.opens j)).isScottOpen.1 hdz hdmem
              have hzmem' : z ∈ C.observe (c.opens j) := by
                change z ∈ (C.observe (c.opens j)).carrier
                exact hzmem
              simp [hsupj, hzmem']
            · have hzmem : z ∉ C.observe (c.opens j) := by
                intro hz
                exact hsupj ((C.observe (c.opens j)).isScottOpen.1
                  (le_sSup hzS) hz)
              simp [hsupj, hzmem]
        · refine ⟨d, hdS, ?_⟩
          intro j hj
          rw [Finset.mem_insert] at hj
          rcases hj with hji | hj
          · have hsupj : sSup S ∉ C.observe (c.opens j) := by
              simpa [hji] using hsup
            have hdnot : d ∉ C.observe (c.opens j) := by
              intro hdmem
              exact hsupj ((C.observe (c.opens j)).isScottOpen.1
                (le_sSup hdS) hdmem)
            simp [signature, hsupj, hdnot]
          · exact hd j hj
  obtain ⟨d, hdS, hd⟩ := hfinite Finset.univ
  refine ⟨d, hdS, funext fun i => ?_⟩
  exact hd i (Finset.mem_univ i)

end RatStepPostCode

end QLambda
