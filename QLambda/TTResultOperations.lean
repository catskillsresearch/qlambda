/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.TTContinuationMonad
import QLambda.TTResultAlgebra
import QLambda.TTResultApproximation
import QLambda.TTTokenTheoryOperations

open Set

namespace QLambda

open Scott1972.ContinuousLattice

universe u

namespace TTTokenTheory

variable {n : ℕ}

private def resultCode : OutputCode ℕ PUnit.{1} :=
  TTContinuation.resultCode

/-- Semantic token derivation for trace-nonincreasing Kraus precomposition on
the fixed result theory. -/
def PrecomposeDerives (Φ : QuantumOperation n n)
    (s t : TTObservationToken n) : Prop :=
  ∀ ν : FiniteInstrumentComp n PUnit.{1},
    TTObservationToken.Holds resultCode s ν →
    TTObservationToken.Holds resultCode t (ν.precomposeResult Φ)

/-- Scott-continuous TNI precomposition on the rounded result domain. -/
noncomputable def precomposeResultScott (Φ : QuantumOperation n n) :
    ScottMap (TTContinuation.TTResult n) (TTContinuation.TTResult n) :=
  mapOfDerivation resultCode resultCode (PrecomposeDerives Φ)

theorem mem_precomposeResultScott {Φ : QuantumOperation n n}
    {T : TTContinuation.TTResult n} {t : TTObservationToken n} :
    t ∈ precomposeResultScott Φ T ↔
      ∃ s ∈ T, ∃ u, PrecomposeDerives Φ s u ∧
        TTObservationToken.RoundedBelow resultCode t u := by
  dsimp [precomposeResultScott, mapOfDerivation, RoundedTheory.extendRelation]
  exact RoundedTheory.mem_extendRelation
    (B := TTObservationToken.roundedBasis (n := n) resultCode)
    (C := TTObservationToken.roundedBasis (n := n) resultCode)

theorem precomposeResultScott_mono (Φ : QuantumOperation n n) :
    Monotone (precomposeResultScott Φ) := by
  intro T T' hTT' t ht
  obtain ⟨s, hs, u, hst, htu⟩ := (mem_precomposeResultScott (Φ := Φ)).mp ht
  exact (mem_precomposeResultScott (Φ := Φ)).2
    ⟨s, hTT' hs, u, hst, htu⟩

theorem precomposeResultScott_satisfiedTTTheory
    (Φ : QuantumOperation n n) (ν : FiniteInstrumentComp n PUnit.{1}) :
    precomposeResultScott Φ (ν.satisfiedTTTheory resultCode) =
      (ν.precomposeResult Φ).satisfiedTTTheory resultCode := by
  apply RoundedTheory.ext
  ext t
  constructor
  · intro ht
    obtain ⟨s, hs, u, hst, htu⟩ := (mem_precomposeResultScott (Φ := Φ)).mp ht
    have hc :
        TTObservationToken.Holds resultCode u (ν.precomposeResult Φ) :=
      hst _ ((FiniteInstrumentComp.mem_satisfiedTTTheory resultCode ν s).mp hs)
    exact TTObservationToken.roundedBelow_entails resultCode htu
      (ν.precomposeResult Φ) hc
  · intro ht
    obtain ⟨u, htu, hu⟩ :=
      TTObservationToken.exists_stronglyBelow_holds resultCode
        (ν.precomposeResult Φ) ht
    obtain ⟨s, hs, hall⟩ :=
      TTResultApproximation.exists_precompose_source_token Φ u ν hu
    apply (mem_precomposeResultScott (Φ := Φ)).2
    refine ⟨s, (FiniteInstrumentComp.mem_satisfiedTTTheory resultCode ν s).2 hs,
      u, ?_, ?_⟩
    · intro ν' hs'
      exact hall ν' hs'
    · exact ⟨t, TTObservationToken.entails_refl resultCode t, htu⟩

variable {D : Type u} [CompleteLattice D]

/-- Continuations presented on the values returned by a finite instrument. -/
def PresentedOnValues (μ : FiniteInstrumentComp n D)
    (k : ScottMap D (TTContinuation.TTResult n)) : Type (max u 1) :=
  {ν : D → FiniteInstrumentComp n PUnit.{1} //
    ∀ o : μ.Outcome, (ν (μ.value o)).satisfiedTTTheory resultCode ≤ k (μ.value o)}

namespace PresentedOnValues

variable {μ : FiniteInstrumentComp n D}
variable {k : ScottMap D (TTContinuation.TTResult n)}

def mk (ν : D → FiniteInstrumentComp n PUnit.{1})
    (hν : ∀ o : μ.Outcome,
      (ν (μ.value o)).satisfiedTTTheory resultCode ≤ k (μ.value o)) :
    PresentedOnValues μ k :=
  ⟨ν, hν⟩

def val (ν : PresentedOnValues μ k) : D → FiniteInstrumentComp n PUnit.{1} :=
  ν.1

end PresentedOnValues

/-- Exact finite-instrument aggregation on the result theory. -/
noncomputable def bindPresented (μ : FiniteInstrumentComp n D)
    {k : ScottMap D (TTContinuation.TTResult n)}
    (ν : PresentedOnValues μ k) : TTContinuation.TTResult n :=
  (μ.bind ν.val).satisfiedTTTheory resultCode

theorem bindPresented_eq_of_values (μ : FiniteInstrumentComp n D)
    {ν₁ ν₂ : D → FiniteInstrumentComp n PUnit.{1}}
    (h : ∀ o : μ.Outcome, ν₁ (μ.value o) = ν₂ (μ.value o)) :
    (μ.bind ν₁).satisfiedTTTheory resultCode =
      (μ.bind ν₂).satisfiedTTTheory resultCode :=
  FiniteInstrumentComp.bindPresented_eq_of_values μ h

/-- Branch-local finite observations which semantically force a target
observation after binding the fixed instrument. -/
def AggregateDerives (μ : FiniteInstrumentComp n D)
    (sources : μ.Outcome → TTObservationToken n)
    (target : TTObservationToken n) : Prop :=
  ∀ ν : D → FiniteInstrumentComp n PUnit.{1},
    (∀ o, TTObservationToken.Holds resultCode
      (sources o) (ν (μ.value o))) →
    TTObservationToken.Holds resultCode target (μ.bind ν)

private def resultBasis (n : ℕ) :=
  TTObservationToken.roundedBasis (n := n) resultCode

/-- Rounded result theory generated by finite branch-local observations. -/
noncomputable def aggregateResult (μ : FiniteInstrumentComp n D)
    (k : ScottMap D (TTContinuation.TTResult n)) :
    TTContinuation.TTResult n :=
  sSup {T | ∃ sources target,
    (∀ o, sources o ∈ k (μ.value o)) ∧
    AggregateDerives μ sources target ∧
    T = RoundedTheory.principal (resultBasis n) target}

theorem mem_aggregateResult (μ : FiniteInstrumentComp n D)
    (k : ScottMap D (TTContinuation.TTResult n))
    (t : TTObservationToken n) :
    t ∈ aggregateResult μ k ↔
      ∃ sources, (∀ o, sources o ∈ k (μ.value o)) ∧
        ∃ target, AggregateDerives μ sources target ∧
          TTObservationToken.RoundedBelow resultCode t target := by
  rw [aggregateResult, RoundedTheory.mem_sSup]
  constructor
  · rintro ⟨T, ⟨sources, target, hsources, hderives, rfl⟩, ht⟩
    exact ⟨sources, hsources, target, hderives,
      (RoundedTheory.mem_principal (B := resultBasis n)).mp ht⟩
  · rintro ⟨sources, hsources, target, hderives, ht⟩
    exact ⟨RoundedTheory.principal (resultBasis n) target,
      ⟨sources, target, hsources, hderives, rfl⟩,
      (RoundedTheory.mem_principal (B := resultBasis n)).2 ht⟩

theorem aggregateResult_sSup (μ : FiniteInstrumentComp n D)
    {S : Set (ScottMap D (TTContinuation.TTResult n))}
    (hS : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S) :
    aggregateResult μ (sSup S) =
      sSup (aggregateResult μ '' S) := by
  classical
  apply RoundedTheory.ext
  ext t
  change t ∈ aggregateResult μ (sSup S) ↔
    t ∈ (sSup (aggregateResult μ '' S) : TTContinuation.TTResult n)
  rw [RoundedTheory.mem_sSup]
  constructor
  · intro ht
    obtain ⟨sources, hsources, target, hderives, httarget⟩ :=
      (mem_aggregateResult μ (sSup S) t).mp ht
    have hpoint (o : μ.Outcome) :
        ∃ i : S, sources o ∈
          (i.1 : ScottMap D (TTContinuation.TTResult n)) (μ.value o) := by
      have hs := hsources o
      rw [ScottMap.sSup_apply, RoundedTheory.mem_sSup] at hs
      obtain ⟨T, ⟨i, hi, rfl⟩, hsT⟩ := hs
      exact ⟨⟨i, hi⟩, hsT⟩
    obtain ⟨k₀, hk₀⟩ := hS
    have hfin :
        ∀ F : Finset μ.Outcome,
          ∃ i : S, ∀ o ∈ F, sources o ∈
            (i.1 : ScottMap D (TTContinuation.TTResult n)) (μ.value o) := by
      intro F
      induction F using Finset.induction_on with
      | empty =>
          exact ⟨⟨k₀, hk₀⟩, by simp⟩
      | @insert o F ho ih =>
          obtain ⟨⟨i, hi⟩, hsi⟩ := ih
          obtain ⟨⟨j, hj⟩, hsj⟩ := hpoint o
          obtain ⟨z, hz, hiz, hjz⟩ := hdir i hi j hj
          refine ⟨⟨z, hz⟩, ?_⟩
          intro o' ho'
          rw [Finset.mem_insert] at ho'
          rcases ho' with rfl | ho'
          · exact hjz (μ.value o') hsj
          · exact hiz (μ.value o') (hsi o' ho')
    obtain ⟨⟨i, hi⟩, hsi⟩ := hfin Finset.univ
    have ht_i : t ∈ aggregateResult μ i :=
      (mem_aggregateResult μ i t).2
        ⟨sources, fun o => hsi o (Finset.mem_univ o),
          target, hderives, httarget⟩
    exact ⟨aggregateResult μ i, ⟨i, hi, rfl⟩, ht_i⟩
  · rintro ⟨T, ⟨i, hi, rfl⟩, ht⟩
    obtain ⟨sources, hsources, target, hderives, httarget⟩ :=
      (mem_aggregateResult μ i t).mp ht
    apply (mem_aggregateResult μ (sSup S) t).2
    refine ⟨sources, ?_, target, hderives, httarget⟩
    intro o
    exact (le_sSup hi (μ.value o)) (hsources o)

/-- Scott-continuous finite-instrument aggregation on the rounded result
domain. -/
noncomputable def bindResultScott (μ : FiniteInstrumentComp n D) :
    ScottMap (ScottMap D (TTContinuation.TTResult n))
      (TTContinuation.TTResult n) :=
  ⟨aggregateResult μ, continuous_of_preservesDirectedSup fun _ hS hdir =>
    aggregateResult_sSup μ hS hdir⟩

@[simp]
theorem bindResultScott_apply (μ : FiniteInstrumentComp n D)
    (k : ScottMap D (TTContinuation.TTResult n)) :
    bindResultScott μ k = aggregateResult μ k :=
  rfl

theorem bindResultScott_satisfied
    (μ : FiniteInstrumentComp n D)
    (ν : D → FiniteInstrumentComp n PUnit.{1})
    (k : ScottMap D (TTContinuation.TTResult n))
    (hk : ∀ o : μ.Outcome,
      k (μ.value o) =
        (ν (μ.value o)).satisfiedTTTheory resultCode) :
    bindResultScott μ k =
      (μ.bind ν).satisfiedTTTheory resultCode := by
  apply RoundedTheory.ext
  ext t
  constructor
  · intro ht
    obtain ⟨sources, hsources, target, hderives, httarget⟩ :=
      (mem_aggregateResult μ k t).mp ht
    have htarget : TTObservationToken.Holds resultCode target (μ.bind ν) :=
      hderives ν fun o =>
        (FiniteInstrumentComp.mem_satisfiedTTTheory resultCode
          (ν (μ.value o)) (sources o)).mp
          (by rw [← hk o]; exact hsources o)
    exact TTObservationToken.roundedBelow_entails resultCode
      httarget (μ.bind ν) htarget
  · intro ht
    obtain ⟨target, httarget, htarget⟩ :=
      TTObservationToken.exists_stronglyBelow_holds
        resultCode (μ.bind ν) ht
    obtain ⟨sources, hsources, hderives⟩ :=
      TTResultApproximation.exists_bind_source_tokens μ target ν htarget
    apply (mem_aggregateResult μ k t).2
    refine ⟨sources, ?_, target, hderives, ?_⟩
    · intro o
      rw [hk o]
      exact (FiniteInstrumentComp.mem_satisfiedTTTheory resultCode
        (ν (μ.value o)) (sources o)).2 (hsources o)
    · exact ⟨t, TTObservationToken.entails_refl resultCode t, httarget⟩

end TTTokenTheory

end QLambda
