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

end TTTokenTheory

end QLambda
