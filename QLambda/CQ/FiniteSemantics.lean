/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.CQ.Basic

/-!
# Presentation-independent finite-instrument observations

This module provides only the finite weakest-postcondition equations
needed by Composer semantics.  It has no dependency on the discarded
instrument powerdomain, continuation monad, or ωQVA hierarchy.
-/

open Matrix
open scoped BigOperators

namespace QLambda.FiniteInstrumentComp

variable {n : ℕ} {D E : Type*}

/-- Aggregate a finite instrument against a Kraus-valued
postcondition. -/
noncomputable def wpKraus [Preorder D] (μ : FiniteInstrumentComp n D)
    (P : D → KrausFamily n n) : KrausFamily n n := by
  classical
  exact Finset.univ.toList.flatMap fun o =>
    KrausFamily.comp (P (μ.value o)) (μ.branch o)

theorem applyMat_wpKraus [Preorder D] (μ : FiniteInstrumentComp n D)
    (P : D → KrausFamily n n) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    KrausFamily.applyMat (μ.wpKraus P) ρ =
      ∑ o : μ.Outcome,
        KrausFamily.applyMat
          (KrausFamily.comp (P (μ.value o)) (μ.branch o)) ρ := by
  classical
  unfold wpKraus
  rw [KrausFamily.applyMat_flatMap]
  simp

theorem wpKraus_congr_of_outcome_equiv [Preorder D]
    (μ ν : FiniteInstrumentComp n D)
    (e : μ.Outcome ≃ ν.Outcome)
    (hbranch : ∀ o, ν.branch (e o) = μ.branch o)
    (hvalue : ∀ o, ν.value (e o) = μ.value o)
    (P : D → KrausFamily n n) :
    KrausFamily.SemEq (μ.wpKraus P) (ν.wpKraus P) := by
  intro ρ
  rw [applyMat_wpKraus, applyMat_wpKraus]
  refine Fintype.sum_equiv e
      (fun o => KrausFamily.applyMat
        (KrausFamily.comp (P (μ.value o)) (μ.branch o)) ρ)
      (fun q => KrausFamily.applyMat
        (KrausFamily.comp (P (ν.value q)) (ν.branch q)) ρ)
      ?_
  intro o
  rw [hbranch o, hvalue o]

theorem wpKraus_unit_semEq [Preorder D] (d : D)
    (P : D → KrausFamily n n) :
    KrausFamily.SemEq ((unit (n := n) d).wpKraus P) (P d) := by
  intro ρ
  rw [applyMat_wpKraus]
  change (∑ _ : Unit,
    KrausFamily.applyMat
      (KrausFamily.comp (P d) (KrausFamily.identity n)) ρ) =
    KrausFamily.applyMat (P d) ρ
  simp

theorem wpKraus_ofOperation_semEq [Preorder D]
    (Φ : QuantumOperation n n) (d : D)
    (P : D → KrausFamily n n) :
    KrausFamily.SemEq
      ((ofOperation Φ d).wpKraus P)
      (KrausFamily.comp (P d) Φ.kraus) := by
  intro ρ
  rw [applyMat_wpKraus]
  change
    (∑ _ : Unit,
      KrausFamily.applyMat
        (KrausFamily.comp (P d) Φ.kraus) ρ) =
      KrausFamily.applyMat
        (KrausFamily.comp (P d) Φ.kraus) ρ
  simp

theorem wpKraus_bind_semEq [Preorder D] [Preorder E]
    (μ : FiniteInstrumentComp n D) (f : D → FiniteInstrumentComp n E)
    (P : E → KrausFamily n n) :
    KrausFamily.SemEq ((μ.bind f).wpKraus P)
      (μ.wpKraus fun d => (f d).wpKraus P) := by
  intro ρ
  rw [applyMat_wpKraus, applyMat_wpKraus]
  change
    (∑ p : Σ o : μ.Outcome, (f (μ.value o)).Outcome,
      KrausFamily.applyMat
        (KrausFamily.comp
          (P ((f (μ.value p.1)).value p.2))
          (KrausFamily.comp
            ((f (μ.value p.1)).branch p.2)
            (μ.branch p.1))) ρ) =
      ∑ o : μ.Outcome,
        KrausFamily.applyMat
          (KrausFamily.comp ((f (μ.value o)).wpKraus P) (μ.branch o)) ρ
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro o _
  rw [KrausFamily.applyMat_comp, applyMat_wpKraus]
  simp only [KrausFamily.applyMat_comp]

theorem bind_wpKraus_congr_of_outcome_equiv [Preorder D] [Preorder E]
    (μ ν : FiniteInstrumentComp n D)
    (e : μ.Outcome ≃ ν.Outcome)
    (hbranch : ∀ o, ν.branch (e o) = μ.branch o)
    (hvalue : ∀ o, ν.value (e o) = μ.value o)
    (ξ : D → FiniteInstrumentComp n E)
    (P : E → KrausFamily n n) :
    KrausFamily.SemEq ((μ.bind ξ).wpKraus P) ((ν.bind ξ).wpKraus P) := by
  intro ρ
  calc
    KrausFamily.applyMat ((μ.bind ξ).wpKraus P) ρ =
        KrausFamily.applyMat (μ.wpKraus fun d => (ξ d).wpKraus P) ρ :=
      wpKraus_bind_semEq μ ξ P ρ
    _ = KrausFamily.applyMat (ν.wpKraus fun d => (ξ d).wpKraus P) ρ :=
      wpKraus_congr_of_outcome_equiv μ ν e hbranch hvalue
        (fun d => (ξ d).wpKraus P) ρ
    _ = KrausFamily.applyMat ((ν.bind ξ).wpKraus P) ρ :=
      (wpKraus_bind_semEq ν ξ P ρ).symm

theorem wpKraus_semEq_pred [Preorder D] (μ : FiniteInstrumentComp n D)
    {P Q : D → KrausFamily n n}
    (hPQ : ∀ d, KrausFamily.SemEq (P d) (Q d)) :
    KrausFamily.SemEq (μ.wpKraus P) (μ.wpKraus Q) := by
  intro ρ
  rw [applyMat_wpKraus, applyMat_wpKraus]
  apply Finset.sum_congr rfl
  intro o _
  simp only [KrausFamily.applyMat_comp]
  exact hPQ (μ.value o) (KrausFamily.applyMat (μ.branch o) ρ)

theorem wpKraus_map [Preorder D] [Preorder E]
    (f : D → E) (μ : FiniteInstrumentComp n D) (P : E → KrausFamily n n) :
    (μ.map f).wpKraus P = μ.wpKraus (P ∘ f) := by
  rfl

end QLambda.FiniteInstrumentComp
