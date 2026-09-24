/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.QuantumInstrument

/-!
# Finite instrument computations
-/

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace QLambda

/-- A finite `D`-valued computation on an `n`-dimensional register:
an instrument together with a classical outcome embedding into `D`.

This is a Type-level monad, not a complete lattice.  It therefore
cannot yet instantiate `IsQuantumPowerModel`. -/
structure FiniteInstrumentComp (n : ℕ) (D : Type*) where
  Outcome : Type
  [outcomeFintype : Fintype Outcome]
  branch : Outcome → KrausFamily n n
  value : Outcome → D
  trace_nonincreasing :
    ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (∑ o : Outcome, (Matrix.trace (KrausFamily.applyMat (branch o) ρ)).re) ≤
        (Matrix.trace ρ).re

attribute [instance] FiniteInstrumentComp.outcomeFintype

namespace FiniteInstrumentComp

variable {n : ℕ} {D E F : Type*}

/-- Outcome probability `Tr(Φ_o(ρ))`. -/
def outcomeProb (μ : FiniteInstrumentComp n D) (ρ : SubNormalizedDensity n)
    (o : μ.Outcome) : ℝ :=
  (Matrix.trace (KrausFamily.applyMat (μ.branch o) ρ.mat)).re

/-- Deterministic return of a classical value, leaving the register
untouched. -/
def unit (d : D) : FiniteInstrumentComp n D where
  Outcome := Unit
  branch := fun _ => KrausFamily.identity n
  value := fun _ => d
  trace_nonincreasing := by
    intro ρ _
    simp [KrausFamily.applyMat_identity]

/-- Post-compose classical outcomes. -/
def map (f : D → E) (μ : FiniteInstrumentComp n D) :
    FiniteInstrumentComp n E where
  Outcome := μ.Outcome
  outcomeFintype := μ.outcomeFintype
  branch := μ.branch
  value := f ∘ μ.value
  trace_nonincreasing := μ.trace_nonincreasing

@[simp] theorem map_id (μ : FiniteInstrumentComp n D) :
    map id μ = μ :=
  rfl

@[simp] theorem map_comp (g : E → F) (f : D → E) (μ : FiniteInstrumentComp n D) :
    map (g ∘ f) μ = map g (map f μ) :=
  rfl

/-- Kleisli extension: run `μ`, then the continuation at the returned
value.  Sequential composition of Kraus families implements the
quantum effect. -/
def bind (μ : FiniteInstrumentComp n D) (f : D → FiniteInstrumentComp n E) :
    FiniteInstrumentComp n E where
  Outcome := Σ o : μ.Outcome, (f (μ.value o)).Outcome
  outcomeFintype :=
    letI := μ.outcomeFintype
    letI : ∀ o : μ.Outcome, Fintype ((f (μ.value o)).Outcome) :=
      fun o => (f (μ.value o)).outcomeFintype
    inferInstance
  branch := fun p =>
    KrausFamily.comp ((f (μ.value p.1)).branch p.2) (μ.branch p.1)
  value := fun p => (f (μ.value p.1)).value p.2
  trace_nonincreasing := by
    intro ρ hρ
    let _ := μ.outcomeFintype
    let _ : ∀ o : μ.Outcome, Fintype ((f (μ.value o)).Outcome) :=
      fun o => (f (μ.value o)).outcomeFintype
    have hcont :
        ∀ o : μ.Outcome,
          (∑ o' : (f (μ.value o)).Outcome,
              (Matrix.trace
                (KrausFamily.applyMat
                  (KrausFamily.comp ((f (μ.value o)).branch o') (μ.branch o))
                  ρ)).re) ≤
            (Matrix.trace (KrausFamily.applyMat (μ.branch o) ρ)).re := by
      intro o
      have hpos := KrausFamily.applyMat_posSemidef (μ.branch o) hρ
      have hTNI := (f (μ.value o)).trace_nonincreasing
        (KrausFamily.applyMat (μ.branch o) ρ) hpos
      refine le_trans ?_ hTNI
      refine Finset.sum_le_sum ?_
      intro o' _
      rw [KrausFamily.applyMat_comp]
    calc
      (∑ p : (Σ o : μ.Outcome, (f (μ.value o)).Outcome),
          (Matrix.trace
            (KrausFamily.applyMat
              (KrausFamily.comp ((f (μ.value p.1)).branch p.2) (μ.branch p.1))
              ρ)).re)
          = ∑ o : μ.Outcome, ∑ o' : (f (μ.value o)).Outcome,
              (Matrix.trace
                (KrausFamily.applyMat
                  (KrausFamily.comp ((f (μ.value o)).branch o') (μ.branch o))
                  ρ)).re := by
            rw [Fintype.sum_sigma]
      _ ≤ ∑ o : μ.Outcome,
            (Matrix.trace (KrausFamily.applyMat (μ.branch o) ρ)).re :=
          Finset.sum_le_sum fun o _ => hcont o
      _ ≤ (Matrix.trace ρ).re :=
          μ.trace_nonincreasing ρ hρ

/-- Wrap a single quantum operation as a computation returning `d`. -/
def ofOperation (Φ : QuantumOperation n n) (d : D) :
    FiniteInstrumentComp n D where
  Outcome := Unit
  branch := fun _ => Φ.kraus
  value := fun _ => d
  trace_nonincreasing := by
    intro ρ hρ
    simpa using Φ.trace_nonincreasing ρ hρ

end FiniteInstrumentComp

end QLambda
