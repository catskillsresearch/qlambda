/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.CPMapInstances
import QLambda.Composer.MatrixSemantics

/-!
# Trace-nonincreasing intrinsic superoperators

The CP component is an intrinsic Choi matrix.  Trace non-increase is a
property of its action and therefore does not depend on a Kraus presentation.
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

/-- Trace non-increase for an intrinsic CP map. -/
def TraceNonincreasing {n m : ℕ} (Φ : CPMap n m) : Prop :=
  ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
    (Matrix.trace (Φ.applyMat ρ)).re ≤ (Matrix.trace ρ).re

/-- Intrinsic trace non-increase is exactly the input-effect bound.  Notice
that this bounds the output partial trace of the Choi matrix, not the whole
Choi matrix itself. -/
theorem traceNonincreasing_iff_effect_le_one {n m : ℕ} (Φ : CPMap n m) :
    TraceNonincreasing Φ ↔ Φ.effect ≤ 1 :=
  ⟨CPMap.effect_le_one_of_trace_nonincreasing Φ,
    CPMap.trace_nonincreasing_of_effect_le_one Φ⟩

/-- A finite-dimensional trace-nonincreasing completely positive map. -/
structure Superoperator (n m : ℕ) where
  cp : CPMap n m
  trace_nonincreasing : TraceNonincreasing cp

namespace Superoperator

variable {n m ℓ r : ℕ}

@[ext]
theorem ext {Φ Ψ : Superoperator n m} (h : Φ.cp = Ψ.cp) : Φ = Ψ := by
  cases Φ
  cases Ψ
  cases h
  rfl

/-- Build an intrinsic superoperator from a Kraus family and a proof about
its operator-sum action. -/
def ofKraus (K : KrausFamily n m)
    (hK : ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (KrausFamily.applyMat K ρ)).re ≤
        (Matrix.trace ρ).re) :
    Superoperator n m where
  cp := CPMap.ofKraus K
  trace_nonincreasing := by
    intro ρ hρ
    simpa using hK ρ hρ

/-- Forget a finite Kraus presentation while preserving its TNI proof. -/
def ofQuantumOperation (Φ : QuantumOperation n m) : Superoperator n m :=
  ofKraus Φ.kraus Φ.trace_nonincreasing

@[simp]
theorem cp_ofQuantumOperation (Φ : QuantumOperation n m) :
    (ofQuantumOperation Φ).cp = CPMap.ofKraus Φ.kraus :=
  rfl

/-- Recover an arbitrary finite Kraus presentation. -/
noncomputable def toQuantumOperation (Φ : Superoperator n m) :
    QuantumOperation n m where
  kraus := Φ.cp.toKraus
  trace_nonincreasing := Φ.trace_nonincreasing

@[simp]
theorem ofQuantumOperation_toQuantumOperation (Φ : Superoperator n m) :
    ofQuantumOperation (toQuantumOperation Φ) = Φ := by
  apply ext
  exact CPMap.ofKraus_toKraus Φ.cp

@[simp]
theorem cp_toQuantumOperation (Φ : Superoperator n m) :
    CPMap.ofKraus (toQuantumOperation Φ).kraus = Φ.cp :=
  CPMap.ofKraus_toKraus Φ.cp

/-- Identity superoperator. -/
def identity (n : ℕ) : Superoperator n n where
  cp := CPMap.identity n
  trace_nonincreasing := by
    intro ρ _
    rw [CPMap.applyMat_identity]

/-- Zero superoperator. -/
def zero : Superoperator n m where
  cp := 0
  trace_nonincreasing := by
    intro ρ hρ
    have htr : 0 ≤ Matrix.trace ρ := PosSemidef.trace_nonneg hρ
    rw [CPMap.applyMat_zero, Matrix.trace_zero, Complex.zero_re]
    exact (RCLike.nonneg_iff (K := ℂ).mp htr).1

end Superoperator

end QLambda.Domain.Presheaf
