/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.SuperoperatorInstances

/-!
# Finite retained-output instruments (presheaf)

Named `SuperoperatorInstrument` on disk to avoid clashing with
`CompletedCP.Instrument`.  The Lean name remains `Instrument`.
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

/-- A finite retained-output instrument.  Branches are intrinsic CP maps;
the total outcome weight is trace-nonincreasing. -/
structure Instrument (n m outcomes : ℕ) where
  branch : Fin outcomes → CPMap n m
  trace_nonincreasing :
    ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (∑ i, (Matrix.trace ((branch i).applyMat ρ)).re) ≤
        (Matrix.trace ρ).re

namespace Instrument

variable {n m outcomes : ℕ}

/-- Convert an existing finite Kraus instrument without changing any branch
meaning. -/
def ofQuantumInstrument (Φ : QuantumInstrument n m outcomes) :
    Instrument n m outcomes where
  branch i := CPMap.ofKraus (Φ.branch i)
  trace_nonincreasing := by
    intro ρ hρ
    simpa using Φ.trace_nonincreasing ρ hρ

@[simp]
theorem branch_ofQuantumInstrument (Φ : QuantumInstrument n m outcomes)
    (i : Fin outcomes) :
    (ofQuantumInstrument Φ).branch i = CPMap.ofKraus (Φ.branch i) :=
  rfl

private theorem trace_re_nonneg (Φ : CPMap n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosSemidef) :
    0 ≤ (Matrix.trace (Φ.applyMat ρ)).re := by
  have h :=
    PosSemidef.trace_nonneg (CPMap.applyMat_posSemidef Φ hρ)
  exact (RCLike.nonneg_iff (K := ℂ).mp h).1

/-- Every branch of a finite TNI instrument is itself a superoperator. -/
noncomputable def branchSuperoperator (Φ : Instrument n m outcomes)
    (i : Fin outcomes) : Superoperator n m where
  cp := Φ.branch i
  trace_nonincreasing := by
    intro ρ hρ
    calc
      (Matrix.trace ((Φ.branch i).applyMat ρ)).re
          ≤ ∑ j, (Matrix.trace ((Φ.branch j).applyMat ρ)).re := by
            exact Finset.single_le_sum
              (fun j _ => trace_re_nonneg (Φ.branch j) ρ hρ)
              (Finset.mem_univ i)
      _ ≤ (Matrix.trace ρ).re := Φ.trace_nonincreasing ρ hρ

/-- Computational-basis measurement retaining the quantum register. -/
noncomputable def measure {q : ℕ} (w : Fin q) :
    Instrument (CQ.QDim q) (CQ.QDim q) 2 :=
  ofQuantumInstrument (Composer.measure w)

@[simp]
theorem measure_branch_zero {q : ℕ} (w : Fin q) :
    (measure w).branch 0 =
      CPMap.ofKraus [Composer.projector w false] :=
  rfl

@[simp]
theorem measure_branch_one {q : ℕ} (w : Fin q) :
    (measure w).branch 1 =
      CPMap.ofKraus [Composer.projector w true] :=
  rfl

end Instrument

end QLambda.Domain.Presheaf
