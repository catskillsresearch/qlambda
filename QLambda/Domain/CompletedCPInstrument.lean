/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.CPPresentation

/-!
# Completed-CP instruments
-/

namespace QLambda.Domain

open scoped BigOperators ComplexConjugate MatrixOrder

namespace CompletedCP

/-- Instrument with branches valued in presentation-independent CP maps. -/
structure Instrument (n m outcomes : ℕ) where
  branch : Fin outcomes → CompletedCP n m

namespace Instrument

noncomputable def ofQuantumInstrument
    {outcomes : ℕ} (Φ : QuantumInstrument n m outcomes) :
    Instrument n m outcomes where
  branch o := ofKraus (Φ.branch o)

end Instrument

noncomputable def measure {q : ℕ} (w : Fin q) :
    Instrument (CQ.QDim q) (CQ.QDim q) 2 :=
  Instrument.ofQuantumInstrument (Composer.measure w)

theorem measure_probability_normalization {q : ℕ} (w : Fin q)
    (ρ : Matrix (Fin (CQ.QDim q)) (Fin (CQ.QDim q)) ℂ) :
    (∑ i : Fin 2,
      Matrix.trace
        (KrausFamily.applyMat ((Composer.measure w).branch i) ρ)).re =
      (Matrix.trace ρ).re := by
  rw [Fin.sum_univ_two]
  have hne : (1 : Fin 2) ≠ 0 := by decide
  simp only [Composer.measure, hne, ↓reduceIte]
  rw [KrausFamily.applyMat_single, KrausFamily.applyMat_single]
  rw [Matrix.trace_mul_comm
      (Composer.projector w false * ρ)
      (Composer.projector w false).conjTranspose,
    Matrix.trace_mul_comm
      (Composer.projector w true * ρ)
      (Composer.projector w true).conjTranspose]
  rw [Composer.projector_conjTranspose, Composer.projector_conjTranspose,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Composer.projector_mul_self, Composer.projector_mul_self,
    ← Matrix.trace_add, ← Matrix.add_mul,
    Composer.projector_completeness, Matrix.one_mul]

noncomputable def reset {q : ℕ} (w : Fin q) :
    CompletedCP (CQ.QDim q) (CQ.QDim q) :=
  ofKraus (Composer.reset w).kraus

end CompletedCP

end QLambda.Domain
