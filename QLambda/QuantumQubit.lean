/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.FiniteInstrumentComp

/-!
# Qubit operations and computational-basis measurement
-/

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace QLambda

namespace Qubit

/-- Pauli-X on a qubit. -/
def pauliX : KrausOperator 2 2 :=
  fun i j => if i = j then 0 else 1

theorem pauliX_conjTranspose : pauliXᴴ = pauliX := by
  ext i j
  simp [pauliX, conjTranspose]
  fin_cases i <;> fin_cases j <;> simp

theorem pauliX_mul_self : pauliXᴴ * pauliX = 1 := by
  rw [pauliX_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply]

/-- Pauli-X as a quantum operation. -/
def pauliXOp : QuantumOperation 2 2 :=
  QuantumOperation.ofIsometry pauliX pauliX_mul_self

/-- Computational-basis projector `|0⟩⟨0|`. -/
def proj0 : KrausOperator 2 2 :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- Computational-basis projector `|1⟩⟨1|`. -/
def proj1 : KrausOperator 2 2 :=
  fun i j => if i = 1 ∧ j = 1 then 1 else 0

theorem proj0_mul_self : proj0 * proj0 = proj0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, Matrix.mul_apply]

theorem proj1_mul_self : proj1 * proj1 = proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj1, Matrix.mul_apply]

theorem proj0_conjTranspose : proj0ᴴ = proj0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, conjTranspose]

theorem proj1_conjTranspose : proj1ᴴ = proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj1, conjTranspose]

theorem proj0_add_proj1 : proj0 + proj1 = (1 : KrausOperator 2 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, proj1]

theorem trace_proj_apply (P : KrausOperator 2 2)
    (hP : P * P = P) (hHerm : Pᴴ = P)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (KrausFamily.applyMat [P] ρ) = Matrix.trace (P * ρ) := by
  rw [KrausFamily.applyMat_single, Matrix.trace_mul_comm (P * ρ) Pᴴ, hHerm,
    ← Matrix.mul_assoc, hP]

/-- Computational-basis measurement as a two-outcome instrument. -/
def measureZ : QuantumInstrument 2 2 2 where
  branch := fun i => if i = 0 then [proj0] else [proj1]
  trace_nonincreasing := by
    intro ρ _
    have h0 := trace_proj_apply proj0 proj0_mul_self proj0_conjTranspose ρ
    have h1 := trace_proj_apply proj1 proj1_mul_self proj1_conjTranspose ρ
    have hsum :
        Matrix.trace (proj0 * ρ) + Matrix.trace (proj1 * ρ) =
          Matrix.trace ρ := by
      rw [← Matrix.trace_add, ← Matrix.add_mul, proj0_add_proj1, Matrix.one_mul]
    rw [Fin.sum_univ_two]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ↓reduceIte]
    rw [h0, h1, ← Complex.add_re, hsum]

/-- Computational-basis measurement returning a boolean. -/
def measureZComp : FiniteInstrumentComp 2 Bool where
  Outcome := Bool
  branch := fun b => if b then [proj1] else [proj0]
  value := id
  trace_nonincreasing := by
    intro ρ _
    have h0 := trace_proj_apply proj0 proj0_mul_self proj0_conjTranspose ρ
    have h1 := trace_proj_apply proj1 proj1_mul_self proj1_conjTranspose ρ
    have hsum :
        Matrix.trace (proj0 * ρ) + Matrix.trace (proj1 * ρ) =
          Matrix.trace ρ := by
      rw [← Matrix.trace_add, ← Matrix.add_mul, proj0_add_proj1, Matrix.one_mul]
    rw [Fintype.sum_bool]
    change
      (KrausFamily.applyMat [proj1] ρ).trace.re +
        (KrausFamily.applyMat [proj0] ρ).trace.re ≤ _
    rw [h1, h0, ← Complex.add_re, add_comm, hsum]

end Qubit


end QLambda
