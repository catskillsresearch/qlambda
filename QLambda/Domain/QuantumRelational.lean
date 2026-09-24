/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Composer.MatrixSemantics
import QLambda.Domain.QuantumFunctionInstances
import QLambda.Domain.CompletedCP

/-!
# Quantum posets, functions, and circuit embedding

Barrel plus the finite Composer circuit embedding into quantum relations.
-/

open Matrix
open QLambda.Composer

namespace QLambda.Domain

/-- Square isometries over `ℂ` are unitaries. -/
theorem unitary_of_isometry {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (h : Uᴴ * U = 1) : U * Uᴴ = 1 :=
  (mul_eq_one_comm (a := Uᴴ) (b := U)).mp h

namespace CircuitEmbedding

/-- Hadamard as a quantum function on the discrete qubit. -/
noncomputable def h : QuantumRel .qubit .qubit :=
  QuantumRel.ofUnitary (hMatrix (0 : Fin 1))

/-- Pauli-X as a quantum function on the discrete qubit. -/
noncomputable def x : QuantumRel .qubit .qubit :=
  QuantumRel.ofUnitary (xMatrix (0 : Fin 1))

/-- T as a quantum function on the discrete qubit. -/
noncomputable def t : QuantumRel .qubit .qubit :=
  QuantumRel.ofUnitary (tMatrix (0 : Fin 1))

/-- Rational-angle `RY` as a quantum function on the discrete qubit. -/
noncomputable def ry (θ : ℚ) : QuantumRel .qubit .qubit :=
  QuantumRel.ofUnitary (ryMatrix (θ : ℝ) (0 : Fin 1))

/-- Saturated `CX` as a quantum function on a four-dimensional atom,
isomorphic to the two-qubit tensor. -/
noncomputable def cx : QuantumRel (.atomic 4) (.atomic 4) :=
  QuantumRel.ofUnitary (cxMatrix (0 : Fin 2) (1 : Fin 2))

/-- Computational-basis measurement, as a relation from the qubit to the
classical bit. -/
def measure : QuantumRel .qubit .bit :=
  QuantumRel.qubitMeasure

/-- Fresh `|0⟩` allocation.  This is an isometry-shaped relation, not a
Weaver function into the two-dimensional atom. -/
def new0 : QuantumRel .unit .qubit :=
  QuantumRel.new0

theorem h_isFunction : h.IsFunction :=
  QuantumRel.ofUnitary_isFunction _
    (hMatrix_isometry (0 : Fin 1))
    (unitary_of_isometry _ (hMatrix_isometry (0 : Fin 1)))

theorem x_isFunction : x.IsFunction :=
  QuantumRel.ofUnitary_isFunction _
    (xMatrix_isometry (0 : Fin 1))
    (unitary_of_isometry _ (xMatrix_isometry (0 : Fin 1)))

theorem t_isFunction : t.IsFunction :=
  QuantumRel.ofUnitary_isFunction _
    (tMatrix_isometry (0 : Fin 1))
    (unitary_of_isometry _ (tMatrix_isometry (0 : Fin 1)))

theorem ry_isFunction (θ : ℚ) : (ry θ).IsFunction :=
  QuantumRel.ofUnitary_isFunction _
    (ryMatrix_isometry (θ : ℝ) (0 : Fin 1))
    (unitary_of_isometry _ (ryMatrix_isometry (θ : ℝ) (0 : Fin 1)))

theorem cx_isFunction : cx.IsFunction :=
  QuantumRel.ofUnitary_isFunction _
    (cxMatrix_isometry (0 : Fin 2) (1 : Fin 2))
    (unitary_of_isometry _ (cxMatrix_isometry (0 : Fin 2) (1 : Fin 2)))

/-- Discrete-qubit Hadamard as a monotone quantum function. -/
noncomputable def hFun : QuantumFunction .qubit .qubit where
  rel := h
  isFunction := h_isFunction
  monotone := by
    change h.comp (QuantumRel.id .qubit) ≤ (QuantumRel.id .qubit).comp h
    rw [QuantumRel.comp_id, QuantumRel.id_comp]

noncomputable def xFun : QuantumFunction .qubit .qubit where
  rel := x
  isFunction := x_isFunction
  monotone := by
    change x.comp (QuantumRel.id .qubit) ≤ (QuantumRel.id .qubit).comp x
    rw [QuantumRel.comp_id, QuantumRel.id_comp]

noncomputable def tFun : QuantumFunction .qubit .qubit where
  rel := t
  isFunction := t_isFunction
  monotone := by
    change t.comp (QuantumRel.id .qubit) ≤ (QuantumRel.id .qubit).comp t
    rw [QuantumRel.comp_id, QuantumRel.id_comp]

end CircuitEmbedding

/-- The first-order CP presentation of a unitary quantum function is the
singleton Kraus family. -/
noncomputable def completedCP_ofUnitary {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) :
    CompletedCP n n :=
  CompletedCP.ofKraus [U]

@[simp] theorem completedCP_ofUnitary_h :
    completedCP_ofUnitary (hMatrix (0 : Fin 1)) = CompletedCP.h (0 : Fin 1) :=
  rfl

@[simp] theorem completedCP_ofUnitary_x :
    completedCP_ofUnitary (xMatrix (0 : Fin 1)) = CompletedCP.x (0 : Fin 1) :=
  rfl

@[simp] theorem completedCP_ofUnitary_t :
    completedCP_ofUnitary (tMatrix (0 : Fin 1)) = CompletedCP.t (0 : Fin 1) :=
  rfl

@[simp] theorem completedCP_ofUnitary_ry (θ : ℚ) :
    completedCP_ofUnitary (ryMatrix (θ : ℝ) (0 : Fin 1)) =
      CompletedCP.ry θ (0 : Fin 1) :=
  rfl

@[simp] theorem completedCP_ofUnitary_cx :
    completedCP_ofUnitary (cxMatrix (0 : Fin 2) (1 : Fin 2)) =
      CompletedCP.cx (0 : Fin 2) (1 : Fin 2) :=
  rfl


end QLambda.Domain
