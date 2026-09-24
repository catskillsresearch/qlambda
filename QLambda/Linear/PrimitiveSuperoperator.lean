/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.DenotationInstances
import QLambda.Domain.Presheaf.SuperoperatorInstances
import QLambda.Domain.Presheaf.SuperoperatorInstrument

/-!
# Intrinsic superoperator meaning of source primitives

Each physical primitive already has a presentation-independent `CompletedCP`
class.  This file exhibits the matching intrinsic TNI superoperator and
proves that the two presentations agree.  Measurement is likewise the
existing two-branch instrument, rewritten as intrinsic Choi maps.
-/

namespace QLambda.Linear

open Domain
open Domain.Presheaf

namespace Prim

theorem ketZero_eq_allocZeroMatrix :
    ketZero = CompletedCP.allocZeroMatrix 0 := by
  ext i j
  simp [ketZero, CompletedCP.allocZeroMatrix]

noncomputable def superoperator (p : Prim) :
    Superoperator (CQ.QDim p.inputQ) (CQ.QDim p.outputQ) :=
  match p with
  | .new0 => Superoperator.allocateZero 0
  | .x => Superoperator.x (0 : Fin 1)
  | .h => Superoperator.h (0 : Fin 1)
  | .t => Superoperator.t (0 : Fin 1)
  | .ry θ => Superoperator.ry (θ : ℝ) (0 : Fin 1)
  | .cx => Superoperator.cx (0 : Fin 2) (1 : Fin 2)
  | .reset => Superoperator.reset (0 : Fin 1)

@[simp]
theorem superoperator_new0 :
    superoperator .new0 = Superoperator.allocateZero 0 :=
  rfl

@[simp]
theorem superoperator_x :
    superoperator .x = Superoperator.x (0 : Fin 1) :=
  rfl

@[simp]
theorem superoperator_h :
    superoperator .h = Superoperator.h (0 : Fin 1) :=
  rfl

@[simp]
theorem superoperator_t :
    superoperator .t = Superoperator.t (0 : Fin 1) :=
  rfl

@[simp]
theorem superoperator_ry (θ : ℚ) :
    superoperator (.ry θ) = Superoperator.ry (θ : ℝ) (0 : Fin 1) :=
  rfl

@[simp]
theorem superoperator_cx :
    superoperator .cx = Superoperator.cx (0 : Fin 2) (1 : Fin 2) :=
  rfl

@[simp]
theorem superoperator_reset :
    superoperator .reset = Superoperator.reset (0 : Fin 1) :=
  rfl

theorem cp_superoperator (p : Prim) :
    (superoperator p).cp = CPMap.ofKraus p.kraus := by
  cases p
  · rw [superoperator_new0, Superoperator.cp_allocateZero, kraus,
      ketZero_eq_allocZeroMatrix]; rfl
  · rw [superoperator_x]; rfl
  · rw [superoperator_h]; rfl
  · rw [superoperator_t]; rfl
  · rw [superoperator_ry]; rfl
  · rw [superoperator_cx]; rfl
  · rw [superoperator_reset, Superoperator.cp_reset]; rfl

/-- The intrinsic superoperator and the completed Kraus class of a primitive
are the same first-order CP map. -/
theorem superoperator_completedCP (p : Prim) :
    (superoperator p).cp.toCompleted = completedCP p := by
  rw [completedCP, cp_superoperator, CPMap.toCompleted_ofKraus]

end Prim

/-- Computational-basis measurement as an intrinsic two-branch instrument. -/
noncomputable def qubitInstrument :
    Instrument (CQ.QDim 1) (CQ.QDim 1) 2 :=
  Instrument.measure (0 : Fin 1)

theorem qubitInstrument_zero :
    qubitInstrument.branch 0 =
      CPMap.ofCompleted (qubitMeasurement.branch 0) := by
  rw [qubitInstrument, Instrument.measure_branch_zero,
    qubitMeasurement_zero, CPMap.ofCompleted_ofKraus]

theorem qubitInstrument_one :
    qubitInstrument.branch 1 =
      CPMap.ofCompleted (qubitMeasurement.branch 1) := by
  rw [qubitInstrument, Instrument.measure_branch_one,
    qubitMeasurement_one, CPMap.ofCompleted_ofKraus]

end QLambda.Linear
