/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.HardwareAdequacy

/-!
# Counterexample to state-independent hardware tree completeness

The operational machine suppresses measurement outcomes having zero Born
weight on its concrete state.  Such an outcome need not be the zero quantum
channel.  Consequently the old positive-only `EvaluationTree` cannot provide
state-independent channel completeness.  The sound repair is implemented in
`HardwareChannelSemantics`: the executable machine stays normalized, while a
proof-only subnormalized semantics executes both branches.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QLambda
namespace HardwareCompletenessCounterexample

open HardwareOperational
open HardwareObservation
open TTPhysicalPrimitives

/-- The normalized computational basis state `|0⟩⟨0|`. -/
def ketZeroDensity : NormalizedDensity 2 where
  mat := Qubit.proj0
  posSemidef := by
    have h :=
      KrausFamily.applyMat_posSemidef ([Qubit.proj0] : KrausFamily 2 2)
        (Matrix.PosSemidef.one :
          (1 : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef)
    rw [KrausFamily.applyMat_single, Matrix.mul_one,
      Qubit.proj0_conjTranspose, Qubit.proj0_mul_self] at h
    exact h
  trace_eq_one := by
    simp [Matrix.trace, Qubit.proj0]

/-- On `|0⟩`, the `true` measurement outcome has zero Born weight. -/
theorem measure_true_ketZero_eq_zero {C : Type}
    (s : Config C) (hs : s.quantum = ketZeroDensity) :
    measureProbability s true = 0 := by
  rw [measureProbability, hs]
  simp [NormalizedDensity.bornWeight, measureBranch,
    Qubit.measureZComp, ketZeroDensity, KrausFamily.applyMat_single,
    Qubit.proj1_conjTranspose, Matrix.trace, Qubit.proj0, Qubit.proj1,
    Matrix.mul_apply]

/-- On `|0⟩`, the `false` measurement outcome has unit Born weight. -/
theorem measure_false_ketZero_eq_one {C : Type}
    (s : Config C) (hs : s.quantum = ketZeroDensity) :
    measureProbability s false = 1 := by
  rw [← measureProbability_false_add_true s,
    measure_true_ketZero_eq_zero s hs]
  ring

/-- The omitted `true` projector is not the zero channel, even after the
identity prefix. -/
theorem true_measurement_identity_not_zero :
    ¬ KrausFamily.SemEq
      (KrausFamily.comp (measureBranch true) (KrausFamily.identity 2))
      KrausFamily.zero := by
  intro h
  have hz := h Qubit.proj1
  rw [KrausFamily.applyMat_comp, KrausFamily.applyMat_identity,
    KrausFamily.applyMat_zero] at hz
  change
    KrausFamily.applyMat ([Qubit.proj1] : KrausFamily 2 2) Qubit.proj1 = 0
    at hz
  rw [KrausFamily.applyMat_single, Qubit.proj1_conjTranspose,
    Qubit.proj1_mul_self, Qubit.proj1_mul_self] at hz
  have h11 := congrFun (congrFun hz (1 : Fin 2)) (1 : Fin 2)
  simp [Qubit.proj1] at h11

/-- Concrete counterexample to replacing a state-specific zero Born branch by
a globally zero channel.  This is precisely the extra implication required by
the one-child measurement constructors in `EvaluationTree`.

Consequently, completeness against state-independent TT channel observations
cannot use the old positive-only trees for all normalized initial states.
`HardwareChannelSemantics.ChannelTree` repairs exactly this mismatch by
executing every branch over subnormalized, possibly-zero states. -/
theorem zero_Born_weight_does_not_imply_zero_channel :
    ∃ (C : Type) (s : Config C) (b : Bool),
      measureProbability s b = 0 ∧
      ¬ KrausFamily.SemEq
        (KrausFamily.comp (measureBranch b) (KrausFamily.identity 2))
        KrausFamily.zero := by
  let s : Config Unit :=
    initialConfig (.prim (.ret ())) ketZeroDensity
  refine ⟨Unit, s, true, ?_, true_measurement_identity_not_zero⟩
  exact measure_true_ketZero_eq_zero s rfl

end HardwareCompletenessCounterexample
end QLambda
