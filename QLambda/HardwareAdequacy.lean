/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.HardwareLogicalRelation
import QLambda.ScottFixApproximation

/-!
# Hardware adequacy

This file gives unconditional finite bridges from hardware executions to
physical TT observations. Individual symbolic histories yield genuine
one-outcome operations, while branch-complete evaluation trees combine all
nonzero probability and measurement alternatives into one finite instrument.
Terminal values are realized through `HardwareLogicalRelation.ValueRel`.

The normalized-tree theorem below is retained as a conditional legacy
interface.  It is not inhabited for arbitrary normalized starts: a
zero-Born-weight branch need not be a globally zero channel.  The sound
state-independent replacement is
`HardwareChannelSemantics.ChannelTreeCompleteness`, based on proof-only
subnormalized trees which retain every branch.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QLambda
namespace HardwareAdequacy

open Scott1972.ContinuousLattice
open HardwareOperational
open HardwareObservation
open HardwareLogicalRelation
open TTPhysicalPrimitives
open TTPhysicalEmbedding
open TTContinuation

abbrev QubitQ := TTExternalContinuationPower 2

variable (D₀ : QDomain.{0})
variable (j₀ : IsContinuousLatticeProjection D₀.carrier
  (QuantumFunctor (QModel QubitQ) D₀.carrier))

abbrev HValue := HSemanticValue D₀ j₀
abbrev HComp := HSemanticComp D₀ j₀

/-! ## Symbolic histories are physical operations -/

/-- A source probability in the unit interval is a physical operation. -/
noncomputable def sourceProbabilityOperation (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : QuantumOperation 2 2 where
  kraus := QuantumAction.kraus (.sourceProbability p)
  trace_nonincreasing := by
    intro ρ hρ
    rw [QuantumAction.apply_sourceProbability p hp₀ ρ, Matrix.trace_smul]
    have htr : 0 ≤ (Matrix.trace ρ).re := by
      change 0 ≤ ∑ x : Fin 2, (ρ x x).re
      exact Finset.sum_nonneg fun x _ =>
        (Complex.nonneg_iff.mp hρ.diag_nonneg).1
    change ((p : ℂ) * Matrix.trace ρ).re ≤ (Matrix.trace ρ).re
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith

/-- Either branch of the projective measurement is trace-nonincreasing. -/
def measurementOperation (b : Bool) : QuantumOperation 2 2 where
  kraus := measureBranch b
  trace_nonincreasing := by
    intro ρ hρ
    have hsum := Qubit.measureZComp.trace_nonincreasing ρ hρ
    change
      (∑ b : Bool,
        (Matrix.trace
          (KrausFamily.applyMat (Qubit.measureZComp.branch b) ρ)).re) ≤
        (Matrix.trace ρ).re at hsum
    rw [Fintype.sum_bool] at hsum
    have hsum' :
      (Matrix.trace
          (KrausFamily.applyMat (Qubit.measureZComp.branch true) ρ)).re +
        (Matrix.trace
          (KrausFamily.applyMat (Qubit.measureZComp.branch false) ρ)).re ≤
        (Matrix.trace ρ).re := by
      exact hsum
    have hfalse : 0 ≤
        (Matrix.trace
          (KrausFamily.applyMat (Qubit.measureZComp.branch false) ρ)).re := by
      have hp := KrausFamily.applyMat_posSemidef
        (Qubit.measureZComp.branch false) hρ
      change 0 ≤ ∑ x : Fin 2,
        ((KrausFamily.applyMat
          (Qubit.measureZComp.branch false) ρ) x x).re
      exact Finset.sum_nonneg fun x _ =>
        (Complex.nonneg_iff.mp hp.diag_nonneg).1
    have htrue : 0 ≤
        (Matrix.trace
          (KrausFamily.applyMat (Qubit.measureZComp.branch true) ρ)).re := by
      have hp := KrausFamily.applyMat_posSemidef
        (Qubit.measureZComp.branch true) hρ
      change 0 ≤ ∑ x : Fin 2,
        ((KrausFamily.applyMat
          (Qubit.measureZComp.branch true) ρ) x x).re
      exact Finset.sum_nonneg fun x _ =>
        (Complex.nonneg_iff.mp hp.diag_nonneg).1
    cases b
    · change
        (Matrix.trace
          (KrausFamily.applyMat (Qubit.measureZComp.branch false) ρ)).re ≤ _
      exact le_trans (le_add_of_nonneg_left htrue) hsum'
    · change
        (Matrix.trace
          (KrausFamily.applyMat (Qubit.measureZComp.branch true) ρ)).re ≤ _
      exact le_trans (le_add_of_nonneg_right hfalse) hsum'

@[simp] theorem measurementOperation_kraus (b : Bool) :
    (measurementOperation b).kraus = QuantumAction.kraus (.measurement b) :=
  rfl

/-- The symbolic action of every labelled machine step is
trace-nonincreasing.  This proposition-valued formulation is important:
`MachineStep` is proof data and cannot be eliminated into a runtime
`QuantumOperation`. -/
theorem machineStep_action_trace_nonincreasing {C : Type}
    {s t : Config C} {p : ℝ} {selectors : List Bool}
    {action : QuantumAction}
    (h : MachineStep s p selectors action t) :
    ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ, ρ.PosSemidef →
      (Matrix.trace (KrausFamily.applyMat action.kraus ρ)).re ≤
        (Matrix.trace ρ).re := by
  cases h with
  | internal h =>
      cases h with
      | «variable» => exact (QuantumOperation.identity 2).trace_nonincreasing
      | «lambda» => exact (QuantumOperation.identity 2).trace_nonincreasing
      | recursive => exact (QuantumOperation.identity 2).trace_nonincreasing
      | application => exact (QuantumOperation.identity 2).trace_nonincreasing
      | evaluateArgument =>
          exact (QuantumOperation.identity 2).trace_nonincreasing
      | beta => exact (QuantumOperation.identity 2).trace_nonincreasing
      | recBeta => exact (QuantumOperation.identity 2).trace_nonincreasing
      | returnPrimitive =>
          exact (QuantumOperation.identity 2).trace_nonincreasing
      | pauliXPrimitive => exact Qubit.pauliXOp.trace_nonincreasing
      | internalLeft =>
          exact (QuantumOperation.identity 2).trace_nonincreasing
      | internalRight =>
          exact (QuantumOperation.identity 2).trace_nonincreasing
  | probabilityLeft hp hp1 =>
      exact (sourceProbabilityOperation _ hp.le hp1).trace_nonincreasing
  | probabilityRight hp hp1 =>
      exact (sourceProbabilityOperation _
        (sub_nonneg.mpr hp1.le) (by linarith)).trace_nonincreasing
  | measurement hp =>
      exact (measurementOperation _).trace_nonincreasing
  | external h =>
      cases h <;> exact (QuantumOperation.identity 2).trace_nonincreasing

/-- A valid trace's composed symbolic history is trace-nonincreasing. -/
theorem executionTrace_history_trace_nonincreasing {C : Type}
    {s t : Config C} {p : ℝ} {selectors : List Bool}
    {actions : List QuantumAction} {depth : ℕ}
    (h : ExecutionTrace s t p selectors actions depth) :
    ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ, ρ.PosSemidef →
      (Matrix.trace
        (KrausFamily.applyMat (QuantumAction.composeHistory actions) ρ)).re ≤
          (Matrix.trace ρ).re := by
  induction h with
  | refl => exact (QuantumOperation.identity 2).trace_nonincreasing
  | cons head tail ih =>
      intro ρ hρ
      rw [QuantumAction.composeHistory_cons, KrausFamily.applyMat_comp]
      exact (ih _ (KrausFamily.applyMat_posSemidef _ hρ)).trans
        (machineStep_action_trace_nonincreasing head ρ hρ)

/-- The physical operation intrinsic to a completed observation. -/
noncomputable def finiteObservationOperation {C : Type}
    {start : Config C} (o : FiniteObservation start) :
    QuantumOperation 2 2 where
  kraus := o.kraus
  trace_nonincreasing := executionTrace_history_trace_nonincreasing o.trace

@[simp] theorem finiteObservationOperation_kraus {C : Type}
    {start : Config C} (o : FiniteObservation start) :
    (finiteObservationOperation o).kraus = o.kraus :=
  rfl

/-- Realize the terminal runtime value through the hardware logical relation
and attach it to the observation's physical operation. -/
noncomputable def observationInstrument {C : Type}
    {start : Config C} (o : FiniteObservation start)
    (d : HValue D₀ j₀)
    (_hvalue : ValueRel D₀ j₀ (fun _ => d) o.isTerminal.value d) :
    FiniteInstrumentComp 2 (HValue D₀ j₀) :=
  FiniteInstrumentComp.ofOperation (finiteObservationOperation o) d

/-- More generally, payload realization is supplied independently of the
terminal semantic value. -/
noncomputable def realizedObservationInstrument {C : Type}
    (realize : C → HValue D₀ j₀)
    {start : Config C} (o : FiniteObservation start)
    (d : HValue D₀ j₀)
    (_hvalue : ValueRel D₀ j₀ realize o.isTerminal.value d) :
    FiniteInstrumentComp 2 (HValue D₀ j₀) :=
  FiniteInstrumentComp.ofOperation (finiteObservationOperation o) d

@[simp] theorem realizedObservationInstrument_branch {C : Type}
    (realize : C → HValue D₀ j₀)
    {start : Config C} (o : FiniteObservation start)
    (d : HValue D₀ j₀)
    (hvalue : ValueRel D₀ j₀ realize o.isTerminal.value d)
    (u : (realizedObservationInstrument D₀ j₀ realize o d hvalue).Outcome) :
    (realizedObservationInstrument D₀ j₀ realize o d hvalue).branch u =
      o.kraus := by
  change (finiteObservationOperation o).kraus = o.kraus
  exact finiteObservationOperation_kraus o

@[simp] theorem realizedObservationInstrument_value {C : Type}
    (realize : C → HValue D₀ j₀)
    {start : Config C} (o : FiniteObservation start)
    (d : HValue D₀ j₀)
    (hvalue : ValueRel D₀ j₀ realize o.isTerminal.value d)
    (u : (realizedObservationInstrument D₀ j₀ realize o d hvalue).Outcome) :
    (realizedObservationInstrument D₀ j₀ realize o d hvalue).value u = d :=
  rfl

/-- Concrete-state consistency: the branch of the realized finite instrument
maps the initial normalized state to the accumulated weight times the terminal
normalized state. -/
theorem realizedObservationInstrument_state_consistent {C : Type}
    (realize : C → HValue D₀ j₀)
    {start : Config C} (o : FiniteObservation start)
    (d : HValue D₀ j₀)
    (hvalue : ValueRel D₀ j₀ realize o.isTerminal.value d)
    (u : (realizedObservationInstrument D₀ j₀ realize o d hvalue).Outcome) :
    KrausFamily.applyMat
        ((realizedObservationInstrument D₀ j₀ realize o d hvalue).branch u)
        start.quantum.mat =
      (o.weight : ℂ) • o.terminal.quantum.mat := by
  rw [realizedObservationInstrument_branch]
  exact o.apply_kraus_eq_weight_smul

/-! ## TT token characterization -/

/-- Existing physical embedding adequacy applies directly to every realized
hardware observation. -/
theorem token_of_realizedObservation {C : Type}
    (realize : C → HValue D₀ j₀)
    {start : Config C} (o : FiniteObservation start)
    (d : HValue D₀ j₀)
    (hvalue : ValueRel D₀ j₀ realize o.isTerminal.value d)
    (ξ : HValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HValue D₀ j₀) (TTResult 2))
    (hk : QLambda.Adequacy.PresentedAt
      (realizedObservationInstrument D₀ j₀ realize o d hvalue) k ξ)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈
        (taggedEmbed
          (realizedObservationInstrument D₀ j₀ realize o d hvalue) i k) ↔
      TTObservationToken.Holds resultCode token
        ((realizedObservationInstrument D₀ j₀ realize o d hvalue).bind ξ) :=
  QLambda.Adequacy.token_of_taggedEmbed _ ξ k hk i token

/-! ## External selector paths -/

/-- Apply a chronological path of external selectors without discarding the
unresolved tagged subtree which remains afterward. -/
noncomputable def selectPath {D : Type} [CompleteLattice D] :
    List Bool → TTExternalContinuationPower 2 D →
      TTExternalContinuationPower 2 D
  | [], q => q
  | b :: bs, q => selectPath bs (selectBranch b q)

@[simp] theorem selectPath_nil {D : Type} [CompleteLattice D]
    (q : TTExternalContinuationPower 2 D) :
    selectPath [] q = q :=
  rfl

@[simp] theorem selectPath_cons {D : Type} [CompleteLattice D]
    (b : Bool) (bs : List Bool) (q : TTExternalContinuationPower 2 D) :
    selectPath (b :: bs) q = selectPath bs (selectBranch b q) :=
  rfl

theorem selectPath_append {D : Type} [CompleteLattice D]
    (xs ys : List Bool) (q : TTExternalContinuationPower 2 D) :
    selectPath (xs ++ ys) q = selectPath ys (selectPath xs q) := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.cons_append, selectPath_cons]
      exact ih (selectBranch b q)

/-- Heap coordinate of a selected child subtree. -/
def branchCoordinate (selector : Bool) (i : ℕ) : ℕ :=
  if selector then 2 * i + 2 else 2 * i + 1

/-- Decode the finite external-selector path stored in a heap coordinate.
Coordinate zero leaves the current external node unresolved. -/
def coordinatePath : ℕ → List Bool
  | 0 => []
  | i + 1 => (i % 2 ≠ 0) :: coordinatePath (i / 2)
termination_by i => i
decreasing_by omega

@[simp] theorem coordinatePath_left (i : ℕ) :
    coordinatePath (branchCoordinate false i) =
      false :: coordinatePath i := by
  simp [branchCoordinate, coordinatePath]

@[simp] theorem coordinatePath_right (i : ℕ) :
    coordinatePath (branchCoordinate true i) =
      true :: coordinatePath i := by
  rw [show branchCoordinate true i = (2 * i + 1) + 1 by
    simp [branchCoordinate]]
  rw [coordinatePath]
  rw [show (2 * i + 1) / 2 = i by omega]
  simp

/-- Encode an explicit selector path above a remaining heap coordinate. -/
def encodePath : List Bool → ℕ → ℕ
  | [], i => i
  | selector :: selectors, i =>
      branchCoordinate selector (encodePath selectors i)

@[simp] theorem coordinatePath_encodePath
    (selectors : List Bool) (i : ℕ) :
    coordinatePath (encodePath selectors i) =
      selectors ++ coordinatePath i := by
  induction selectors with
  | nil => rfl
  | cons selector selectors ih =>
      cases selector <;>
        simp [encodePath, ih]

/-- Explicit `selectBranch` operations and the residual heap coordinate
encode one combined path in the original tagged computation. -/
theorem selectPath_apply_encode {D : Type} [CompleteLattice D]
    (selectors : List Bool) (q : TTExternalContinuationPower 2 D)
    (i : ℕ) :
    selectPath selectors q i = q (encodePath selectors i) := by
  induction selectors generalizing q i with
  | nil => rfl
  | cons selector selectors ih =>
      rw [selectPath_cons, ih]
      cases selector <;> rfl

/-- Physical primitive/tree embeddings are coordinate-constant, so any
unused explicit selector suffix leaves them unchanged. -/
@[simp] theorem selectPath_taggedEmbed {D : Type} [CompleteLattice D]
    (selectors : List Bool) (μ : FiniteInstrumentComp 2 D) :
    selectPath selectors (taggedEmbed μ) = taggedEmbed μ := by
  induction selectors with
  | nil => rfl
  | cons selector selectors ih =>
      rw [selectPath_cons]
      have hbranch :
          selectBranch selector (taggedEmbed μ) = taggedEmbed μ := by
        funext i
        cases selector <;> rfl
      rw [hbranch, ih]

/-! ## Exact adequacy boundary -/

/-- A simultaneous realization of every terminal leaf of one completed
evaluation tree. -/
structure RealizedTree {C : Type} (realize : C → HValue D₀ j₀)
    {start : Config C}
    (tree : EvaluationTree C (KrausFamily.identity 2) start) where
  value : TreeLeaf C → HValue D₀ j₀
  related : ∀ o, ValueRel D₀ j₀ realize
    (tree.instrument.value o).isTerminal.value
      (value (tree.instrument.value o))

/-- Map all terminal leaves of a branch-complete tree through their logical
relation realization. -/
noncomputable def realizedTreeInstrument {C : Type}
    (realize : C → HValue D₀ j₀)
    {start : Config C}
    (tree : EvaluationTree C (KrausFamily.identity 2) start)
    (R : RealizedTree D₀ j₀ realize tree) :
    FiniteInstrumentComp 2 (HValue D₀ j₀) :=
  tree.instrument.map R.value

/-- Unconditional token characterization for a whole evaluation tree.
Crucially, probability and measurement branches have already been combined
inside `tree.instrument`. -/
theorem token_of_realizedTree {C : Type}
    (realize : C → HValue D₀ j₀)
    {start : Config C}
    (tree : EvaluationTree C (KrausFamily.identity 2) start)
    (R : RealizedTree D₀ j₀ realize tree)
    (ξ : HValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HValue D₀ j₀) (TTResult 2))
    (hk : QLambda.Adequacy.PresentedAt
      (realizedTreeInstrument D₀ j₀ realize tree R) k ξ)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ taggedEmbed
        (realizedTreeInstrument D₀ j₀ realize tree R) i k ↔
      TTObservationToken.Holds resultCode token
        ((realizedTreeInstrument D₀ j₀ realize tree R).bind ξ) :=
  QLambda.Adequacy.token_of_taggedEmbed _ ξ k hk i token

/-- One terminal outcome is compatible when the selectors it consumed form
a prefix of the explicit path followed by the residual coordinate path. -/
def TreeOutcomeCompatible {C : Type} {start : Config C}
    (tree : EvaluationTree C (KrausFamily.identity 2) start)
    (selectors : List Bool) (i : ℕ)
    (o : tree.instrument.Outcome) : Prop :=
    List.IsPrefix (tree.instrument.value o).selectors
      (selectors ++ coordinatePath i)

/-- Restrict a realized tree instrument to exactly the terminal outcomes
compatible with the explicit selectors and residual heap coordinate. -/
noncomputable def restrictedRealizedTreeInstrument {C : Type}
    (realize : C → HValue D₀ j₀) {start : Config C}
    (tree : EvaluationTree C (KrausFamily.identity 2) start)
    (R : RealizedTree D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ) :
    FiniteInstrumentComp 2 (HValue D₀ j₀) := by
  classical
  let μ := realizedTreeInstrument D₀ j₀ realize tree R
  let compatible : μ.Outcome → Prop :=
    fun o => TreeOutcomeCompatible tree selectors i o
  letI : DecidablePred compatible := Classical.decPred compatible
  letI : Fintype (Subtype compatible) :=
    Fintype.subtype (Finset.univ.filter compatible)
      (fun o => by simp [compatible])
  exact
    { Outcome := Subtype compatible
      outcomeFintype := inferInstance
      branch := fun o => μ.branch o.1
      value := fun o => μ.value o.1
      trace_nonincreasing := by
        intro ρ hρ
        let weight : μ.Outcome → ℝ := fun o =>
          (Matrix.trace (KrausFamily.applyMat (μ.branch o) ρ)).re
        have hsubset :
            (Finset.univ.filter compatible) ⊆
              (Finset.univ : Finset μ.Outcome) :=
          Finset.filter_subset _ _
        have hnonneg :
            ∀ o ∈ (Finset.univ : Finset μ.Outcome),
              o ∉ Finset.univ.filter compatible → 0 ≤ weight o := by
          intro o _ _
          have hp := KrausFamily.applyMat_posSemidef (μ.branch o) hρ
          change 0 ≤ ∑ x, ((KrausFamily.applyMat (μ.branch o) ρ) x x).re
          exact Finset.sum_nonneg fun x _ =>
            (Complex.nonneg_iff.mp hp.diag_nonneg).1
        have hle :
            ∑ o ∈ Finset.univ.filter compatible, weight o ≤
              ∑ o : μ.Outcome, weight o := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
        rw [Finset.sum_subtype (p := compatible)
          (Finset.univ.filter compatible)
          (fun o => by simp) weight] at hle
        change (∑ o : Subtype compatible, weight o.1) ≤
          (Matrix.trace ρ).re
        exact hle.trans (μ.trace_nonincreasing ρ hρ) }

/-- Token characterization after coordinate/path restriction. -/
theorem token_of_restrictedRealizedTree {C : Type}
    (realize : C → HValue D₀ j₀) {start : Config C}
    (tree : EvaluationTree C (KrausFamily.identity 2) start)
    (R : RealizedTree D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ)
    (ξ : HValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HValue D₀ j₀) (TTResult 2))
    (hk : QLambda.Adequacy.PresentedAt
      (restrictedRealizedTreeInstrument D₀ j₀ realize tree R selectors i)
      k ξ)
    (token : TTObservationToken 2) :
    token ∈ embed
        (restrictedRealizedTreeInstrument D₀ j₀ realize tree R selectors i)
        k ↔
      TTObservationToken.Holds resultCode token
        ((restrictedRealizedTreeInstrument D₀ j₀ realize tree R selectors i).bind
          ξ) :=
  QLambda.Adequacy.token_of_embed _ ξ k hk token

/-! ## Unconditional soundness interface

`ConfigRel` deliberately relates only the classical CEK control and stack.
Consequently it cannot by itself remember the accumulated Kraus prefix of a
tree node.  The following invariant states exactly the additional, one-sided
fact needed for operational soundness.  It is pointwise order, not equality,
and makes no completeness or finite-generation assertion. -/

/-- One realized branch-complete tree is sound for a denotation when every
coordinate/path restriction of its physically aggregated instrument lies
below the correspondingly selected denotation.  Probability and measurement
remain aggregated inside `tree.instrument`; this invariant never replaces
them by a lattice join of separate branches. -/
structure EvaluationTreePointwiseSound {C : Type}
    (realize : C → HValue D₀ j₀) {start : Config C}
    (denotation : HComp D₀ j₀)
    (tree : EvaluationTree C (KrausFamily.identity 2) start)
    (R : RealizedTree D₀ j₀ realize tree) : Prop where
  restricted_le_selected :
    ∀ selectors i k,
      embed
          (restrictedRealizedTreeInstrument D₀ j₀ realize tree R selectors i)
          k ≤
        selectPath selectors denotation i k

/-- Exact pointwise embedding consequence of the one-sided tree invariant.
The initial `ConfigRel` premise records that `denotation` is the computation
represented by the starting CEK state; no completeness hypothesis is used. -/
theorem realizedTree_restricted_le_selected_of_pointwiseSound {C : Type}
    (realize : C → HValue D₀ j₀) {start : Config C}
    (denotation : HComp D₀ j₀)
    (_hstart : ConfigRel D₀ j₀ realize start denotation)
    (tree : EvaluationTree C (KrausFamily.identity 2) start)
    (R : RealizedTree D₀ j₀ realize tree)
    (hsound : EvaluationTreePointwiseSound D₀ j₀ realize denotation tree R)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HValue D₀ j₀) (TTResult 2)) :
    embed
        (restrictedRealizedTreeInstrument D₀ j₀ realize tree R selectors i)
        k ≤
      selectPath selectors denotation i k :=
  hsound.restricted_le_selected selectors i k

/-- Minimum token-level soundness, with no finite-presentation assumption:
every TT token produced by the restricted, physically aggregated tree occurs
in the selected denotation at the same coordinate and continuation. -/
theorem token_mem_selected_of_pointwiseSound {C : Type}
    (realize : C → HValue D₀ j₀) {start : Config C}
    (denotation : HComp D₀ j₀)
    (hstart : ConfigRel D₀ j₀ realize start denotation)
    (tree : EvaluationTree C (KrausFamily.identity 2) start)
    (R : RealizedTree D₀ j₀ realize tree)
    (hsound : EvaluationTreePointwiseSound D₀ j₀ realize denotation tree R)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HValue D₀ j₀) (TTResult 2))
    (token : TTObservationToken 2)
    (htoken : token ∈ embed
      (restrictedRealizedTreeInstrument D₀ j₀ realize tree R selectors i) k) :
    token ∈ selectPath selectors denotation i k :=
  realizedTree_restricted_le_selected_of_pointwiseSound D₀ j₀ realize
    denotation hstart tree R hsound selectors i k htoken

/-- Global one-sided operational soundness.  Unlike
`TreeOperationalCompleteness`, this asks only for inclusion of each finite
tree result and says nothing about whether finite trees generate the whole
selected denotation. -/
structure TreeOperationalSoundness {C : Type}
    (realize : C → HValue D₀ j₀) (start : Config C)
    (denotation : HComp D₀ j₀) : Prop where
  tree_pointwise :
    ∀ (tree : EvaluationTree C (KrausFamily.identity 2) start)
      (R : RealizedTree D₀ j₀ realize tree),
      EvaluationTreePointwiseSound D₀ j₀ realize denotation tree R

/-- A terminal primitive tree consumes no selector and is compatible with
every explicit path and residual coordinate. -/
theorem terminalTree_pathCompatible {C : Type} {s : Config C}
    (h : Terminal s) (selectors : List Bool) (i : ℕ) :
    ∀ o, TreeOutcomeCompatible
      (EvaluationTree.terminal
        (κ := KrausFamily.identity 2) h) selectors i o := by
  intro o
  exact List.nil_prefix

/-- One external selector is supplied exactly by its child heap coordinate. -/
theorem oneExternal_coordinate_prefix (selector : Bool) :
    List.IsPrefix [selector]
      ([] ++ coordinatePath (branchCoordinate selector 0)) := by
  cases selector <;> simp

/-- One external selector may instead be supplied explicitly while coordinate
zero leaves the child unresolved. -/
theorem oneExternal_explicit_prefix (selector : Bool) :
    List.IsPrefix [selector] ([selector] ++ coordinatePath 0) :=
  by simp [coordinatePath]

/-- Mixed probabilistic/external sanity check at unresolved coordinate zero:
a terminal outcome consuming no selector is retained, while a sibling outcome
which still needs external `false` is filtered out rather than causing the
whole probabilistic instrument to be rejected. -/
theorem mixed_terminal_external_root_filter :
    List.IsPrefix [] ([] ++ coordinatePath 0) ∧
      ¬ List.IsPrefix [false] ([] ++ coordinatePath 0) := by
  simp [coordinatePath]

/-- Whole-tree result observations available at one fuel stage for the exact
explicit-selector/residual-coordinate pair. -/
def treeResultsAtFuel {C : Type}
    (realize : C → HValue D₀ j₀) (start : Config C)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HValue D₀ j₀) (TTResult 2))
    (fuel : ℕ) : Set (TTResult 2) :=
  {T | ∃ (tree : EvaluationTree C (KrausFamily.identity 2) start)
      (R : RealizedTree D₀ j₀ realize tree),
      tree.depth ≤ fuel ∧
      T = embed
        (restrictedRealizedTreeInstrument D₀ j₀ realize tree R selectors i) k}

theorem treeResultsAtFuel_mono {C : Type}
    (realize : C → HValue D₀ j₀) (start : Config C)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HValue D₀ j₀) (TTResult 2))
    {fuel fuel' : ℕ} (h : fuel ≤ fuel') :
    treeResultsAtFuel D₀ j₀ realize start selectors i k fuel ⊆
      treeResultsAtFuel D₀ j₀ realize start selectors i k fuel' := by
  rintro T ⟨tree, R, hdepth, rfl⟩
  exact ⟨tree, R, hdepth.trans h, rfl⟩

/-- Exhaustive set of finite whole-tree results, explicitly presented
as the union of fuel stages. -/
def finiteTreeResults {C : Type}
    (realize : C → HValue D₀ j₀) (start : Config C)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HValue D₀ j₀) (TTResult 2)) :
    Set (TTResult 2) :=
  {T | ∃ fuel, T ∈
    treeResultsAtFuel D₀ j₀ realize start selectors i k fuel}

/-- Every result represented at a finite fuel stage is below the selected
denotation.  This is the order-theoretic soundness half, independent of the
reverse (operational completeness) inclusion. -/
theorem treeResultsAtFuel_le_selected_of_soundness {C : Type}
    (realize : C → HValue D₀ j₀) (start : Config C)
    (denotation : HComp D₀ j₀)
    (_hstart : ConfigRel D₀ j₀ realize start denotation)
    (hsound : TreeOperationalSoundness D₀ j₀ realize start denotation)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HValue D₀ j₀) (TTResult 2))
    (fuel : ℕ) :
    ∀ T ∈ treeResultsAtFuel D₀ j₀ realize start selectors i k fuel,
      T ≤ selectPath selectors denotation i k := by
  intro T hT
  rcases hT with ⟨tree, R, _hdepth, rfl⟩
  exact (hsound.tree_pointwise tree R).restricted_le_selected selectors i k

/-- The same soundness statement for the exhaustive union of finite fuel
stages. -/
theorem finiteTreeResults_le_selected_of_soundness {C : Type}
    (realize : C → HValue D₀ j₀) (start : Config C)
    (denotation : HComp D₀ j₀)
    (hstart : ConfigRel D₀ j₀ realize start denotation)
    (hsound : TreeOperationalSoundness D₀ j₀ realize start denotation)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HValue D₀ j₀) (TTResult 2)) :
    ∀ T ∈ finiteTreeResults D₀ j₀ realize start selectors i k,
      T ≤ selectPath selectors denotation i k := by
  rintro T ⟨fuel, hT⟩
  exact treeResultsAtFuel_le_selected_of_soundness D₀ j₀ realize start
    denotation hstart hsound selectors i k fuel T hT

/-- Legacy normalized-tree completeness interface.  It states that after
fixing both the explicit selector path and residual heap coordinate, each
result continuation is the nondeterministic supremum of compatible,
branch-complete finite evaluation trees.  This premise is generally
uninhabited for the positive-only normalized trees; use
`HardwareChannelSemantics.ChannelTreeCompleteness` for new results. -/
structure TreeOperationalCompleteness {C : Type}
    (realize : C → HValue D₀ j₀) (start : Config C)
    (denotation : HComp D₀ j₀) : Prop where
  selected_result_eq_tree_sup :
    ∀ selectors i k,
      selectPath selectors denotation i k =
        sSup (finiteTreeResults D₀ j₀ realize start selectors i k)

/-- Equality-based operational completeness entails the one-sided soundness
invariant.  The converse is not used or claimed. -/
theorem TreeOperationalCompleteness.toSoundness {C : Type}
    {realize : C → HValue D₀ j₀} {start : Config C}
    {denotation : HComp D₀ j₀}
    (hcomplete :
      TreeOperationalCompleteness D₀ j₀ realize start denotation) :
    TreeOperationalSoundness D₀ j₀ realize start denotation := by
  constructor
  intro tree R
  constructor
  intro selectors i k
  rw [hcomplete.selected_result_eq_tree_sup selectors i k]
  apply le_sSup
  exact ⟨tree.depth, tree, R, le_rfl, rfl⟩

/-- Closed-term token adequacy conditional only on the branch-complete
CEK/tree fundamental lemma (besides the standard finite presentation of the
chosen result continuation). -/
theorem closed_term_tree_token_adequacy_iff {C : Type}
    (realize : C → HValue D₀ j₀)
    (start : Config C)
    (denotation : HComp D₀ j₀)
    (hcomplete : TreeOperationalCompleteness D₀ j₀ realize start denotation)
    (selectors : List Bool)
    (ξ : HValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ selectPath selectors denotation i k ↔
      ∃ fuel, ∃
          (tree : EvaluationTree C (KrausFamily.identity 2) start)
          (R : RealizedTree D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        TTObservationToken.Holds resultCode token
          ((restrictedRealizedTreeInstrument D₀ j₀ realize tree R selectors i).bind
            ξ) := by
  rw [hcomplete.selected_result_eq_tree_sup selectors i k,
    RoundedTheory.mem_sSup]
  constructor
  · rintro ⟨_, ⟨fuel, hq⟩, ht⟩
    rcases hq with ⟨tree, R, hdepth, rfl⟩
    refine ⟨fuel, tree, R, hdepth, ?_⟩
    exact (token_of_restrictedRealizedTree D₀ j₀ realize tree R selectors i
      ξ k (fun o => hk _) token).1 ht
  · rintro ⟨fuel, tree, R, hdepth, ht⟩
    refine ⟨embed
      (restrictedRealizedTreeInstrument D₀ j₀ realize tree R selectors i)
      k, ?_, ?_⟩
    · exact ⟨fuel, tree, R, hdepth, rfl⟩
    · exact (token_of_restrictedRealizedTree D₀ j₀ realize tree R selectors i
        ξ k (fun o => hk _) token).2 ht

/-- The hardware adequacy statement specialized to an initial closed-program
configuration and its compositional interpreter denotation.  The sole
remaining semantic premise is the branch-complete CEK fundamental lemma. -/
theorem initialConfig_tree_token_adequacy_iff {C : Type}
    (realize : C → HValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HValue D₀ j₀))
    (hcomplete : TreeOperationalCompleteness D₀ j₀ realize
      (initialConfig code quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv))
    (selectors : List Bool)
    (ξ : HValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) i k ↔
      ∃ fuel, ∃
          (tree : EvaluationTree C (KrausFamily.identity 2)
            (initialConfig code quantum))
          (R : RealizedTree D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        TTObservationToken.Holds resultCode token
          ((restrictedRealizedTreeInstrument D₀ j₀ realize tree R selectors i).bind
            ξ) :=
  closed_term_tree_token_adequacy_iff D₀ j₀ realize
    (initialConfig code quantum)
    (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv)
    hcomplete selectors ξ k hk i token

/-! ## Recursive finite approximations -/

/-- Recursive values are the supremum of their finite unfoldings from bottom. -/
theorem recLambdaValue_eq_iSup_finite
    (self arg : Name)
    (body : ScottMap (Env (HValue D₀ j₀)) (HComp D₀ j₀))
    (ρ : Env (HValue D₀ j₀)) :
    recLambdaValue (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
        self arg body ρ =
      ⨆ fuel, ScottFixApproximation.iterateBot
        (recFunctional (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
          self arg body ρ) fuel := by
  exact ScottFixApproximation.fix_eq_iSup_iterateBot _

/-- Every finite recursive unfolding lies below the recursive value. -/
theorem finite_rec_unfolding_le
    (self arg : Name)
    (body : ScottMap (Env (HValue D₀ j₀)) (HComp D₀ j₀))
    (ρ : Env (HValue D₀ j₀)) (fuel : ℕ) :
    ScottFixApproximation.iterateBot
        (recFunctional (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
          self arg body ρ) fuel ≤
      recLambdaValue (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
        self arg body ρ := by
  exact ScottFixApproximation.iterateBot_le_fix _ fuel

end HardwareAdequacy
end QLambda
