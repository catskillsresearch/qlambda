/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.HardwareAdequacy

/-!
# Proof-only channel semantics for the hardware CEK machine

`HardwareOperational.Config` remains the executable machine with normalized
states and positive-only measurement transitions.  This module supplies the
state-independent proof semantics needed by the TT channel model.  Its states
are subnormalized, so every physical branch exists, including a zero branch.
No normalization or positivity test is performed in this layer.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

set_option maxHeartbeats 800000

namespace QLambda
namespace HardwareChannelSemantics

open HardwareOperational
open HardwareObservation
open HardwareAdequacy
open HardwareLogicalRelation
open TTPhysicalPrimitives
open TTPhysicalEmbedding
open TTContinuation
open Scott1972.ContinuousLattice

/-- A proof configuration has exactly the executable CEK data, but carries a
possibly-zero subnormalized state. -/
structure ChannelConfig (C : Type) where
  control : Control C
  env : RuntimeEnv C
  stack : EvalStack C
  quantum : SubNormalizedDensity 2

/-- The classical CEK relation is unchanged by the proof-only quantum state.
It is intentionally independent of the subnormalized matrix; physical effects
are tracked exactly by `ChannelTree.state_exact`. -/
def ChannelConfigRel {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C) (answer : HSemanticComp D₀ j₀) : Prop :=
  ∃ current k,
    ControlRel D₀ j₀ realize s.control s.env current ∧
    StackRel D₀ j₀ realize s.stack k ∧
    answer = k current

/-- Forget only the normalization proof of an executable configuration. -/
def ofConfig {C : Type} (s : Config C) : ChannelConfig C where
  control := s.control
  env := s.env
  stack := s.stack
  quantum :=
    { mat := s.quantum.mat
      posSemidef := s.quantum.posSemidef
      trace_le_one := by rw [s.quantum.trace_eq_one]; norm_num }

@[simp] theorem ofConfig_control {C : Type} (s : Config C) :
    (ofConfig s).control = s.control := rfl

@[simp] theorem ofConfig_quantum_mat {C : Type} (s : Config C) :
    (ofConfig s).quantum.mat = s.quantum.mat := rfl

/-- Apply a trace-nonincreasing operation without normalizing its output. -/
noncomputable def applyOperation (Φ : QuantumOperation 2 2)
    (ρ : SubNormalizedDensity 2) : SubNormalizedDensity 2 where
  mat := KrausFamily.applyMat Φ.kraus ρ.mat
  posSemidef := KrausFamily.applyMat_posSemidef Φ.kraus ρ.posSemidef
  trace_le_one := (Φ.trace_nonincreasing ρ.mat ρ.posSemidef).trans
    ρ.trace_le_one

@[simp] theorem applyOperation_mat (Φ : QuantumOperation 2 2)
    (ρ : SubNormalizedDensity 2) :
    (applyOperation Φ ρ).mat = KrausFamily.applyMat Φ.kraus ρ.mat := rfl

@[simp] theorem applyOperation_identity (ρ : SubNormalizedDensity 2) :
    applyOperation (QuantumOperation.identity 2) ρ = ρ := by
  apply SubNormalizedDensity.ext
  exact KrausFamily.applyMat_identity ρ.mat

/-- Every operation sends the zero proof-state to zero. -/
theorem applyOperation_bot (Φ : QuantumOperation 2 2) :
    applyOperation Φ (⊥ : SubNormalizedDensity 2) = ⊥ := by
  apply SubNormalizedDensity.ext
  simp [applyOperation, SubNormalizedDensity.mat_bot, KrausFamily.applyMat]

/-- Administrative CEK reduction in the proof semantics.  Pauli-X is the only
constructor here that changes the proof-state. -/
inductive ChannelInternalStep {C : Type} :
    ChannelConfig C → ChannelConfig C → Prop where
  | variable {s : ChannelConfig C} {x : Name} {v : RuntimeValue C}
      (h : RuntimeEnv.lookup x s.env = some v) :
      ChannelInternalStep {s with control := .term (.var x)}
        {s with control := .value v}
  | lambda {s : ChannelConfig C} {x : Name}
      {body : Term (QubitPrimitive C)} :
      ChannelInternalStep {s with control := .term (.lam x body)}
        {s with control := .value (.closure x body s.env)}
  | recursive {s : ChannelConfig C} {self arg : Name}
      {body : Term (QubitPrimitive C)} :
      ChannelInternalStep {s with control := .term (.recLam self arg body)}
        {s with control := .value (.recClosure self arg body s.env)}
  | application {s : ChannelConfig C}
      {fn arg : Term (QubitPrimitive C)} :
      ChannelInternalStep {s with control := .term (.app fn arg)}
        { s with
          control := .term fn
          stack := .argument arg s.env :: s.stack}
  | evaluateArgument {s : ChannelConfig C} {fn : RuntimeValue C}
      {arg : Term (QubitPrimitive C)} {callEnv : RuntimeEnv C}
      {rest : EvalStack C} :
      ChannelInternalStep
        { s with
          control := .value fn
          stack := .argument arg callEnv :: rest}
        { s with
          control := .term arg
          env := callEnv
          stack := .function fn :: rest}
  | beta {s : ChannelConfig C} {x : Name}
      {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
      {arg : RuntimeValue C} {rest : EvalStack C} :
      ChannelInternalStep
        { s with
          control := .value arg
          stack := .function (.closure x body closureEnv) :: rest}
        { s with
          control := .term body
          env := RuntimeEnv.bind x arg closureEnv
          stack := rest}
  | recBeta {s : ChannelConfig C} {self x : Name}
      {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
      {arg : RuntimeValue C} {rest : EvalStack C} :
      ChannelInternalStep
        { s with
          control := .value arg
          stack := .function (.recClosure self x body closureEnv) :: rest}
        { s with
          control := .term body
          env := RuntimeEnv.bind x arg
            (RuntimeEnv.bind self
              (.recClosure self x body closureEnv) closureEnv)
          stack := rest}
  | returnPrimitive {s : ChannelConfig C} {value : C} :
      ChannelInternalStep {s with control := .term (.prim (.ret value))}
        {s with control := .value (.payload value)}
  | pauliXPrimitive {s : ChannelConfig C} {value : C} :
      ChannelInternalStep {s with control := .term (.prim (.pauliX value))}
        { s with
          control := .value (.payload value)
          quantum := applyOperation Qubit.pauliXOp s.quantum}
  | internalLeft {s : ChannelConfig C}
      {left right : Term (QubitPrimitive C)} :
      ChannelInternalStep {s with control := .term (.intern left right)}
        {s with control := .term left}
  | internalRight {s : ChannelConfig C}
      {left right : Term (QubitPrimitive C)} :
      ChannelInternalStep {s with control := .term (.intern left right)}
        {s with control := .term right}

/-- Physical action is read from executable control rather than eliminated
from proof data. -/
noncomputable def channelInternalOperation {C : Type}
    (s : ChannelConfig C) : QuantumOperation 2 2 :=
  match s.control with
  | .term (.prim (.pauliX _)) => Qubit.pauliXOp
  | _ => QuantumOperation.identity 2

/-- Internal proof steps evolve their subnormalized state by their declared
operation. -/
theorem internal_quantum_exact {C : Type} {s t : ChannelConfig C}
    (h : ChannelInternalStep s t) :
    t.quantum = applyOperation (channelInternalOperation s) s.quantum := by
  cases h <;> simp [channelInternalOperation]

/-- Total external selection. -/
inductive ChannelExternalStep {C : Type} :
    ChannelConfig C → Bool → ChannelConfig C → Prop where
  | selectFalse {s : ChannelConfig C}
      {left right : Term (QubitPrimitive C)} :
      ChannelExternalStep {s with control := .term (.extern left right)}
        false {s with control := .term left}
  | selectTrue {s : ChannelConfig C}
      {left right : Term (QubitPrimitive C)} :
      ChannelExternalStep {s with control := .term (.extern left right)}
        true {s with control := .term right}

/-- A terminal proof configuration. -/
structure ChannelTerminal {C : Type} (s : ChannelConfig C) where
  value : RuntimeValue C
  control_eq : s.control = .value value
  stack_eq : s.stack = []

/-- A related terminal proof configuration returns an exactly related value,
just as in the normalized machine. -/
theorem terminal_related {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} (hterminal : ChannelTerminal s)
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    ∃ d : HSemanticValue D₀ j₀,
      ValueRel D₀ j₀ realize hterminal.value d ∧
      answer = semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) d := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  rw [hterminal.control_eq] at hcontrol
  rw [hterminal.stack_eq] at hstack
  cases hcontrol with
  | value _ d _ hvalue =>
      cases hstack
      exact ⟨d, hvalue, rfl⟩

/-- One leaf of a channel tree, including consumed external selectors. -/
structure ChannelLeaf (C : Type) where
  terminal : ChannelConfig C
  isTerminal : ChannelTerminal terminal
  selectors : List Bool

def prependSelector {C : Type} (b : Bool) (leaf : ChannelLeaf C) :
    ChannelLeaf C :=
  { leaf with selectors := b :: leaf.selectors }

/-- Branch-complete proof evaluation.  Probability and measurement always
have two children.  In particular, neither constructor asks whether its
current concrete branch has positive trace. -/
inductive ChannelTree (C : Type) : ChannelConfig C → Type where
  | terminal {s : ChannelConfig C} (h : ChannelTerminal s) : ChannelTree C s
  | internal {s t : ChannelConfig C} (h : ChannelInternalStep s t)
      (next : ChannelTree C t) : ChannelTree C s
  | external {s t : ChannelConfig C} (selector : Bool)
      (h : ChannelExternalStep s selector t)
      (next : ChannelTree C t) : ChannelTree C s
  | probability {s : ChannelConfig C} {p : ℝ}
      {left right : Term (QubitPrimitive C)}
      (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
      (leftTree : ChannelTree C
        { s with
          control := .term left
          quantum := applyOperation
            (sourceProbabilityOperation p hp₀ hp₁) s.quantum})
      (rightTree : ChannelTree C
        { s with
          control := .term right
          quantum := applyOperation
            (sourceProbabilityOperation (1 - p)
              (sub_nonneg.mpr hp₁) (by linarith)) s.quantum}) :
      ChannelTree C {s with control := .term (.prob p left right)}
  | measurement {s : ChannelConfig C} {zeroValue oneValue : C}
      (zeroTree : ChannelTree C
        { s with
          control := .value (.payload zeroValue)
          quantum := applyOperation (measurementOperation false) s.quantum})
      (oneTree : ChannelTree C
        { s with
          control := .value (.payload oneValue)
          quantum := applyOperation (measurementOperation true) s.quantum}) :
      ChannelTree C
        {s with control := .term (.prim (.measureZ zeroValue oneValue))}

namespace ChannelTree

/-- Exact height, used as proof-evaluation fuel. -/
noncomputable def depth {C : Type} {s : ChannelConfig C} :
    ChannelTree C s → ℕ
  | .terminal _ => 0
  | .internal _ next => next.depth + 1
  | .external _ _ next => next.depth + 1
  | .probability _ _ left right => max left.depth right.depth + 1
  | .measurement zero one => max zero.depth one.depth + 1

/-- Fold every branch of a channel tree into one finite physical instrument. -/
noncomputable def instrument {C : Type} {s : ChannelConfig C} :
    ChannelTree C s → FiniteInstrumentComp 2 (ChannelLeaf C)
  | .terminal h => FiniteInstrumentComp.unit ⟨s, h, []⟩
  | .internal _h next =>
      (FiniteInstrumentComp.ofOperation (channelInternalOperation s) ()).bind
        (fun _ => next.instrument)
  | .external selector _h next =>
      next.instrument.map (prependSelector selector)
  | .probability hp₀ hp₁ left right =>
      (probabilityInstrument _ hp₀ hp₁).bind
        (fun b => if b then right.instrument else left.instrument)
  | .measurement zero one =>
      Qubit.measureZComp.bind
        (fun b => if b then one.instrument else zero.instrument)

/- Every folded branch sends the root proof-state exactly to its leaf
proof-state.  There is no scalar restoration because branch states remain
subnormalized throughout. -/
theorem state_exact {C : Type} {s : ChannelConfig C}
    (tree : ChannelTree C s) :
    ∀ o : tree.instrument.Outcome,
      KrausFamily.applyMat (tree.instrument.branch o) s.quantum.mat =
        (tree.instrument.value o).terminal.quantum.mat := by
  induction tree with
  | terminal h =>
      intro o
      change KrausFamily.applyMat (KrausFamily.identity 2) _ = _
      exact KrausFamily.applyMat_identity _
  | @internal source target h next ih =>
      rintro ⟨u, o⟩
      change
        KrausFamily.applyMat
            (KrausFamily.comp (next.instrument.branch o)
              (channelInternalOperation source).kraus)
            source.quantum.mat =
          (next.instrument.value o).terminal.quantum.mat
      rw [KrausFamily.applyMat_comp]
      rw [← applyOperation_mat, ← internal_quantum_exact h]
      exact ih o
  | external selector h next ih =>
      intro o
      cases h
      · change
          KrausFamily.applyMat (next.instrument.branch o) _ =
            (prependSelector false
              (next.instrument.value o)).terminal.quantum.mat
        exact ih o
      · change
          KrausFamily.applyMat (next.instrument.branch o) _ =
            (prependSelector true
              (next.instrument.value o)).terminal.quantum.mat
        exact ih o
  | @probability source p leftTerm rightTerm hp₀ hp₁ left right
      ihLeft ihRight =>
      rintro ⟨b, o⟩
      change Bool at b
      change
        KrausFamily.applyMat
          (KrausFamily.comp
            ((if b = true then right.instrument else left.instrument).branch o)
            (QuantumAction.kraus
              (.sourceProbability (if b = true then 1 - p else p))))
          source.quantum.mat =
        ((if b = true then right.instrument else left.instrument).value o).terminal.quantum.mat
      rw [KrausFamily.applyMat_comp]
      cases b
      · change
          KrausFamily.applyMat (left.instrument.branch o)
              (KrausFamily.applyMat
                (sourceProbabilityOperation _ hp₀ hp₁).kraus
                  source.quantum.mat) =
            (left.instrument.value o).terminal.quantum.mat
        rw [← applyOperation_mat]
        exact ihLeft o
      · change
          KrausFamily.applyMat (right.instrument.branch o)
              (KrausFamily.applyMat
                (sourceProbabilityOperation (1 - p)
                  (sub_nonneg.mpr hp₁) (by linarith)).kraus
                  source.quantum.mat) =
            (right.instrument.value o).terminal.quantum.mat
        rw [← applyOperation_mat]
        exact ihRight o
  | @measurement source zeroValue oneValue zero one ihZero ihOne =>
      rintro ⟨b, o⟩
      change Bool at b
      change
        KrausFamily.applyMat
          (KrausFamily.comp
            ((if b = true then one.instrument else zero.instrument).branch o)
            (if b = true then [Qubit.proj1] else [Qubit.proj0]))
          source.quantum.mat =
        ((if b = true then one.instrument else zero.instrument).value o).terminal.quantum.mat
      rw [KrausFamily.applyMat_comp]
      cases b
      · change
          KrausFamily.applyMat (zero.instrument.branch o)
              (KrausFamily.applyMat (measurementOperation false).kraus
                source.quantum.mat) =
            (zero.instrument.value o).terminal.quantum.mat
        rw [← applyOperation_mat]
        exact ihZero o
      · change
          KrausFamily.applyMat (one.instrument.branch o)
              (KrausFamily.applyMat (measurementOperation true).kraus
                source.quantum.mat) =
            (one.instrument.value o).terminal.quantum.mat
        rw [← applyOperation_mat]
        exact ihOne o

/-- Fuel-indexed branch-complete channel trees. -/
def atFuel {C : Type} (start : ChannelConfig C) (fuel : ℕ) :
    Set (ChannelTree C start) :=
  {tree | tree.depth ≤ fuel}

theorem atFuel_mono {C : Type} {start : ChannelConfig C}
    {fuel fuel' : ℕ} (h : fuel ≤ fuel') :
    atFuel start fuel ⊆ atFuel start fuel' :=
  fun _ ht => ht.trans h

end ChannelTree

/-! ## Correspondence with the executable normalized machine -/

/-- A positive proof-level measurement branch normalizes to exactly the
existing executable measurement transition. -/
theorem positive_measurement_correspondence {C : Type}
    (s : Config C) (zeroValue oneValue : C) (b : Bool)
    (hpositive : 0 < measureProbability s b) :
    ∃ t : Config C,
      HardwareOperational.WeightedStep
        ({s with control := .term (.prim (.measureZ zeroValue oneValue))} :
          Config C)
        (measureProbability s b) t ∧
      (applyOperation (measurementOperation b) (ofConfig s).quantum).mat =
        (measureProbability s b : ℂ) • t.quantum.mat := by
  let t : Config C :=
    {s with
      control := .value (.payload (if b then oneValue else zeroValue))
      quantum := measuredState s b hpositive}
  refine ⟨t, .measurement hpositive, ?_⟩
  exact QuantumAction.apply_measurement s b hpositive

/-- Positive source-probability branches are exactly the executable weighted
steps, while the same formula remains meaningful at weight zero in the proof
semantics. -/
theorem positive_probability_left_correspondence {C : Type}
    (s : Config C) (p : ℝ) (left right : Term (QubitPrimitive C))
    (hp : 0 < p) (hp₁ : p ≤ 1) :
    ∃ t : Config C,
      HardwareOperational.WeightedStep
        ({s with control := .term (.prob p left right)} : Config C)
        p t ∧
      (applyOperation (sourceProbabilityOperation p hp.le hp₁)
        (ofConfig s).quantum).mat = (p : ℂ) • t.quantum.mat := by
  refine ⟨{s with control := .term left}, .probabilityLeft hp hp₁, ?_⟩
  exact QuantumAction.apply_sourceProbability p hp.le s.quantum.mat

theorem positive_probability_right_correspondence {C : Type}
    (s : Config C) (p : ℝ) (left right : Term (QubitPrimitive C))
    (hp₀ : 0 ≤ p) (hp₁ : p < 1) :
    ∃ t : Config C,
      HardwareOperational.WeightedStep
        ({s with control := .term (.prob p left right)} : Config C)
        (1 - p) t ∧
      (applyOperation
        (sourceProbabilityOperation (1 - p)
          (sub_nonneg.mpr hp₁.le) (by linarith))
        (ofConfig s).quantum).mat =
          ((1 - p : ℝ) : ℂ) • t.quantum.mat := by
  refine ⟨{s with control := .term right}, .probabilityRight hp₀ hp₁, ?_⟩
  exact QuantumAction.apply_sourceProbability (1 - p)
    (sub_nonneg.mpr hp₁.le) s.quantum.mat

/-! ## Coordinate restriction and TT observations -/

/-- A semantic value assignment for channel leaves.  Kept separate so the
physical channel tree itself is independent of the denotational model. -/
structure ChannelTreeRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {start : ChannelConfig C} (tree : ChannelTree C start) where
  value : ChannelLeaf C → HSemanticValue D₀ j₀
  related : ∀ o, ValueRel D₀ j₀ realize
    (tree.instrument.value o).isTerminal.value
      (value (tree.instrument.value o))

noncomputable def realizedInstrument {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {start : ChannelConfig C} (tree : ChannelTree C start)
    (R : ChannelTreeRealization D₀ j₀ realize tree) :
    FiniteInstrumentComp 2 (HSemanticValue D₀ j₀) :=
  tree.instrument.map R.value

def OutcomeCompatible {C : Type} {start : ChannelConfig C}
    (tree : ChannelTree C start) (selectors : List Bool) (i : ℕ)
    (o : tree.instrument.Outcome) : Prop :=
  List.IsPrefix (tree.instrument.value o).selectors
    (selectors ++ HardwareAdequacy.coordinatePath i)

noncomputable def restrictedInstrument {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {start : ChannelConfig C} (tree : ChannelTree C start)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ) :
    FiniteInstrumentComp 2 (HSemanticValue D₀ j₀) := by
  classical
  let μ := realizedInstrument D₀ j₀ realize tree R
  let compatible : μ.Outcome → Prop :=
    fun o => OutcomeCompatible tree selectors i o
  letI : DecidablePred compatible := Classical.decPred compatible
  letI : Fintype (Subtype compatible) :=
    Fintype.subtype (Finset.univ.filter compatible) (fun o => by
      simp [compatible])
  exact
    { Outcome := Subtype compatible
      branch := fun o => μ.branch o.1
      value := fun o => μ.value o.1
      trace_nonincreasing := by
        intro ρ hρ
        let weight : μ.Outcome → ℝ := fun o =>
          (Matrix.trace (KrausFamily.applyMat (μ.branch o) ρ)).re
        have hle :
            ∑ o ∈ Finset.univ.filter compatible, weight o ≤
              ∑ o : μ.Outcome, weight o := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _)
          intro o _ _
          have hp := KrausFamily.applyMat_posSemidef (μ.branch o) hρ
          change 0 ≤ ∑ x, ((KrausFamily.applyMat (μ.branch o) ρ) x x).re
          exact Finset.sum_nonneg fun x _ =>
            (Complex.nonneg_iff.mp hp.diag_nonneg).1
        rw [Finset.sum_subtype (p := compatible)
          (Finset.univ.filter compatible) (fun o => by simp) weight] at hle
        exact hle.trans (μ.trace_nonincreasing ρ hρ) }

theorem token_of_restrictedInstrument {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {start : ChannelConfig C} (tree : ChannelTree C start)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : QLambda.Adequacy.PresentedAt
      (restrictedInstrument D₀ j₀ realize tree R selectors i) k ξ)
    (token : TTObservationToken 2) :
    token ∈ embed (restrictedInstrument D₀ j₀ realize tree R selectors i) k ↔
      TTObservationToken.Holds resultCode token
        ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind ξ) :=
  QLambda.Adequacy.token_of_embed _ ξ k hk token

/-! ## Sound replacement for the old normalized-start target -/

def channelTreeResults {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (start : ChannelConfig C) (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    Set (TTResult 2) :=
  {T | ∃ fuel, ∃ (tree : ChannelTree C start)
      (R : ChannelTreeRealization D₀ j₀ realize tree),
      tree.depth ≤ fuel ∧
      T = embed (restrictedInstrument D₀ j₀ realize tree R selectors i) k}

/-- Channel-tree completeness is the sound equality target for `interp`.
Unlike the normalized-tree statement, its operational side never drops a
nonzero channel merely because one chosen input state annihilates it. -/
structure ChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (start : ChannelConfig C) (denotation : HSemanticComp D₀ j₀) : Prop where
  selected_result_eq_channelTree_sup :
    ∀ selectors i k,
      HardwareAdequacy.selectPath selectors denotation i k =
        sSup (channelTreeResults D₀ j₀ realize start selectors i k)

/-- Initial proof configuration corresponding to an executable normalized
start. -/
def initialChannelConfig {C : Type} (code : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2) : ChannelConfig C :=
  ofConfig (initialConfig code quantum)

/-- The repaired initial proof state uses the natural empty-environment
logical relation and denotes the compositional interpreter exactly. -/
theorem initialChannelConfig_related {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    ChannelConfigRel D₀ j₀ realize (initialChannelConfig code quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) := by
  refine ⟨interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv,
    id, ?_, StackRel.nil, rfl⟩
  exact ControlRel.term code [] semanticEnv
    (env_nil D₀ j₀ realize semanticEnv)

/-- The return primitive has a complete one-step channel tree. -/
def returnTree {C : Type} (value : C) (quantum : NormalizedDensity 2) :
    ChannelTree C (initialChannelConfig (.prim (.ret value)) quantum) := by
  let s := initialChannelConfig (.prim (.ret value)) quantum
  let tree := ChannelTree.internal
    (ChannelInternalStep.returnPrimitive (s := s) (value := value))
    (ChannelTree.terminal
      (s := {s with control := .value (.payload value)})
      { value := .payload value, control_eq := rfl, stack_eq := rfl })
  simpa [s, initialChannelConfig, ofConfig, initialConfig] using tree

/-- Pauli-X has a complete one-step channel tree with exact unnormalized
operation semantics (normalization happens only in the executable machine). -/
noncomputable def pauliXTree {C : Type} (value : C)
    (quantum : NormalizedDensity 2) :
    ChannelTree C (initialChannelConfig (.prim (.pauliX value)) quantum) := by
  let s := initialChannelConfig (.prim (.pauliX value)) quantum
  let tree := ChannelTree.internal
    (ChannelInternalStep.pauliXPrimitive (s := s) (value := value))
    (ChannelTree.terminal
      (s := { s with
        control := .value (.payload value)
        quantum := applyOperation Qubit.pauliXOp s.quantum })
      { value := .payload value, control_eq := rfl, stack_eq := rfl })
  simpa [s, initialChannelConfig, ofConfig, initialConfig] using tree

/-- Measurement always has both channel children, including a child whose
state is zero on the selected initial density. -/
noncomputable def measurementTree {C : Type} (zeroValue oneValue : C)
    (quantum : NormalizedDensity 2) :
    ChannelTree C
      (initialChannelConfig (.prim (.measureZ zeroValue oneValue)) quantum) :=
  ChannelTree.measurement
    (s := initialChannelConfig
      (.prim (.measureZ zeroValue oneValue)) quantum)
    (ChannelTree.terminal
      { value := .payload zeroValue
        control_eq := rfl
        stack_eq := rfl })
    (ChannelTree.terminal
      { value := .payload oneValue
        control_eq := rfl
        stack_eq := rfl })

/-- Closed-term TT adequacy from the repaired channel-tree completeness
statement. -/
theorem initialConfig_channel_tree_token_adequacy_iff {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hcomplete : ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig code quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv))
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig code quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        TTObservationToken.Holds resultCode token
          ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind ξ) := by
  rw [hcomplete.selected_result_eq_channelTree_sup selectors i k,
    RoundedTheory.mem_sSup]
  constructor
  · rintro ⟨_, ⟨fuel, tree, R, hdepth, rfl⟩, htoken⟩
    refine ⟨fuel, tree, R, hdepth, ?_⟩
    exact (token_of_restrictedInstrument D₀ j₀ realize tree R selectors i
      ξ k (fun o => hk _) token).1 htoken
  · rintro ⟨fuel, tree, R, hdepth, htoken⟩
    refine ⟨embed
      (restrictedInstrument D₀ j₀ realize tree R selectors i) k, ?_, ?_⟩
    · exact ⟨fuel, tree, R, hdepth, rfl⟩
    · exact (token_of_restrictedInstrument D₀ j₀ realize tree R selectors i
        ξ k (fun o => hk _) token).2 htoken

/-- Recursive denotations still admit the finite Scott approximants needed by
a fuel induction for `ChannelTreeCompleteness`. -/
theorem recLambdaValue_eq_iSup_channel_finite
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (self arg : Name)
    (body : ScottMap (Env (HSemanticValue D₀ j₀)) (HSemanticComp D₀ j₀))
    (ρ : Env (HSemanticValue D₀ j₀)) :
    recLambdaValue (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) self arg body ρ =
      ⨆ fuel, ScottFixApproximation.iterateBot
        (recFunctional (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) self arg body ρ) fuel :=
  ScottFixApproximation.fix_eq_iSup_iterateBot _

end HardwareChannelSemantics
end QLambda
