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

/-- Realize every payload leaf by the supplied classical embedding. -/
noncomputable def payloadLeafValue {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (leaf : ChannelLeaf C) : HSemanticValue D₀ j₀ :=
  match leaf.isTerminal.value with
  | .payload c => realize c
  | .closure .. => ⊥
  | .recClosure .. => ⊥

theorem ValueRel.payload_eq {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀} {c : C}
    {d : HSemanticValue D₀ j₀}
    (h : ValueRel D₀ j₀ realize (.payload c) d) :
    d = realize c := by
  cases h
  rfl

theorem payloadLeafValue_payload {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (leaf : ChannelLeaf C) {c : C}
    (hc : leaf.isTerminal.value = .payload c) :
    payloadLeafValue D₀ j₀ realize leaf = realize c := by
  simp [payloadLeafValue, hc]

/-- The return primitive has a complete one-step channel tree. -/
def returnTree {C : Type} (value : C) (quantum : NormalizedDensity 2) :
    ChannelTree C (initialChannelConfig (.prim (.ret value)) quantum) :=
  ChannelTree.internal
    (ChannelInternalStep.returnPrimitive
      (s := initialChannelConfig (.prim (.ret value)) quantum)
      (value := value))
    (ChannelTree.terminal
      { value := .payload value, control_eq := rfl, stack_eq := rfl })

/-- Pauli-X has a complete one-step channel tree with exact unnormalized
operation semantics (normalization happens only in the executable machine). -/
noncomputable def pauliXTree {C : Type} (value : C)
    (quantum : NormalizedDensity 2) :
    ChannelTree C (initialChannelConfig (.prim (.pauliX value)) quantum) :=
  ChannelTree.internal
    (ChannelInternalStep.pauliXPrimitive
      (s := initialChannelConfig (.prim (.pauliX value)) quantum)
      (value := value))
    (ChannelTree.terminal
      { value := .payload value, control_eq := rfl, stack_eq := rfl })

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

/-- The left one-sided execution of an internal choice between returns. -/
def internReturnLeftTree {C : Type} (leftValue rightValue : C)
    (quantum : NormalizedDensity 2) :
    ChannelTree C
      (initialChannelConfig
        (.intern (.prim (.ret leftValue)) (.prim (.ret rightValue))) quantum) :=
  ChannelTree.internal
    (ChannelInternalStep.internalLeft
      (s := initialChannelConfig
        (.intern (.prim (.ret leftValue)) (.prim (.ret rightValue))) quantum))
    (returnTree leftValue quantum)

/-- The right one-sided execution of an internal choice between returns. -/
def internReturnRightTree {C : Type} (leftValue rightValue : C)
    (quantum : NormalizedDensity 2) :
    ChannelTree C
      (initialChannelConfig
        (.intern (.prim (.ret leftValue)) (.prim (.ret rightValue))) quantum) :=
  ChannelTree.internal
    (ChannelInternalStep.internalRight
      (s := initialChannelConfig
        (.intern (.prim (.ret leftValue)) (.prim (.ret rightValue))) quantum))
    (returnTree rightValue quantum)

theorem returnTree_depth {C : Type} (value : C)
    (quantum : NormalizedDensity 2) :
    (returnTree value quantum).depth = 1 := by
  simp [returnTree, ChannelTree.depth]

theorem pauliXTree_depth {C : Type} (value : C)
    (quantum : NormalizedDensity 2) :
    (pauliXTree value quantum).depth = 1 := by
  simp [pauliXTree, ChannelTree.depth]

theorem measurementTree_depth {C : Type} (zeroValue oneValue : C)
    (quantum : NormalizedDensity 2) :
    (measurementTree zeroValue oneValue quantum).depth = 1 := by
  simp [measurementTree, ChannelTree.depth]

theorem internReturnLeftTree_depth {C : Type} (leftValue rightValue : C)
    (quantum : NormalizedDensity 2) :
    (internReturnLeftTree leftValue rightValue quantum).depth = 2 := by
  simp [internReturnLeftTree, returnTree, ChannelTree.depth]

theorem internReturnRightTree_depth {C : Type} (leftValue rightValue : C)
    (quantum : NormalizedDensity 2) :
    (internReturnRightTree leftValue rightValue quantum).depth = 2 := by
  simp [internReturnRightTree, returnTree, ChannelTree.depth]

theorem returnTree_leaf_payload {C : Type} (value : C)
    (quantum : NormalizedDensity 2)
    (o : (returnTree value quantum).instrument.Outcome) :
    ((returnTree value quantum).instrument.value o).isTerminal.value =
      .payload value := by
  rcases o with ⟨⟨⟩, ⟨⟩⟩
  rfl

theorem pauliXTree_leaf_payload {C : Type} (value : C)
    (quantum : NormalizedDensity 2)
    (o : (pauliXTree value quantum).instrument.Outcome) :
    ((pauliXTree value quantum).instrument.value o).isTerminal.value =
      .payload value := by
  rcases o with ⟨⟨⟩, ⟨⟩⟩
  rfl

theorem measurementTree_leaf_payload {C : Type}
    (zeroValue oneValue : C) (quantum : NormalizedDensity 2)
    (o : (measurementTree zeroValue oneValue quantum).instrument.Outcome) :
    ((measurementTree zeroValue oneValue quantum).instrument.value o
      ).isTerminal.value =
      .payload (match o.1 with
        | true => oneValue
        | false => zeroValue) := by
  obtain ⟨b, hb⟩ := o
  cases b <;> (cases hb; rfl)

theorem returnTree_selectors {C : Type} (value : C)
    (quantum : NormalizedDensity 2)
    (o : (returnTree value quantum).instrument.Outcome) :
    ((returnTree value quantum).instrument.value o).selectors = [] := by
  rcases o with ⟨⟨⟩, ⟨⟩⟩
  rfl

theorem pauliXTree_selectors {C : Type} (value : C)
    (quantum : NormalizedDensity 2)
    (o : (pauliXTree value quantum).instrument.Outcome) :
    ((pauliXTree value quantum).instrument.value o).selectors = [] := by
  rcases o with ⟨⟨⟩, ⟨⟩⟩
  rfl

theorem measurementTree_selectors {C : Type}
    (zeroValue oneValue : C) (quantum : NormalizedDensity 2)
    (o : (measurementTree zeroValue oneValue quantum).instrument.Outcome) :
    ((measurementTree zeroValue oneValue quantum).instrument.value o
      ).selectors = [] := by
  obtain ⟨b, hb⟩ := o
  cases b <;> (cases hb; rfl)

theorem returnTree_compatible {C : Type} (value : C)
    (quantum : NormalizedDensity 2) (selectors : List Bool) (i : ℕ)
    (o : (returnTree value quantum).instrument.Outcome) :
    OutcomeCompatible (returnTree value quantum) selectors i o := by
  simpa [OutcomeCompatible, returnTree_selectors] using List.nil_prefix

theorem pauliXTree_compatible {C : Type} (value : C)
    (quantum : NormalizedDensity 2) (selectors : List Bool) (i : ℕ)
    (o : (pauliXTree value quantum).instrument.Outcome) :
    OutcomeCompatible (pauliXTree value quantum) selectors i o := by
  simpa [OutcomeCompatible, pauliXTree_selectors] using List.nil_prefix

theorem measurementTree_compatible {C : Type}
    (zeroValue oneValue : C) (quantum : NormalizedDensity 2)
    (selectors : List Bool) (i : ℕ)
    (o : (measurementTree zeroValue oneValue quantum).instrument.Outcome) :
    OutcomeCompatible (measurementTree zeroValue oneValue quantum)
      selectors i o := by
  simpa [OutcomeCompatible, measurementTree_selectors] using List.nil_prefix

theorem internReturnLeftTree_leaf_payload {C : Type}
    (leftValue rightValue : C) (quantum : NormalizedDensity 2)
    (o : (internReturnLeftTree leftValue rightValue quantum).instrument.Outcome) :
    ((internReturnLeftTree leftValue rightValue quantum).instrument.value o
      ).isTerminal.value = .payload leftValue := by
  rcases o with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
  rfl

theorem internReturnRightTree_leaf_payload {C : Type}
    (leftValue rightValue : C) (quantum : NormalizedDensity 2)
    (o : (internReturnRightTree leftValue rightValue quantum).instrument.Outcome) :
    ((internReturnRightTree leftValue rightValue quantum).instrument.value o
      ).isTerminal.value = .payload rightValue := by
  rcases o with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
  rfl

theorem internReturnLeftTree_compatible {C : Type}
    (leftValue rightValue : C) (quantum : NormalizedDensity 2)
    (selectors : List Bool) (i : ℕ)
    (o : (internReturnLeftTree leftValue rightValue quantum).instrument.Outcome) :
    OutcomeCompatible (internReturnLeftTree leftValue rightValue quantum)
      selectors i o := by
  rcases o with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
  simp [OutcomeCompatible, internReturnLeftTree, returnTree,
    ChannelTree.instrument]
  exact List.nil_prefix

theorem internReturnRightTree_compatible {C : Type}
    (leftValue rightValue : C) (quantum : NormalizedDensity 2)
    (selectors : List Bool) (i : ℕ)
    (o : (internReturnRightTree leftValue rightValue quantum).instrument.Outcome) :
    OutcomeCompatible (internReturnRightTree leftValue rightValue quantum)
      selectors i o := by
  rcases o with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
  simp [OutcomeCompatible, internReturnRightTree, returnTree,
    ChannelTree.instrument]
  exact List.nil_prefix

noncomputable def returnTreeRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (value : C) (quantum : NormalizedDensity 2) :
    ChannelTreeRealization D₀ j₀ realize (returnTree value quantum) where
  value := payloadLeafValue D₀ j₀ realize
  related := by
    intro o
    have hc := returnTree_leaf_payload value quantum o
    unfold payloadLeafValue
    rw [hc]
    exact ValueRel.payload value

noncomputable def pauliXTreeRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (value : C) (quantum : NormalizedDensity 2) :
    ChannelTreeRealization D₀ j₀ realize (pauliXTree value quantum) where
  value := payloadLeafValue D₀ j₀ realize
  related := by
    intro o
    have hc := pauliXTree_leaf_payload value quantum o
    unfold payloadLeafValue
    rw [hc]
    exact ValueRel.payload value

noncomputable def measurementTreeRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (zeroValue oneValue : C) (quantum : NormalizedDensity 2) :
    ChannelTreeRealization D₀ j₀ realize
      (measurementTree zeroValue oneValue quantum) where
  value := payloadLeafValue D₀ j₀ realize
  related := by
    intro o
    have hc := measurementTree_leaf_payload zeroValue oneValue quantum o
    unfold payloadLeafValue
    rw [hc]
    obtain ⟨b, hb⟩ := o
    cases b <;> exact ValueRel.payload _

noncomputable def internReturnLeftTreeRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (leftValue rightValue : C) (quantum : NormalizedDensity 2) :
    ChannelTreeRealization D₀ j₀ realize
      (internReturnLeftTree leftValue rightValue quantum) where
  value := payloadLeafValue D₀ j₀ realize
  related := by
    intro o
    have hc := internReturnLeftTree_leaf_payload leftValue rightValue quantum o
    unfold payloadLeafValue
    rw [hc]
    exact ValueRel.payload leftValue

noncomputable def internReturnRightTreeRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (leftValue rightValue : C) (quantum : NormalizedDensity 2) :
    ChannelTreeRealization D₀ j₀ realize
      (internReturnRightTree leftValue rightValue quantum) where
  value := payloadLeafValue D₀ j₀ realize
  related := by
    intro o
    have hc := internReturnRightTree_leaf_payload leftValue rightValue quantum o
    unfold payloadLeafValue
    rw [hc]
    exact ValueRel.payload rightValue

/-- Restriction of a fully compatible tree is only a subtype reindexing. -/
noncomputable def restrictedOutcomeEquiv {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {start : ChannelConfig C} (tree : ChannelTree C start)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ)
    (hall : ∀ o, OutcomeCompatible tree selectors i o) :
    (realizedInstrument D₀ j₀ realize tree R).Outcome ≃
      (restrictedInstrument D₀ j₀ realize tree R selectors i).Outcome :=
  (Equiv.subtypeUnivEquiv hall).symm

theorem embed_restricted_of_all_compatible {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {start : ChannelConfig C} (tree : ChannelTree C start)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ)
    (hall : ∀ o, OutcomeCompatible tree selectors i o) :
    embed (restrictedInstrument D₀ j₀ realize tree R selectors i) =
      embed (realizedInstrument D₀ j₀ realize tree R) := by
  refine embed_congr_of_outcome_equiv
      (restrictedInstrument D₀ j₀ realize tree R selectors i)
      (realizedInstrument D₀ j₀ realize tree R)
      (restrictedOutcomeEquiv D₀ j₀ realize tree R selectors i hall).symm
      ?_ ?_
  · intro o
    rfl
  · intro o
    rfl

theorem returnTree_branch {C : Type} (value : C)
    (quantum : NormalizedDensity 2)
    (o : (returnTree value quantum).instrument.Outcome) :
    (returnTree value quantum).instrument.branch o =
      KrausFamily.identity 2 := by
  rcases o with ⟨⟨⟩, ⟨⟩⟩
  change KrausFamily.comp (KrausFamily.identity 2)
      (channelInternalOperation
        (initialChannelConfig (.prim (.ret value)) quantum)).kraus =
    KrausFamily.identity 2
  simp [channelInternalOperation, initialChannelConfig, ofConfig,
    initialConfig, QuantumOperation.identity]

theorem pauliXTree_branch {C : Type} (value : C)
    (quantum : NormalizedDensity 2)
    (o : (pauliXTree value quantum).instrument.Outcome) :
    (pauliXTree value quantum).instrument.branch o =
      Qubit.pauliXOp.kraus := by
  rcases o with ⟨⟨⟩, ⟨⟩⟩
  change KrausFamily.comp (KrausFamily.identity 2)
      (channelInternalOperation
        (initialChannelConfig (.prim (.pauliX value)) quantum)).kraus =
    Qubit.pauliXOp.kraus
  simp [channelInternalOperation, initialChannelConfig, ofConfig,
    initialConfig]

theorem returnTree_realized_eq_unit {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (value : C) (quantum : NormalizedDensity 2) :
    embed (realizedInstrument D₀ j₀ realize (returnTree value quantum)
      (returnTreeRealization D₀ j₀ realize value quantum)) =
      embed (FiniteInstrumentComp.unit (n := 2) (realize value)) := by
  let μ := realizedInstrument D₀ j₀ realize (returnTree value quantum)
    (returnTreeRealization D₀ j₀ realize value quantum)
  let _ : Unique μ.Outcome :=
    { default := ⟨⟨⟩, ⟨⟩⟩
      uniq := by intro o; rcases o with ⟨⟨⟩, ⟨⟩⟩; rfl }
  refine embed_eq_unit_of_unique μ (realize value) ?_ ?_
  · intro o
    change payloadLeafValue D₀ j₀ realize
        ((returnTree value quantum).instrument.value o) = realize value
    rw [payloadLeafValue_payload D₀ j₀ realize _
      (returnTree_leaf_payload value quantum o)]
  · intro o
    exact returnTree_branch value quantum o

theorem pauliXTree_realized_eq_ofOperation {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (value : C) (quantum : NormalizedDensity 2) :
    embed (realizedInstrument D₀ j₀ realize (pauliXTree value quantum)
      (pauliXTreeRealization D₀ j₀ realize value quantum)) =
      embed (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
        (realize value)) := by
  let μ := realizedInstrument D₀ j₀ realize (pauliXTree value quantum)
    (pauliXTreeRealization D₀ j₀ realize value quantum)
  let _ : Unique μ.Outcome :=
    { default := ⟨⟨⟩, ⟨⟩⟩
      uniq := by intro o; rcases o with ⟨⟨⟩, ⟨⟩⟩; rfl }
  refine embed_eq_ofOperation_of_unique μ Qubit.pauliXOp (realize value) ?_ ?_
  · intro o
    change payloadLeafValue D₀ j₀ realize
        ((pauliXTree value quantum).instrument.value o) = realize value
    rw [payloadLeafValue_payload D₀ j₀ realize _
      (pauliXTree_leaf_payload value quantum o)]
  · intro o
    exact pauliXTree_branch value quantum o

/-- The two-outcome measurement tree reindexes to the primitive
computational-basis instrument. -/
theorem measurementTree_realized_eq_measureZ {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (zeroValue oneValue : C) (quantum : NormalizedDensity 2) :
    embed (realizedInstrument D₀ j₀ realize
        (measurementTree zeroValue oneValue quantum)
        (measurementTreeRealization D₀ j₀ realize zeroValue oneValue quantum)) =
      embed (Qubit.measureZComp.map
        (fun b => if b then realize oneValue else realize zeroValue)) := by
  let μ := realizedInstrument D₀ j₀ realize
    (measurementTree zeroValue oneValue quantum)
    (measurementTreeRealization D₀ j₀ realize zeroValue oneValue quantum)
  let ν := Qubit.measureZComp.map
    (fun b => if b then realize oneValue else realize zeroValue)
  refine embed_congr_of_outcome_equiv μ ν ?e ?hbranch ?hvalue
  · exact
      { toFun := fun o => o.1
        invFun := fun b =>
          match b with
          | true => ⟨true, ⟨⟩⟩
          | false => ⟨false, ⟨⟩⟩
        left_inv := by
          intro o
          obtain ⟨b, hb⟩ := o
          cases b <;> (cases hb; rfl)
        right_inv := by
          intro b
          cases b <;> rfl }
  · intro o
    obtain ⟨b, hb⟩ := o
    cases b
    · cases hb
      change Qubit.measureZComp.branch false =
        KrausFamily.comp (KrausFamily.identity 2)
          (Qubit.measureZComp.branch false)
      simp
    · cases hb
      change Qubit.measureZComp.branch true =
        KrausFamily.comp (KrausFamily.identity 2)
          (Qubit.measureZComp.branch true)
      simp
  · intro o
    obtain ⟨b, hb⟩ := o
    cases b
    · cases hb
      change realize zeroValue =
        payloadLeafValue D₀ j₀ realize
          ((measurementTree zeroValue oneValue quantum).instrument.value
            ⟨false, ⟨⟩⟩)
      rw [payloadLeafValue_payload D₀ j₀ realize _
        (measurementTree_leaf_payload zeroValue oneValue quantum ⟨false, ⟨⟩⟩)]
    · cases hb
      change realize oneValue =
        payloadLeafValue D₀ j₀ realize
          ((measurementTree zeroValue oneValue quantum).instrument.value
            ⟨true, ⟨⟩⟩)
      rw [payloadLeafValue_payload D₀ j₀ realize _
        (measurementTree_leaf_payload zeroValue oneValue quantum ⟨true, ⟨⟩⟩)]

theorem internReturnLeftTree_realized_eq_unit {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (leftValue rightValue : C) (quantum : NormalizedDensity 2) :
    embed (realizedInstrument D₀ j₀ realize
        (internReturnLeftTree leftValue rightValue quantum)
        (internReturnLeftTreeRealization D₀ j₀ realize
          leftValue rightValue quantum)) =
      embed (FiniteInstrumentComp.unit (n := 2) (realize leftValue)) := by
  let μ := realizedInstrument D₀ j₀ realize
    (internReturnLeftTree leftValue rightValue quantum)
    (internReturnLeftTreeRealization D₀ j₀ realize
      leftValue rightValue quantum)
  let _ : Unique μ.Outcome :=
    { default := ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
      uniq := by
        intro o
        rcases o with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
        rfl }
  refine embed_eq_unit_of_unique μ (realize leftValue) ?_ ?_
  · intro o
    change payloadLeafValue D₀ j₀ realize
      ((internReturnLeftTree leftValue rightValue quantum).instrument.value o) =
        realize leftValue
    rw [payloadLeafValue_payload D₀ j₀ realize _
      (internReturnLeftTree_leaf_payload leftValue rightValue quantum o)]
  · intro o
    rcases o with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    change
      KrausFamily.comp
        (KrausFamily.comp (KrausFamily.identity 2)
          (QuantumOperation.identity 2).kraus)
        (QuantumOperation.identity 2).kraus = KrausFamily.identity 2
    simp [QuantumOperation.identity]

theorem internReturnRightTree_realized_eq_unit {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (leftValue rightValue : C) (quantum : NormalizedDensity 2) :
    embed (realizedInstrument D₀ j₀ realize
        (internReturnRightTree leftValue rightValue quantum)
        (internReturnRightTreeRealization D₀ j₀ realize
          leftValue rightValue quantum)) =
      embed (FiniteInstrumentComp.unit (n := 2) (realize rightValue)) := by
  let μ := realizedInstrument D₀ j₀ realize
    (internReturnRightTree leftValue rightValue quantum)
    (internReturnRightTreeRealization D₀ j₀ realize
      leftValue rightValue quantum)
  let _ : Unique μ.Outcome :=
    { default := ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
      uniq := by
        intro o
        rcases o with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
        rfl }
  refine embed_eq_unit_of_unique μ (realize rightValue) ?_ ?_
  · intro o
    change payloadLeafValue D₀ j₀ realize
      ((internReturnRightTree leftValue rightValue quantum).instrument.value o) =
        realize rightValue
    rw [payloadLeafValue_payload D₀ j₀ realize _
      (internReturnRightTree_leaf_payload leftValue rightValue quantum o)]
  · intro o
    rcases o with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    change
      KrausFamily.comp
        (KrausFamily.comp (KrausFamily.identity 2)
          (QuantumOperation.identity 2).kraus)
        (QuantumOperation.identity 2).kraus = KrausFamily.identity 2
    simp [QuantumOperation.identity]

theorem ChannelInternalStep.eq_of_return {C : Type}
    {s t : ChannelConfig C} {value : C}
    (h : ChannelInternalStep s t)
    (hc : s.control = .term (.prim (.ret value))) :
    t.control = .value (.payload value) ∧
      t.env = s.env ∧ t.stack = s.stack ∧ t.quantum = s.quantum := by
  cases h <;> cases hc
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem ChannelInternalStep.eq_of_pauliX {C : Type}
    {s t : ChannelConfig C} {value : C}
    (h : ChannelInternalStep s t)
    (hc : s.control = .term (.prim (.pauliX value))) :
    t.control = .value (.payload value) ∧
      t.env = s.env ∧ t.stack = s.stack ∧
      t.quantum = applyOperation Qubit.pauliXOp s.quantum := by
  cases h <;> cases hc
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem ChannelInternalStep.eq_of_intern {C : Type}
    {s t : ChannelConfig C} {left right : Term (QubitPrimitive C)}
    (h : ChannelInternalStep s t)
    (hc : s.control = .term (.intern left right)) :
    (t = {s with control := .term left}) ∨
      (t = {s with control := .term right}) := by
  cases h <;> cases hc
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem ChannelInternalStep.not_measureZ {C : Type}
    {s t : ChannelConfig C} {zeroValue oneValue : C}
    (h : ChannelInternalStep s t)
    (hc : s.control = .term (.prim (.measureZ zeroValue oneValue))) :
    False := by
  cases h <;> cases hc

theorem ChannelInternalStep.not_value_nil {C : Type}
    {s t : ChannelConfig C} {v : RuntimeValue C}
    (h : ChannelInternalStep s t)
    (hc : s.control = .value v) (hs : s.stack = []) : False := by
  cases h with
  | evaluateArgument => cases hs
  | beta => cases hs
  | recBeta => cases hs
  | returnPrimitive => cases hc
  | pauliXPrimitive => cases hc
  | lambda => cases hc
  | recursive => cases hc
  | application => cases hc
  | internalLeft => cases hc
  | internalRight => cases hc
  | «variable» => cases hc

theorem ChannelExternalStep.not_prim {C : Type}
    {s t : ChannelConfig C} {b : Bool} {p : QubitPrimitive C}
    (h : ChannelExternalStep s b t)
    (hc : s.control = .term (.prim p)) : False := by
  cases h <;> cases hc

theorem ChannelExternalStep.not_intern {C : Type}
    {s t : ChannelConfig C} {b : Bool}
    {left right : Term (QubitPrimitive C)}
    (h : ChannelExternalStep s b t)
    (hc : s.control = .term (.intern left right)) : False := by
  cases h <;> cases hc

theorem ChannelExternalStep.not_value {C : Type}
    {s t : ChannelConfig C} {b : Bool} {v : RuntimeValue C}
    (h : ChannelExternalStep s b t)
    (hc : s.control = .value v) : False := by
  cases h <;> cases hc

/-- Any completing channel tree from a closed return primitive embeds as
deterministic return of that payload. -/
theorem embed_of_ret_tree {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (value : C) (quantum : NormalizedDensity 2)
    (tree : ChannelTree C
      (initialChannelConfig (.prim (.ret value)) quantum))
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ) :
    embed (restrictedInstrument D₀ j₀ realize tree R selectors i) =
      embed (FiniteInstrumentComp.unit (n := 2) (realize value)) := by
  have hctrl :
      (initialChannelConfig (.prim (.ret value)) quantum).control =
        .term (.prim (.ret value)) := rfl
  have hstack :
      (initialChannelConfig (.prim (.ret value)) quantum).stack = [] := rfl
  cases tree with
  | terminal hterm =>
      have := hterm.control_eq
      simp [initialChannelConfig, ofConfig, initialConfig] at this
  | internal h next =>
      have ht := ChannelInternalStep.eq_of_return h hctrl
      have hnextctrl := ht.1
      have hnextstack := ht.2.2.1.trans hstack
      cases next with
      | terminal hterm =>
          have hvalue : hterm.value = .payload value := by
            injection hterm.control_eq.symm.trans hnextctrl
          have hall : ∀ o, OutcomeCompatible
              (ChannelTree.internal h (ChannelTree.terminal hterm))
              selectors i o := by
            intro o
            simp [OutcomeCompatible, ChannelTree.instrument]
            exact List.nil_prefix
          rw [embed_restricted_of_all_compatible D₀ j₀ realize _ R
            selectors i hall]
          let μ := realizedInstrument D₀ j₀ realize
            (ChannelTree.internal h (ChannelTree.terminal hterm)) R
          let _ : Unique μ.Outcome :=
            { default := ⟨⟨⟩, ⟨⟩⟩
              uniq := by intro o; rcases o with ⟨⟨⟩, ⟨⟩⟩; rfl }
          refine embed_eq_unit_of_unique μ (realize value) ?_ ?_
          · intro o
            have hrel := R.related o
            have hpay :
                ((ChannelTree.internal h (ChannelTree.terminal hterm)
                  ).instrument.value o).isTerminal.value =
                  .payload value := by
              simp [ChannelTree.instrument]
              exact hvalue
            rw [hpay] at hrel
            exact ValueRel.payload_eq D₀ j₀ hrel
          · intro o
            rcases o with ⟨⟨⟩, ⟨⟩⟩
            change KrausFamily.comp (KrausFamily.identity 2)
                (channelInternalOperation
                  (initialChannelConfig (.prim (.ret value)) quantum)).kraus =
              KrausFamily.identity 2
            simp [channelInternalOperation, initialChannelConfig, ofConfig,
              initialConfig, QuantumOperation.identity]
      | internal h' _ =>
          exact False.elim
            (ChannelInternalStep.not_value_nil h' hnextctrl
              (ht.2.2.1.trans hstack))
      | external _ h' _ =>
          exact False.elim (ChannelExternalStep.not_value h' hnextctrl)
      | probability _ _ _ _ => cases hnextctrl
      | measurement _ _ => cases hnextctrl
  | external _ h _ =>
      exact False.elim (ChannelExternalStep.not_prim h hctrl)

theorem embed_of_pauliX_tree {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (value : C) (quantum : NormalizedDensity 2)
    (tree : ChannelTree C
      (initialChannelConfig (.prim (.pauliX value)) quantum))
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ) :
    embed (restrictedInstrument D₀ j₀ realize tree R selectors i) =
      embed (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
        (realize value)) := by
  have hctrl :
      (initialChannelConfig (.prim (.pauliX value)) quantum).control =
        .term (.prim (.pauliX value)) := rfl
  have hstack :
      (initialChannelConfig (.prim (.pauliX value)) quantum).stack = [] := rfl
  cases tree with
  | terminal hterm =>
      have := hterm.control_eq
      simp [initialChannelConfig, ofConfig, initialConfig] at this
  | internal h next =>
      have ht := ChannelInternalStep.eq_of_pauliX h hctrl
      have hnextctrl := ht.1
      have hnextstack := ht.2.2.1.trans hstack
      cases next with
      | terminal hterm =>
          have hvalue : hterm.value = .payload value := by
            injection hterm.control_eq.symm.trans hnextctrl
          have hall : ∀ o, OutcomeCompatible
              (ChannelTree.internal h (ChannelTree.terminal hterm))
              selectors i o := by
            intro o
            simp [OutcomeCompatible, ChannelTree.instrument]
            exact List.nil_prefix
          rw [embed_restricted_of_all_compatible D₀ j₀ realize _ R
            selectors i hall]
          let μ := realizedInstrument D₀ j₀ realize
            (ChannelTree.internal h (ChannelTree.terminal hterm)) R
          let _ : Unique μ.Outcome :=
            { default := ⟨⟨⟩, ⟨⟩⟩
              uniq := by intro o; rcases o with ⟨⟨⟩, ⟨⟩⟩; rfl }
          refine embed_eq_ofOperation_of_unique μ Qubit.pauliXOp
            (realize value) ?_ ?_
          · intro o
            have hrel := R.related o
            have hpay :
                ((ChannelTree.internal h (ChannelTree.terminal hterm)
                  ).instrument.value o).isTerminal.value =
                  .payload value := by
              simp [ChannelTree.instrument]
              exact hvalue
            rw [hpay] at hrel
            exact ValueRel.payload_eq D₀ j₀ hrel
          · intro o
            rcases o with ⟨⟨⟩, ⟨⟩⟩
            change KrausFamily.comp (KrausFamily.identity 2)
                (channelInternalOperation
                  (initialChannelConfig (.prim (.pauliX value)) quantum)).kraus =
              Qubit.pauliXOp.kraus
            simp [channelInternalOperation, initialChannelConfig, ofConfig,
              initialConfig]
      | internal h' _ =>
          exact False.elim
            (ChannelInternalStep.not_value_nil h' hnextctrl hnextstack)
      | external _ h' _ =>
          exact False.elim (ChannelExternalStep.not_value h' hnextctrl)
      | probability _ _ _ _ => cases hnextctrl
      | measurement _ _ => cases hnextctrl
  | external _ h _ =>
      exact False.elim (ChannelExternalStep.not_prim h hctrl)

/-- Any completing channel tree from a closed measure-Z primitive embeds as
the two-outcome computational-basis instrument.  The start is generalized
first so indexed elimination can enter the measurement constructor. -/
theorem embed_of_measureZ_tree {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (zeroValue oneValue : C) (quantum : NormalizedDensity 2)
    (tree : ChannelTree C
      (initialChannelConfig (.prim (.measureZ zeroValue oneValue)) quantum))
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ) :
    embed (restrictedInstrument D₀ j₀ realize tree R selectors i) =
      embed (Qubit.measureZComp.map
        (fun b => if b then realize oneValue else realize zeroValue)) := by
  revert tree R
  generalize hs : initialChannelConfig
      (.prim (.measureZ zeroValue oneValue)) quantum = s
  intro tree R
  have hctrl :
      s.control = .term (.prim (.measureZ zeroValue oneValue)) := by
    cases hs; rfl
  have hstack : s.stack = [] := by
    cases hs; rfl
  cases tree with
  | terminal hterm =>
      have := hterm.control_eq.symm.trans hctrl
      cases this
  | internal h next =>
      exact False.elim (ChannelInternalStep.not_measureZ h hctrl)
  | external _ h _ =>
      exact False.elim (ChannelExternalStep.not_prim h hctrl)
  | probability _ _ _ _ =>
      cases hctrl
  | @measurement source z' o' zeroTree oneTree =>
      have hctrl0 :
          ({source with
              control := .value (.payload z')
              quantum := applyOperation (measurementOperation false)
                source.quantum}).control =
            .value (.payload z') := rfl
      have hstack0 :
          ({source with
              control := .value (.payload z')
              quantum := applyOperation (measurementOperation false)
                source.quantum}).stack = [] := hstack
      have hctrl1 :
          ({source with
              control := .value (.payload o')
              quantum := applyOperation (measurementOperation true)
                source.quantum}).control =
            .value (.payload o') := rfl
      have hstack1 :
          ({source with
              control := .value (.payload o')
              quantum := applyOperation (measurementOperation true)
                source.quantum}).stack = [] := hstack
      cases zeroTree with
      | terminal hz =>
          cases oneTree with
          | terminal ho =>
              have hval0 : hz.value = .payload z' :=
                (by injection hz.control_eq : _ = hz.value).symm
              have hval1 : ho.value = .payload o' :=
                (by injection ho.control_eq : _ = ho.value).symm
              have hzid : z' = zeroValue := by
                cases hctrl
                rfl
              have hoid : o' = oneValue := by
                cases hctrl
                rfl
              have hall : ∀ o, OutcomeCompatible
                  (ChannelTree.measurement
                    (ChannelTree.terminal hz) (ChannelTree.terminal ho))
                  selectors i o := by
                intro o
                obtain ⟨b, hb⟩ := o
                cases b
                · cases hb
                  simp [OutcomeCompatible, ChannelTree.instrument]
                  exact List.nil_prefix
                · cases hb
                  simp [OutcomeCompatible, ChannelTree.instrument]
                  exact List.nil_prefix
              rw [embed_restricted_of_all_compatible D₀ j₀ realize _ R
                selectors i hall]
              let μ := realizedInstrument D₀ j₀ realize
                (ChannelTree.measurement
                  (ChannelTree.terminal hz) (ChannelTree.terminal ho)) R
              let ν := Qubit.measureZComp.map
                (fun b => if b then realize oneValue else realize zeroValue)
              refine embed_congr_of_outcome_equiv μ ν ?e ?hbranch ?hvalue
              · exact
                  { toFun := fun o => o.1
                    invFun := fun b =>
                      match b with
                      | true => ⟨true, ⟨⟩⟩
                      | false => ⟨false, ⟨⟩⟩
                    left_inv := by
                      intro o
                      obtain ⟨b, hb⟩ := o
                      cases b <;> (cases hb; rfl)
                    right_inv := by
                      intro b
                      cases b <;> rfl }
              · intro o
                obtain ⟨b, hb⟩ := o
                cases b
                · cases hb
                  change Qubit.measureZComp.branch false =
                    KrausFamily.comp (KrausFamily.identity 2)
                      (Qubit.measureZComp.branch false)
                  simp
                · cases hb
                  change Qubit.measureZComp.branch true =
                    KrausFamily.comp (KrausFamily.identity 2)
                      (Qubit.measureZComp.branch true)
                  simp
              · intro o
                obtain ⟨b, hb⟩ := o
                cases b
                · cases hb
                  have hrel := R.related ⟨false, ⟨⟩⟩
                  have hpay :
                      ((ChannelTree.measurement
                          (ChannelTree.terminal hz)
                          (ChannelTree.terminal ho)).instrument.value
                        ⟨false, ⟨⟩⟩).isTerminal.value =
                        .payload z' := by
                    simp [ChannelTree.instrument]
                    exact hval0
                  rw [hpay] at hrel
                  exact ((ValueRel.payload_eq D₀ j₀ hrel).trans
                    (congrArg realize hzid)).symm
                · cases hb
                  have hrel := R.related ⟨true, ⟨⟩⟩
                  have hpay :
                      ((ChannelTree.measurement
                          (ChannelTree.terminal hz)
                          (ChannelTree.terminal ho)).instrument.value
                        ⟨true, ⟨⟩⟩).isTerminal.value =
                        .payload o' := by
                    simp [ChannelTree.instrument]
                    exact hval1
                  rw [hpay] at hrel
                  exact ((ValueRel.payload_eq D₀ j₀ hrel).trans
                    (congrArg realize hoid)).symm
          | internal h' _ =>
              exact False.elim
                (ChannelInternalStep.not_value_nil h' hctrl1 hstack1)
          | external _ h' _ =>
              exact False.elim (ChannelExternalStep.not_value h' hctrl1)
      | internal h' _ =>
          exact False.elim
            (ChannelInternalStep.not_value_nil h' hctrl0 hstack0)
      | external _ h' _ =>
          exact False.elim (ChannelExternalStep.not_value h' hctrl0)

/-- Every completing tree for an internal choice of two closed returns chooses
exactly one side and embeds as that deterministic return. -/
theorem embed_of_intern_returns_tree {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (leftValue rightValue : C) (quantum : NormalizedDensity 2)
    (tree : ChannelTree C
      (initialChannelConfig
        (.intern (.prim (.ret leftValue)) (.prim (.ret rightValue))) quantum))
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ) :
    embed (restrictedInstrument D₀ j₀ realize tree R selectors i) =
        embed (FiniteInstrumentComp.unit (n := 2) (realize leftValue)) ∨
      embed (restrictedInstrument D₀ j₀ realize tree R selectors i) =
        embed (FiniteInstrumentComp.unit (n := 2) (realize rightValue)) := by
  let start := initialChannelConfig
    (.intern (.prim (.ret leftValue)) (.prim (.ret rightValue))) quantum
  have hctrl : start.control =
      .term (.intern (.prim (.ret leftValue)) (.prim (.ret rightValue))) := rfl
  have hstack : start.stack = [] := rfl
  dsimp [start] at tree hctrl hstack
  cases tree with
  | terminal hterm =>
      have := hterm.control_eq.symm.trans hctrl
      cases this
  | @internal _ target h next =>
      rcases ChannelInternalStep.eq_of_intern h hctrl with ht | ht
      · left
        subst target
        have hnextctrl :
            ({start with control := .term (.prim (.ret leftValue))}).control =
              .term (.prim (.ret leftValue)) := rfl
        cases next with
        | terminal hterm =>
            have := hterm.control_eq.symm.trans hnextctrl
            cases this
        | internal hret final =>
            have hr := ChannelInternalStep.eq_of_return hret hnextctrl
            have hfinalctrl := hr.1
            have hfinalstack := hr.2.2.1.trans hstack
            cases final with
            | terminal hterm =>
                have hvalue : hterm.value = .payload leftValue := by
                  injection hterm.control_eq.symm.trans hfinalctrl
                have hall : ∀ o, OutcomeCompatible
                    (ChannelTree.internal h
                      (ChannelTree.internal hret (ChannelTree.terminal hterm)))
                    selectors i o := by
                  intro o
                  rcases o with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
                  simp [OutcomeCompatible, ChannelTree.instrument]
                  exact List.nil_prefix
                rw [embed_restricted_of_all_compatible D₀ j₀ realize _ R
                  selectors i hall]
                let μ := realizedInstrument D₀ j₀ realize
                  (ChannelTree.internal h
                    (ChannelTree.internal hret (ChannelTree.terminal hterm))) R
                let _ : Unique μ.Outcome :=
                  { default := ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
                    uniq := by
                      intro o
                      rcases o with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
                      rfl }
                refine embed_eq_unit_of_unique μ (realize leftValue) ?_ ?_
                · intro o
                  have hrel := R.related o
                  have hpay :
                      ((ChannelTree.internal h
                        (ChannelTree.internal hret
                          (ChannelTree.terminal hterm))).instrument.value o
                        ).isTerminal.value = .payload leftValue := by
                    simp [ChannelTree.instrument]
                    exact hvalue
                  rw [hpay] at hrel
                  exact ValueRel.payload_eq D₀ j₀ hrel
                · intro o
                  rcases o with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
                  change
                    KrausFamily.comp
                      (KrausFamily.comp (KrausFamily.identity 2)
                        (QuantumOperation.identity 2).kraus)
                      (QuantumOperation.identity 2).kraus =
                        KrausFamily.identity 2
                  simp [QuantumOperation.identity]
            | internal h' _ =>
                exact False.elim
                  (ChannelInternalStep.not_value_nil h' hfinalctrl hfinalstack)
            | external _ h' _ =>
                exact False.elim (ChannelExternalStep.not_value h' hfinalctrl)
            | probability _ _ _ _ => cases hfinalctrl
            | measurement _ _ => cases hfinalctrl
        | external _ h' _ =>
            exact False.elim (ChannelExternalStep.not_prim h' hnextctrl)
      · right
        subst target
        have hnextctrl :
            ({start with control := .term (.prim (.ret rightValue))}).control =
              .term (.prim (.ret rightValue)) := rfl
        cases next with
        | terminal hterm =>
            have := hterm.control_eq.symm.trans hnextctrl
            cases this
        | internal hret final =>
            have hr := ChannelInternalStep.eq_of_return hret hnextctrl
            have hfinalctrl := hr.1
            have hfinalstack := hr.2.2.1.trans hstack
            cases final with
            | terminal hterm =>
                have hvalue : hterm.value = .payload rightValue := by
                  injection hterm.control_eq.symm.trans hfinalctrl
                have hall : ∀ o, OutcomeCompatible
                    (ChannelTree.internal h
                      (ChannelTree.internal hret (ChannelTree.terminal hterm)))
                    selectors i o := by
                  intro o
                  rcases o with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
                  simp [OutcomeCompatible, ChannelTree.instrument]
                  exact List.nil_prefix
                rw [embed_restricted_of_all_compatible D₀ j₀ realize _ R
                  selectors i hall]
                let μ := realizedInstrument D₀ j₀ realize
                  (ChannelTree.internal h
                    (ChannelTree.internal hret (ChannelTree.terminal hterm))) R
                let _ : Unique μ.Outcome :=
                  { default := ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
                    uniq := by
                      intro o
                      rcases o with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
                      rfl }
                refine embed_eq_unit_of_unique μ (realize rightValue) ?_ ?_
                · intro o
                  have hrel := R.related o
                  have hpay :
                      ((ChannelTree.internal h
                        (ChannelTree.internal hret
                          (ChannelTree.terminal hterm))).instrument.value o
                        ).isTerminal.value = .payload rightValue := by
                    simp [ChannelTree.instrument]
                    exact hvalue
                  rw [hpay] at hrel
                  exact ValueRel.payload_eq D₀ j₀ hrel
                · intro o
                  rcases o with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
                  change
                    KrausFamily.comp
                      (KrausFamily.comp (KrausFamily.identity 2)
                        (QuantumOperation.identity 2).kraus)
                      (QuantumOperation.identity 2).kraus =
                        KrausFamily.identity 2
                  simp [QuantumOperation.identity]
            | internal h' _ =>
                exact False.elim
                  (ChannelInternalStep.not_value_nil h' hfinalctrl hfinalstack)
            | external _ h' _ =>
                exact False.elim (ChannelExternalStep.not_value h' hfinalctrl)
            | probability _ _ _ _ => cases hfinalctrl
            | measurement _ _ => cases hfinalctrl
        | external _ h' _ =>
            exact False.elim (ChannelExternalStep.not_prim h' hnextctrl)
  | external _ h _ =>
      exact False.elim (ChannelExternalStep.not_intern h hctrl)

/-- Closed return primitives satisfy channel-tree completeness exactly. -/
theorem return_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (value : C) (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.prim (.ret value)) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.prim (.ret value)) semanticEnv) where
  selected_result_eq_channelTree_sup := by
    intro selectors i k
    have hdenote :
        interp (hardwarePrimitive D₀ j₀ realize)
            (.prim (.ret value)) semanticEnv =
          taggedEmbed (FiniteInstrumentComp.unit (n := 2) (realize value)) := by
      simp [hardwarePrimitive_ret, taggedEmbed_unit]
    rw [hdenote, selectPath_taggedEmbed, taggedEmbed_apply]
    refine le_antisymm ?_ ?_
    · apply le_sSup
      refine ⟨1, returnTree value quantum,
        returnTreeRealization D₀ j₀ realize value quantum, ?_, ?_⟩
      · simp [returnTree_depth]
      · rw [embed_restricted_of_all_compatible D₀ j₀ realize
            (returnTree value quantum)
            (returnTreeRealization D₀ j₀ realize value quantum)
            selectors i (returnTree_compatible value quantum selectors i),
          returnTree_realized_eq_unit]
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      rw [embed_of_ret_tree D₀ j₀ realize value quantum tree R selectors i]

/-- Closed Pauli-X primitives satisfy channel-tree completeness exactly. -/
theorem pauliX_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (value : C) (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.prim (.pauliX value)) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.prim (.pauliX value)) semanticEnv) where
  selected_result_eq_channelTree_sup := by
    intro selectors i k
    have hdenote :
        interp (hardwarePrimitive D₀ j₀ realize)
            (.prim (.pauliX value)) semanticEnv =
          taggedEmbed (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
            (realize value)) := by
      simp [hardwarePrimitive_pauliX]
    rw [hdenote, selectPath_taggedEmbed, taggedEmbed_apply]
    refine le_antisymm ?_ ?_
    · apply le_sSup
      refine ⟨1, pauliXTree value quantum,
        pauliXTreeRealization D₀ j₀ realize value quantum, ?_, ?_⟩
      · simp [pauliXTree_depth]
      · rw [embed_restricted_of_all_compatible D₀ j₀ realize
            (pauliXTree value quantum)
            (pauliXTreeRealization D₀ j₀ realize value quantum)
            selectors i (pauliXTree_compatible value quantum selectors i),
          pauliXTree_realized_eq_ofOperation]
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      rw [embed_of_pauliX_tree D₀ j₀ realize value quantum tree R selectors i]

/-- Closed measure-Z primitives satisfy channel-tree completeness exactly. -/
theorem measureZ_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (zeroValue oneValue : C) (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.prim (.measureZ zeroValue oneValue)) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.prim (.measureZ zeroValue oneValue)) semanticEnv) where
  selected_result_eq_channelTree_sup := by
    intro selectors i k
    have hdenote :
        interp (hardwarePrimitive D₀ j₀ realize)
            (.prim (.measureZ zeroValue oneValue)) semanticEnv =
          taggedEmbed (Qubit.measureZComp.map
            (fun b => if b then realize oneValue else realize zeroValue)) := by
      simp [hardwarePrimitive_measureZ]
    rw [hdenote, selectPath_taggedEmbed, taggedEmbed_apply]
    refine le_antisymm ?_ ?_
    · apply le_sSup
      refine ⟨1, measurementTree zeroValue oneValue quantum,
        measurementTreeRealization D₀ j₀ realize zeroValue oneValue quantum,
        ?_, ?_⟩
      · simp [measurementTree_depth]
      · rw [embed_restricted_of_all_compatible D₀ j₀ realize
            (measurementTree zeroValue oneValue quantum)
            (measurementTreeRealization D₀ j₀ realize
              zeroValue oneValue quantum)
            selectors i
            (measurementTree_compatible zeroValue oneValue quantum
              selectors i),
          measurementTree_realized_eq_measureZ]
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      rw [embed_of_measureZ_tree D₀ j₀ realize zeroValue oneValue quantum
        tree R selectors i]

/-- A closed internal choice between two returns is the supremum of its two
one-sided completing channel trees. -/
theorem intern_returns_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (leftValue rightValue : C) (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.intern (.prim (.ret leftValue)) (.prim (.ret rightValue))) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.intern (.prim (.ret leftValue)) (.prim (.ret rightValue)))
        semanticEnv) where
  selected_result_eq_channelTree_sup := by
    intro selectors i k
    let leftResult :=
      embed (FiniteInstrumentComp.unit (n := 2) (realize leftValue)) k
    let rightResult :=
      embed (FiniteInstrumentComp.unit (n := 2) (realize rightValue)) k
    have hselected :
        HardwareAdequacy.selectPath selectors
            (interp (hardwarePrimitive D₀ j₀ realize)
              (.intern (.prim (.ret leftValue)) (.prim (.ret rightValue)))
              semanticEnv) i k =
          leftResult ⊔ rightResult := by
      rw [interp_intern_apply, HardwareAdequacy.selectPath_apply_encode,
        TTContinuation.computation_intern_apply,
        TTContinuation.internalChoice_apply, interp_prim_apply,
        interp_prim_apply, hardwarePrimitive_ret, hardwarePrimitive_ret]
      rw [← taggedEmbed_unit (n := 2) (realize leftValue),
        ← taggedEmbed_unit (n := 2) (realize rightValue)]
      rfl
    rw [hselected]
    refine le_antisymm ?_ ?_
    · apply sup_le
      · apply le_sSup
        refine ⟨2, internReturnLeftTree leftValue rightValue quantum,
          internReturnLeftTreeRealization D₀ j₀ realize
            leftValue rightValue quantum, ?_, ?_⟩
        · simp [internReturnLeftTree_depth]
        · rw [embed_restricted_of_all_compatible D₀ j₀ realize
              (internReturnLeftTree leftValue rightValue quantum)
              (internReturnLeftTreeRealization D₀ j₀ realize
                leftValue rightValue quantum)
              selectors i
              (internReturnLeftTree_compatible leftValue rightValue quantum
                selectors i),
            internReturnLeftTree_realized_eq_unit]
      · apply le_sSup
        refine ⟨2, internReturnRightTree leftValue rightValue quantum,
          internReturnRightTreeRealization D₀ j₀ realize
            leftValue rightValue quantum, ?_, ?_⟩
        · simp [internReturnRightTree_depth]
        · rw [embed_restricted_of_all_compatible D₀ j₀ realize
              (internReturnRightTree leftValue rightValue quantum)
              (internReturnRightTreeRealization D₀ j₀ realize
                leftValue rightValue quantum)
              selectors i
              (internReturnRightTree_compatible leftValue rightValue quantum
                selectors i),
            internReturnRightTree_realized_eq_unit]
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      rcases embed_of_intern_returns_tree D₀ j₀ realize
          leftValue rightValue quantum tree R selectors i with hleft | hright
      · rw [hleft]
        exact le_sup_left
      · rw [hright]
        exact le_sup_right

/-- The first intern step is a classical identity operation. -/
theorem channelInternalOperation_intern {C : Type}
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2) :
    channelInternalOperation
      (initialChannelConfig (.intern left right) quantum) =
      QuantumOperation.identity 2 :=
  rfl

theorem initialChannelConfig_intern_left {C : Type}
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2) :
    { initialChannelConfig (.intern left right) quantum with
        control := .term left } =
      initialChannelConfig left quantum :=
  rfl

theorem initialChannelConfig_intern_right {C : Type}
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2) :
    { initialChannelConfig (.intern left right) quantum with
        control := .term right } =
      initialChannelConfig right quantum :=
  rfl

/-- Wrap a completed left child as one intern branch. -/
def wrapInternLeft {C : Type}
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (child : ChannelTree C (initialChannelConfig left quantum)) :
    ChannelTree C (initialChannelConfig (.intern left right) quantum) :=
  ChannelTree.internal
    (ChannelInternalStep.internalLeft
      (s := initialChannelConfig (.intern left right) quantum))
    child

/-- Wrap a completed right child as one intern branch. -/
def wrapInternRight {C : Type}
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (child : ChannelTree C (initialChannelConfig right quantum)) :
    ChannelTree C (initialChannelConfig (.intern left right) quantum) :=
  ChannelTree.internal
    (ChannelInternalStep.internalRight
      (s := initialChannelConfig (.intern left right) quantum))
    child

theorem wrapInternLeft_depth {C : Type}
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (child : ChannelTree C (initialChannelConfig left quantum)) :
    (wrapInternLeft left right quantum child).depth = child.depth + 1 :=
  rfl

theorem wrapInternRight_depth {C : Type}
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (child : ChannelTree C (initialChannelConfig right quantum)) :
    (wrapInternRight left right quantum child).depth = child.depth + 1 :=
  rfl

/-- Drop the administrative intern node from a realization. -/
noncomputable def internalChildRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} (h : ChannelInternalStep s t)
    (next : ChannelTree C t)
    (R : ChannelTreeRealization D₀ j₀ realize (ChannelTree.internal h next)) :
    ChannelTreeRealization D₀ j₀ realize next where
  value := R.value
  related := fun o => R.related ⟨⟨⟩, o⟩

/-- Lift a child realization across an administrative intern node. -/
noncomputable def wrapInternalRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} (h : ChannelInternalStep s t)
    (next : ChannelTree C t)
    (R : ChannelTreeRealization D₀ j₀ realize next) :
    ChannelTreeRealization D₀ j₀ realize (ChannelTree.internal h next) where
  value := R.value
  related := fun p => R.related p.2

/-- An identity internal step is only a unit-sigma reindexing of outcomes. -/
theorem embed_restricted_internal_of_identity {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} (h : ChannelInternalStep s t)
    (hop : channelInternalOperation s = QuantumOperation.identity 2)
    (next : ChannelTree C t)
    (R : ChannelTreeRealization D₀ j₀ realize (ChannelTree.internal h next))
    (selectors : List Bool) (i : ℕ) :
    embed (restrictedInstrument D₀ j₀ realize
        (ChannelTree.internal h next) R selectors i) =
      embed (restrictedInstrument D₀ j₀ realize next
        (internalChildRealization D₀ j₀ realize h next R) selectors i) := by
  let μ := restrictedInstrument D₀ j₀ realize
    (ChannelTree.internal h next) R selectors i
  let ν := restrictedInstrument D₀ j₀ realize next
    (internalChildRealization D₀ j₀ realize h next R) selectors i
  refine embed_congr_of_outcome_equiv μ ν ?e ?hbranch ?hvalue
  · exact
      { toFun := fun p => ⟨p.1.2, p.2⟩
        invFun := fun q => ⟨⟨⟨⟩, q.1⟩, q.2⟩
        left_inv := by
          intro p
          rcases p with ⟨⟨⟨⟩, o⟩, hp⟩
          rfl
        right_inv := by
          intro q
          rcases q with ⟨o, ho⟩
          rfl }
  · intro p
    change next.instrument.branch p.1.2 =
      KrausFamily.comp (next.instrument.branch p.1.2)
        (channelInternalOperation s).kraus
    rw [hop]
    simp [QuantumOperation.identity]
  · intro p
    rfl

theorem selectPath_intern {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize) (.intern left right)
          semanticEnv) i k =
      HardwareAdequacy.selectPath selectors
          (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv) i k ⊔
        HardwareAdequacy.selectPath selectors
          (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv) i k := by
  rw [interp_intern_apply, HardwareAdequacy.selectPath_apply_encode,
    TTContinuation.computation_intern_apply,
    TTContinuation.internalChoice_apply, HardwareAdequacy.selectPath_apply_encode,
    HardwareAdequacy.selectPath_apply_encode]

/-- Internal choice of any two completed closed terms is the join of their
channel-tree suprema. -/
theorem intern_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hleft : ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig left quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv))
    (hright : ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig right quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)) :
    ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.intern left right) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) (.intern left right)
        semanticEnv) where
  selected_result_eq_channelTree_sup := by
    intro selectors i k
    rw [selectPath_intern, hleft.selected_result_eq_channelTree_sup,
      hright.selected_result_eq_channelTree_sup]
    refine le_antisymm ?_ ?_
    · apply sup_le
      · apply sSup_le
        rintro T ⟨fuel, child, R, hdepth, rfl⟩
        apply le_sSup
        refine ⟨fuel + 1,
          wrapInternLeft left right quantum child,
          wrapInternalRealization D₀ j₀ realize
            (ChannelInternalStep.internalLeft
              (s := initialChannelConfig (.intern left right) quantum)
              (left := left) (right := right))
            child R,
          ?_, ?_⟩
        · simpa [wrapInternLeft_depth] using Nat.succ_le_succ hdepth
        · exact congrArg (fun f => f k)
            (embed_restricted_internal_of_identity D₀ j₀ realize
              (ChannelInternalStep.internalLeft
                (s := initialChannelConfig (.intern left right) quantum)
                (left := left) (right := right))
              (channelInternalOperation_intern left right quantum)
              child
              (wrapInternalRealization D₀ j₀ realize
                (ChannelInternalStep.internalLeft
                  (s := initialChannelConfig (.intern left right) quantum)
                  (left := left) (right := right))
                child R)
              selectors i).symm
      · apply sSup_le
        rintro T ⟨fuel, child, R, hdepth, rfl⟩
        apply le_sSup
        refine ⟨fuel + 1,
          wrapInternRight left right quantum child,
          wrapInternalRealization D₀ j₀ realize
            (ChannelInternalStep.internalRight
              (s := initialChannelConfig (.intern left right) quantum)
              (left := left) (right := right))
            child R,
          ?_, ?_⟩
        · simpa [wrapInternRight_depth] using Nat.succ_le_succ hdepth
        · exact congrArg (fun f => f k)
            (embed_restricted_internal_of_identity D₀ j₀ realize
              (ChannelInternalStep.internalRight
                (s := initialChannelConfig (.intern left right) quantum)
                (left := left) (right := right))
              (channelInternalOperation_intern left right quantum)
              child
              (wrapInternalRealization D₀ j₀ realize
                (ChannelInternalStep.internalRight
                  (s := initialChannelConfig (.intern left right) quantum)
                  (left := left) (right := right))
                child R)
              selectors i).symm
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      have hctrl :
          (initialChannelConfig (.intern left right) quantum).control =
            .term (.intern left right) :=
        rfl
      have hop := channelInternalOperation_intern left right quantum
      cases tree with
      | terminal hterm =>
          have := hterm.control_eq.symm.trans hctrl
          cases this
      | @internal _ t h next =>
          rcases ChannelInternalStep.eq_of_intern h hctrl with ht | ht
          · cases ht
            have := embed_restricted_internal_of_identity D₀ j₀ realize
              h hop next R selectors i
            rw [this]
            apply le_sup_of_le_left
            apply le_sSup
            exact ⟨next.depth,
              next,
              internalChildRealization D₀ j₀ realize h next R,
              le_rfl, rfl⟩
          · cases ht
            have := embed_restricted_internal_of_identity D₀ j₀ realize
              h hop next R selectors i
            rw [this]
            apply le_sup_of_le_right
            apply le_sSup
            exact ⟨next.depth,
              next,
              internalChildRealization D₀ j₀ realize h next R,
              le_rfl, rfl⟩
      | external _ hex _ =>
          exact False.elim (ChannelExternalStep.not_intern hex hctrl)

theorem intern_ret_pauliX_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (leftValue rightValue : C) (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.intern (.prim (.ret leftValue)) (.prim (.pauliX rightValue)))
        quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.intern (.prim (.ret leftValue)) (.prim (.pauliX rightValue)))
        semanticEnv) :=
  intern_channelTreeCompleteness D₀ j₀ realize _ _ quantum semanticEnv
    (return_channelTreeCompleteness D₀ j₀ realize leftValue quantum
      semanticEnv)
    (pauliX_channelTreeCompleteness D₀ j₀ realize rightValue quantum
      semanticEnv)

theorem intern_ret_measureZ_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (leftValue zeroValue oneValue : C) (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.intern (.prim (.ret leftValue))
          (.prim (.measureZ zeroValue oneValue)))
        quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.intern (.prim (.ret leftValue))
          (.prim (.measureZ zeroValue oneValue)))
        semanticEnv) :=
  intern_channelTreeCompleteness D₀ j₀ realize _ _ quantum semanticEnv
    (return_channelTreeCompleteness D₀ j₀ realize leftValue quantum
      semanticEnv)
    (measureZ_channelTreeCompleteness D₀ j₀ realize zeroValue oneValue
      quantum semanticEnv)

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
