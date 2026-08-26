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
@[ext]
structure ChannelConfig (C : Type) where
  control : Control C
  env : RuntimeEnv C
  stack : EvalStack C
  quantum : SubNormalizedDensity 2

/-- The proof-state version of the closed-program CEK invariant. -/
def ChannelConfig.WellScoped {C : Type} (s : ChannelConfig C) : Prop :=
  Control.WellScoped s.env s.control ∧ EvalStack.WellScoped s.stack

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

/-- Observation-indexed relation used by the stacked fundamental theorem.
Unlike `ChannelConfigRel`, it remembers the parent coordinate saved by each
pending frame and relates one final TT observation directly. -/
def PathChannelConfigRel {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C)
    (active : ℕ)
    (observedStack : ObservedStack C)
    (finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (result : TTResult 2) : Prop :=
  observedStack.erase = s.stack ∧
    ∃ current currentK,
      ControlRel D₀ j₀ realize s.control s.env current ∧
      PathStackRel D₀ j₀ realize finalK observedStack currentK ∧
      result = current active currentK

/-- Forget only the normalization proof of an executable configuration. -/
def ofConfig {C : Type} (s : Config C) : ChannelConfig C where
  control := s.control
  env := s.env
  stack := s.stack
  quantum :=
    { mat := s.quantum.mat
      posSemidef := s.quantum.posSemidef
      trace_le_one := by rw [s.quantum.trace_eq_one]; norm_num }

theorem ofConfig_wellScoped {C : Type} {s : Config C}
    (h : Config.WellScoped s) :
    ChannelConfig.WellScoped (ofConfig s) :=
  h

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

@[simp] theorem applyOperation_sourceProbability_one
    (ρ : SubNormalizedDensity 2) :
    applyOperation
      (sourceProbabilityOperation 1 zero_le_one (le_refl 1)) ρ = ρ := by
  apply SubNormalizedDensity.ext
  rw [applyOperation_mat]
  change KrausFamily.applyMat
    (QuantumAction.kraus (.sourceProbability 1)) ρ.mat = ρ.mat
  rw [QuantumAction.apply_sourceProbability 1 zero_le_one ρ.mat]
  simp

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

/-- Proof-semantic administrative steps preserve the same lexical scoping
invariant as executable CEK steps. -/
theorem ChannelInternalStep.preserve_wellScoped {C : Type}
    {s t : ChannelConfig C} (hstep : ChannelInternalStep s t)
    (hscoped : ChannelConfig.WellScoped s) :
    ChannelConfig.WellScoped t := by
  cases hstep with
  | @«variable» base x value hlookup =>
      rcases hscoped with ⟨⟨henv, _⟩, hstack⟩
      exact ⟨⟨henv, henv x value hlookup⟩, hstack⟩
  | @lambda base x body =>
      rcases hscoped with ⟨⟨henv, hcover⟩, hstack⟩
      exact ⟨⟨henv, .closure x body base.env henv hcover⟩, hstack⟩
  | @recursive base self arg body =>
      rcases hscoped with ⟨⟨henv, hcover⟩, hstack⟩
      exact ⟨⟨henv, .recClosure self arg body base.env henv hcover⟩, hstack⟩
  | @application base fn arg =>
      rcases hscoped with ⟨⟨henv, hcover⟩, hstack⟩
      refine ⟨⟨henv, ?_⟩, ?_⟩
      · intro x hx
        exact hcover x (by simp [free, hx])
      · intro frame hframe
        simp only [List.mem_cons] at hframe
        rcases hframe with rfl | hframe
        · refine ⟨henv, ?_⟩
          intro x hx
          exact hcover x (by simp [free, hx])
        · exact hstack frame hframe
  | @evaluateArgument base fn arg callEnv rest =>
      rcases hscoped with ⟨⟨_henv, hfn⟩, hstack⟩
      have hargFrame :
          Frame.WellScoped (.argument arg callEnv) :=
        hstack _ (by simp)
      rcases hargFrame with ⟨hcallEnv, harg⟩
      refine ⟨⟨hcallEnv, harg⟩, ?_⟩
      intro frame hframe
      simp only [List.mem_cons] at hframe
      rcases hframe with rfl | hframe
      · exact hfn
      · exact hstack frame (by simp [hframe])
  | @beta base x body closureEnv arg rest =>
      rcases hscoped with ⟨⟨_henv, harg⟩, hstack⟩
      have hclosureFrame :=
        hstack (.function (.closure x body closureEnv)) (by simp)
      change RuntimeValue.WellScoped (.closure x body closureEnv) at hclosureFrame
      cases hclosureFrame with
      | closure _ _ _ hclosureEnv hfree =>
          have hclosureEnv' : RuntimeEnv.WellScoped closureEnv :=
            hclosureEnv
          refine ⟨⟨RuntimeEnv.WellScoped.bind hclosureEnv' harg, ?_⟩, ?_⟩
          · intro y hy
            by_cases hyx : y = x
            · subst y
              exact ⟨arg, by simp [RuntimeEnv.bind, RuntimeEnv.lookup]⟩
            · obtain ⟨value, hvalue⟩ :=
                hfree y (by simp [free, hy, hyx])
              exact ⟨value, by
                simp [RuntimeEnv.bind, RuntimeEnv.lookup, hyx, hvalue]⟩
          · intro frame hframe
            exact hstack frame (by simp [hframe])
  | @recBeta base self x body closureEnv arg rest =>
      rcases hscoped with ⟨⟨_henv, harg⟩, hstack⟩
      have hrecFrame :=
        hstack (.function (.recClosure self x body closureEnv)) (by simp)
      change RuntimeValue.WellScoped
        (.recClosure self x body closureEnv) at hrecFrame
      cases hrecFrame with
      | recClosure _ _ _ _ hclosureEnv hfree =>
          have hclosureEnv' : RuntimeEnv.WellScoped closureEnv :=
            hclosureEnv
          have hself :
              RuntimeEnv.WellScoped
                (RuntimeEnv.bind self
                  (.recClosure self x body closureEnv) closureEnv) :=
            RuntimeEnv.WellScoped.bind hclosureEnv'
              (.recClosure self x body closureEnv hclosureEnv hfree)
          refine ⟨⟨RuntimeEnv.WellScoped.bind hself harg, ?_⟩, ?_⟩
          · intro y hy
            by_cases hyx : y = x
            · subst y
              exact ⟨arg, by simp [RuntimeEnv.bind, RuntimeEnv.lookup]⟩
            · by_cases hyself : y = self
              · subst y
                exact ⟨.recClosure self x body closureEnv, by
                  simp [RuntimeEnv.bind, RuntimeEnv.lookup, hyx]⟩
              · obtain ⟨value, hvalue⟩ :=
                  hfree y (by simp [free, hy, hyself, hyx])
                exact ⟨value, by
                  simp [RuntimeEnv.bind, RuntimeEnv.lookup, hyx, hyself,
                    hvalue]⟩
          · intro frame hframe
            exact hstack frame (by simp [hframe])
  | @returnPrimitive base value =>
      rcases hscoped with ⟨⟨henv, _⟩, hstack⟩
      exact ⟨⟨henv, .payload value⟩, hstack⟩
  | @pauliXPrimitive base value =>
      rcases hscoped with ⟨⟨henv, _⟩, hstack⟩
      exact ⟨⟨henv, .payload value⟩, hstack⟩
  | @internalLeft base left right =>
      rcases hscoped with ⟨⟨henv, hcover⟩, hstack⟩
      exact ⟨⟨henv, fun x hx => hcover x (by simp [free, hx])⟩, hstack⟩
  | @internalRight base left right =>
      rcases hscoped with ⟨⟨henv, hcover⟩, hstack⟩
      exact ⟨⟨henv, fun x hx => hcover x (by simp [free, hx])⟩, hstack⟩

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

theorem ChannelExternalStep.preserve_wellScoped {C : Type}
    {s t : ChannelConfig C} {selector : Bool}
    (hstep : ChannelExternalStep s selector t)
    (hscoped : ChannelConfig.WellScoped s) :
    ChannelConfig.WellScoped t := by
  cases hstep with
  | @selectFalse base left right =>
      rcases hscoped with ⟨⟨henv, hcover⟩, hstack⟩
      exact ⟨⟨henv, fun x hx => hcover x (by simp [free, hx])⟩, hstack⟩
  | @selectTrue base left right =>
      rcases hscoped with ⟨⟨henv, hcover⟩, hstack⟩
      exact ⟨⟨henv, fun x hx => hcover x (by simp [free, hx])⟩, hstack⟩

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
  physicalPath : List Bool

def prependSelector {C : Type} (b : Bool) (leaf : ChannelLeaf C) :
    ChannelLeaf C :=
  { leaf with selectors := b :: leaf.selectors }

def prependPhysical {C : Type} (b : Bool) (leaf : ChannelLeaf C) :
    ChannelLeaf C :=
  { leaf with physicalPath := b :: leaf.physicalPath }

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
      (hp₀ : 0 < p) (hp₁ : p < 1)
      (leftTree : ChannelTree C
        { s with
          control := .term left
          quantum := applyOperation
            (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum})
      (rightTree : ChannelTree C
        { s with
          control := .term right
          quantum := applyOperation
            (sourceProbabilityOperation (1 - p)
              (sub_nonneg.mpr hp₁.le) (by linarith)) s.quantum}) :
      ChannelTree C {s with control := .term (.prob p left right)}
  | probabilityZero {s : ChannelConfig C}
      {left right : Term (QubitPrimitive C)}
      (rightTree : ChannelTree C
        { s with
          control := .term right
          quantum := applyOperation
            (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
            s.quantum}) :
      ChannelTree C {s with control := .term (.prob 0 left right)}
  | probabilityOne {s : ChannelConfig C}
      {left right : Term (QubitPrimitive C)}
      (leftTree : ChannelTree C
        { s with
          control := .term left
          quantum := applyOperation
            (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
            s.quantum}) :
      ChannelTree C {s with control := .term (.prob 1 left right)}
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
  | .probabilityZero right => right.depth + 1
  | .probabilityOne left => left.depth + 1
  | .measurement zero one => max zero.depth one.depth + 1

/-- Fold every branch of a channel tree into one finite physical instrument. -/
noncomputable def instrument {C : Type} {s : ChannelConfig C} :
    ChannelTree C s → FiniteInstrumentComp 2 (ChannelLeaf C)
  | .terminal h => FiniteInstrumentComp.unit ⟨s, h, [], []⟩
  | .internal _h next =>
      (FiniteInstrumentComp.ofOperation (channelInternalOperation s) ()).bind
        (fun _ => next.instrument)
  | .external selector _h next =>
      next.instrument.map (prependSelector selector)
  | .probability hp₀ hp₁ left right =>
      (probabilityInstrument _ hp₀.le hp₁.le).bind
        (fun b => (if b then right.instrument else left.instrument).map
          (prependPhysical b))
  | .probabilityZero right =>
      right.instrument.map (prependPhysical true)
  | .probabilityOne left =>
      left.instrument.map (prependPhysical false)
  | .measurement zero one =>
      Qubit.measureZComp.bind
        (fun b => if b then one.instrument else zero.instrument)

/-- Every terminal value in a finite tree from a well-scoped source is itself
well scoped.  This is the reachability fact used to make arbitrary leaf
realizations canonical. -/
theorem terminalValues_wellScoped {C : Type} {s : ChannelConfig C}
    (tree : ChannelTree C s) (hscoped : ChannelConfig.WellScoped s) :
    ∀ o : tree.instrument.Outcome,
      RuntimeValue.WellScoped (tree.instrument.value o).isTerminal.value := by
  induction tree with
  | terminal h =>
      intro o
      rcases hscoped with ⟨hcontrol, _⟩
      rw [h.control_eq] at hcontrol
      exact hcontrol.2
  | internal h next ih =>
      rintro ⟨u, o⟩
      exact ih (h.preserve_wellScoped hscoped) o
  | external selector h next ih =>
      intro o
      exact ih (h.preserve_wellScoped hscoped) o
  | @probability source p leftTerm rightTerm hp₀ hp₁ left right ihLeft ihRight =>
      rintro ⟨b, o⟩
      change Bool at b
      rcases hscoped with ⟨⟨henv, hcover⟩, hstack⟩
      cases b
      · apply ihLeft
        exact ⟨⟨henv, fun x hx => hcover x (by simp [free, hx])⟩, hstack⟩
      · apply ihRight
        exact ⟨⟨henv, fun x hx => hcover x (by simp [free, hx])⟩, hstack⟩
  | @probabilityZero source leftTerm rightTerm right ihRight =>
      intro o
      rcases hscoped with ⟨⟨henv, hcover⟩, hstack⟩
      apply ihRight
      exact ⟨⟨henv, fun x hx => hcover x (by simp [free, hx])⟩, hstack⟩
  | @probabilityOne source leftTerm rightTerm left ihLeft =>
      intro o
      rcases hscoped with ⟨⟨henv, hcover⟩, hstack⟩
      apply ihLeft
      exact ⟨⟨henv, fun x hx => hcover x (by simp [free, hx])⟩, hstack⟩
  | @measurement source zeroValue oneValue zero one ihZero ihOne =>
      rintro ⟨b, o⟩
      change Bool at b
      rcases hscoped with ⟨⟨henv, _hcover⟩, hstack⟩
      cases b
      · apply ihZero
        exact ⟨⟨henv, .payload zeroValue⟩, hstack⟩
      · apply ihOne
        exact ⟨⟨henv, .payload oneValue⟩, hstack⟩

/- Every folded branch sends the root proof-state exactly to its leaf
proof-state.  There is no scalar restoration because branch states remain
subnormalized throughout. -/
set_option maxHeartbeats 2000000 in
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
                (sourceProbabilityOperation _ hp₀.le hp₁.le).kraus
                  source.quantum.mat) =
            (left.instrument.value o).terminal.quantum.mat
        rw [← applyOperation_mat]
        exact ihLeft o
      · change
          KrausFamily.applyMat (right.instrument.branch o)
              (KrausFamily.applyMat
                (sourceProbabilityOperation (1 - p)
                  (sub_nonneg.mpr hp₁.le) (by linarith)).kraus
                  source.quantum.mat) =
            (right.instrument.value o).terminal.quantum.mat
        rw [← applyOperation_mat]
        exact ihRight o
  | @probabilityZero source leftTerm rightTerm right ihRight =>
      intro o
      change right.instrument.Outcome at o
      change
        KrausFamily.applyMat (right.instrument.branch o) source.quantum.mat =
          (right.instrument.value o).terminal.quantum.mat
      have hm :
          (applyOperation
            (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
            source.quantum).mat = source.quantum.mat :=
        congrArg SubNormalizedDensity.mat
          (applyOperation_sourceProbability_one source.quantum)
      rw [← hm]
      exact ihRight o
  | @probabilityOne source leftTerm rightTerm left ihLeft =>
      intro o
      change left.instrument.Outcome at o
      change
        KrausFamily.applyMat (left.instrument.branch o) source.quantum.mat =
          (left.instrument.value o).terminal.quantum.mat
      have hm :
          (applyOperation
            (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
            source.quantum).mat = source.quantum.mat :=
        congrArg SubNormalizedDensity.mat
          (applyOperation_sourceProbability_one source.quantum)
      rw [← hm]
      exact ihLeft o
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

theorem instrument_outcome_nonempty {C : Type} {s : ChannelConfig C}
    (tree : ChannelTree C s) : Nonempty tree.instrument.Outcome := by
  induction tree with
  | terminal _ =>
      exact ⟨⟨⟩⟩
  | internal _ next ih =>
      exact ⟨⟨⟨⟩, Classical.choice ih⟩⟩
  | external _ _ next ih =>
      exact ih
  | probability _ _ left right ihLeft ihRight =>
      exact ⟨⟨false, Classical.choice ihLeft⟩⟩
  | probabilityZero right ihRight =>
      exact ihRight
  | probabilityOne left ihLeft =>
      exact ihLeft
  | measurement zero one ihZero ihOne =>
      exact ⟨⟨false, Classical.choice ihZero⟩⟩

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

/-- A well-scoped terminal value makes every admissible leaf realization
canonical, even though `ChannelTreeRealization` itself remains unrestricted. -/
theorem ChannelTreeRealization.value_eq_of_wellScoped {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {start : ChannelConfig C} {tree : ChannelTree C start}
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (o : tree.instrument.Outcome)
    (hscoped : RuntimeValue.WellScoped
      (tree.instrument.value o).isTerminal.value)
    {d : HSemanticValue D₀ j₀}
    (hd : ValueRel D₀ j₀ realize
      (tree.instrument.value o).isTerminal.value d) :
    R.value (tree.instrument.value o) = d :=
  valueRel_functional D₀ j₀ realize hscoped (R.related o) hd

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

/-- Availability of a complete semantic observation at one combined external
path. Interior physical choices require both children; exact endpoints require
only the nonzero child. -/
def resultAvailableAt {C : Type} {start : ChannelConfig C} :
    (tree : ChannelTree C start) → List Bool → Prop
  | .terminal _, _ => True
  | .internal _ next, path => resultAvailableAt next path
  | .external b _ next, path =>
      ∃ rest, path = b :: rest ∧ resultAvailableAt next rest
  | .probability _ _ left right, path =>
      resultAvailableAt left path ∧ resultAvailableAt right path
  | .probabilityZero right, path => resultAvailableAt right path
  | .probabilityOne left, path => resultAvailableAt left path
  | .measurement zero one, path =>
      resultAvailableAt zero path ∧ resultAvailableAt one path

def ResultAvailable {C : Type} {start : ChannelConfig C}
    (tree : ChannelTree C start) (selectors : List Bool) (i : ℕ) : Prop :=
  resultAvailableAt tree (selectors ++ HardwareAdequacy.coordinatePath i)

/-- Explicit selectors and the residual coordinate determine exactly the
same compatible leaves as their single encoded coordinate. -/
theorem outcomeCompatible_encodePath {C : Type}
    {start : ChannelConfig C} (tree : ChannelTree C start)
    (selectors : List Bool) (i : ℕ) (o : tree.instrument.Outcome) :
    OutcomeCompatible tree selectors i o ↔
      OutcomeCompatible tree [] (HardwareAdequacy.encodePath selectors i) o := by
  simp [OutcomeCompatible, HardwareAdequacy.coordinatePath_encodePath]

/-- Result availability depends only on the combined encoded path. -/
theorem resultAvailable_encodePath {C : Type}
    {start : ChannelConfig C} (tree : ChannelTree C start)
    (selectors : List Bool) (i : ℕ) :
    ResultAvailable tree selectors i ↔
      ResultAvailable tree [] (HardwareAdequacy.encodePath selectors i) := by
  simp [ResultAvailable, HardwareAdequacy.coordinatePath_encodePath]

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

/-- Physical embedding of a coordinate restriction is invariant under
combining explicit selectors with the residual heap coordinate.  The two
finite instruments differ only by a proof-subtype reindexing. -/
theorem embed_restrictedInstrument_encodePath {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {start : ChannelConfig C} (tree : ChannelTree C start)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ) :
    embed (restrictedInstrument D₀ j₀ realize tree R selectors i) =
      embed (restrictedInstrument D₀ j₀ realize tree R []
        (HardwareAdequacy.encodePath selectors i)) := by
  classical
  let μ := restrictedInstrument D₀ j₀ realize tree R selectors i
  let ν := restrictedInstrument D₀ j₀ realize tree R []
    (HardwareAdequacy.encodePath selectors i)
  let e : μ.Outcome ≃ ν.Outcome :=
    { toFun := fun o => ⟨o.1,
        (outcomeCompatible_encodePath tree selectors i o.1).mp o.2⟩
      invFun := fun o => ⟨o.1,
        (outcomeCompatible_encodePath tree selectors i o.1).mpr o.2⟩
      left_inv := by rintro ⟨o, ho⟩; rfl
      right_inv := by rintro ⟨o, ho⟩; rfl }
  apply embed_congr_of_outcome_equiv μ ν e
  · intro o
    rfl
  · intro o
    rfl

/-- A coordinate with no compatible completed outcome is unresolved and
contributes lattice bottom, rather than the non-bottom vacuous TT theory of an
empty physical instrument. -/
noncomputable def restrictedResult {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {start : ChannelConfig C} (tree : ChannelTree C start)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    TTResult 2 := by
  classical
  exact
    if ResultAvailable tree selectors i
    then embed (restrictedInstrument D₀ j₀ realize tree R selectors i) k
    else ⊥

/-- Restricted results admit the same selector-to-coordinate normalization
as their underlying instruments. -/
theorem restrictedResult_encodePath {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {start : ChannelConfig C} (tree : ChannelTree C start)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    restrictedResult D₀ j₀ realize tree R selectors i k =
      restrictedResult D₀ j₀ realize tree R []
        (HardwareAdequacy.encodePath selectors i) k := by
  classical
  unfold restrictedResult
  apply if_congr (resultAvailable_encodePath tree selectors i)
  · exact congrArg
      (fun f : ScottMap
        (ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) (TTResult 2) => f k)
      (embed_restrictedInstrument_encodePath D₀ j₀ realize tree R selectors i)
  · rfl

theorem restrictedResult_eq_embed {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {start : ChannelConfig C} (tree : ChannelTree C start)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (havail : ResultAvailable tree selectors i) :
    restrictedResult D₀ j₀ realize tree R selectors i k =
      embed (restrictedInstrument D₀ j₀ realize tree R selectors i) k := by
  simp [restrictedResult, havail]

theorem restrictedResult_eq_bot {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {start : ChannelConfig C} (tree : ChannelTree C start)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hunavailable : ¬ ResultAvailable tree selectors i) :
    restrictedResult D₀ j₀ realize tree R selectors i k = ⊥ := by
  simp [restrictedResult, hunavailable]

theorem restrictedResult_le_embed {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {start : ChannelConfig C} (tree : ChannelTree C start)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    restrictedResult D₀ j₀ realize tree R selectors i k ≤
      embed (restrictedInstrument D₀ j₀ realize tree R selectors i) k := by
  classical
  by_cases havail : ResultAvailable tree selectors i
  · rw [restrictedResult_eq_embed D₀ j₀ realize tree R selectors i k havail]
  · rw [restrictedResult_eq_bot D₀ j₀ realize tree R selectors i k havail]
    exact bot_le

theorem restrictedOutcome_nonempty_of_all_compatible {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {start : ChannelConfig C} (tree : ChannelTree C start)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ)
    (hall : ∀ o, OutcomeCompatible tree selectors i o) :
    Nonempty
      (restrictedInstrument D₀ j₀ realize tree R selectors i).Outcome := by
  obtain ⟨o⟩ := tree.instrument_outcome_nonempty
  exact ⟨⟨o, hall o⟩⟩

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
      T = restrictedResult D₀ j₀ realize tree R selectors i k}

theorem channelTreeResults_encodePath {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (start : ChannelConfig C) (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    channelTreeResults D₀ j₀ realize start selectors i k =
      channelTreeResults D₀ j₀ realize start []
        (HardwareAdequacy.encodePath selectors i) k := by
  ext T
  constructor
  · rintro ⟨fuel, tree, R, hdepth, rfl⟩
    exact ⟨fuel, tree, R, hdepth,
      restrictedResult_encodePath D₀ j₀ realize tree R selectors i k⟩
  · rintro ⟨fuel, tree, R, hdepth, rfl⟩
    exact ⟨fuel, tree, R, hdepth,
      (restrictedResult_encodePath D₀ j₀ realize tree R selectors i k).symm⟩

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

/-- Completeness at the sound finitely-presented continuation boundary.
Unlike `ChannelTreeCompleteness`, this interface only asks for continuations
whose value observations are represented by finite physical instruments. -/
structure PresentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (start : ChannelConfig C) (denotation : HSemanticComp D₀ j₀) : Prop where
  selected_result_eq_channelTree_sup_presented :
    ∀ selectors i
      (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
      (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)),
      (∀ d, k d = (ξ d).satisfiedTTTheory resultCode) →
      HardwareAdequacy.selectPath selectors denotation i k =
        sSup (channelTreeResults D₀ j₀ realize start selectors i k)

/-- Coordinate-only form proved by the path-indexed fundamental theorem.
Explicit selector lists are recovered by `encodePath`. -/
structure CoordinatePresentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (start : ChannelConfig C) (denotation : HSemanticComp D₀ j₀) : Prop where
  coordinate_result_eq_channelTree_sup_presented :
    ∀ i
      (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
      (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)),
      (∀ d, k d = (ξ d).satisfiedTTTheory resultCode) →
      denotation i k =
        sSup (channelTreeResults D₀ j₀ realize start [] i k)

theorem CoordinatePresentedChannelTreeCompleteness.toPresented {C : Type}
    {D₀ : QDomain.{0}}
    {j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier)}
    {realize : C → HSemanticValue D₀ j₀}
    {start : ChannelConfig C} {denotation : HSemanticComp D₀ j₀}
    (h : CoordinatePresentedChannelTreeCompleteness D₀ j₀ realize
      start denotation) :
    PresentedChannelTreeCompleteness D₀ j₀ realize start denotation where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ k hk
    rw [HardwareAdequacy.selectPath_apply_encode,
      h.coordinate_result_eq_channelTree_sup_presented
        (HardwareAdequacy.encodePath selectors i) ξ k hk,
      ← channelTreeResults_encodePath D₀ j₀ realize start selectors i k]

/-- The packaged statement used by the stacked fundamental lemma: the CEK
state denotes `denotation`, and finite channel trees are complete for every
finitely represented final continuation. -/
structure PresentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (start : ChannelConfig C) (denotation : HSemanticComp D₀ j₀) : Prop where
  related : ChannelConfigRel D₀ j₀ realize start denotation
  complete : PresentedChannelTreeCompleteness D₀ j₀ realize start denotation

/-- One realized channel tree is pointwise below its denotation. -/
structure ChannelTreePointwiseSound {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {start : ChannelConfig C} (denotation : HSemanticComp D₀ j₀)
    (tree : ChannelTree C start)
    (R : ChannelTreeRealization D₀ j₀ realize tree) : Prop where
  restricted_le_selected :
    ∀ selectors i k,
      restrictedResult D₀ j₀ realize tree R selectors i k ≤
        HardwareAdequacy.selectPath selectors denotation i k

/-- Pointwise soundness at the finitely-presented continuation boundary. -/
structure PresentedChannelTreePointwiseSound {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {start : ChannelConfig C} (denotation : HSemanticComp D₀ j₀)
    (tree : ChannelTree C start)
    (R : ChannelTreeRealization D₀ j₀ realize tree) : Prop where
  restricted_le_selected_presented :
    ∀ selectors i
      (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
      (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)),
      (∀ d, k d = (ξ d).satisfiedTTTheory resultCode) →
      restrictedResult D₀ j₀ realize tree R selectors i k ≤
        HardwareAdequacy.selectPath selectors denotation i k

/-- Global one-sided soundness of all finite channel trees. -/
structure ChannelOperationalSoundness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (start : ChannelConfig C) (denotation : HSemanticComp D₀ j₀) : Prop where
  tree_pointwise :
    ∀ (tree : ChannelTree C start)
      (R : ChannelTreeRealization D₀ j₀ realize tree),
      ChannelTreePointwiseSound D₀ j₀ realize denotation tree R

/-- Global one-sided soundness at represented final continuations. -/
structure PresentedChannelOperationalSoundness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (start : ChannelConfig C) (denotation : HSemanticComp D₀ j₀) : Prop where
  tree_pointwise :
    ∀ (tree : ChannelTree C start)
      (R : ChannelTreeRealization D₀ j₀ realize tree),
      PresentedChannelTreePointwiseSound D₀ j₀ realize denotation tree R

/-- Exact completeness implies completeness at every finitely-presented
continuation. -/
theorem ChannelTreeCompleteness.toPresented {C : Type}
    {D₀ : QDomain.{0}}
    {j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier)}
    {realize : C → HSemanticValue D₀ j₀}
    {start : ChannelConfig C} {denotation : HSemanticComp D₀ j₀}
    (h : ChannelTreeCompleteness D₀ j₀ realize start denotation) :
    PresentedChannelTreeCompleteness D₀ j₀ realize start denotation where
  selected_result_eq_channelTree_sup_presented :=
    fun selectors i _ξ k _hk =>
      h.selected_result_eq_channelTree_sup selectors i k

/-- Exact channel-tree completeness contains its one-sided soundness half. -/
theorem ChannelTreeCompleteness.toSoundness {C : Type}
    {D₀ : QDomain.{0}}
    {j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier)}
    {realize : C → HSemanticValue D₀ j₀}
    {start : ChannelConfig C} {denotation : HSemanticComp D₀ j₀}
    (h : ChannelTreeCompleteness D₀ j₀ realize start denotation) :
    ChannelOperationalSoundness D₀ j₀ realize start denotation where
  tree_pointwise := by
    intro tree R
    constructor
    intro selectors i k
    rw [h.selected_result_eq_channelTree_sup selectors i k]
    apply le_sSup
    exact ⟨tree.depth, tree, R, le_rfl, rfl⟩

/-- Presented completeness likewise contains represented-continuation
soundness. -/
theorem PresentedChannelTreeCompleteness.toSoundness {C : Type}
    {D₀ : QDomain.{0}}
    {j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier)}
    {realize : C → HSemanticValue D₀ j₀}
    {start : ChannelConfig C} {denotation : HSemanticComp D₀ j₀}
    (h : PresentedChannelTreeCompleteness D₀ j₀ realize start denotation) :
    PresentedChannelOperationalSoundness D₀ j₀ realize start denotation where
  tree_pointwise := by
    intro tree R
    constructor
    intro selectors i ξ k hk
    rw [h.selected_result_eq_channelTree_sup_presented selectors i ξ k hk]
    apply le_sSup
    exact ⟨tree.depth, tree, R, le_rfl, rfl⟩

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

theorem initialChannelConfig_wellScoped {C : Type}
    {code : Term (QubitPrimitive C)} (hclosed : Closed code)
    (quantum : NormalizedDensity 2) :
    ChannelConfig.WellScoped (initialChannelConfig code quantum) :=
  ofConfig_wellScoped (initialConfig_wellScoped hclosed quantum)

/-- The initial state also satisfies the observation-indexed relation at any
encoded path and finitely presented final continuation. -/
theorem initialPathChannelConfig_related {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (active : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    PathChannelConfigRel D₀ j₀ realize
      (initialChannelConfig code quantum) active [] k
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv active k) := by
  refine ⟨rfl, interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv,
    k, ?_, PathStackRel.nil, rfl⟩
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

/-- A well-scoped related terminal tree realizes exactly the deterministic
semantic return selected by the logical relation. -/
theorem terminal_realized_eq_unit {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} (hterminal : ChannelTerminal s)
    (hscoped : ChannelConfig.WellScoped s)
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize s answer)
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.terminal hterminal)) :
    ∃ d : HSemanticValue D₀ j₀,
      answer = semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) d ∧
      embed (realizedInstrument D₀ j₀ realize
        (ChannelTree.terminal hterminal) R) =
        embed (FiniteInstrumentComp.unit (n := 2) d) := by
  obtain ⟨d, hd, hanswer⟩ := terminal_related D₀ j₀ hterminal hrel
  refine ⟨d, hanswer, ?_⟩
  let μ := realizedInstrument D₀ j₀ realize
    (ChannelTree.terminal hterminal) R
  letI : Unique μ.Outcome :=
    { default := ⟨⟩
      uniq := by intro o; rcases o with ⟨⟩; rfl }
  refine embed_eq_unit_of_unique μ d ?_ ?_
  · intro o
    rcases o with ⟨⟩
    change R.value ⟨s, hterminal, [], []⟩ = d
    have hvalueScoped : RuntimeValue.WellScoped hterminal.value := by
      rcases hscoped with ⟨hcontrol, _⟩
      rw [hterminal.control_eq] at hcontrol
      exact hcontrol.2
    exact valueRel_functional D₀ j₀ realize hvalueScoped (R.related ⟨⟩) hd
  · intro o
    rcases o with ⟨⟩
    rfl

/-- Terminal channel trees satisfy pointwise soundness with equality. -/
theorem terminal_channelTreePointwiseSound {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} (hterminal : ChannelTerminal s)
    (hscoped : ChannelConfig.WellScoped s)
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize s answer)
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.terminal hterminal)) :
    ChannelTreePointwiseSound D₀ j₀ realize answer
      (ChannelTree.terminal hterminal) R := by
  obtain ⟨d, hanswer, hrealized⟩ :=
    terminal_realized_eq_unit D₀ j₀ hterminal hscoped hrel R
  constructor
  intro selectors i k
  have hall : ∀ o, OutcomeCompatible
      (ChannelTree.terminal hterminal) selectors i o := by
    intro o
    rcases o with ⟨⟩
    exact List.nil_prefix
  rw [restrictedResult_eq_embed D₀ j₀ realize
    (ChannelTree.terminal hterminal) R selectors i k (by
      simp [ResultAvailable, resultAvailableAt])]
  rw [congrArg (fun f : ScottMap
      (ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) (TTResult 2) => f k)
    (embed_restricted_of_all_compatible D₀ j₀ realize
      (ChannelTree.terminal hterminal) R selectors i hall)]
  rw [hrealized, embed_unit, hanswer,
    HardwareAdequacy.selectPath_apply_encode]
  rfl

/-- A well-scoped related terminal tree realizes the denotation exactly,
not merely as an upper bound. -/
theorem terminal_restrictedResult_eq {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} (hterminal : ChannelTerminal s)
    (hscoped : ChannelConfig.WellScoped s)
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize s answer)
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.terminal hterminal))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    restrictedResult D₀ j₀ realize
        (ChannelTree.terminal hterminal) R selectors i k =
      HardwareAdequacy.selectPath selectors answer i k := by
  obtain ⟨d, hanswer, hrealized⟩ :=
    terminal_realized_eq_unit D₀ j₀ hterminal hscoped hrel R
  have hall : ∀ o, OutcomeCompatible
      (ChannelTree.terminal hterminal) selectors i o := by
    intro o
    rcases o with ⟨⟩
    exact List.nil_prefix
  rw [restrictedResult_eq_embed D₀ j₀ realize
    (ChannelTree.terminal hterminal) R selectors i k (by
      simp [ResultAvailable, resultAvailableAt])]
  rw [congrArg (fun f : ScottMap
      (ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) (TTResult 2) => f k)
    (embed_restricted_of_all_compatible D₀ j₀ realize
      (ChannelTree.terminal hterminal) R selectors i hall)]
  rw [hrealized, embed_unit, hanswer,
    HardwareAdequacy.selectPath_apply_encode]
  rfl

/-- Canonical realization of a related terminal value. -/
noncomputable def terminalValueRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} (hterminal : ChannelTerminal s)
    {d : HSemanticValue D₀ j₀}
    (hd : ValueRel D₀ j₀ realize hterminal.value d) :
    ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.terminal hterminal) where
  value := fun _ => d
  related := by
    intro o
    rcases o with ⟨⟩
    exact hd

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

theorem ChannelInternalStep.not_extern {C : Type}
    {s t : ChannelConfig C} {left right : Term (QubitPrimitive C)}
    (h : ChannelInternalStep s t)
    (hc : s.control = .term (.extern left right)) : False := by
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

theorem ChannelInternalStep.eq_of_application {C : Type}
    {s t : ChannelConfig C} {fn arg : Term (QubitPrimitive C)}
    (h : ChannelInternalStep s t)
    (hc : s.control = .term (.app fn arg)) :
    t = { s with
      control := .term fn
      stack := .argument arg s.env :: s.stack } := by
  cases h <;> cases hc
  rfl

theorem ChannelInternalStep.eq_of_lambda {C : Type}
    {s t : ChannelConfig C} {x : Name} {body : Term (QubitPrimitive C)}
    (h : ChannelInternalStep s t)
    (hc : s.control = .term (.lam x body)) :
    t = { s with control := .value (.closure x body s.env) } := by
  cases h <;> cases hc
  rfl

theorem ChannelInternalStep.eq_of_recursive {C : Type}
    {s t : ChannelConfig C} {self arg : Name}
    {body : Term (QubitPrimitive C)}
    (h : ChannelInternalStep s t)
    (hc : s.control = .term (.recLam self arg body)) :
    t = { s with
      control := .value (.recClosure self arg body s.env) } := by
  cases h <;> cases hc
  rfl

theorem ChannelInternalStep.eq_of_evaluateArgument {C : Type}
    {s t : ChannelConfig C} {fn : RuntimeValue C}
    {arg : Term (QubitPrimitive C)} {callEnv : RuntimeEnv C}
    {rest : EvalStack C}
    (h : ChannelInternalStep s t)
    (hc : s.control = .value fn)
    (hs : s.stack = .argument arg callEnv :: rest) :
    t = { s with
      control := .term arg
      env := callEnv
      stack := .function fn :: rest } := by
  cases h with
  | evaluateArgument =>
      cases hc
      cases hs
      rfl
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

theorem ChannelInternalStep.eq_of_beta {C : Type}
    {s t : ChannelConfig C} {x : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    {arg : RuntimeValue C} {rest : EvalStack C}
    (h : ChannelInternalStep s t)
    (hc : s.control = .value arg)
    (hs : s.stack = .function (.closure x body closureEnv) :: rest) :
    t = { s with
      control := .term body
      env := RuntimeEnv.bind x arg closureEnv
      stack := rest } := by
  cases h with
  | beta =>
      cases hc
      cases hs
      rfl
  | evaluateArgument => cases hs
  | recBeta => cases hs
  | returnPrimitive => cases hc
  | pauliXPrimitive => cases hc
  | lambda => cases hc
  | recursive => cases hc
  | application => cases hc
  | internalLeft => cases hc
  | internalRight => cases hc
  | «variable» => cases hc

theorem ChannelInternalStep.eq_of_recBeta {C : Type}
    {s t : ChannelConfig C} {self x : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    {arg : RuntimeValue C} {rest : EvalStack C}
    (h : ChannelInternalStep s t)
    (hc : s.control = .value arg)
    (hs : s.stack =
      .function (.recClosure self x body closureEnv) :: rest) :
    t = { s with
      control := .term body
      env :=
        RuntimeEnv.bind x arg
          (RuntimeEnv.bind self
            (.recClosure self x body closureEnv) closureEnv)
      stack := rest } := by
  cases h with
  | recBeta =>
      cases hc
      cases hs
      rfl
  | evaluateArgument => cases hs
  | beta => cases hs
  | returnPrimitive => cases hc
  | pauliXPrimitive => cases hc
  | lambda => cases hc
  | recursive => cases hc
  | application => cases hc
  | internalLeft => cases hc
  | internalRight => cases hc
  | «variable» => cases hc

theorem ChannelInternalStep.eq_of_variable {C : Type}
    {s t : ChannelConfig C} {x : Name} {v : RuntimeValue C}
    (h : ChannelInternalStep s t)
    (hc : s.control = .term (.var x))
    (hlookup : RuntimeEnv.lookup x s.env = some v) :
    t = { s with control := .value v } := by
  cases h <;> cases hc
  · rename_i hlook
    rw [hlookup] at hlook
    injection hlook with hv
    subst hv
    rfl

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

theorem ChannelExternalStep.eq_of_extern {C : Type}
    {s t : ChannelConfig C} {b : Bool}
    {left right : Term (QubitPrimitive C)}
    (h : ChannelExternalStep s b t)
    (hc : s.control = .term (.extern left right)) :
    t = {s with control := .term (if b then right else left)} := by
  cases h <;> cases hc <;> rfl

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
      | probabilityZero _ => cases hnextctrl
      | probabilityOne _ => cases hnextctrl
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
      | probabilityZero _ => cases hnextctrl
      | probabilityOne _ => cases hnextctrl
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
  | probabilityZero _ =>
      cases hctrl
  | probabilityOne _ =>
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
            | probabilityZero _ => cases hfinalctrl
            | probabilityOne _ => cases hfinalctrl
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
            | probabilityZero _ => cases hfinalctrl
            | probabilityOne _ => cases hfinalctrl
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
      · rw [restrictedResult_eq_embed D₀ j₀ realize
            (returnTree value quantum)
            (returnTreeRealization D₀ j₀ realize value quantum)
            selectors i k
            (by simp [ResultAvailable, resultAvailableAt, returnTree]),
          embed_restricted_of_all_compatible D₀ j₀ realize
            (returnTree value quantum)
            (returnTreeRealization D₀ j₀ realize value quantum)
            selectors i (returnTree_compatible value quantum selectors i),
          returnTree_realized_eq_unit]
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      exact (restrictedResult_le_embed D₀ j₀ realize tree R selectors i k).trans_eq
        (congrArg (fun f => f k)
          (embed_of_ret_tree D₀ j₀ realize value quantum tree R selectors i))

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
      · rw [restrictedResult_eq_embed D₀ j₀ realize
            (pauliXTree value quantum)
            (pauliXTreeRealization D₀ j₀ realize value quantum)
            selectors i k
            (by simp [ResultAvailable, resultAvailableAt, pauliXTree]),
          embed_restricted_of_all_compatible D₀ j₀ realize
            (pauliXTree value quantum)
            (pauliXTreeRealization D₀ j₀ realize value quantum)
            selectors i (pauliXTree_compatible value quantum selectors i),
          pauliXTree_realized_eq_ofOperation]
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      exact (restrictedResult_le_embed D₀ j₀ realize tree R selectors i k).trans_eq
        (congrArg (fun f => f k)
          (embed_of_pauliX_tree D₀ j₀ realize value quantum tree R selectors i))

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
      · rw [restrictedResult_eq_embed D₀ j₀ realize
            (measurementTree zeroValue oneValue quantum)
            (measurementTreeRealization D₀ j₀ realize
              zeroValue oneValue quantum)
            selectors i k
            (by simp [ResultAvailable, resultAvailableAt, measurementTree]),
          embed_restricted_of_all_compatible D₀ j₀ realize
            (measurementTree zeroValue oneValue quantum)
            (measurementTreeRealization D₀ j₀ realize
              zeroValue oneValue quantum)
            selectors i
            (measurementTree_compatible zeroValue oneValue quantum
              selectors i),
          measurementTree_realized_eq_measureZ]
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      exact (restrictedResult_le_embed D₀ j₀ realize tree R selectors i k).trans_eq
        (congrArg (fun f => f k)
          (embed_of_measureZ_tree D₀ j₀ realize zeroValue oneValue quantum
            tree R selectors i))

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
        · rw [restrictedResult_eq_embed D₀ j₀ realize
              (internReturnLeftTree leftValue rightValue quantum)
              (internReturnLeftTreeRealization D₀ j₀ realize
                leftValue rightValue quantum)
              selectors i k
              (by simp [ResultAvailable, resultAvailableAt,
                internReturnLeftTree, returnTree]),
            embed_restricted_of_all_compatible D₀ j₀ realize
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
        · rw [restrictedResult_eq_embed D₀ j₀ realize
              (internReturnRightTree leftValue rightValue quantum)
              (internReturnRightTreeRealization D₀ j₀ realize
                leftValue rightValue quantum)
              selectors i k
              (by simp [ResultAvailable, resultAvailableAt,
                internReturnRightTree, returnTree]),
            embed_restricted_of_all_compatible D₀ j₀ realize
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
      · exact (restrictedResult_le_embed D₀ j₀ realize tree R selectors i k).trans
          ((congrArg (fun f => f k) hleft).le.trans le_sup_left)
      · exact (restrictedResult_le_embed D₀ j₀ realize tree R selectors i k).trans
          ((congrArg (fun f => f k) hright).le.trans le_sup_right)

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

theorem restrictedResult_internal_of_identity {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} (h : ChannelInternalStep s t)
    (hop : channelInternalOperation s = QuantumOperation.identity 2)
    (next : ChannelTree C t)
    (R : ChannelTreeRealization D₀ j₀ realize (ChannelTree.internal h next))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    restrictedResult D₀ j₀ realize
        (ChannelTree.internal h next) R selectors i k =
      restrictedResult D₀ j₀ realize next
        (internalChildRealization D₀ j₀ realize h next R) selectors i k := by
  classical
  let childR := internalChildRealization D₀ j₀ realize h next R
  have havail_iff :
      ResultAvailable (ChannelTree.internal h next) selectors i ↔
        ResultAvailable next selectors i := by
    rfl
  by_cases havail :
      ResultAvailable (ChannelTree.internal h next) selectors i
  · rw [restrictedResult_eq_embed D₀ j₀ realize
          (ChannelTree.internal h next) R selectors i k havail,
        restrictedResult_eq_embed D₀ j₀ realize next childR selectors i k
          (havail_iff.mp havail),
        embed_restricted_internal_of_identity D₀ j₀ realize h hop next R
          selectors i]
  · have hunavailableChild : ¬ ResultAvailable next selectors i :=
      fun hc => havail (havail_iff.mpr hc)
    rw [restrictedResult_eq_bot D₀ j₀ realize
          (ChannelTree.internal h next) R selectors i k havail,
        restrictedResult_eq_bot D₀ j₀ realize next childR selectors i k
          hunavailableChild]

/-- An internal step embeds as its declared operation bound to the restricted
child.  Identity is the special case whose Kraus family is absorbed. -/
theorem embed_restricted_internal {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} (h : ChannelInternalStep s t)
    (next : ChannelTree C t)
    (R : ChannelTreeRealization D₀ j₀ realize (ChannelTree.internal h next))
    (selectors : List Bool) (i : ℕ) :
    embed (restrictedInstrument D₀ j₀ realize
        (ChannelTree.internal h next) R selectors i) =
      embed
        ((FiniteInstrumentComp.ofOperation
            (channelInternalOperation s) ()).bind
          (fun _ =>
            restrictedInstrument D₀ j₀ realize next
              (internalChildRealization D₀ j₀ realize h next R)
              selectors i)) := by
  let μ := restrictedInstrument D₀ j₀ realize
    (ChannelTree.internal h next) R selectors i
  let childR := internalChildRealization D₀ j₀ realize h next R
  let ν :=
    (FiniteInstrumentComp.ofOperation
        (channelInternalOperation s) ()).bind
      (fun _ =>
        restrictedInstrument D₀ j₀ realize next childR selectors i)
  refine embed_congr_of_outcome_equiv μ ν ?e ?hbranch ?hvalue
  · exact
      { toFun := fun p => ⟨⟨⟩, ⟨p.1.2, p.2⟩⟩
        invFun := fun q => ⟨⟨⟨⟩, q.2.1⟩, q.2.2⟩
        left_inv := by
          intro p
          rcases p with ⟨⟨⟨⟩, o⟩, hp⟩
          rfl
        right_inv := by
          intro q
          rcases q with ⟨⟨⟩, ⟨o, ho⟩⟩
          rfl }
  · intro p
    rfl
  · intro p
    rfl

theorem ChannelInternalStep.eq_config_of_pauliX {C : Type}
    {s t : ChannelConfig C} {value : C}
    (h : ChannelInternalStep s t)
    (hc : s.control = .term (.prim (.pauliX value))) :
    t = {s with
      control := .value (.payload value)
      quantum := applyOperation Qubit.pauliXOp s.quantum} := by
  have ht := ChannelInternalStep.eq_of_pauliX h hc
  apply ChannelConfig.ext
  · exact ht.1
  · exact ht.2.1
  · exact ht.2.2.1
  · exact ht.2.2.2

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
        · exact
            (restrictedResult_internal_of_identity D₀ j₀ realize
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
              selectors i k).symm
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
        · exact
            (restrictedResult_internal_of_identity D₀ j₀ realize
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
              selectors i k).symm
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
            have := restrictedResult_internal_of_identity D₀ j₀ realize
              h hop next R selectors i k
            rw [this]
            apply le_sup_of_le_left
            apply le_sSup
            exact ⟨next.depth,
              next,
              internalChildRealization D₀ j₀ realize h next R,
              le_rfl, rfl⟩
          · cases ht
            have := restrictedResult_internal_of_identity D₀ j₀ realize
              h hop next R selectors i k
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

/-- Remove one already-consumed external selector from a leaf. -/
def dropSelector {C : Type} (leaf : ChannelLeaf C) : ChannelLeaf C :=
  { leaf with selectors := leaf.selectors.tail }

@[simp] theorem dropSelector_prependSelector {C : Type}
    (b : Bool) (leaf : ChannelLeaf C) :
    dropSelector (prependSelector b leaf) = leaf := by
  cases leaf
  rfl

/-- Wrap a completed child under one external-selection node. -/
def wrapExtern {C : Type} (b : Bool)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (child : ChannelTree C
      (initialChannelConfig (if b then right else left) quantum)) :
    ChannelTree C
      (initialChannelConfig (.extern left right) quantum) :=
  ChannelTree.external b
    (by
      cases b
      · simpa [initialChannelConfig, ofConfig, initialConfig] using
          (ChannelExternalStep.selectFalse
            (s := initialChannelConfig (.extern left right) quantum))
      · simpa [initialChannelConfig, ofConfig, initialConfig] using
          (ChannelExternalStep.selectTrue
            (s := initialChannelConfig (.extern left right) quantum)))
    child

theorem wrapExtern_depth {C : Type} (b : Bool)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (child : ChannelTree C
      (initialChannelConfig (if b then right else left) quantum)) :
    (wrapExtern b left right quantum child).depth = child.depth + 1 :=
  rfl

/-- Restrict a parent external realization to its selected child. -/
noncomputable def externalChildRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} (b : Bool)
    (h : ChannelExternalStep s b t)
    (next : ChannelTree C t)
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.external b h next)) :
    ChannelTreeRealization D₀ j₀ realize next where
  value := fun leaf => R.value (prependSelector b leaf)
  related := fun o => R.related o

/-- Lift a child realization through one external-selection node. -/
noncomputable def wrapExternalRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} (b : Bool)
    (h : ChannelExternalStep s b t)
    (next : ChannelTree C t)
    (R : ChannelTreeRealization D₀ j₀ realize next) :
    ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.external b h next) where
  value := fun leaf => R.value (dropSelector leaf)
  related := by
    intro o
    change ValueRel D₀ j₀ realize
      (next.instrument.value o).isTerminal.value
      (R.value (dropSelector (prependSelector b (next.instrument.value o))))
    simpa using R.related o

/-- Restriction across an external node consumes exactly its selector. -/
theorem embed_restricted_external_of_path {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} (b : Bool)
    (h : ChannelExternalStep s b t)
    (next : ChannelTree C t)
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.external b h next))
    (selectors childSelectors : List Bool) (i j : ℕ)
    (hpath : selectors ++ HardwareAdequacy.coordinatePath i =
      b :: (childSelectors ++ HardwareAdequacy.coordinatePath j)) :
    embed (restrictedInstrument D₀ j₀ realize
        (ChannelTree.external b h next) R selectors i) =
      embed (restrictedInstrument D₀ j₀ realize next
        (externalChildRealization D₀ j₀ realize b h next R)
        childSelectors j) := by
  let μ := restrictedInstrument D₀ j₀ realize
    (ChannelTree.external b h next) R selectors i
  let ν := restrictedInstrument D₀ j₀ realize next
    (externalChildRealization D₀ j₀ realize b h next R) childSelectors j
  refine embed_congr_of_outcome_equiv μ ν ?e ?hbranch ?hvalue
  · exact
      { toFun := fun p =>
          ⟨p.1, by
            have hp : OutcomeCompatible (ChannelTree.external b h next)
                selectors i p.1 := p.2
            change List.IsPrefix
              (b :: (next.instrument.value p.1).selectors)
              (selectors ++ HardwareAdequacy.coordinatePath i) at hp
            rw [hpath] at hp
            have hp' : List.IsPrefix
                (next.instrument.value p.1).selectors
                (childSelectors ++ HardwareAdequacy.coordinatePath j) := by
              simpa using hp
            change OutcomeCompatible next childSelectors j p.1
            exact hp'⟩
        invFun := fun q =>
          ⟨q.1, by
            have hq : OutcomeCompatible next childSelectors j q.1 := q.2
            change List.IsPrefix
              (next.instrument.value q.1).selectors
              (childSelectors ++ HardwareAdequacy.coordinatePath j) at hq
            change List.IsPrefix
              (b :: (next.instrument.value q.1).selectors)
              (selectors ++ HardwareAdequacy.coordinatePath i)
            rw [hpath]
            simpa using hq⟩
        left_inv := by
          intro p
          rcases p with ⟨o, ho⟩
          rfl
        right_inv := by
          intro q
          rcases q with ⟨o, ho⟩
          rfl }
  · intro p
    rfl
  · intro p
    rfl

theorem embed_restricted_external_cons {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} (b : Bool)
    (h : ChannelExternalStep s b t)
    (next : ChannelTree C t)
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.external b h next))
    (selectors : List Bool) (i : ℕ) :
    embed (restrictedInstrument D₀ j₀ realize
        (ChannelTree.external b h next) R (b :: selectors) i) =
      embed (restrictedInstrument D₀ j₀ realize next
        (externalChildRealization D₀ j₀ realize b h next R)
        selectors i) :=
  embed_restricted_external_of_path D₀ j₀ realize b h next R
    (b :: selectors) selectors i i rfl

theorem embed_restricted_external_coordinate {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} (b : Bool)
    (h : ChannelExternalStep s b t)
    (next : ChannelTree C t)
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.external b h next))
    (j : ℕ) :
    embed (restrictedInstrument D₀ j₀ realize
        (ChannelTree.external b h next) R []
        (HardwareAdequacy.branchCoordinate b j)) =
      embed (restrictedInstrument D₀ j₀ realize next
        (externalChildRealization D₀ j₀ realize b h next R) [] j) := by
  apply embed_restricted_external_of_path D₀ j₀ realize b h next R
  cases b <;> simp

theorem restrictedResult_external_of_path {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} (b : Bool)
    (h : ChannelExternalStep s b t)
    (next : ChannelTree C t)
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.external b h next))
    (selectors childSelectors : List Bool) (i j : ℕ)
    (hpath : selectors ++ HardwareAdequacy.coordinatePath i =
      b :: (childSelectors ++ HardwareAdequacy.coordinatePath j))
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    restrictedResult D₀ j₀ realize
        (ChannelTree.external b h next) R selectors i k =
      restrictedResult D₀ j₀ realize next
        (externalChildRealization D₀ j₀ realize b h next R)
        childSelectors j k := by
  classical
  let childR := externalChildRealization D₀ j₀ realize b h next R
  have havail_iff :
      ResultAvailable (ChannelTree.external b h next) selectors i ↔
        ResultAvailable next childSelectors j := by
    simp [ResultAvailable, resultAvailableAt, hpath]
  by_cases havail :
      ResultAvailable (ChannelTree.external b h next) selectors i
  · rw [restrictedResult_eq_embed D₀ j₀ realize
          (ChannelTree.external b h next) R selectors i k havail,
        restrictedResult_eq_embed D₀ j₀ realize next childR childSelectors j k
          (havail_iff.mp havail),
        embed_restricted_external_of_path D₀ j₀ realize b h next R
          selectors childSelectors i j hpath]
  · have hunavailableChild :
        ¬ ResultAvailable next childSelectors j :=
      fun hc => havail (havail_iff.mpr hc)
    rw [restrictedResult_eq_bot D₀ j₀ realize
          (ChannelTree.external b h next) R selectors i k havail,
        restrictedResult_eq_bot D₀ j₀ realize next childR childSelectors j k
          hunavailableChild]

theorem restrictedResult_external_cons {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} (b : Bool)
    (h : ChannelExternalStep s b t)
    (next : ChannelTree C t)
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.external b h next))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    restrictedResult D₀ j₀ realize
        (ChannelTree.external b h next) R (b :: selectors) i k =
      restrictedResult D₀ j₀ realize next
        (externalChildRealization D₀ j₀ realize b h next R)
        selectors i k :=
  restrictedResult_external_of_path D₀ j₀ realize b h next R
    (b :: selectors) selectors i i rfl k

theorem restrictedResult_external_coordinate {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} (b : Bool)
    (h : ChannelExternalStep s b t)
    (next : ChannelTree C t)
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.external b h next))
    (j : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    restrictedResult D₀ j₀ realize
        (ChannelTree.external b h next) R []
        (HardwareAdequacy.branchCoordinate b j) k =
      restrictedResult D₀ j₀ realize next
        (externalChildRealization D₀ j₀ realize b h next R) [] j k := by
  apply restrictedResult_external_of_path D₀ j₀ realize b h next R
  cases b <;> simp

theorem restrictedResult_external_root {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} (b : Bool)
    (h : ChannelExternalStep s b t)
    (next : ChannelTree C t)
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.external b h next))
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    restrictedResult D₀ j₀ realize
        (ChannelTree.external b h next) R [] 0 k = ⊥ := by
  apply restrictedResult_eq_bot
  simp [ResultAvailable, resultAvailableAt,
    HardwareAdequacy.coordinatePath]

theorem restrictedResult_external_mismatch {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} (b c : Bool) (hbc : b ≠ c)
    (h : ChannelExternalStep s b t)
    (next : ChannelTree C t)
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.external b h next))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    restrictedResult D₀ j₀ realize
        (ChannelTree.external b h next) R (c :: selectors) i k = ⊥ := by
  apply restrictedResult_eq_bot
  cases b <;> cases c <;>
    simp_all [ResultAvailable, resultAvailableAt]

theorem restrictedResult_external_coordinate_mismatch {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} (b c : Bool) (hbc : b ≠ c)
    (h : ChannelExternalStep s b t)
    (next : ChannelTree C t)
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.external b h next))
    (j : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    restrictedResult D₀ j₀ realize
        (ChannelTree.external b h next) R []
        (HardwareAdequacy.branchCoordinate c j) k = ⊥ := by
  apply restrictedResult_eq_bot
  cases b <;> cases c <;>
    simp_all [ResultAvailable, resultAvailableAt]

theorem selectPath_extern_cons {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (b : Bool) (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    HardwareAdequacy.selectPath (b :: selectors)
        (interp (hardwarePrimitive D₀ j₀ realize) (.extern left right)
          semanticEnv) i k =
      HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize)
          (if b then right else left) semanticEnv) i k := by
  rw [HardwareAdequacy.selectPath_cons, interp_extern_apply]
  cases b
  · rw [TTContinuation.computation_extern_select_false]
    simp
  · rw [TTContinuation.computation_extern_select_true]
    simp

theorem selectPath_extern_coordinate {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (b : Bool) (j : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    interp (hardwarePrimitive D₀ j₀ realize) (.extern left right)
        semanticEnv (HardwareAdequacy.branchCoordinate b j) k =
      interp (hardwarePrimitive D₀ j₀ realize)
        (if b then right else left) semanticEnv j k := by
  rw [interp_extern_apply]
  cases b
  · change (TTContinuation.selectBranch false
        (HasComputationChoice.extern
          (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv,
            interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)) j) k =
      _
    rw [TTContinuation.computation_extern_select_false]
    simp
  · change (TTContinuation.selectBranch true
        (HasComputationChoice.extern
          (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv,
            interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)) j) k =
      _
    rw [TTContinuation.computation_extern_select_true]
    simp

/-- The tree-result supremum below a consumed external selector is exactly the
corresponding child supremum. -/
theorem external_cons_channelTreeSup {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (b : Bool) (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    sSup (channelTreeResults D₀ j₀ realize
        (initialChannelConfig (.extern left right) quantum)
        (b :: selectors) i k) =
      sSup (channelTreeResults D₀ j₀ realize
        (initialChannelConfig (if b then right else left) quantum)
        selectors i k) := by
  let source := initialChannelConfig (.extern left right) quantum
  let target := initialChannelConfig (if b then right else left) quantum
  have hb : ChannelExternalStep source b target := by
    cases b
    · simpa [source, target, initialChannelConfig, ofConfig, initialConfig]
        using (ChannelExternalStep.selectFalse (s := source))
    · simpa [source, target, initialChannelConfig, ofConfig, initialConfig]
        using (ChannelExternalStep.selectTrue (s := source))
  apply le_antisymm
  · apply sSup_le
    rintro T ⟨_, tree, R, _, rfl⟩
    have hctrl : source.control = .term (.extern left right) := rfl
    cases tree with
    | terminal hterm =>
        have := hterm.control_eq.symm.trans hctrl
        cases this
    | internal h _ =>
        exact False.elim (ChannelInternalStep.not_extern h hctrl)
    | external c h next =>
        have ht := ChannelExternalStep.eq_of_extern h hctrl
        cases b <;> cases c
        · cases ht
          rw [restrictedResult_external_cons]
          apply le_sSup
          exact ⟨next.depth, next,
            externalChildRealization D₀ j₀ realize false h next R, le_rfl, rfl⟩
        · rw [restrictedResult_external_mismatch D₀ j₀ realize true false
            (by decide) h next R selectors i k]
          exact bot_le
        · rw [restrictedResult_external_mismatch D₀ j₀ realize false true
            (by decide) h next R selectors i k]
          exact bot_le
        · cases ht
          rw [restrictedResult_external_cons]
          apply le_sSup
          exact ⟨next.depth, next,
            externalChildRealization D₀ j₀ realize true h next R, le_rfl, rfl⟩
  · apply sSup_le
    rintro T ⟨fuel, child, R, hdepth, rfl⟩
    apply le_sSup
    refine ⟨fuel + 1, ChannelTree.external b hb child,
      wrapExternalRealization D₀ j₀ realize b hb child R, ?_, ?_⟩
    · change child.depth + 1 ≤ fuel + 1
      omega
    · rw [restrictedResult_external_cons]
      rfl

/-- The same shift when the external selector is supplied by the heap
coordinate rather than by an explicit selector list. -/
theorem external_coordinate_channelTreeSup {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (b : Bool) (j : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    sSup (channelTreeResults D₀ j₀ realize
        (initialChannelConfig (.extern left right) quantum) []
        (HardwareAdequacy.branchCoordinate b j) k) =
      sSup (channelTreeResults D₀ j₀ realize
        (initialChannelConfig (if b then right else left) quantum) [] j k) := by
  let source := initialChannelConfig (.extern left right) quantum
  let target := initialChannelConfig (if b then right else left) quantum
  have hb : ChannelExternalStep source b target := by
    cases b
    · simpa [source, target, initialChannelConfig, ofConfig, initialConfig]
        using (ChannelExternalStep.selectFalse (s := source))
    · simpa [source, target, initialChannelConfig, ofConfig, initialConfig]
        using (ChannelExternalStep.selectTrue (s := source))
  apply le_antisymm
  · apply sSup_le
    rintro T ⟨_, tree, R, _, rfl⟩
    have hctrl : source.control = .term (.extern left right) := rfl
    cases tree with
    | terminal hterm =>
        have := hterm.control_eq.symm.trans hctrl
        cases this
    | internal h _ =>
        exact False.elim (ChannelInternalStep.not_extern h hctrl)
    | external c h next =>
        have ht := ChannelExternalStep.eq_of_extern h hctrl
        cases b <;> cases c
        · cases ht
          rw [restrictedResult_external_coordinate]
          apply le_sSup
          exact ⟨next.depth, next,
            externalChildRealization D₀ j₀ realize false h next R, le_rfl, rfl⟩
        · rw [restrictedResult_external_coordinate_mismatch D₀ j₀ realize
            true false (by decide) h next R j k]
          exact bot_le
        · rw [restrictedResult_external_coordinate_mismatch D₀ j₀ realize
            false true (by decide) h next R j k]
          exact bot_le
        · cases ht
          rw [restrictedResult_external_coordinate]
          apply le_sSup
          exact ⟨next.depth, next,
            externalChildRealization D₀ j₀ realize true h next R, le_rfl, rfl⟩
  · apply sSup_le
    rintro T ⟨fuel, child, R, hdepth, rfl⟩
    apply le_sSup
    refine ⟨fuel + 1, ChannelTree.external b hb child,
      wrapExternalRealization D₀ j₀ realize b hb child R, ?_, ?_⟩
    · change child.depth + 1 ≤ fuel + 1
      omega
    · rw [restrictedResult_external_coordinate]
      rfl

/-- At the unresolved external root every completing tree contributes bottom. -/
theorem external_root_channelTreeSup {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    sSup (channelTreeResults D₀ j₀ realize
      (initialChannelConfig (.extern left right) quantum) [] 0 k) = ⊥ := by
  apply le_antisymm
  · apply sSup_le
    rintro T ⟨_, tree, R, _, rfl⟩
    have hctrl :
        (initialChannelConfig (.extern left right) quantum).control =
          .term (.extern left right) := rfl
    cases tree with
    | terminal hterm =>
        have := hterm.control_eq.symm.trans hctrl
        cases this
    | internal h _ =>
        exact False.elim (ChannelInternalStep.not_extern h hctrl)
    | external _ h next =>
        rw [restrictedResult_external_root]
  · exact bot_le

/-- Compositional channel-tree completeness for external choice. -/
theorem extern_channelTreeCompleteness {C : Type}
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
      (initialChannelConfig (.extern left right) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) (.extern left right)
        semanticEnv) where
  selected_result_eq_channelTree_sup := by
    intro selectors i k
    cases selectors with
    | cons b selectors =>
        rw [selectPath_extern_cons]
        cases b
        · simp only [Bool.false_eq_true, if_false]
          rw [hleft.selected_result_eq_channelTree_sup,
            external_cons_channelTreeSup]
          simp
        · simp only [if_true]
          rw [hright.selected_result_eq_channelTree_sup,
            external_cons_channelTreeSup]
          simp
    | nil =>
        cases i with
        | zero =>
            rw [HardwareAdequacy.selectPath_nil, interp_extern_apply,
              external_root_channelTreeSup]
            change (TTContinuation.externalChoice
              (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv,
                interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)
              0) k = ⊥
            rw [TTContinuation.externalChoice_root_bot]
            exact ScottMap.bot_apply k
        | succ n =>
            by_cases heven : n % 2 = 0
            · have hi : n + 1 =
                  HardwareAdequacy.branchCoordinate false (n / 2) := by
                simp [HardwareAdequacy.branchCoordinate]
                omega
              rw [hi, HardwareAdequacy.selectPath_nil,
                selectPath_extern_coordinate]
              simp only [Bool.false_eq_true, if_false]
              have hc :=
                hleft.selected_result_eq_channelTree_sup [] (n / 2) k
              have hc' :
                  interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv
                      (n / 2) k =
                    sSup (channelTreeResults D₀ j₀ realize
                      (initialChannelConfig left quantum) [] (n / 2) k) := by
                simpa using hc
              exact hc'.trans
                (external_coordinate_channelTreeSup D₀ j₀ realize left right
                  quantum false (n / 2) k).symm
            · have hodd : n % 2 = 1 := by omega
              have hi : n + 1 =
                  HardwareAdequacy.branchCoordinate true (n / 2) := by
                simp [HardwareAdequacy.branchCoordinate]
                omega
              rw [hi, HardwareAdequacy.selectPath_nil,
                selectPath_extern_coordinate]
              simp only [if_true]
              have hc :=
                hright.selected_result_eq_channelTree_sup [] (n / 2) k
              have hc' :
                  interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv
                      (n / 2) k =
                    sSup (channelTreeResults D₀ j₀ realize
                      (initialChannelConfig right quantum) [] (n / 2) k) := by
                simpa using hc
              exact hc'.trans
                (external_coordinate_channelTreeSup D₀ j₀ realize left right
                  quantum true (n / 2) k).symm

theorem extern_returns_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (leftValue rightValue : C) (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.extern (.prim (.ret leftValue)) (.prim (.ret rightValue))) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.extern (.prim (.ret leftValue)) (.prim (.ret rightValue)))
        semanticEnv) :=
  extern_channelTreeCompleteness D₀ j₀ realize _ _ quantum semanticEnv
    (return_channelTreeCompleteness D₀ j₀ realize leftValue quantum semanticEnv)
    (return_channelTreeCompleteness D₀ j₀ realize rightValue quantum semanticEnv)

/-- Remove one probability/measurement provenance tag from a leaf. -/
def dropPhysical {C : Type} (leaf : ChannelLeaf C) : ChannelLeaf C :=
  { leaf with physicalPath := leaf.physicalPath.tail }

@[simp] theorem dropPhysical_prependPhysical {C : Type}
    (b : Bool) (leaf : ChannelLeaf C) :
    dropPhysical (prependPhysical b leaf) = leaf := by
  cases leaf
  rfl

/-- Restrict a realized binary probability tree to its left child. -/
noncomputable def probabilityLeftRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {p : ℝ}
    {leftTerm rightTerm : Term (QubitPrimitive C)}
    (hp₀ : 0 < p) (hp₁ : p < 1)
    (left : ChannelTree C
      { s with
        control := .term leftTerm
        quantum := applyOperation
          (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum })
    (right : ChannelTree C
      { s with
        control := .term rightTerm
        quantum := applyOperation
          (sourceProbabilityOperation (1 - p)
            (sub_nonneg.mpr hp₁.le) (by linarith)) s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.probability hp₀ hp₁ left right)) :
    ChannelTreeRealization D₀ j₀ realize left where
  value := fun leaf => R.value (prependPhysical false leaf)
  related := by
    intro o
    exact R.related ⟨false, o⟩

/-- Restrict a realized binary probability tree to its right child. -/
noncomputable def probabilityRightRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {p : ℝ}
    {leftTerm rightTerm : Term (QubitPrimitive C)}
    (hp₀ : 0 < p) (hp₁ : p < 1)
    (left : ChannelTree C
      { s with
        control := .term leftTerm
        quantum := applyOperation
          (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum })
    (right : ChannelTree C
      { s with
        control := .term rightTerm
        quantum := applyOperation
          (sourceProbabilityOperation (1 - p)
            (sub_nonneg.mpr hp₁.le) (by linarith)) s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.probability hp₀ hp₁ left right)) :
    ChannelTreeRealization D₀ j₀ realize right where
  value := fun leaf => R.value (prependPhysical true leaf)
  related := by
    intro o
    exact R.related ⟨true, o⟩

/-- Reassemble child realizations using their retained physical provenance. -/
noncomputable def wrapProbabilityRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {p : ℝ}
    {leftTerm rightTerm : Term (QubitPrimitive C)}
    (hp₀ : 0 < p) (hp₁ : p < 1)
    (left : ChannelTree C
      { s with
        control := .term leftTerm
        quantum := applyOperation
          (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum })
    (right : ChannelTree C
      { s with
        control := .term rightTerm
        quantum := applyOperation
          (sourceProbabilityOperation (1 - p)
            (sub_nonneg.mpr hp₁.le) (by linarith)) s.quantum })
    (leftR : ChannelTreeRealization D₀ j₀ realize left)
    (rightR : ChannelTreeRealization D₀ j₀ realize right) :
    ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.probability hp₀ hp₁ left right) where
  value := fun leaf =>
    match leaf.physicalPath with
    | false :: _ => leftR.value (dropPhysical leaf)
    | true :: _ => rightR.value (dropPhysical leaf)
    | [] => ⊥
  related := by
    rintro ⟨b, o⟩
    cases b
    · change ValueRel D₀ j₀ realize
        (left.instrument.value o).isTerminal.value
        (leftR.value (dropPhysical
          (prependPhysical false (left.instrument.value o))))
      simpa using leftR.related o
    · change ValueRel D₀ j₀ realize
        (right.instrument.value o).isTerminal.value
        (rightR.value (dropPhysical
          (prependPhysical true (right.instrument.value o))))
      simpa using rightR.related o

/-- Restriction commutes with an interior physical probability node.  This is
an outcome reindexing theorem; no lattice operation is used to model the
probability. -/
theorem embed_restricted_probability {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {p : ℝ}
    {leftTerm rightTerm : Term (QubitPrimitive C)}
    (hp₀ : 0 < p) (hp₁ : p < 1)
    (left : ChannelTree C
      { s with
        control := .term leftTerm
        quantum := applyOperation
          (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum })
    (right : ChannelTree C
      { s with
        control := .term rightTerm
        quantum := applyOperation
          (sourceProbabilityOperation (1 - p)
            (sub_nonneg.mpr hp₁.le) (by linarith)) s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.probability hp₀ hp₁ left right))
    (selectors : List Bool) (i : ℕ) :
    embed (restrictedInstrument D₀ j₀ realize
        (ChannelTree.probability hp₀ hp₁ left right) R selectors i) =
      embed ((FiniteInstrumentComp.weightedCoin (n := 2) p hp₀.le hp₁.le).bind
        (fun b => if b then
          restrictedInstrument D₀ j₀ realize right
            (probabilityRightRealization D₀ j₀ realize hp₀ hp₁ left right R)
            selectors i
        else
          restrictedInstrument D₀ j₀ realize left
            (probabilityLeftRealization D₀ j₀ realize hp₀ hp₁ left right R)
            selectors i)) := by
  let μ := restrictedInstrument D₀ j₀ realize
    (ChannelTree.probability hp₀ hp₁ left right) R selectors i
  let leftR :=
    probabilityLeftRealization D₀ j₀ realize hp₀ hp₁ left right R
  let rightR :=
    probabilityRightRealization D₀ j₀ realize hp₀ hp₁ left right R
  let ν := (FiniteInstrumentComp.weightedCoin (n := 2) p hp₀.le hp₁.le).bind
    (fun b => if b then
      restrictedInstrument D₀ j₀ realize right rightR selectors i
    else
      restrictedInstrument D₀ j₀ realize left leftR selectors i)
  refine embed_congr_of_outcome_equiv μ ν ?_ ?_ ?_
  · exact
      { toFun := by
          rintro ⟨⟨b, o⟩, hq⟩
          cases b
          · exact ⟨false, ⟨o, hq⟩⟩
          · exact ⟨true, ⟨o, hq⟩⟩
        invFun := by
          rintro ⟨b, q⟩
          cases b
          · rcases q with ⟨o, hq⟩
            exact ⟨⟨false, o⟩, hq⟩
          · rcases q with ⟨o, hq⟩
            exact ⟨⟨true, o⟩, hq⟩
        left_inv := by
          intro q
          rcases q with ⟨⟨b, o⟩, hq⟩
          cases b <;> rfl
        right_inv := by
          intro q
          rcases q with ⟨b, q⟩
          cases b
          · rcases q with ⟨o, hq⟩
            rfl
          · rcases q with ⟨o, hq⟩
            rfl }
  · intro q
    rcases q with ⟨⟨b, o⟩, hq⟩
    cases b <;> rfl
  · intro q
    rcases q with ⟨⟨b, o⟩, hq⟩
    cases b
    · change leftR.value (left.instrument.value o) =
        R.value (prependPhysical false (left.instrument.value o))
      rfl
    · change rightR.value (right.instrument.value o) =
        R.value (prependPhysical true (right.instrument.value o))
      rfl

/-- Project a realized measurement tree to its zero-outcome child. -/
noncomputable def measurementZeroRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {zeroValue oneValue : C}
    (zero : ChannelTree C
      { s with
        control := .value (.payload zeroValue)
        quantum := applyOperation (measurementOperation false) s.quantum })
    (one : ChannelTree C
      { s with
        control := .value (.payload oneValue)
        quantum := applyOperation (measurementOperation true) s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.measurement zero one)) :
    ChannelTreeRealization D₀ j₀ realize zero where
  value := R.value
  related := by
    intro o
    exact R.related ⟨false, o⟩

/-- Project a realized measurement tree to its one-outcome child. -/
noncomputable def measurementOneRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {zeroValue oneValue : C}
    (zero : ChannelTree C
      { s with
        control := .value (.payload zeroValue)
        quantum := applyOperation (measurementOperation false) s.quantum })
    (one : ChannelTree C
      { s with
        control := .value (.payload oneValue)
        quantum := applyOperation (measurementOperation true) s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.measurement zero one)) :
    ChannelTreeRealization D₀ j₀ realize one where
  value := R.value
  related := by
    intro o
    exact R.related ⟨true, o⟩

/-- A canonical semantic representative for any channel leaf for which a
logical-relation witness exists.  This is used to combine independently
chosen realizations of the two measurement children. -/
noncomputable def relatedLeafValue {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (leaf : ChannelLeaf C) : HSemanticValue D₀ j₀ :=
  by
    classical
    exact if h : ∃ d, ValueRel D₀ j₀ realize leaf.isTerminal.value d then
      Classical.choose h
    else
      ⊥

theorem relatedLeafValue_related {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (leaf : ChannelLeaf C)
    (h : ∃ d, ValueRel D₀ j₀ realize leaf.isTerminal.value d) :
    ValueRel D₀ j₀ realize leaf.isTerminal.value
      (relatedLeafValue D₀ j₀ realize leaf) := by
  rw [relatedLeafValue, dif_pos h]
  exact Classical.choose_spec h

/-- Reassemble independently realized measurement children.  Unlike source
probability, measurement does not record a branch tag in `ChannelLeaf`, so a
canonical representative of the leaf's logical value is used. -/
noncomputable def wrapMeasurementRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {zeroValue oneValue : C}
    (zero : ChannelTree C
      { s with
        control := .value (.payload zeroValue)
        quantum := applyOperation (measurementOperation false) s.quantum })
    (one : ChannelTree C
      { s with
        control := .value (.payload oneValue)
        quantum := applyOperation (measurementOperation true) s.quantum })
    (zeroR : ChannelTreeRealization D₀ j₀ realize zero)
    (oneR : ChannelTreeRealization D₀ j₀ realize one) :
    ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.measurement zero one) where
  value := relatedLeafValue D₀ j₀ realize
  related := by
    rintro ⟨b, o⟩
    cases b
    · exact relatedLeafValue_related D₀ j₀ realize _
        ⟨zeroR.value (zero.instrument.value o), zeroR.related o⟩
    · exact relatedLeafValue_related D₀ j₀ realize _
        ⟨oneR.value (one.instrument.value o), oneR.related o⟩

/-- Restriction commutes with an interior computational-basis measurement.
The parent restriction and the measurement of its restricted children differ
only by their nested proof-subtype outcome representation. -/
theorem embed_restricted_measurement {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {zeroValue oneValue : C}
    (zero : ChannelTree C
      { s with
        control := .value (.payload zeroValue)
        quantum := applyOperation (measurementOperation false) s.quantum })
    (one : ChannelTree C
      { s with
        control := .value (.payload oneValue)
        quantum := applyOperation (measurementOperation true) s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.measurement zero one))
    (selectors : List Bool) (i : ℕ) :
    embed (restrictedInstrument D₀ j₀ realize
        (ChannelTree.measurement zero one) R selectors i) =
      embed (Qubit.measureZComp.bind
        (fun b => if b then
          restrictedInstrument D₀ j₀ realize one
            (measurementOneRealization D₀ j₀ realize zero one R) selectors i
        else
          restrictedInstrument D₀ j₀ realize zero
            (measurementZeroRealization D₀ j₀ realize zero one R) selectors i)) := by
  let μ := restrictedInstrument D₀ j₀ realize
    (ChannelTree.measurement zero one) R selectors i
  let zeroR := measurementZeroRealization D₀ j₀ realize zero one R
  let oneR := measurementOneRealization D₀ j₀ realize zero one R
  let ν := Qubit.measureZComp.bind
    (fun b => if b then
      restrictedInstrument D₀ j₀ realize one oneR selectors i
    else
      restrictedInstrument D₀ j₀ realize zero zeroR selectors i)
  refine embed_congr_of_outcome_equiv μ ν ?_ ?_ ?_
  · exact
      { toFun := by
          rintro ⟨⟨b, o⟩, hq⟩
          cases b
          · exact ⟨false, ⟨o, hq⟩⟩
          · exact ⟨true, ⟨o, hq⟩⟩
        invFun := by
          rintro ⟨b, q⟩
          cases b
          · rcases q with ⟨o, hq⟩
            exact ⟨⟨false, o⟩, hq⟩
          · rcases q with ⟨o, hq⟩
            exact ⟨⟨true, o⟩, hq⟩
        left_inv := by
          rintro ⟨⟨b, o⟩, hq⟩
          cases b <;> rfl
        right_inv := by
          rintro ⟨b, q⟩
          cases b
          · rcases q with ⟨o, hq⟩
            rfl
          · rcases q with ⟨o, hq⟩
            rfl }
  · rintro ⟨⟨b, o⟩, hq⟩
    cases b <;> rfl
  · rintro ⟨⟨b, o⟩, hq⟩
    cases b <;> rfl

theorem satisfiedTTTheory_eq_of_wpKraus_semEq
    {μ ν : FiniteInstrumentComp 2 PUnit.{1}}
    (h : ∀ P : PUnit.{1} → KrausFamily 2 2,
      KrausFamily.SemEq (μ.wpKraus P) (ν.wpKraus P)) :
    μ.satisfiedTTTheory resultCode = ν.satisfiedTTTheory resultCode := by
  apply (FiniteInstrumentComp.satisfiedTTTheory_eq_iff_mutual_finitaryTTRefines
    resultCode).2
  constructor
  · intro c
    exact KrausFamily.residualRefines_of_semEq (h (c.decode resultCode))
  · intro c
    exact KrausFamily.residualRefines_of_semEq
      (KrausFamily.applySemEq_symm (h (c.decode resultCode)))

theorem satisfiedTTTheory_bind_assoc
    {D E : Type} [Preorder D] [Preorder E]
    (μ : FiniteInstrumentComp 2 D)
    (f : D → FiniteInstrumentComp 2 E)
    (g : E → FiniteInstrumentComp 2 PUnit.{1}) :
    (((μ.bind f).bind g).satisfiedTTTheory resultCode) =
      ((μ.bind fun d => (f d).bind g).satisfiedTTTheory resultCode) := by
  apply satisfiedTTTheory_eq_of_wpKraus_semEq
  intro P
  exact KrausFamily.applySemEq_trans
    (FiniteInstrumentComp.wpKraus_bind_semEq (μ.bind f) g P)
    (KrausFamily.applySemEq_trans
      (FiniteInstrumentComp.wpKraus_bind_semEq μ f
        (fun e => (g e).wpKraus P))
      (KrausFamily.applySemEq_trans
        (FiniteInstrumentComp.wpKraus_semEq_pred μ fun d =>
          KrausFamily.applySemEq_symm
            (FiniteInstrumentComp.wpKraus_bind_semEq (f d) g P))
        (KrausFamily.applySemEq_symm
          (FiniteInstrumentComp.wpKraus_bind_semEq μ
            (fun d => (f d).bind g) P))))

/-- On a well-scoped tree, changing a leaf realization does not change any
finite observation: `ValueRel` is functional on every terminal leaf. -/
theorem holds_restrictedInstrument_bind_iff_of_wellScoped {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} (tree : ChannelTree C s)
    (hscoped : ChannelConfig.WellScoped s)
    (R S : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (token : TTObservationToken 2) :
    TTObservationToken.Holds resultCode token
        ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind ξ) ↔
      TTObservationToken.Holds resultCode token
        ((restrictedInstrument D₀ j₀ realize tree S selectors i).bind ξ) := by
  classical
  let μ := restrictedInstrument D₀ j₀ realize tree R selectors i
  let ν := restrictedInstrument D₀ j₀ realize tree S selectors i
  have hvalue : ∀ o : μ.Outcome, ν.value o = μ.value o := by
    intro o
    apply valueRel_functional D₀ j₀ realize
      (tree.terminalValues_wellScoped hscoped o.1)
    · exact S.related o.1
    · exact R.related o.1
  have htheory :
      (μ.bind ξ).satisfiedTTTheory resultCode =
        (ν.bind ξ).satisfiedTTTheory resultCode := by
    apply satisfiedTTTheory_eq_of_wpKraus_semEq
    intro P
    exact FiniteInstrumentComp.bind_wpKraus_congr_of_outcome_equiv
      μ ν (Equiv.refl _) (fun _ => rfl) hvalue ξ P
  constructor
  · intro h
    apply (FiniteInstrumentComp.mem_satisfiedTTTheory
      resultCode (ν.bind ξ) token).mp
    rw [← htheory]
    exact (FiniteInstrumentComp.mem_satisfiedTTTheory
      resultCode (μ.bind ξ) token).2 h
  · intro h
    apply (FiniteInstrumentComp.mem_satisfiedTTTheory
      resultCode (μ.bind ξ) token).mp
    rw [htheory]
    exact (FiniteInstrumentComp.mem_satisfiedTTTheory
      resultCode (ν.bind ξ) token).2 h

/-- Well-scoped trees make restricted results independent of the chosen
leaf realization.  Measurement wrap uses a canonical leaf value, so this
recovers the child restricted result after projection. -/
theorem restrictedResult_eq_of_wellScoped {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} (tree : ChannelTree C s)
    (hscoped : ChannelConfig.WellScoped s)
    (R S : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode) :
    restrictedResult D₀ j₀ realize tree R selectors i k =
      restrictedResult D₀ j₀ realize tree S selectors i k := by
  classical
  by_cases havail : ResultAvailable tree selectors i
  · rw [restrictedResult_eq_embed D₀ j₀ realize tree R selectors i k havail,
      restrictedResult_eq_embed D₀ j₀ realize tree S selectors i k havail]
    have hR :=
      TTPhysicalEmbedding.embed_satisfied
        (restrictedInstrument D₀ j₀ realize tree R selectors i) ξ k
        (fun _ => hk _)
    have hS :=
      TTPhysicalEmbedding.embed_satisfied
        (restrictedInstrument D₀ j₀ realize tree S selectors i) ξ k
        (fun _ => hk _)
    rw [hR, hS]
    apply RoundedTheory.ext
    ext token
    exact holds_restrictedInstrument_bind_iff_of_wellScoped D₀ j₀ realize
      tree hscoped R S selectors i ξ token
  · rw [restrictedResult_eq_bot D₀ j₀ realize tree R selectors i k havail,
      restrictedResult_eq_bot D₀ j₀ realize tree S selectors i k havail]

/-- At a finitely-presented continuation, restriction of an interior
probability node is exactly physical weighted aggregation of the two
restricted children. -/
theorem restrictedResult_probability_presented {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {p : ℝ}
    {leftTerm rightTerm : Term (QubitPrimitive C)}
    (hp₀ : 0 < p) (hp₁ : p < 1)
    (left : ChannelTree C
      { s with
        control := .term leftTerm
        quantum := applyOperation
          (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum })
    (right : ChannelTree C
      { s with
        control := .term rightTerm
        quantum := applyOperation
          (sourceProbabilityOperation (1 - p)
            (sub_nonneg.mpr hp₁.le) (by linarith)) s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.probability hp₀ hp₁ left right))
    (selectors : List Bool) (i : ℕ)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode) :
    restrictedResult D₀ j₀ realize
        (ChannelTree.probability hp₀ hp₁ left right) R selectors i k =
      TTWeightedAggregation.weightedResultScott p hp₀.le hp₁.le
        (restrictedResult D₀ j₀ realize left
            (probabilityLeftRealization D₀ j₀ realize hp₀ hp₁ left right R)
            selectors i k,
          restrictedResult D₀ j₀ realize right
            (probabilityRightRealization D₀ j₀ realize hp₀ hp₁ left right R)
            selectors i k) := by
  classical
  let leftR :=
    probabilityLeftRealization D₀ j₀ realize hp₀ hp₁ left right R
  let rightR :=
    probabilityRightRealization D₀ j₀ realize hp₀ hp₁ left right R
  let μL := restrictedInstrument D₀ j₀ realize left leftR selectors i
  let μR := restrictedInstrument D₀ j₀ realize right rightR selectors i
  let μW := (FiniteInstrumentComp.weightedCoin (n := 2) p hp₀.le hp₁.le).bind
    (fun b => if b then μR else μL)
  have havail_iff :
      ResultAvailable (ChannelTree.probability hp₀ hp₁ left right) selectors i ↔
        ResultAvailable left selectors i ∧ ResultAvailable right selectors i :=
    Iff.rfl
  by_cases hleft : ResultAvailable left selectors i
  · by_cases hright : ResultAvailable right selectors i
    · rw [restrictedResult_eq_embed D₀ j₀ realize left leftR selectors i k hleft,
        restrictedResult_eq_embed D₀ j₀ realize right rightR selectors i k hright,
        restrictedResult_eq_embed D₀ j₀ realize
          (ChannelTree.probability hp₀ hp₁ left right) R selectors i k
          (havail_iff.mpr ⟨hleft, hright⟩)]
      rw [embed_restricted_probability D₀ j₀ realize hp₀ hp₁ left right R
        selectors i]
      change embed μW k =
        TTWeightedAggregation.weightedResultScott p hp₀.le hp₁.le
          (embed μL k, embed μR k)
      calc
        embed μW k =
            (μW.bind ξ).satisfiedTTTheory resultCode :=
          TTPhysicalEmbedding.embed_satisfied μW ξ k (fun _ => hk _)
        _ = ((μL.bind ξ).weightedResult p hp₀.le hp₁.le
              (μR.bind ξ)).satisfiedTTTheory resultCode := by
          have hassoc :=
            satisfiedTTTheory_bind_assoc
              (FiniteInstrumentComp.weightedCoin (n := 2) p hp₀.le hp₁.le)
              (fun b => if b then μR else μL) ξ
          have hif : ∀ b : Bool,
              (if b then μR else μL).bind ξ =
                if b then μR.bind ξ else μL.bind ξ := by
            intro b
            split_ifs <;> rfl
          change
              (((FiniteInstrumentComp.weightedCoin (n := 2) p hp₀.le hp₁.le).bind
                  (fun b => if b then μR else μL)).bind ξ).satisfiedTTTheory
                resultCode =
              ((μL.bind ξ).weightedResult p hp₀.le hp₁.le
                (μR.bind ξ)).satisfiedTTTheory resultCode
          rw [hassoc]
          congr 1
          exact congrArg
            ((FiniteInstrumentComp.weightedCoin (n := 2) p hp₀.le hp₁.le).bind)
            (funext hif)
        _ = TTWeightedAggregation.weightedResultScott p hp₀.le hp₁.le
              ((μL.bind ξ).satisfiedTTTheory resultCode,
                (μR.bind ξ).satisfiedTTTheory resultCode) :=
          (TTWeightedAggregation.weightedResultScott_satisfied_interior
            p hp₀ hp₁ (μL.bind ξ) (μR.bind ξ)).symm
        _ = TTWeightedAggregation.weightedResultScott p hp₀.le hp₁.le
              (embed μL k, embed μR k) := by
          rw [TTPhysicalEmbedding.embed_satisfied μL ξ k (fun _ => hk _),
            TTPhysicalEmbedding.embed_satisfied μR ξ k (fun _ => hk _)]
    · rw [restrictedResult_eq_bot D₀ j₀ realize right rightR selectors i k hright,
        TTWeightedAggregation.weightedResultScott_bot_right p hp₀ hp₁]
      apply restrictedResult_eq_bot
      exact fun h => hright (havail_iff.mp h).2
  · rw [restrictedResult_eq_bot D₀ j₀ realize left leftR selectors i k hleft,
      TTWeightedAggregation.weightedResultScott_bot_left p hp₀ hp₁]
    apply restrictedResult_eq_bot
    exact fun h => hleft (havail_iff.mp h).1

/-- At a finitely-presented continuation, an available measurement node is
exactly finite physical measurement followed by the restricted children.
Unavailable nodes are covered separately by `restrictedResult_eq_bot`. -/
theorem restrictedResult_measurement_presented {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {zeroValue oneValue : C}
    (zero : ChannelTree C
      { s with
        control := .value (.payload zeroValue)
        quantum := applyOperation (measurementOperation false) s.quantum })
    (one : ChannelTree C
      { s with
        control := .value (.payload oneValue)
        quantum := applyOperation (measurementOperation true) s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.measurement zero one))
    (selectors : List Bool) (i : ℕ)
    (hzero : ResultAvailable zero selectors i)
    (hone : ResultAvailable one selectors i)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode) :
    restrictedResult D₀ j₀ realize
        (ChannelTree.measurement zero one) R selectors i k =
      ((Qubit.measureZComp.bind
        (fun b => if b then
          restrictedInstrument D₀ j₀ realize one
            (measurementOneRealization D₀ j₀ realize zero one R) selectors i
        else
          restrictedInstrument D₀ j₀ realize zero
            (measurementZeroRealization D₀ j₀ realize zero one R) selectors i)
        ).bind ξ).satisfiedTTTheory resultCode := by
  classical
  let zeroR := measurementZeroRealization D₀ j₀ realize zero one R
  let oneR := measurementOneRealization D₀ j₀ realize zero one R
  let μM := Qubit.measureZComp.bind
    (fun b => if b then
      restrictedInstrument D₀ j₀ realize one oneR selectors i
    else
      restrictedInstrument D₀ j₀ realize zero zeroR selectors i)
  have havail_iff :
      ResultAvailable (ChannelTree.measurement zero one) selectors i ↔
        ResultAvailable zero selectors i ∧ ResultAvailable one selectors i :=
    Iff.rfl
  rw [restrictedResult_eq_embed D₀ j₀ realize
      (ChannelTree.measurement zero one) R selectors i k
      (havail_iff.mpr ⟨hzero, hone⟩),
    embed_restricted_measurement D₀ j₀ realize zero one R selectors i]
  change embed μM k = (μM.bind ξ).satisfiedTTTheory resultCode
  exact TTPhysicalEmbedding.embed_satisfied μM ξ k (fun _ => hk _)

theorem ChannelInternalStep.not_prob {C : Type}
    {s t : ChannelConfig C} {p : ℝ}
    {left right : Term (QubitPrimitive C)}
    (h : ChannelInternalStep s t)
    (hc : s.control = .term (.prob p left right)) : False := by
  cases h <;> cases hc

theorem ChannelExternalStep.not_prob {C : Type}
    {s t : ChannelConfig C} {b : Bool} {p : ℝ}
    {left right : Term (QubitPrimitive C)}
    (h : ChannelExternalStep s b t)
    (hc : s.control = .term (.prob p left right)) : False := by
  cases h <;> cases hc

/-- Left child start after an interior source-probability split. -/
noncomputable def probLeftConfig {C : Type} (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2) : ChannelConfig C :=
  { initialChannelConfig (.prob p left right) quantum with
      control := .term left
      quantum := applyOperation (sourceProbabilityOperation p hp₀ hp₁)
        (initialChannelConfig (.prob p left right) quantum).quantum }

/-- Right child start after an interior source-probability split. -/
noncomputable def probRightConfig {C : Type} (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2) : ChannelConfig C :=
  { initialChannelConfig (.prob p left right) quantum with
      control := .term right
      quantum := applyOperation
        (sourceProbabilityOperation (1 - p)
          (sub_nonneg.mpr hp₁) (by linarith))
        (initialChannelConfig (.prob p left right) quantum).quantum }

noncomputable def wrapProb {C : Type} {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (leftChild : ChannelTree C
      (probLeftConfig p hp₀.le hp₁.le left right quantum))
    (rightChild : ChannelTree C
      (probRightConfig p hp₀.le hp₁.le left right quantum)) :
    ChannelTree C (initialChannelConfig (.prob p left right) quantum) :=
  ChannelTree.probability (s := initialChannelConfig (.prob p left right) quantum)
    hp₀ hp₁ leftChild rightChild

noncomputable def wrapProbZero {C : Type}
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (rightChild : ChannelTree C
      { initialChannelConfig (.prob 0 left right) quantum with
        control := .term right
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
          (initialChannelConfig (.prob 0 left right) quantum).quantum }) :
    ChannelTree C (initialChannelConfig (.prob 0 left right) quantum) :=
  ChannelTree.probabilityZero
    (s := initialChannelConfig (.prob 0 left right) quantum) rightChild

noncomputable def wrapProbOne {C : Type}
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (leftChild : ChannelTree C
      { initialChannelConfig (.prob 1 left right) quantum with
        control := .term left
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
          (initialChannelConfig (.prob 1 left right) quantum).quantum }) :
    ChannelTree C (initialChannelConfig (.prob 1 left right) quantum) :=
  ChannelTree.probabilityOne
    (s := initialChannelConfig (.prob 1 left right) quantum) leftChild

theorem wrapProb_depth {C : Type} {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (leftChild : ChannelTree C
      (probLeftConfig p hp₀.le hp₁.le left right quantum))
    (rightChild : ChannelTree C
      (probRightConfig p hp₀.le hp₁.le left right quantum)) :
    (wrapProb hp₀ hp₁ left right quantum leftChild rightChild).depth =
      max leftChild.depth rightChild.depth + 1 :=
  rfl

theorem wrapProbZero_depth {C : Type}
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (rightChild : ChannelTree C
      { initialChannelConfig (.prob 0 left right) quantum with
        control := .term right
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
          (initialChannelConfig (.prob 0 left right) quantum).quantum }) :
    (wrapProbZero left right quantum rightChild).depth =
      rightChild.depth + 1 :=
  rfl

theorem wrapProbOne_depth {C : Type}
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (leftChild : ChannelTree C
      { initialChannelConfig (.prob 1 left right) quantum with
        control := .term left
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
          (initialChannelConfig (.prob 1 left right) quantum).quantum }) :
    (wrapProbOne left right quantum leftChild).depth =
      leftChild.depth + 1 :=
  rfl

/-- Endpoint `p = 0` retains only the live right child. -/
noncomputable def probabilityZeroRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C}
    {leftTerm rightTerm : Term (QubitPrimitive C)}
    (right : ChannelTree C
      { s with
        control := .term rightTerm
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
          s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.probabilityZero (left := leftTerm) right)) :
    ChannelTreeRealization D₀ j₀ realize right where
  value := fun leaf => R.value (prependPhysical true leaf)
  related := fun o => R.related o

noncomputable def wrapProbabilityZeroRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C}
    {leftTerm rightTerm : Term (QubitPrimitive C)}
    (right : ChannelTree C
      { s with
        control := .term rightTerm
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
          s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize right) :
    ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.probabilityZero (left := leftTerm) right) where
  value := fun leaf => R.value (dropPhysical leaf)
  related := by
    intro o
    change ValueRel D₀ j₀ realize
      (right.instrument.value o).isTerminal.value
      (R.value (dropPhysical
        (prependPhysical true (right.instrument.value o))))
    simpa using R.related o

noncomputable def probabilityOneRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C}
    {leftTerm rightTerm : Term (QubitPrimitive C)}
    (left : ChannelTree C
      { s with
        control := .term leftTerm
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
          s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.probabilityOne (right := rightTerm) left)) :
    ChannelTreeRealization D₀ j₀ realize left where
  value := fun leaf => R.value (prependPhysical false leaf)
  related := fun o => R.related o

noncomputable def wrapProbabilityOneRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C}
    {leftTerm rightTerm : Term (QubitPrimitive C)}
    (left : ChannelTree C
      { s with
        control := .term leftTerm
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
          s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize left) :
    ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.probabilityOne (right := rightTerm) left) where
  value := fun leaf => R.value (dropPhysical leaf)
  related := by
    intro o
    change ValueRel D₀ j₀ realize
      (left.instrument.value o).isTerminal.value
      (R.value (dropPhysical
        (prependPhysical false (left.instrument.value o))))
    simpa using R.related o

theorem embed_restricted_probabilityZero {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C}
    {leftTerm rightTerm : Term (QubitPrimitive C)}
    (right : ChannelTree C
      { s with
        control := .term rightTerm
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
          s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.probabilityZero (left := leftTerm) right))
    (selectors : List Bool) (i : ℕ) :
    embed (restrictedInstrument D₀ j₀ realize
        (ChannelTree.probabilityZero (left := leftTerm) right) R
        selectors i) =
      embed (restrictedInstrument D₀ j₀ realize right
        (probabilityZeroRealization D₀ j₀ realize right R)
        selectors i) := by
  let μ := restrictedInstrument D₀ j₀ realize
    (ChannelTree.probabilityZero (left := leftTerm) right) R selectors i
  let ν := restrictedInstrument D₀ j₀ realize right
    (probabilityZeroRealization D₀ j₀ realize right R) selectors i
  refine embed_congr_of_outcome_equiv μ ν ?e ?hbranch ?hvalue
  · exact
      { toFun := fun p => ⟨p.1, p.2⟩
        invFun := fun q => ⟨q.1, q.2⟩
        left_inv := by
          intro p
          rcases p with ⟨o, ho⟩
          rfl
        right_inv := by
          intro q
          rcases q with ⟨o, ho⟩
          rfl }
  · intro p
    rfl
  · intro p
    rfl

theorem embed_restricted_probabilityOne {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C}
    {leftTerm rightTerm : Term (QubitPrimitive C)}
    (left : ChannelTree C
      { s with
        control := .term leftTerm
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
          s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.probabilityOne (right := rightTerm) left))
    (selectors : List Bool) (i : ℕ) :
    embed (restrictedInstrument D₀ j₀ realize
        (ChannelTree.probabilityOne (right := rightTerm) left) R
        selectors i) =
      embed (restrictedInstrument D₀ j₀ realize left
        (probabilityOneRealization D₀ j₀ realize left R)
        selectors i) := by
  let μ := restrictedInstrument D₀ j₀ realize
    (ChannelTree.probabilityOne (right := rightTerm) left) R selectors i
  let ν := restrictedInstrument D₀ j₀ realize left
    (probabilityOneRealization D₀ j₀ realize left R) selectors i
  refine embed_congr_of_outcome_equiv μ ν ?e ?hbranch ?hvalue
  · exact
      { toFun := fun p => ⟨p.1, p.2⟩
        invFun := fun q => ⟨q.1, q.2⟩
        left_inv := by
          intro p
          rcases p with ⟨o, ho⟩
          rfl
        right_inv := by
          intro q
          rcases q with ⟨o, ho⟩
          rfl }
  · intro p
    rfl
  · intro p
    rfl

theorem restrictedResult_probabilityZero {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C}
    {leftTerm rightTerm : Term (QubitPrimitive C)}
    (right : ChannelTree C
      { s with
        control := .term rightTerm
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
          s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.probabilityZero (left := leftTerm) right))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    restrictedResult D₀ j₀ realize
        (ChannelTree.probabilityZero (left := leftTerm) right) R
        selectors i k =
      restrictedResult D₀ j₀ realize right
        (probabilityZeroRealization D₀ j₀ realize right R)
        selectors i k := by
  classical
  let childR := probabilityZeroRealization D₀ j₀ realize right R
  have havail_iff :
      ResultAvailable
          (ChannelTree.probabilityZero (left := leftTerm) right)
          selectors i ↔
        ResultAvailable right selectors i :=
    Iff.rfl
  by_cases havail :
      ResultAvailable
        (ChannelTree.probabilityZero (left := leftTerm) right)
        selectors i
  · rw [restrictedResult_eq_embed D₀ j₀ realize _ R selectors i k havail,
      restrictedResult_eq_embed D₀ j₀ realize right childR selectors i k
        (havail_iff.mp havail),
      embed_restricted_probabilityZero]
  · rw [restrictedResult_eq_bot D₀ j₀ realize _ R selectors i k havail,
      restrictedResult_eq_bot D₀ j₀ realize right childR selectors i k
        (fun hc => havail (havail_iff.mpr hc))]

theorem restrictedResult_probabilityOne {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C}
    {leftTerm rightTerm : Term (QubitPrimitive C)}
    (left : ChannelTree C
      { s with
        control := .term leftTerm
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
          s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.probabilityOne (right := rightTerm) left))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    restrictedResult D₀ j₀ realize
        (ChannelTree.probabilityOne (right := rightTerm) left) R
        selectors i k =
      restrictedResult D₀ j₀ realize left
        (probabilityOneRealization D₀ j₀ realize left R)
        selectors i k := by
  classical
  let childR := probabilityOneRealization D₀ j₀ realize left R
  have havail_iff :
      ResultAvailable
          (ChannelTree.probabilityOne (right := rightTerm) left)
          selectors i ↔
        ResultAvailable left selectors i :=
    Iff.rfl
  by_cases havail :
      ResultAvailable
        (ChannelTree.probabilityOne (right := rightTerm) left)
        selectors i
  · rw [restrictedResult_eq_embed D₀ j₀ realize _ R selectors i k havail,
      restrictedResult_eq_embed D₀ j₀ realize left childR selectors i k
        (havail_iff.mp havail),
      embed_restricted_probabilityOne]
  · rw [restrictedResult_eq_bot D₀ j₀ realize _ R selectors i k havail,
      restrictedResult_eq_bot D₀ j₀ realize left childR selectors i k
        (fun hc => havail (havail_iff.mpr hc))]

/-- Invert a probability-zero tree at a general source configuration. -/
theorem restrictedResult_of_control_prob_zero {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C}
    (tree : ChannelTree C s)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.prob 0 left right))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    restrictedResult D₀ j₀ realize tree R selectors i k ≤
      sSup (channelTreeResults D₀ j₀ realize
        { s with
          control := .term right
          quantum := applyOperation
            (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
            s.quantum }
        selectors i k) := by
  cases tree with
  | terminal hterm =>
      have := hterm.control_eq.symm.trans hc
      cases this
  | internal h _ =>
      exact False.elim (ChannelInternalStep.not_prob h hc)
  | external _ h _ =>
      exact False.elim (ChannelExternalStep.not_prob h hc)
  | probability hp₀' _ _ _ =>
      have hp : (0 : ℝ) = 0 := rfl
      injection hc with hterm
      injection hterm with hp0
      exact (lt_irrefl (0 : ℝ) (hp0 ▸ hp₀')).elim
  | @probabilityZero _ L R next =>
      injection hc with hterm
      injection hterm with _ hL hR
      subst hL
      subst hR
      rw [restrictedResult_probabilityZero]
      apply le_sSup
      exact ⟨next.depth, next,
        probabilityZeroRealization D₀ j₀ realize next R, le_rfl, rfl⟩
  | probabilityOne _ =>
      injection hc with hterm
      injection hterm with hp01
      exact (one_ne_zero hp01).elim
  | measurement _ _ =>
      cases hc

/-- Invert a probability-one tree at a general source configuration. -/
theorem restrictedResult_of_control_prob_one {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C}
    (tree : ChannelTree C s)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.prob 1 left right))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    restrictedResult D₀ j₀ realize tree R selectors i k ≤
      sSup (channelTreeResults D₀ j₀ realize
        { s with
          control := .term left
          quantum := applyOperation
            (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
            s.quantum }
        selectors i k) := by
  cases tree with
  | terminal hterm =>
      have := hterm.control_eq.symm.trans hc
      cases this
  | internal h _ =>
      exact False.elim (ChannelInternalStep.not_prob h hc)
  | external _ h _ =>
      exact False.elim (ChannelExternalStep.not_prob h hc)
  | probability _ hp₁' _ _ =>
      injection hc with hterm
      injection hterm with hp1
      exact (lt_irrefl (1 : ℝ) (hp1 ▸ hp₁')).elim
  | probabilityZero _ =>
      injection hc with hterm
      injection hterm with hp10
      exact (zero_ne_one hp10).elim
  | @probabilityOne _ L R next =>
      injection hc with hterm
      injection hterm with _ hL hR
      subst hL
      subst hR
      rw [restrictedResult_probabilityOne]
      apply le_sSup
      exact ⟨next.depth, next,
        probabilityOneRealization D₀ j₀ realize next R, le_rfl, rfl⟩
  | measurement _ _ =>
      cases hc

/-- Invert an interior probability tree at a presented continuation. -/
theorem restrictedResult_of_control_prob_presented {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C}
    (tree : ChannelTree C s)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    {p : ℝ} {left right : Term (QubitPrimitive C)}
    (hp₀ : 0 < p) (hp₁ : p < 1)
    (hc : s.control = .term (.prob p left right))
    (selectors : List Bool) (i : ℕ)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode) :
    restrictedResult D₀ j₀ realize tree R selectors i k ≤
      TTWeightedAggregation.weightedResultScott p hp₀.le hp₁.le
        (sSup (channelTreeResults D₀ j₀ realize
            { s with
              control := .term left
              quantum := applyOperation
                (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum }
            selectors i k),
          sSup (channelTreeResults D₀ j₀ realize
            { s with
              control := .term right
              quantum := applyOperation
                (sourceProbabilityOperation (1 - p)
                  (sub_nonneg.mpr hp₁.le) (by linarith)) s.quantum }
            selectors i k)) := by
  cases tree with
  | terminal hterm =>
      have := hterm.control_eq.symm.trans hc
      cases this
  | internal h _ =>
      exact False.elim (ChannelInternalStep.not_prob h hc)
  | external _ h _ =>
      exact False.elim (ChannelExternalStep.not_prob h hc)
  | probability hp₀' hp₁' leftT rightT =>
      have hp : p = p := rfl
      -- After cases, `hc` identifies the source weight with `p`.
      cases hc
      rw [restrictedResult_probability_presented D₀ j₀ realize
        hp₀' hp₁' leftT rightT R selectors i ξ k hk]
      exact
        (TTWeightedAggregation.weightedResultScott
          p hp₀.le hp₁.le).monotone
          ⟨le_sSup ⟨leftT.depth, leftT,
              probabilityLeftRealization D₀ j₀ realize hp₀' hp₁'
                leftT rightT R, le_rfl, rfl⟩,
            le_sSup ⟨rightT.depth, rightT,
              probabilityRightRealization D₀ j₀ realize hp₀' hp₁'
                leftT rightT R, le_rfl, rfl⟩⟩
  | probabilityZero _ =>
      injection hc with hterm
      injection hterm with hp0
      exact (ne_of_gt hp₀ hp0.symm).elim
  | probabilityOne _ =>
      injection hc with hterm
      injection hterm with hp1
      exact (ne_of_lt hp₁ hp1.symm).elim
  | measurement _ _ =>
      cases hc

theorem selectPath_prob {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (p : Prob) (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize) (.prob p left right)
          semanticEnv) i k =
      TTContinuation.probChoice p
        (HardwareAdequacy.selectPath selectors
          (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv) i,
          HardwareAdequacy.selectPath selectors
            (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)
            i) k := by
  rw [interp_prob_apply, HardwareAdequacy.selectPath_apply_encode,
    TTContinuation.computation_prob_apply,
    HardwareAdequacy.selectPath_apply_encode,
    HardwareAdequacy.selectPath_apply_encode,
    TTContinuation.probChoice_apply]

theorem selectPath_prob_zero {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize) (.prob 0 left right)
          semanticEnv) i k =
      HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv) i k := by
  rw [selectPath_prob, TTContinuation.probChoice_zero]

theorem selectPath_prob_one {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize) (.prob 1 left right)
          semanticEnv) i k =
      HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv) i k := by
  rw [selectPath_prob, TTContinuation.probChoice_one]

theorem applyOperation_sourceProbability_of_one
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hp : p = 1)
    (ρ : SubNormalizedDensity 2) :
    applyOperation (sourceProbabilityOperation p hp₀ hp₁) ρ = ρ := by
  subst hp
  exact applyOperation_sourceProbability_one ρ

theorem applyOperation_sourceProbability_one_initial {C : Type}
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2) :
    applyOperation
        (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
        (initialChannelConfig (.prob 0 left right) quantum).quantum =
      (initialChannelConfig right quantum).quantum := by
  apply SubNormalizedDensity.ext
  rw [applyOperation_sourceProbability_one]
  rfl

theorem probRightConfig_zero_eq {C : Type}
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2) :
    probRightConfig 0 (le_refl 0) zero_le_one left right quantum =
      initialChannelConfig right quantum := by
  unfold probRightConfig
  apply ChannelConfig.ext
  · rfl
  · rfl
  · rfl
  · exact applyOperation_sourceProbability_of_one
      (sub_nonneg.mpr (zero_le_one : (0 : ℝ) ≤ 1))
      (by linarith : (1 - 0 : ℝ) ≤ 1) (sub_zero 1)
      (initialChannelConfig (.prob 0 left right) quantum).quantum

theorem probLeftConfig_one_eq {C : Type}
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2) :
    probLeftConfig 1 zero_le_one (le_refl 1) left right quantum =
      initialChannelConfig left quantum := by
  unfold probLeftConfig
  apply ChannelConfig.ext
  · rfl
  · rfl
  · rfl
  · apply SubNormalizedDensity.ext
    rw [applyOperation_sourceProbability_one]
    rfl

/-- Physical weighted bind of two restricted children, used only to name the
folded interior probability instrument.  Lattice join is never used. -/
theorem embed_restricted_prob_bind {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {p : ℝ}
    {leftTerm rightTerm : Term (QubitPrimitive C)}
    (hp₀ : 0 < p) (hp₁ : p < 1)
    (left : ChannelTree C
      { s with
        control := .term leftTerm
        quantum := applyOperation
          (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum })
    (right : ChannelTree C
      { s with
        control := .term rightTerm
        quantum := applyOperation
          (sourceProbabilityOperation (1 - p)
            (sub_nonneg.mpr hp₁.le) (by linarith)) s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.probability hp₀ hp₁ left right))
    (selectors : List Bool) (i : ℕ) :
    embed (restrictedInstrument D₀ j₀ realize
        (ChannelTree.probability hp₀ hp₁ left right) R selectors i) =
      embed ((probabilityInstrument p hp₀.le hp₁.le).bind
        (fun b => if b then
          restrictedInstrument D₀ j₀ realize right
            (probabilityRightRealization D₀ j₀ realize hp₀ hp₁ left right R)
            selectors i
        else
          restrictedInstrument D₀ j₀ realize left
            (probabilityLeftRealization D₀ j₀ realize hp₀ hp₁ left right R)
            selectors i)) := by
  simpa [FiniteInstrumentComp.weightedResult] using
    (embed_restricted_probability D₀ j₀ realize hp₀ hp₁ left right R
      selectors i).trans
      (embed_congr_of_outcome_equiv
        ((FiniteInstrumentComp.weightedCoin (n := 2) p hp₀.le hp₁.le).bind
          (fun b => if b then
            restrictedInstrument D₀ j₀ realize right
              (probabilityRightRealization D₀ j₀ realize hp₀ hp₁ left right R)
              selectors i
          else
            restrictedInstrument D₀ j₀ realize left
              (probabilityLeftRealization D₀ j₀ realize hp₀ hp₁ left right R)
              selectors i))
        ((probabilityInstrument p hp₀.le hp₁.le).bind
          (fun b => if b then
            restrictedInstrument D₀ j₀ realize right
              (probabilityRightRealization D₀ j₀ realize hp₀ hp₁ left right R)
              selectors i
          else
            restrictedInstrument D₀ j₀ realize left
              (probabilityLeftRealization D₀ j₀ realize hp₀ hp₁ left right R)
              selectors i))
        { toFun := id
          invFun := id
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
        (by
          intro q
          rcases q with ⟨b, o⟩
          cases b <;> rfl)
        (by
          intro q
          rcases q with ⟨b, o⟩
          cases b <;> rfl))

theorem ChannelTreeCompleteness.congr {C : Type}
    {D₀ : QDomain.{0}}
    {j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier)}
    {realize : C → HSemanticValue D₀ j₀}
    {start start' : ChannelConfig C}
    {denotation denotation' : HSemanticComp D₀ j₀}
    (hstart : start = start') (hden : denotation = denotation')
    (h : ChannelTreeCompleteness D₀ j₀ realize start denotation) :
    ChannelTreeCompleteness D₀ j₀ realize start' denotation' := by
  subst hstart
  subst hden
  exact h

theorem PresentedChannelTreeCompleteness.congr {C : Type}
    {D₀ : QDomain.{0}}
    {j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier)}
    {realize : C → HSemanticValue D₀ j₀}
    {start start' : ChannelConfig C}
    {denotation denotation' : HSemanticComp D₀ j₀}
    (hstart : start = start') (hden : denotation = denotation')
    (h : PresentedChannelTreeCompleteness D₀ j₀ realize start denotation) :
    PresentedChannelTreeCompleteness D₀ j₀ realize start' denotation' := by
  subst hstart
  subst hden
  exact h

/-- Endpoint completeness at weight zero: the live right child is copied,
and the discarded left branch contributes no physical observation. -/
theorem prob_zero_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hright : ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig right quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)) :
    ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.prob 0 left right) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) (.prob 0 left right)
        semanticEnv) where
  selected_result_eq_channelTree_sup := by
    intro selectors i k
    have hright' :=
      ChannelTreeCompleteness.congr
        (show
            { initialChannelConfig (.prob 0 left right) quantum with
              control := .term right
              quantum := applyOperation
                (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                (initialChannelConfig (.prob 0 left right) quantum).quantum } =
              initialChannelConfig right quantum from
          ChannelConfig.ext rfl rfl rfl
            (applyOperation_sourceProbability_one_initial left right quantum)).symm
        rfl hright
    rw [selectPath_prob_zero,
      hright'.selected_result_eq_channelTree_sup]
    apply le_antisymm
    · apply sSup_le
      rintro T ⟨fuel, child, R, hdepth, rfl⟩
      apply le_sSup
      refine ⟨fuel + 1, wrapProbZero left right quantum child,
        wrapProbabilityZeroRealization D₀ j₀ realize
          (s := initialChannelConfig (.prob 0 left right) quantum)
          (leftTerm := left) (rightTerm := right) child R, ?_, ?_⟩
      · simpa [wrapProbZero_depth] using Nat.succ_le_succ hdepth
      · exact
          (restrictedResult_probabilityZero D₀ j₀ realize child
            (wrapProbabilityZeroRealization D₀ j₀ realize
              (s := initialChannelConfig (.prob 0 left right) quantum)
              (leftTerm := left) (rightTerm := right) child R)
            selectors i k).symm
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      have hle :=
        restrictedResult_of_control_prob_zero D₀ j₀ realize tree R rfl
          selectors i k
      exact hle

/-- Endpoint completeness at weight one: the live left child is copied. -/
theorem prob_one_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hleft : ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig left quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv)) :
    ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.prob 1 left right) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) (.prob 1 left right)
        semanticEnv) where
  selected_result_eq_channelTree_sup := by
    intro selectors i k
    have hleft' :=
      ChannelTreeCompleteness.congr
        (show
            { initialChannelConfig (.prob 1 left right) quantum with
              control := .term left
              quantum := applyOperation
                (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                (initialChannelConfig (.prob 1 left right) quantum).quantum } =
              initialChannelConfig left quantum from
          ChannelConfig.ext rfl rfl rfl (by
            apply SubNormalizedDensity.ext
            rw [applyOperation_sourceProbability_one]
            rfl)).symm
        rfl hleft
    rw [selectPath_prob_one, hleft'.selected_result_eq_channelTree_sup]
    apply le_antisymm
    · apply sSup_le
      rintro T ⟨fuel, child, R, hdepth, rfl⟩
      apply le_sSup
      refine ⟨fuel + 1, wrapProbOne left right quantum child,
        wrapProbabilityOneRealization D₀ j₀ realize
          (s := initialChannelConfig (.prob 1 left right) quantum)
          (leftTerm := left) (rightTerm := right) child R, ?_, ?_⟩
      · simpa [wrapProbOne_depth] using Nat.succ_le_succ hdepth
      · exact
          (restrictedResult_probabilityOne D₀ j₀ realize child
            (wrapProbabilityOneRealization D₀ j₀ realize
              (s := initialChannelConfig (.prob 1 left right) quantum)
              (leftTerm := left) (rightTerm := right) child R)
            selectors i k).symm
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      have hle :=
        restrictedResult_of_control_prob_one D₀ j₀ realize tree R rfl
          selectors i k
      exact hle

/-- Interior probabilistic choice, at a finitely presented continuation, is
the physical weighted combination of the two child-tree suprema. -/
theorem prob_channelTreeCompleteness_presented {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hleft : ChannelTreeCompleteness D₀ j₀ realize
      (probLeftConfig p hp₀.le hp₁.le left right quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv))
    (hright : ChannelTreeCompleteness D₀ j₀ realize
      (probRightConfig p hp₀.le hp₁.le left right quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.prob p left right) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) (.prob p left right)
        semanticEnv) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ k hk
    have hpI : 0 ≤ p ∧ p ≤ 1 := ⟨hp₀.le, hp₁.le⟩
    rw [selectPath_prob, TTContinuation.probChoice_apply, dif_pos hpI,
      hleft.selected_result_eq_channelTree_sup,
      hright.selected_result_eq_channelTree_sup]
    let SL :=
      channelTreeResults D₀ j₀ realize
        (probLeftConfig p hp₀.le hp₁.le left right quantum) selectors i k
    let SR :=
      channelTreeResults D₀ j₀ realize
        (probRightConfig p hp₀.le hp₁.le left right quantum) selectors i k
    refine le_antisymm ?_ ?_
    · by_cases hL : SL.Nonempty
      · by_cases hR : SR.Nonempty
        · rw [TTWeightedAggregation.weightedResultScott_sSup_product
            p hp₀.le hp₁.le SL SR hL hR]
          apply sSup_le
          rintro _ ⟨⟨TL, TR⟩, ⟨⟨fuelL, leftT, leftR, hdepthL, rfl⟩,
              ⟨fuelR, rightT, rightR, hdepthR, rfl⟩⟩, rfl⟩
          apply le_sSup
          refine ⟨max fuelL fuelR + 1,
            wrapProb hp₀ hp₁ left right quantum leftT rightT,
            wrapProbabilityRealization D₀ j₀ realize hp₀ hp₁ leftT rightT
              leftR rightR, ?_, ?_⟩
          · simp [wrapProb_depth]
            omega
          · exact
              (restrictedResult_probability_presented D₀ j₀ realize hp₀ hp₁
                leftT rightT
                (wrapProbabilityRealization D₀ j₀ realize hp₀ hp₁
                  leftT rightT leftR rightR)
                selectors i ξ k hk).symm
        · have hbot :
              TTWeightedAggregation.weightedResultScott p hp₀.le hp₁.le
                (sSup SL, sSup SR) = ⊥ := by
            have : sSup SR = ⊥ := by
              have hempty : SR = ∅ :=
                Set.not_nonempty_iff_eq_empty.mp hR
              rw [hempty, sSup_empty]
            rw [this, TTWeightedAggregation.weightedResultScott_bot_right
              p hp₀ hp₁]
          rw [hbot]
          exact bot_le
      · have hbot :
            TTWeightedAggregation.weightedResultScott p hp₀.le hp₁.le
              (sSup SL, sSup SR) = ⊥ := by
          have : sSup SL = ⊥ := by
            have hempty : SL = ∅ :=
              Set.not_nonempty_iff_eq_empty.mp hL
            rw [hempty, sSup_empty]
          rw [this, TTWeightedAggregation.weightedResultScott_bot_left
            p hp₀ hp₁]
        rw [hbot]
        exact bot_le
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      have hle :=
        restrictedResult_of_control_prob_presented D₀ j₀ realize tree R
          hp₀ hp₁ rfl selectors i ξ k hk
      have hL :
          { initialChannelConfig (.prob p left right) quantum with
              control := .term left
              quantum := applyOperation
                (sourceProbabilityOperation p hp₀.le hp₁.le)
                (initialChannelConfig (.prob p left right) quantum).quantum } =
            probLeftConfig p hp₀.le hp₁.le left right quantum := by
        apply ChannelConfig.ext <;> rfl
      have hR :
          { initialChannelConfig (.prob p left right) quantum with
              control := .term right
              quantum := applyOperation
                (sourceProbabilityOperation (1 - p)
                  (sub_nonneg.mpr hp₁.le) (by linarith))
                (initialChannelConfig (.prob p left right) quantum).quantum } =
            probRightConfig p hp₀.le hp₁.le left right quantum := by
        apply ChannelConfig.ext <;> rfl
      simpa [hL, hR] using hle

theorem prob_returns_zero_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (leftValue rightValue : C) (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.prob 0 (.prim (.ret leftValue)) (.prim (.ret rightValue)))
        quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.prob 0 (.prim (.ret leftValue)) (.prim (.ret rightValue)))
        semanticEnv) :=
  prob_zero_channelTreeCompleteness D₀ j₀ realize _ _ quantum semanticEnv
    (return_channelTreeCompleteness D₀ j₀ realize rightValue quantum
      semanticEnv)

theorem prob_returns_one_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (leftValue rightValue : C) (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.prob 1 (.prim (.ret leftValue)) (.prim (.ret rightValue)))
        quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.prob 1 (.prim (.ret leftValue)) (.prim (.ret rightValue)))
        semanticEnv) :=
  prob_one_channelTreeCompleteness D₀ j₀ realize _ _ quantum semanticEnv
    (return_channelTreeCompleteness D₀ j₀ realize leftValue quantum
      semanticEnv)

/-- Compositional interior probability at the presented-continuation
boundary, plus exact endpoint completeness for every `0 ≤ p ≤ 1`.
Interior weights remain physical coin aggregation, never lattice join. -/
theorem prob_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hleft : ChannelTreeCompleteness D₀ j₀ realize
      (if p = 0 then initialChannelConfig right quantum
        else if p = 1 then initialChannelConfig left quantum
        else probLeftConfig p hp₀ hp₁ left right quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (if p = 0 then right else left) semanticEnv))
    (hright : ChannelTreeCompleteness D₀ j₀ realize
      (if p = 1 then initialChannelConfig left quantum
        else if p = 0 then initialChannelConfig right quantum
        else probRightConfig p hp₀ hp₁ left right quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (if p = 1 then left else right) semanticEnv)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.prob p left right) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) (.prob p left right)
        semanticEnv) := by
  by_cases hz : p = 0
  · subst p
    exact
      (prob_zero_channelTreeCompleteness D₀ j₀ realize left right quantum
        semanticEnv (by simpa using hright)).toPresented
  · by_cases ho : p = 1
    · subst p
      exact
        (prob_one_channelTreeCompleteness D₀ j₀ realize left right quantum
          semanticEnv (by simpa using hleft)).toPresented
    · have hp₀' : 0 < p := lt_of_le_of_ne hp₀ (Ne.symm hz)
      have hp₁' : p < 1 := lt_of_le_of_ne hp₁ ho
      exact
        prob_channelTreeCompleteness_presented D₀ j₀ realize p hp₀' hp₁'
          left right quantum semanticEnv (by simpa [hz, ho] using hleft)
          (by simpa [hz, ho] using hright)

/-- Endpoint probabilistic returns are exactly complete.  Interior weights
use the compositional presented theorem once each scaled child is known
to be complete; the zero-weight branch is never replaced by lattice join. -/
theorem prob_returns_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (p : ℝ) (hp : p = 0 ∨ p = 1)
    (leftValue rightValue : C) (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.prob p (.prim (.ret leftValue)) (.prim (.ret rightValue)))
        quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.prob p (.prim (.ret leftValue)) (.prim (.ret rightValue)))
        semanticEnv) := by
  rcases hp with rfl | rfl
  · exact prob_returns_zero_channelTreeCompleteness D₀ j₀ realize
      leftValue rightValue quantum semanticEnv
  · exact prob_returns_one_channelTreeCompleteness D₀ j₀ realize
      leftValue rightValue quantum semanticEnv

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
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind ξ) := by
  classical
  rw [hcomplete.selected_result_eq_channelTree_sup selectors i k,
    RoundedTheory.mem_sSup]
  constructor
  · rintro ⟨_, ⟨fuel, tree, R, hdepth, rfl⟩, htoken⟩
    by_cases havail : ResultAvailable tree selectors i
    · refine ⟨fuel, tree, R, hdepth, havail, ?_⟩
      apply (token_of_restrictedInstrument D₀ j₀ realize tree R selectors i
        ξ k (fun o => hk _) token).1
      rw [restrictedResult_eq_embed D₀ j₀ realize tree R selectors i k havail]
        at htoken
      exact htoken
    · rw [restrictedResult_eq_bot D₀ j₀ realize tree R selectors i k havail]
        at htoken
      have hfalse : False := by
        rw [← sSup_empty, RoundedTheory.mem_sSup] at htoken
        simpa using htoken
      exact hfalse.elim
  · rintro ⟨fuel, tree, R, hdepth, havail, htoken⟩
    refine ⟨restrictedResult D₀ j₀ realize tree R selectors i k, ?_, ?_⟩
    · exact ⟨fuel, tree, R, hdepth, rfl⟩
    · rw [restrictedResult_eq_embed D₀ j₀ realize tree R selectors i k havail]
      exact (token_of_restrictedInstrument D₀ j₀ realize tree R selectors i
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

/-! ## Application, stack bind, and the related-state fundamental lemma -/

/-- Application installs its argument frame at the active coordinate. -/
theorem path_channel_config_application {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {fn arg : Term (QubitPrimitive C)}
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app fn arg)}
      active observedStack finalK result) :
    PathChannelConfigRel D₀ j₀ realize
      {s with
        control := .term fn
        stack := .argument arg s.env :: s.stack}
      active ((.argument arg s.env, active) :: observedStack)
      finalK result := by
  rcases hrel with ⟨herase, current, currentK, hcontrol, hstack, hresult⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨by simp [herase], interp (hardwarePrimitive D₀ j₀ realize) fn
        semanticEnv, _, ControlRel.term fn s.env semanticEnv henv,
        PathStackRel.argument arg s.env semanticEnv active observedStack
          currentK henv hstack, ?_⟩
      rw [hresult, interp_app_apply]
      rfl

/-- An explicit external choice consumes one branch coordinate only from the
active control; saved frame coordinates remain unchanged. -/
theorem path_channel_config_externalSelect {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {selected : Bool}
    {left right : Term (QubitPrimitive C)}
    {childCoordinate : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      {s with control := .term (.extern left right)}
      (HardwareAdequacy.branchCoordinate selected childCoordinate)
      observedStack finalK result) :
    PathChannelConfigRel D₀ j₀ realize
      {s with control := .term (if selected then right else left)}
      childCoordinate observedStack finalK result := by
  rcases hrel with ⟨herase, current, currentK, hcontrol, hstack, hresult⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨herase, interp (hardwarePrimitive D₀ j₀ realize)
        (if selected then right else left) semanticEnv, currentK,
        ControlRel.term _ s.env semanticEnv henv, hstack, ?_⟩
      rw [hresult]
      exact selectPath_extern_coordinate D₀ j₀ realize left right semanticEnv
        selected childCoordinate currentK

theorem path_channel_config_probabilityZero {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      {s with control := .term (.prob 0 left right)}
      active observedStack finalK result) :
    PathChannelConfigRel D₀ j₀ realize
      {s with
        control := .term right
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1)) s.quantum}
      active observedStack finalK result := by
  rcases hrel with ⟨herase, current, currentK, hcontrol, hstack, hresult⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨herase,
        interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv,
        currentK, ControlRel.term right s.env semanticEnv henv, hstack, ?_⟩
      rw [hresult]
      exact selectPath_prob_zero D₀ j₀ realize left right semanticEnv
        [] active currentK

theorem path_channel_config_probabilityOne {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      {s with control := .term (.prob 1 left right)}
      active observedStack finalK result) :
    PathChannelConfigRel D₀ j₀ realize
      {s with
        control := .term left
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1)) s.quantum}
      active observedStack finalK result := by
  rcases hrel with ⟨herase, current, currentK, hcontrol, hstack, hresult⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨herase,
        interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv,
        currentK, ControlRel.term left s.env semanticEnv henv, hstack, ?_⟩
      rw [hresult]
      exact selectPath_prob_one D₀ j₀ realize left right semanticEnv
        [] active currentK

/-- Returning a function restores the coordinate saved by its argument
frame and installs the corresponding function frame at that coordinate. -/
theorem path_channel_config_evaluateArgument {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {fn : RuntimeValue C}
    {arg : Term (QubitPrimitive C)} {callEnv : RuntimeEnv C}
    {rest : EvalStack C} {active saved : ℕ}
    {observedRest : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      {s with
        control := .value fn
        stack := .argument arg callEnv :: rest}
      active ((.argument arg callEnv, saved) :: observedRest)
      finalK result) :
    PathChannelConfigRel D₀ j₀ realize
      {s with
        control := .term arg
        env := callEnv
        stack := .function fn :: rest}
      saved ((.function fn, saved) :: observedRest) finalK result := by
  rcases hrel with ⟨herase, current, currentK, hcontrol, hstack, hresult⟩
  cases hcontrol with
  | value _ f _ hfn =>
      cases hstack with
      | argument _ _ semanticEnv _ _ restK henv hrest =>
          have heraseRest : observedRest.erase = rest := by
            simpa using congrArg List.tail herase
          refine ⟨by simp [heraseRest],
            interp (hardwarePrimitive D₀ j₀ realize) arg semanticEnv, _,
            ControlRel.term arg callEnv semanticEnv henv,
            PathStackRel.function fn f saved observedRest restK hfn hrest, ?_⟩
          rw [hresult]
          change
            TTContinuation.continuation
                ((TTContinuation.atCoordinate saved).comp
                  (applyContinuation (Q := TTExternalContinuationPower 2)
                    (D₀ := D₀) (j₀ := j₀)
                    (interp (hardwarePrimitive D₀ j₀ realize) arg)
                    semanticEnv))
                restK f =
              interp (hardwarePrimitive D₀ j₀ realize) arg semanticEnv saved
                (TTContinuation.continuation
                  ((TTContinuation.atCoordinate saved).comp
                    (semanticUnfold (Q := TTExternalContinuationPower 2)
                      (D₀ := D₀) (j₀ := j₀) f))
                  restK)
          simp only [ScottMap.comp_apply, TTContinuation.atCoordinate_apply,
            TTContinuation.continuation_apply]
          rw [applyContinuation_apply]
          rfl

/-- Closure beta pops the function frame and resumes the body at the
coordinate saved by that frame. -/
theorem path_channel_config_beta {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {x : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    {arg : RuntimeValue C} {rest : EvalStack C}
    {active saved : ℕ} {observedRest : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      {s with
        control := .value arg
        stack := .function (.closure x body closureEnv) :: rest}
      active ((.function (.closure x body closureEnv), saved) :: observedRest)
      finalK result) :
    PathChannelConfigRel D₀ j₀ realize
      {s with
        control := .term body
        env := RuntimeEnv.bind x arg closureEnv
        stack := rest}
      saved observedRest finalK result := by
  rcases hrel with ⟨herase, current, currentK, hcontrol, hstack, hresult⟩
  cases hcontrol with
  | value _ d _ harg =>
      cases hstack with
      | function _ f _ _ restK hfn hrest =>
          cases hfn with
          | closure _ _ _ semanticEnv henv =>
              have heraseRest : observedRest.erase = rest := by
                simpa using congrArg List.tail herase
              refine ⟨heraseRest,
                interp (hardwarePrimitive D₀ j₀ realize) body
                  (envUpdate (Q := TTExternalContinuationPower 2)
                    (D₀ := D₀) (j₀ := j₀) x (semanticEnv, d)),
                restK, ControlRel.term body _ _
                  (closure_beta_env D₀ j₀ henv harg), hrest, ?_⟩
              rw [hresult]
              simp only [semanticUnit, TTContinuation.taggedUnit,
                TTContinuation.continuation_apply, ScottMap.comp_apply,
                TTContinuation.atCoordinate_apply]
              exact congrArg (fun q : HSemanticComp D₀ j₀ =>
                q saved restK) (closure_application D₀ j₀
                  x body closureEnv semanticEnv arg d henv harg)

/-- Recursive beta has the same saved-coordinate discipline as ordinary
beta, while extending the body environment with both recursive binders. -/
theorem path_channel_config_recBeta {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {self x : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    {arg : RuntimeValue C} {rest : EvalStack C}
    {active saved : ℕ} {observedRest : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      {s with
        control := .value arg
        stack :=
          .function (.recClosure self x body closureEnv) :: rest}
      active
      ((.function (.recClosure self x body closureEnv), saved) :: observedRest)
      finalK result) :
    PathChannelConfigRel D₀ j₀ realize
      {s with
        control := .term body
        env :=
          RuntimeEnv.bind x arg
            (RuntimeEnv.bind self
              (.recClosure self x body closureEnv) closureEnv)
        stack := rest}
      saved observedRest finalK result := by
  rcases hrel with ⟨herase, current, currentK, hcontrol, hstack, hresult⟩
  cases hcontrol with
  | value _ d _ harg =>
      cases hstack with
      | function _ f _ _ restK hfn hrest =>
          cases hfn with
          | recClosure _ _ _ _ semanticEnv henv =>
              have heraseRest : observedRest.erase = rest := by
                simpa using congrArg List.tail herase
              refine ⟨heraseRest,
                interp (hardwarePrimitive D₀ j₀ realize) body
                  (envUpdate (Q := TTExternalContinuationPower 2)
                    (D₀ := D₀) (j₀ := j₀) x
                    (envUpdate (Q := TTExternalContinuationPower 2)
                      (D₀ := D₀) (j₀ := j₀) self
                      (semanticEnv,
                        recLambdaValue
                          (Q := TTExternalContinuationPower 2)
                          (D₀ := D₀) (j₀ := j₀) self x
                          (interp (hardwarePrimitive D₀ j₀ realize) body)
                          semanticEnv),
                      d)),
                restK, ControlRel.term body _ _
                  (recClosure_unfold_env D₀ j₀ henv harg), hrest, ?_⟩
              rw [hresult]
              simp only [semanticUnit, TTContinuation.taggedUnit,
                TTContinuation.continuation_apply, ScottMap.comp_apply,
                TTContinuation.atCoordinate_apply]
              exact congrArg (fun q : HSemanticComp D₀ j₀ =>
                q saved restK) (recClosure_application D₀ j₀
                  self x body closureEnv semanticEnv arg d henv harg)

/-- Recursive abstraction installs the related recursive closure without
changing the path-indexed result. -/
theorem path_channel_config_recursive {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {self arg : Name}
    {body : Term (QubitPrimitive C)}
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      {s with control := .term (.recLam self arg body)}
      active observedStack finalK result) :
    PathChannelConfigRel D₀ j₀ realize
      {s with control := .value (.recClosure self arg body s.env)}
      active observedStack finalK result := by
  rcases hrel with ⟨herase, current, currentK, hcontrol, hstack, hresult⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨herase,
        semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (recLambdaValue (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self arg
            (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv),
        currentK,
        ControlRel.value _ _ s.env
          (recClosure_created D₀ j₀ realize self arg body
            s.env semanticEnv henv),
        hstack, ?_⟩
      rw [hresult, interp_recLam_apply]

/-- Ordinary abstraction installs the related closure at the same
path-indexed result. -/
theorem path_channel_config_lambda {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {x : Name} {body : Term (QubitPrimitive C)}
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      {s with control := .term (.lam x body)}
      active observedStack finalK result) :
    PathChannelConfigRel D₀ j₀ realize
      {s with control := .value (.closure x body s.env)}
      active observedStack finalK result := by
  rcases hrel with ⟨herase, current, currentK, hcontrol, hstack, hresult⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨herase,
        semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (lambdaValue (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) x
            (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv),
        currentK,
        ControlRel.value _ _ s.env
          (closure_created D₀ j₀ realize x body s.env semanticEnv henv),
        hstack, ?_⟩
      rw [hresult, interp_lam_apply]

/-- A returned value is observed by applying the current continuation, so
the path-indexed relation does not depend on the active coordinate. -/
theorem path_channel_config_value_reindex {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {value : RuntimeValue C}
    (hc : s.control = .value value)
    {active active' : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result) :
    PathChannelConfigRel D₀ j₀ realize
      s active' observedStack finalK result := by
  rcases hrel with ⟨herase, current, currentK, hcontrol, hstack, hresult⟩
  rw [hc] at hcontrol
  cases hcontrol with
  | value _ d _ hvalue =>
      refine ⟨herase, semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) d, currentK,
        hc.symm ▸ ControlRel.value value d s.env hvalue, hstack, ?_⟩
      rw [hresult]
      rfl

/-- Variable lookup installs the related runtime value at the same
path-indexed result. -/
theorem path_channel_config_variable {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {x : Name} {v : RuntimeValue C}
    (hc : s.control = .term (.var x))
    (hlookup : RuntimeEnv.lookup x s.env = some v)
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result) :
    PathChannelConfigRel D₀ j₀ realize
      {s with control := .value v}
      active observedStack finalK result := by
  rcases hrel with ⟨herase, current, currentK, hcontrol, hstack, hresult⟩
  rw [hc] at hcontrol
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨herase,
        semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) (semanticEnv x),
        currentK,
        ControlRel.value v (semanticEnv x) s.env
          (env_lookup D₀ j₀ henv hlookup),
        hstack, ?_⟩
      rw [hresult, interp_var_apply]

theorem channel_config_lambda {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {x : Name} {body : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.lam x body)} answer) :
    ChannelConfigRel D₀ j₀ realize
      {s with control := .value (.closure x body s.env)} answer := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (lambdaValue (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) x
            (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv),
        k, ControlRel.value _ _ s.env
          (closure_created D₀ j₀ realize x body s.env semanticEnv henv),
        hstack, ?_⟩
      rw [interp_lam_apply]

theorem channel_config_recursive {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {self arg : Name}
    {body : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.recLam self arg body)} answer) :
    ChannelConfigRel D₀ j₀ realize
      {s with control := .value (.recClosure self arg body s.env)}
      answer := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (recLambdaValue (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self arg
            (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv),
        k, ControlRel.value _ _ s.env
          (recClosure_created D₀ j₀ realize self arg body
            s.env semanticEnv henv),
        hstack, ?_⟩
      rw [interp_recLam_apply]

theorem channel_config_variable {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {x : Name} {v : RuntimeValue C}
    (hlookup : RuntimeEnv.lookup x s.env = some v)
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.var x)} answer) :
    ChannelConfigRel D₀ j₀ realize
      {s with control := .value v} answer := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) (semanticEnv x), k,
        ControlRel.value v (semanticEnv x) s.env
          (env_lookup D₀ j₀ henv hlookup), hstack, ?_⟩
      rw [interp_var_apply]

theorem channel_config_application {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {fn arg : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app fn arg)} answer) :
    ChannelConfigRel D₀ j₀ realize
      {s with control := .term fn,
              stack := .argument arg s.env :: s.stack} answer := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨interp (hardwarePrimitive D₀ j₀ realize) fn semanticEnv,
        (fun mf => k
          (semanticBind (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)
            (applyContinuation (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀)
              (interp (hardwarePrimitive D₀ j₀ realize) arg) semanticEnv)
            mf)), ?_, ?_, ?_⟩
      · exact ControlRel.term fn s.env semanticEnv henv
      · exact stack_push_argument D₀ j₀ henv hstack
      · exact (application_under_stack D₀ j₀ realize
          fn arg semanticEnv k).symm

theorem channel_config_evaluateArgument {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {fn : RuntimeValue C}
    {arg : Term (QubitPrimitive C)} {callEnv : RuntimeEnv C}
    {rest : EvalStack C} {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize
      {s with control := .value fn,
              stack := .argument arg callEnv :: rest} answer) :
    ChannelConfigRel D₀ j₀ realize
      {s with control := .term arg,
              env := callEnv,
              stack := .function fn :: rest} answer := by
  rcases hrel with ⟨current, outer, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | value _ f _ hfn =>
      cases hstack with
      | argument _ _ semanticEnv _ k henv hrest =>
          refine ⟨interp (hardwarePrimitive D₀ j₀ realize) arg semanticEnv,
            (fun ma => k
              (semanticBind (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀)
                (semanticUnfold (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) f)
                ma)), ?_, ?_, ?_⟩
          · exact ControlRel.term arg callEnv semanticEnv henv
          · exact stack_argument_to_function D₀ j₀ hfn hrest
          · exact (evaluateArgument_under_stack D₀ j₀
              arg semanticEnv f k).symm

theorem channel_config_beta {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {x : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    {arg : RuntimeValue C} {rest : EvalStack C}
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize
      {s with control := .value arg,
              stack := .function (.closure x body closureEnv) :: rest}
      answer) :
    ChannelConfigRel D₀ j₀ realize
      {s with control := .term body,
              env := RuntimeEnv.bind x arg closureEnv,
              stack := rest} answer := by
  rcases hrel with ⟨current, outer, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | value _ d _ harg =>
      cases hstack with
      | function _ f _ k hfn hrest =>
          cases hfn with
          | closure _ _ _ semanticEnv henv =>
              refine ⟨interp (hardwarePrimitive D₀ j₀ realize) body
                (envUpdate (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) x (semanticEnv, d)), k, ?_, hrest, ?_⟩
              · exact ControlRel.term body _ _
                  (closure_beta_env D₀ j₀ henv harg)
              · exact congrArg k (closure_application D₀ j₀
                  x body closureEnv semanticEnv arg d henv harg)

theorem channel_config_recBeta {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {self x : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    {arg : RuntimeValue C} {rest : EvalStack C}
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize
      {s with control := .value arg,
              stack :=
                .function (.recClosure self x body closureEnv) :: rest}
      answer) :
    ChannelConfigRel D₀ j₀ realize
      {s with control := .term body,
              env :=
                RuntimeEnv.bind x arg
                  (RuntimeEnv.bind self
                    (.recClosure self x body closureEnv) closureEnv),
              stack := rest} answer := by
  rcases hrel with ⟨current, outer, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | value _ d _ harg =>
      cases hstack with
      | function _ f _ k hfn hrest =>
          cases hfn with
          | recClosure _ _ _ _ semanticEnv henv =>
              refine ⟨interp (hardwarePrimitive D₀ j₀ realize) body
                (envUpdate (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) x
                  (envUpdate (Q := TTExternalContinuationPower 2)
                    (D₀ := D₀) (j₀ := j₀) self
                    (semanticEnv,
                      recLambdaValue
                        (Q := TTExternalContinuationPower 2)
                        (D₀ := D₀) (j₀ := j₀) self x
                        (interp (hardwarePrimitive D₀ j₀ realize) body)
                        semanticEnv),
                    d)), k, ?_, hrest, ?_⟩
              · exact ControlRel.term body _ _
                  (recClosure_unfold_env D₀ j₀ henv harg)
              · exact congrArg k (recClosure_application D₀ j₀
                  self x body closureEnv semanticEnv arg d henv harg)

theorem channel_config_internalLeft {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.intern left right)} answer) :
    ∃ targetAnswer,
      ChannelConfigRel D₀ j₀ realize
        {s with control := .term left} targetAnswer ∧
      targetAnswer ≤ answer := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨k (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv),
        ?_, ?_⟩
      · exact ⟨_, k, ControlRel.term left s.env semanticEnv henv,
          hstack, rfl⟩
      · exact stack_monotone D₀ j₀ hstack
          (internal_left_le D₀ j₀ realize left right semanticEnv)

theorem channel_config_internalRight {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.intern left right)} answer) :
    ∃ targetAnswer,
      ChannelConfigRel D₀ j₀ realize
        {s with control := .term right} targetAnswer ∧
      targetAnswer ≤ answer := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨k (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv),
        ?_, ?_⟩
      · exact ⟨_, k, ControlRel.term right s.env semanticEnv henv,
          hstack, rfl⟩
      · exact stack_monotone D₀ j₀ hstack
          (internal_right_le D₀ j₀ realize left right semanticEnv)

theorem channel_config_probabilityLeft {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {p : Prob}
    {left right : Term (QubitPrimitive C)}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.prob p left right)} answer) :
    ∃ targetAnswer,
      ChannelConfigRel D₀ j₀ realize
        {s with control := .term left} targetAnswer ∧
      HasWeightedBranchSemantics.weightedBranch answer p targetAnswer := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨k (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv),
        ?_, ?_⟩
      · exact ⟨_, k, ControlRel.term left s.env semanticEnv henv,
          hstack, rfl⟩
      · exact stack_weightedBranch D₀ j₀ hstack
          (probability_left_weighted D₀ j₀ realize p left right
            hp₀ hp₁ semanticEnv)

theorem channel_config_probabilityRight {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {p : Prob}
    {left right : Term (QubitPrimitive C)}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.prob p left right)} answer) :
    ∃ targetAnswer,
      ChannelConfigRel D₀ j₀ realize
        {s with control := .term right} targetAnswer ∧
      HasWeightedBranchSemantics.weightedBranch answer (1 - p)
        targetAnswer := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨k (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv),
        ?_, ?_⟩
      · exact ⟨_, k, ControlRel.term right s.env semanticEnv henv,
          hstack, rfl⟩
      · exact stack_weightedBranch D₀ j₀ hstack
          (probability_right_weighted D₀ j₀ realize p left right
            hp₀ hp₁ semanticEnv)

theorem channel_config_externalSelect {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {selected : Bool}
    {left right : Term (QubitPrimitive C)}
    (hcommute :
      ∀ current k,
        StackRel D₀ j₀ realize s.stack k →
        HasExternalSelection.select selected (k current) =
          k (HasExternalSelection.select selected current))
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.extern left right)} answer) :
    ChannelConfigRel D₀ j₀ realize
      {s with control := .term (if selected then right else left)}
      (HasExternalSelection.select selected answer) := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨interp (hardwarePrimitive D₀ j₀ realize)
        (if selected then right else left) semanticEnv, k, ?_, hstack, ?_⟩
      · exact ControlRel.term _ s.env semanticEnv henv
      · rw [hcommute _ k hstack,
          external_select D₀ j₀ realize selected left right semanticEnv]

theorem channel_config_externalSelect_nil {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} (hstack : s.stack = [])
    {selected : Bool} {left right : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.extern left right)} answer) :
    ChannelConfigRel D₀ j₀ realize
      {s with control := .term (if selected then right else left)}
      (HasExternalSelection.select selected answer) := by
  apply channel_config_externalSelect D₀ j₀ (s := s)
  intro current k hk
  rw [hstack] at hk
  cases hk
  rfl
  exact hrel

/-- Selector paths commute with Kleisli extension by acting on the residual
heap coordinate.  The `evalBranch` combinator is private, so the public
statement records the encoded residual coordinate. -/
theorem selectPath_taggedBind
    {D E : Type} [CompleteLattice D] [CompleteLattice E]
    (h : ScottMap D (TTExternalContinuationPower 2 E))
    (q : TTExternalContinuationPower 2 D)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap E (TTResult 2)) :
    HardwareAdequacy.selectPath selectors
        (TTContinuation.taggedBindScott (n := 2) h q) i k =
      TTContinuation.taggedBindScott (n := 2) h q
        (HardwareAdequacy.encodePath selectors i) k := by
  rw [HardwareAdequacy.selectPath_apply_encode]

theorem selectPath_semanticBind
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (h : ScottMap (HSemanticValue D₀ j₀) (HSemanticComp D₀ j₀))
    (q : HSemanticComp D₀ j₀)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    HardwareAdequacy.selectPath selectors
        (semanticBind (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) h q) i k =
      semanticBind (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) h q
        (HardwareAdequacy.encodePath selectors i) k :=
  selectPath_taggedBind h q selectors i k

/-- Apply-continuation and unfold are residual Scott maps, so selector paths
commute with them by the same residual-coordinate encoding. -/
theorem selectPath_applyContinuation
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (ma : ScottMap (Env (HSemanticValue D₀ j₀)) (HSemanticComp D₀ j₀))
    (ρ : Env (HSemanticValue D₀ j₀))
    (f : HSemanticValue D₀ j₀)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    HardwareAdequacy.selectPath selectors
        (applyContinuation (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) ma ρ f) i k =
      applyContinuation (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) ma ρ f
        (HardwareAdequacy.encodePath selectors i) k := by
  rw [HardwareAdequacy.selectPath_apply_encode]

theorem selectPath_semanticUnfold
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (f : HSemanticValue D₀ j₀)
    (d : HSemanticValue D₀ j₀)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    HardwareAdequacy.selectPath selectors
        (semanticUnfold (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) f d) i k =
      semanticUnfold (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) f d
        (HardwareAdequacy.encodePath selectors i) k := by
  rw [HardwareAdequacy.selectPath_apply_encode]

/-- A unique-successor identity step unwraps every tree at the source to
the unique child configuration. -/
theorem restrictedResult_of_unique_identity {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C}
    (hstep : ChannelInternalStep s t)
    (hop : channelInternalOperation s = QuantumOperation.identity 2)
    (hunq : ∀ {t'}, ChannelInternalStep s t' → t' = t)
    (tree : ChannelTree C s)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    restrictedResult D₀ j₀ realize tree R selectors i k ≤
      sSup (channelTreeResults D₀ j₀ realize t selectors i k) := by
  cases tree with
  | terminal hterm =>
      exact False.elim
        (ChannelInternalStep.not_value_nil hstep hterm.control_eq
          hterm.stack_eq)
  | @internal _ t' h' next =>
      have := restrictedResult_internal_of_identity D₀ j₀ realize
        h' hop next R selectors i k
      rw [this]
      have ht : t' = t := hunq h'
      subst ht
      apply le_sSup
      exact ⟨next.depth, next,
        internalChildRealization D₀ j₀ realize h' next R, le_rfl, rfl⟩
  | external _ hex _ =>
      exact False.elim (by cases hex <;> cases hstep)
  | probability _ _ _ _ =>
      cases hstep
  | probabilityZero _ =>
      cases hstep
  | probabilityOne _ =>
      cases hstep
  | measurement _ _ =>
      cases hstep

/-- Pointwise soundness transfers across an identity-operation tree edge.
The child may denote a refinement of the source, as for internal choice. -/
theorem identity_internal_channelTreePointwiseSound {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C}
    (hstep : ChannelInternalStep s t)
    (hop : channelInternalOperation s = QuantumOperation.identity 2)
    (next : ChannelTree C t)
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.internal hstep next))
    {childAnswer answer : HSemanticComp D₀ j₀}
    (hchild : ChannelTreePointwiseSound D₀ j₀ realize childAnswer next
      (internalChildRealization D₀ j₀ realize hstep next R))
    (hle : childAnswer ≤ answer) :
    ChannelTreePointwiseSound D₀ j₀ realize answer
      (ChannelTree.internal hstep next) R := by
  constructor
  intro selectors i k
  rw [restrictedResult_internal_of_identity D₀ j₀ realize hstep hop
    next R selectors i k]
  exact (hchild.restricted_le_selected selectors i k).trans (by
    rw [HardwareAdequacy.selectPath_apply_encode,
      HardwareAdequacy.selectPath_apply_encode]
    exact hle (HardwareAdequacy.encodePath selectors i) k)

/-- Completeness transfers across any unique-successor identity
administrative step.  Restricted instruments compose by reindexing; the
selector path is unchanged. -/
theorem identity_step_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} {denotation : HSemanticComp D₀ j₀}
    (hstep : ChannelInternalStep s t)
    (hop : channelInternalOperation s = QuantumOperation.identity 2)
    (hunq : ∀ {t'}, ChannelInternalStep s t' → t' = t)
    (hcomplete : ChannelTreeCompleteness D₀ j₀ realize t denotation) :
    ChannelTreeCompleteness D₀ j₀ realize s denotation where
  selected_result_eq_channelTree_sup := by
    intro selectors i k
    rw [hcomplete.selected_result_eq_channelTree_sup]
    apply le_antisymm
    · apply sSup_le
      rintro T ⟨fuel, child, R, hdepth, rfl⟩
      apply le_sSup
      refine ⟨fuel + 1, ChannelTree.internal hstep child,
        wrapInternalRealization D₀ j₀ realize hstep child R, ?_, ?_⟩
      · change child.depth + 1 ≤ fuel + 1
        omega
      · exact
          (restrictedResult_internal_of_identity D₀ j₀ realize hstep hop
            child (wrapInternalRealization D₀ j₀ realize hstep child R)
            selectors i k).symm
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      exact restrictedResult_of_unique_identity D₀ j₀ realize hstep hop
        hunq tree R selectors i k

/-- Presented completeness transfers across a unique-successor identity
administrative step.  This is the form used by the general higher-order
fundamental lemma, whose final continuations are finitely represented. -/
theorem identity_step_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} {denotation : HSemanticComp D₀ j₀}
    (hstep : ChannelInternalStep s t)
    (hop : channelInternalOperation s = QuantumOperation.identity 2)
    (hunq : ∀ {t'}, ChannelInternalStep s t' → t' = t)
    (hcomplete : PresentedChannelTreeCompleteness D₀ j₀ realize
      t denotation) :
    PresentedChannelTreeCompleteness D₀ j₀ realize s denotation where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ k hk
    rw [hcomplete.selected_result_eq_channelTree_sup_presented
      selectors i ξ k hk]
    apply le_antisymm
    · apply sSup_le
      rintro T ⟨fuel, child, R, hdepth, rfl⟩
      apply le_sSup
      refine ⟨fuel + 1, ChannelTree.internal hstep child,
        wrapInternalRealization D₀ j₀ realize hstep child R, ?_, ?_⟩
      · change child.depth + 1 ≤ fuel + 1
        omega
      · exact
          (restrictedResult_internal_of_identity D₀ j₀ realize hstep hop
            child (wrapInternalRealization D₀ j₀ realize hstep child R)
            selectors i k).symm
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      exact restrictedResult_of_unique_identity D₀ j₀ realize hstep hop
        hunq tree R selectors i k

/-- Package an identity-step transfer together with the source logical
relation.  The child relation is normally obtained from the corresponding
`channel_config_*` preservation theorem. -/
theorem PresentedChannelConfigCompleteness.ofIdentityStep {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} {denotation : HSemanticComp D₀ j₀}
    (hsource : ChannelConfigRel D₀ j₀ realize s denotation)
    (hstep : ChannelInternalStep s t)
    (hop : channelInternalOperation s = QuantumOperation.identity 2)
    (hunq : ∀ {t'}, ChannelInternalStep s t' → t' = t)
    (hchild : PresentedChannelConfigCompleteness D₀ j₀ realize
      t denotation) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s denotation where
  related := hsource
  complete := identity_step_presentedChannelTreeCompleteness D₀ j₀ realize
    hstep hop hunq hchild.complete

/-- Presented completeness transfers across the application identity step. -/
theorem application_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {fn arg : Term (QubitPrimitive C)}
    (hc : s.control = .term (.app fn arg))
    {denotation : HSemanticComp D₀ j₀}
    (hsource : ChannelConfigRel D₀ j₀ realize s denotation)
    (hchild : PresentedChannelConfigCompleteness D₀ j₀ realize
      {s with
        control := .term fn
        stack := .argument arg s.env :: s.stack}
      denotation) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s denotation := by
  let t : ChannelConfig C :=
    {s with
      control := .term fn
      stack := .argument arg s.env :: s.stack}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app fn arg)} t :=
      ChannelInternalStep.application (s := s) (fn := fn) (arg := arg)
    have hs : s = {s with control := .term (.app fn arg)} :=
      ChannelConfig.ext hc rfl rfl rfl
    exact hs.symm ▸ happ
  exact PresentedChannelConfigCompleteness.ofIdentityStep D₀ j₀ realize
    hsource hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_of_application h' hc) hchild

/-- Presented completeness transfers across argument evaluation. -/
theorem evaluateArgument_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {fn : RuntimeValue C}
    {arg : Term (QubitPrimitive C)} {callEnv : RuntimeEnv C}
    {rest : EvalStack C}
    (hc : s.control = .value fn)
    (hs : s.stack = .argument arg callEnv :: rest)
    {denotation : HSemanticComp D₀ j₀}
    (hsource : ChannelConfigRel D₀ j₀ realize s denotation)
    (hchild : PresentedChannelConfigCompleteness D₀ j₀ realize
      {s with
        control := .term arg
        env := callEnv
        stack := .function fn :: rest}
      denotation) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s denotation := by
  let t : ChannelConfig C :=
    {s with
      control := .term arg
      env := callEnv
      stack := .function fn :: rest}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with
            control := .value fn
            stack := .argument arg callEnv :: rest} t :=
      ChannelInternalStep.evaluateArgument
        (s := s) (fn := fn) (arg := arg) (callEnv := callEnv)
        (rest := rest)
    have hsrc :
        s = {s with
          control := .value fn
          stack := .argument arg callEnv :: rest} :=
      ChannelConfig.ext hc rfl hs rfl
    exact hsrc.symm ▸ happ
  exact PresentedChannelConfigCompleteness.ofIdentityStep D₀ j₀ realize
    hsource hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_of_evaluateArgument h' hc hs) hchild

/-- Presented completeness transfers across closure beta. -/
theorem beta_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    {arg : RuntimeValue C} {rest : EvalStack C}
    (hc : s.control = .value arg)
    (hs : s.stack = .function (.closure x body closureEnv) :: rest)
    {denotation : HSemanticComp D₀ j₀}
    (hsource : ChannelConfigRel D₀ j₀ realize s denotation)
    (hchild : PresentedChannelConfigCompleteness D₀ j₀ realize
      {s with
        control := .term body
        env := RuntimeEnv.bind x arg closureEnv
        stack := rest}
      denotation) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s denotation := by
  let t : ChannelConfig C :=
    {s with
      control := .term body
      env := RuntimeEnv.bind x arg closureEnv
      stack := rest}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with
            control := .value arg
            stack := .function (.closure x body closureEnv) :: rest} t :=
      ChannelInternalStep.beta (s := s) (x := x) (body := body)
        (closureEnv := closureEnv) (arg := arg) (rest := rest)
    have hsrc :
        s = {s with
          control := .value arg
          stack := .function (.closure x body closureEnv) :: rest} :=
      ChannelConfig.ext hc rfl hs rfl
    exact hsrc.symm ▸ happ
  exact PresentedChannelConfigCompleteness.ofIdentityStep D₀ j₀ realize
    hsource hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_of_beta h' hc hs) hchild

/-- Presented completeness transfers across recursive-closure beta. -/
theorem recBeta_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {self x : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    {arg : RuntimeValue C} {rest : EvalStack C}
    (hc : s.control = .value arg)
    (hs : s.stack =
      .function (.recClosure self x body closureEnv) :: rest)
    {denotation : HSemanticComp D₀ j₀}
    (hsource : ChannelConfigRel D₀ j₀ realize s denotation)
    (hchild : PresentedChannelConfigCompleteness D₀ j₀ realize
      {s with
        control := .term body
        env :=
          RuntimeEnv.bind x arg
            (RuntimeEnv.bind self
              (.recClosure self x body closureEnv) closureEnv)
        stack := rest}
      denotation) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s denotation := by
  let t : ChannelConfig C :=
    {s with
      control := .term body
      env :=
        RuntimeEnv.bind x arg
          (RuntimeEnv.bind self
            (.recClosure self x body closureEnv) closureEnv)
      stack := rest}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with
            control := .value arg
            stack :=
              .function (.recClosure self x body closureEnv) :: rest} t :=
      ChannelInternalStep.recBeta (s := s) (self := self) (x := x)
        (body := body) (closureEnv := closureEnv) (arg := arg)
        (rest := rest)
    have hsrc :
        s = {s with
          control := .value arg
          stack :=
            .function (.recClosure self x body closureEnv) :: rest} :=
      ChannelConfig.ext hc rfl hs rfl
    exact hsrc.symm ▸ happ
  exact PresentedChannelConfigCompleteness.ofIdentityStep D₀ j₀ realize
    hsource hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_of_recBeta h' hc hs) hchild

/-- Presented completeness transfers across ordinary abstraction. -/
theorem lambda_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x : Name} {body : Term (QubitPrimitive C)}
    (hc : s.control = .term (.lam x body))
    {denotation : HSemanticComp D₀ j₀}
    (hsource : ChannelConfigRel D₀ j₀ realize s denotation)
    (hchild : PresentedChannelConfigCompleteness D₀ j₀ realize
      {s with control := .value (.closure x body s.env)}
      denotation) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s denotation := by
  let t : ChannelConfig C :=
    {s with control := .value (.closure x body s.env)}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.lam x body)} t :=
      ChannelInternalStep.lambda (s := s) (x := x) (body := body)
    have hs : s = {s with control := .term (.lam x body)} :=
      ChannelConfig.ext hc rfl rfl rfl
    exact hs.symm ▸ happ
  exact PresentedChannelConfigCompleteness.ofIdentityStep D₀ j₀ realize
    hsource hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_of_lambda h' hc) hchild

/-- Presented completeness transfers across recursive abstraction. -/
theorem recLam_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {self arg : Name}
    {body : Term (QubitPrimitive C)}
    (hc : s.control = .term (.recLam self arg body))
    {denotation : HSemanticComp D₀ j₀}
    (hsource : ChannelConfigRel D₀ j₀ realize s denotation)
    (hchild : PresentedChannelConfigCompleteness D₀ j₀ realize
      {s with control := .value (.recClosure self arg body s.env)}
      denotation) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s denotation := by
  let t : ChannelConfig C :=
    {s with control := .value (.recClosure self arg body s.env)}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.recLam self arg body)} t :=
      ChannelInternalStep.recursive (s := s) (self := self) (arg := arg)
        (body := body)
    have hs : s = {s with control := .term (.recLam self arg body)} :=
      ChannelConfig.ext hc rfl rfl rfl
    exact hs.symm ▸ happ
  exact PresentedChannelConfigCompleteness.ofIdentityStep D₀ j₀ realize
    hsource hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_of_recursive h' hc) hchild

/-- Presented completeness transfers across variable lookup. -/
theorem variable_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x : Name} {v : RuntimeValue C}
    (hc : s.control = .term (.var x))
    (hlookup : RuntimeEnv.lookup x s.env = some v)
    {denotation : HSemanticComp D₀ j₀}
    (hsource : ChannelConfigRel D₀ j₀ realize s denotation)
    (hchild : PresentedChannelConfigCompleteness D₀ j₀ realize
      {s with control := .value v} denotation) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s denotation := by
  let t : ChannelConfig C := {s with control := .value v}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.var x)} t :=
      ChannelInternalStep.variable (s := s) (x := x) (v := v) hlookup
    have hs : s = {s with control := .term (.var x)} :=
      ChannelConfig.ext hc rfl rfl rfl
    exact hs.symm ▸ happ
  exact PresentedChannelConfigCompleteness.ofIdentityStep D₀ j₀ realize
    hsource hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_of_variable h' hc hlookup) hchild

/-- Presented stacked fundamental lemma for `app (lam x body) arg`. -/
theorem stacked_lam_app_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x : Name}
    {body arg : Term (QubitPrimitive C)}
    (hc : s.control = .term (.app (.lam x body) arg))
    {denotation : HSemanticComp D₀ j₀}
    (hsource : ChannelConfigRel D₀ j₀ realize s denotation)
    (harg : PresentedChannelConfigCompleteness D₀ j₀ realize
      {s with
        control := .term arg
        stack := .function (.closure x body s.env) :: s.stack}
      denotation) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s denotation := by
  have hAppEq :
      {s with control := .term (.app (.lam x body) arg)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelLam :=
    channel_config_application D₀ j₀
      (s := s) (fn := .lam x body) (arg := arg)
      (hrel := hAppEq.symm ▸ hsource)
  have hrelClo :=
    channel_config_lambda D₀ j₀
      (s := {s with stack := .argument arg s.env :: s.stack})
      (hrel := by simpa using hrelLam)
  have hClo :=
    evaluateArgument_presentedChannelConfigCompleteness D₀ j₀ realize
      (s := {s with
        control := .value (.closure x body s.env)
        stack := .argument arg s.env :: s.stack})
      (fn := .closure x body s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack)
      rfl rfl hrelClo harg
  have hLam :=
    lambda_presentedChannelConfigCompleteness D₀ j₀ realize
      (s := {s with
        control := .term (.lam x body)
        stack := .argument arg s.env :: s.stack})
      (x := x) (body := body) rfl hrelLam hClo
  exact application_presentedChannelConfigCompleteness D₀ j₀ realize
    hc hsource hLam

/-- Presented stacked fundamental lemma for `app (recLam self x body) arg`. -/
theorem stacked_recLam_app_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {self x : Name}
    {body arg : Term (QubitPrimitive C)}
    (hc : s.control = .term (.app (.recLam self x body) arg))
    {denotation : HSemanticComp D₀ j₀}
    (hsource : ChannelConfigRel D₀ j₀ realize s denotation)
    (harg : PresentedChannelConfigCompleteness D₀ j₀ realize
      {s with
        control := .term arg
        stack :=
          .function (.recClosure self x body s.env) :: s.stack}
      denotation) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s denotation := by
  have hAppEq :
      {s with control := .term (.app (.recLam self x body) arg)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelRec :=
    channel_config_application D₀ j₀
      (s := s) (fn := .recLam self x body) (arg := arg)
      (hrel := hAppEq.symm ▸ hsource)
  have hrelClo :=
    channel_config_recursive D₀ j₀
      (s := {s with stack := .argument arg s.env :: s.stack})
      (hrel := by simpa using hrelRec)
  have hClo :=
    evaluateArgument_presentedChannelConfigCompleteness D₀ j₀ realize
      (s := {s with
        control := .value (.recClosure self x body s.env)
        stack := .argument arg s.env :: s.stack})
      (fn := .recClosure self x body s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack)
      rfl rfl hrelClo harg
  have hRec :=
    recLam_presentedChannelConfigCompleteness D₀ j₀ realize
      (s := {s with
        control := .term (.recLam self x body)
        stack := .argument arg s.env :: s.stack})
      (self := self) (arg := x) (body := body) rfl hrelRec hClo
  exact application_presentedChannelConfigCompleteness D₀ j₀ realize
    hc hsource hRec

/-- Invert an application tree at a general source configuration. -/
theorem restrictedResult_of_control_application {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C}
    (tree : ChannelTree C s)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    {fn arg : Term (QubitPrimitive C)}
    (hc : s.control = .term (.app fn arg))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    restrictedResult D₀ j₀ realize tree R selectors i k ≤
      sSup (channelTreeResults D₀ j₀ realize
        { s with
          control := .term fn
          stack := .argument arg s.env :: s.stack }
        selectors i k) := by
  cases tree with
  | terminal hterm =>
      have := hterm.control_eq.symm.trans hc
      cases this
  | @internal _ t' h' next =>
      have hop : channelInternalOperation s = QuantumOperation.identity 2 := by
        simp [channelInternalOperation, hc]
      have := restrictedResult_internal_of_identity D₀ j₀ realize
        h' hop next R selectors i k
      rw [this]
      have ht : t' =
          { s with
            control := .term fn
            stack := .argument arg s.env :: s.stack } := by
        cases h' <;> cases hc
        rfl
      subst ht
      apply le_sSup
      exact ⟨next.depth, next,
        internalChildRealization D₀ j₀ realize h' next R, le_rfl, rfl⟩
  | external _ hex _ =>
      exact False.elim (by cases hex <;> cases hc)
  | probability _ _ _ _ =>
      cases hc
  | probabilityZero _ =>
      cases hc
  | probabilityOne _ =>
      cases hc
  | measurement _ _ =>
      cases hc

/-- An identity application step transfers channel-tree completeness from
the function-evaluation frame back to the application control. -/
theorem identity_internal_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {fn arg : Term (QubitPrimitive C)}
    (hc : s.control = .term (.app fn arg))
    {denotation : HSemanticComp D₀ j₀}
    (hcomplete : ChannelTreeCompleteness D₀ j₀ realize
      { s with
        control := .term fn
        stack := .argument arg s.env :: s.stack }
      denotation) :
    ChannelTreeCompleteness D₀ j₀ realize s denotation := by
  let t : ChannelConfig C :=
    { s with
      control := .term fn
      stack := .argument arg s.env :: s.stack }
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          { s with control := .term (.app fn arg) } t :=
      ChannelInternalStep.application (s := s) (fn := fn) (arg := arg)
    have hs : s = { s with control := .term (.app fn arg) } :=
      ChannelConfig.ext hc rfl rfl rfl
    exact hs.symm ▸ happ
  refine identity_step_channelTreeCompleteness D₀ j₀ realize hstep ?hop
    ?hunq hcomplete
  · simp [channelInternalOperation, hc]
  · intro t' h'
    exact ChannelInternalStep.eq_of_application h' hc

noncomputable def wrapApp {C : Type}
    (fn arg : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (child : ChannelTree C
      { initialChannelConfig (.app fn arg) quantum with
          control := .term fn
          stack := .argument arg [] :: [] }) :
    ChannelTree C (initialChannelConfig (.app fn arg) quantum) :=
  ChannelTree.internal
    (ChannelInternalStep.application
      (s := initialChannelConfig (.app fn arg) quantum))
    child

/-- Closed application is the identity-step wrapping of function evaluation
under an argument frame. -/
theorem app_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fn arg : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hfn : ChannelTreeCompleteness D₀ j₀ realize
      { initialChannelConfig (.app fn arg) quantum with
          control := .term fn
          stack := .argument arg [] :: [] }
      (interp (hardwarePrimitive D₀ j₀ realize) (.app fn arg)
        semanticEnv)) :
    ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.app fn arg) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) (.app fn arg)
        semanticEnv) :=
  identity_internal_channelTreeCompleteness D₀ j₀ realize
    (show (initialChannelConfig (.app fn arg) quantum).control =
        .term (.app fn arg) from rfl)
    hfn

/-- Function evaluation under an argument frame is residual bind of
`applyContinuation`; selectors act only on the leftover coordinate. -/
theorem selectPath_app {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fn arg : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize) (.app fn arg)
          semanticEnv) i k =
      semanticBind (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (applyContinuation (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (interp (hardwarePrimitive D₀ j₀ realize) arg) semanticEnv)
        (interp (hardwarePrimitive D₀ j₀ realize) fn semanticEnv)
        (HardwareAdequacy.encodePath selectors i) k := by
  rw [interp_app_apply, HardwareAdequacy.selectPath_apply_encode]
  rfl

/-- Argument evaluation under a function frame is residual bind of
`semanticUnfold`. -/
theorem evaluateArgument_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {fn : RuntimeValue C}
    {arg : Term (QubitPrimitive C)} {callEnv : RuntimeEnv C}
    {rest : EvalStack C}
    (hc : s.control = .value fn)
    (hs : s.stack = .argument arg callEnv :: rest)
    {denotation : HSemanticComp D₀ j₀}
    (hcomplete : ChannelTreeCompleteness D₀ j₀ realize
      { s with
        control := .term arg
        env := callEnv
        stack := .function fn :: rest }
      denotation) :
    ChannelTreeCompleteness D₀ j₀ realize s denotation := by
  let t : ChannelConfig C :=
    { s with
      control := .term arg
      env := callEnv
      stack := .function fn :: rest }
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          { s with
            control := .value fn
            stack := .argument arg callEnv :: rest } t :=
      ChannelInternalStep.evaluateArgument
        (s := s) (fn := fn) (arg := arg) (callEnv := callEnv)
        (rest := rest)
    have hsrc :
        s = { s with
          control := .value fn
          stack := .argument arg callEnv :: rest } :=
      ChannelConfig.ext hc rfl hs rfl
    exact hsrc.symm ▸ happ
  refine identity_step_channelTreeCompleteness D₀ j₀ realize hstep ?hop
    ?hunq hcomplete
  · simp [channelInternalOperation, hc]
  · intro t' h'
    exact ChannelInternalStep.eq_of_evaluateArgument h' hc hs

/-- Closure beta is an identity administrative step into the body. -/
theorem beta_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    {arg : RuntimeValue C} {rest : EvalStack C}
    (hc : s.control = .value arg)
    (hs : s.stack = .function (.closure x body closureEnv) :: rest)
    {denotation : HSemanticComp D₀ j₀}
    (hcomplete : ChannelTreeCompleteness D₀ j₀ realize
      { s with
        control := .term body
        env := RuntimeEnv.bind x arg closureEnv
        stack := rest }
      denotation) :
    ChannelTreeCompleteness D₀ j₀ realize s denotation := by
  let t : ChannelConfig C :=
    { s with
      control := .term body
      env := RuntimeEnv.bind x arg closureEnv
      stack := rest }
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          { s with
            control := .value arg
            stack := .function (.closure x body closureEnv) :: rest } t :=
      ChannelInternalStep.beta (s := s) (x := x) (body := body)
        (closureEnv := closureEnv) (arg := arg) (rest := rest)
    have hsrc :
        s = { s with
          control := .value arg
          stack := .function (.closure x body closureEnv) :: rest } :=
      ChannelConfig.ext hc rfl hs rfl
    exact hsrc.symm ▸ happ
  refine identity_step_channelTreeCompleteness D₀ j₀ realize hstep ?hop
    ?hunq hcomplete
  · simp [channelInternalOperation, hc]
  · intro t' h'
    exact ChannelInternalStep.eq_of_beta h' hc hs

/-- Recursive-closure beta is an identity step into one finite unfolding. -/
theorem recBeta_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {self x : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    {arg : RuntimeValue C} {rest : EvalStack C}
    (hc : s.control = .value arg)
    (hs : s.stack =
      .function (.recClosure self x body closureEnv) :: rest)
    {denotation : HSemanticComp D₀ j₀}
    (hcomplete : ChannelTreeCompleteness D₀ j₀ realize
      { s with
        control := .term body
        env :=
          RuntimeEnv.bind x arg
            (RuntimeEnv.bind self
              (.recClosure self x body closureEnv) closureEnv)
        stack := rest }
      denotation) :
    ChannelTreeCompleteness D₀ j₀ realize s denotation := by
  let t : ChannelConfig C :=
    { s with
      control := .term body
      env :=
        RuntimeEnv.bind x arg
          (RuntimeEnv.bind self
            (.recClosure self x body closureEnv) closureEnv)
      stack := rest }
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          { s with
            control := .value arg
            stack :=
              .function (.recClosure self x body closureEnv) :: rest }
          t :=
      ChannelInternalStep.recBeta (s := s) (self := self) (x := x)
        (body := body) (closureEnv := closureEnv) (arg := arg)
        (rest := rest)
    have hsrc :
        s = { s with
          control := .value arg
          stack :=
            .function (.recClosure self x body closureEnv) :: rest } :=
      ChannelConfig.ext hc rfl hs rfl
    exact hsrc.symm ▸ happ
  refine identity_step_channelTreeCompleteness D₀ j₀ realize hstep ?hop
    ?hunq hcomplete
  · simp [channelInternalOperation, hc]
  · intro t' h'
    exact ChannelInternalStep.eq_of_recBeta h' hc hs

/-- Abstraction is an identity step to the related closure value. -/
theorem lambda_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x : Name} {body : Term (QubitPrimitive C)}
    (hc : s.control = .term (.lam x body))
    {denotation : HSemanticComp D₀ j₀}
    (hcomplete : ChannelTreeCompleteness D₀ j₀ realize
      { s with control := .value (.closure x body s.env) }
      denotation) :
    ChannelTreeCompleteness D₀ j₀ realize s denotation := by
  let t : ChannelConfig C :=
    { s with control := .value (.closure x body s.env) }
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          { s with control := .term (.lam x body) } t :=
      ChannelInternalStep.lambda (s := s) (x := x) (body := body)
    have hsrc : s = { s with control := .term (.lam x body) } :=
      ChannelConfig.ext hc rfl rfl rfl
    exact hsrc.symm ▸ happ
  refine identity_step_channelTreeCompleteness D₀ j₀ realize hstep ?hop
    ?hunq hcomplete
  · simp [channelInternalOperation, hc]
  · intro t' h'
    exact ChannelInternalStep.eq_of_lambda h' hc

/-- Recursive abstraction is an identity step to the related recursive
closure; the denotation remains the Scott fixed point, not a finite
unfolding. -/
theorem recLam_identity_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {self arg : Name}
    {body : Term (QubitPrimitive C)}
    (hc : s.control = .term (.recLam self arg body))
    {denotation : HSemanticComp D₀ j₀}
    (hcomplete : ChannelTreeCompleteness D₀ j₀ realize
      { s with
        control := .value (.recClosure self arg body s.env) }
      denotation) :
    ChannelTreeCompleteness D₀ j₀ realize s denotation := by
  let t : ChannelConfig C :=
    { s with control := .value (.recClosure self arg body s.env) }
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          { s with control := .term (.recLam self arg body) } t :=
      ChannelInternalStep.recursive (s := s) (self := self) (arg := arg)
        (body := body)
    have hsrc :
        s = { s with control := .term (.recLam self arg body) } :=
      ChannelConfig.ext hc rfl rfl rfl
    exact hsrc.symm ▸ happ
  refine identity_step_channelTreeCompleteness D₀ j₀ realize hstep ?hop
    ?hunq hcomplete
  · simp [channelInternalOperation, hc]
  · intro t' h'
    exact ChannelInternalStep.eq_of_recursive h' hc

/-- Finite Scott unfoldings of a recursive closure are the denotations
used by fuel induction: the full fixed point is their supremum. -/
theorem recLambdaValue_iSup_le_related
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (self arg : Name)
    (body : ScottMap (Env (HSemanticValue D₀ j₀)) (HSemanticComp D₀ j₀))
    (ρ : Env (HSemanticValue D₀ j₀))
    (fuel : ℕ) :
    ScottFixApproximation.iterateBot
        (recFunctional (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) self arg body ρ) fuel ≤
      recLambdaValue (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) self arg body ρ :=
  ScottFixApproximation.iterateBot_le_fix _ _

/-- Related CEK states inherit channel-tree completeness along any identity
administrative step that is not internal choice.  The empty-stack initial
theorem is the special case of a related start. -/
theorem related_identity_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C}
    {denotation : HSemanticComp D₀ j₀}
    {fn arg : Term (QubitPrimitive C)}
    (hc : s.control = .term (.app fn arg))
    (_hrel : ChannelConfigRel D₀ j₀ realize s denotation)
    (hcomplete : ChannelTreeCompleteness D₀ j₀ realize
      { s with
        control := .term fn
        stack := .argument arg s.env :: s.stack }
      denotation) :
    ChannelTreeCompleteness D₀ j₀ realize s denotation :=
  identity_internal_channelTreeCompleteness D₀ j₀ realize hc hcomplete

/-- The initial related configuration inherits channel-tree completeness
from any proof that the closed term is complete. -/
theorem related_initial_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hcomplete : ChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig code quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv)) :
    ChannelConfigRel D₀ j₀ realize (initialChannelConfig code quantum)
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) ∧
      ChannelTreeCompleteness D₀ j₀ realize
        (initialChannelConfig code quantum)
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
  ⟨initialChannelConfig_related D₀ j₀ realize code quantum semanticEnv,
    hcomplete⟩

/-- Recursive denotations are the supremum of finite Scott unfoldings, so a
fuel-bounded completeness proof for each `iterateBot` stage lifts by Scott
continuity of `selectPath`. -/
theorem selectPath_recLambdaValue_iSup
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (self arg : Name)
    (body : ScottMap (Env (HSemanticValue D₀ j₀)) (HSemanticComp D₀ j₀))
    (ρ : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    HardwareAdequacy.selectPath selectors
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (recLambdaValue (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self arg body ρ)) i k =
      HardwareAdequacy.selectPath selectors
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (⨆ fuel, ScottFixApproximation.iterateBot
            (recFunctional (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) self arg body ρ) fuel)) i k := by
  rw [recLambdaValue_eq_iSup_channel_finite]

/-- Closed recursive abstractions denote the unit of the Scott fixed point,
which is the supremum of the finite unfoldings used by fuel induction. -/
theorem recLam_denotation_eq_iSup_iterateBot {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    interp (hardwarePrimitive D₀ j₀ realize) (.recLam self arg body)
        semanticEnv =
      semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (⨆ fuel, ScottFixApproximation.iterateBot
          (recFunctional (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self arg
            (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv)
          fuel) := by
  rw [interp_recLam_apply, recLambdaValue_eq_iSup_channel_finite]

/-- Closed recursive abstractions denote the unit of the Scott fixed point.
Selector paths commute with that unit, so fuel induction may replace the
fixed point by the supremum of `iterateBot` stages. -/
theorem selectPath_recLam {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize) (.recLam self arg body)
          semanticEnv) i k =
      HardwareAdequacy.selectPath selectors
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (⨆ fuel, ScottFixApproximation.iterateBot
            (recFunctional (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) self arg
              (interp (hardwarePrimitive D₀ j₀ realize) body)
              semanticEnv) fuel)) i k := by
  rw [recLam_denotation_eq_iSup_iterateBot]

/-- Each finite unfolding is below the recursive denotation, so a
fuel-indexed lower bound for `iterateBot` is a lower bound for `recLam`. -/
theorem selectPath_iterateBot_le_recLam {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (fuel : ℕ)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    HardwareAdequacy.selectPath selectors
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (ScottFixApproximation.iterateBot
            (recFunctional (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) self arg
              (interp (hardwarePrimitive D₀ j₀ realize) body)
              semanticEnv) fuel)) i k ≤
      HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize) (.recLam self arg body)
          semanticEnv) i k := by
  rw [interp_recLam_apply, HardwareAdequacy.selectPath_apply_encode,
    HardwareAdequacy.selectPath_apply_encode]
  exact
    (semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)).monotone
      (ScottFixApproximation.iterateBot_le_fix _ _)
      (HardwareAdequacy.encodePath selectors i) k

/-- Tagged unit is evaluation: a finite unfolding and the recursive value
are compared only after the same result continuation. -/
theorem semanticUnit_apply_eq
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (d : HSemanticValue D₀ j₀) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) d i k =
      k d :=
  rfl

/-- Scott continuity of the result continuation moves it through the
supremum of finite unfoldings. -/
theorem continuation_iSup_iterateBot
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (self arg : Name)
    (body : ScottMap (Env (HSemanticValue D₀ j₀)) (HSemanticComp D₀ j₀))
    (ρ : Env (HSemanticValue D₀ j₀))
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    k (recLambdaValue (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) self arg body ρ) =
      ⨆ fuel, k (ScottFixApproximation.iterateBot
        (recFunctional (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) self arg body ρ) fuel) := by
  rw [recLambdaValue_eq_iSup_channel_finite]
  rw [← sSup_range,
    k.preservesDirectedSup_coe
      (Set.range
        (ScottFixApproximation.iterateBot
          (recFunctional (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self arg body ρ)))
      (ScottFixApproximation.iterateBot_range_nonempty _)
      (ScottFixApproximation.iterateBot_range_directed _),
    ← Set.range_comp, sSup_range]
  rfl

/-- The recursive unit at any coordinate is the supremum of the finite
unfolding units at that same continuation. -/
theorem semanticUnit_recLambdaValue_eq_iSup_iterateBot
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (self arg : Name)
    (body : ScottMap (Env (HSemanticValue D₀ j₀)) (HSemanticComp D₀ j₀))
    (ρ : Env (HSemanticValue D₀ j₀))
    (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (recLambdaValue (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) self arg body ρ) i k =
      ⨆ fuel,
        semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (ScottFixApproximation.iterateBot
            (recFunctional (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) self arg body ρ) fuel) i k := by
  simpa [semanticUnit_apply_eq] using
    continuation_iSup_iterateBot D₀ j₀ self arg body ρ k

/-- One successor unfolding is exactly `recFunctional` at the previous
finite stage. -/
theorem semanticUnit_iterateBot_succ
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (self arg : Name)
    (body : ScottMap (Env (HSemanticValue D₀ j₀)) (HSemanticComp D₀ j₀))
    (ρ : Env (HSemanticValue D₀ j₀))
    (fuel : ℕ) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (ScottFixApproximation.iterateBot
          (recFunctional (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self arg body ρ) (fuel + 1)) i k =
      semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (recFunctional (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) self arg body ρ
          (ScottFixApproximation.iterateBot
            (recFunctional (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) self arg body ρ) fuel)) i k := by
  rw [ScottFixApproximation.iterateBot_succ]

/-- Tokens of a recursive value are exactly tokens of some finite
unfolding.  Membership in the Scott supremum of rounded theories is
existential in the fuel. -/
theorem mem_recLambdaValue_iff_exists_iterateBot
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (self arg : Name)
    (body : ScottMap (Env (HSemanticValue D₀ j₀)) (HSemanticComp D₀ j₀))
    (ρ : Env (HSemanticValue D₀ j₀))
    (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (token : TTObservationToken 2) :
    token ∈
        semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (recLambdaValue (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self arg body ρ) i k ↔
      ∃ fuel,
        token ∈
          semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)
            (ScottFixApproximation.iterateBot
              (recFunctional (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀) self arg body ρ) fuel) i k := by
  rw [semanticUnit_recLambdaValue_eq_iSup_iterateBot]
  rw [← sSup_range, RoundedTheory.mem_sSup]
  constructor
  · rintro ⟨T, ⟨fuel, rfl⟩, ht⟩
    exact ⟨fuel, ht⟩
  · rintro ⟨fuel, ht⟩
    exact ⟨_, ⟨fuel, rfl⟩, ht⟩

/-- Closed `recLam` tokens are tokens of some finite unfolding. -/
theorem mem_selectPath_recLam_iff_exists_iterateBot {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize) (.recLam self arg body)
          semanticEnv) i k ↔
      ∃ fuel,
        token ∈ HardwareAdequacy.selectPath selectors
          (semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)
            (ScottFixApproximation.iterateBot
              (recFunctional (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀) self arg
                (interp (hardwarePrimitive D₀ j₀ realize) body)
                semanticEnv) fuel)) i k := by
  constructor
  · intro ht
    rw [interp_recLam_apply, HardwareAdequacy.selectPath_apply_encode] at ht
    obtain ⟨fuel, hfuel⟩ :=
      (mem_recLambdaValue_iff_exists_iterateBot D₀ j₀ self arg
        (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv
        (HardwareAdequacy.encodePath selectors i) k token).mp ht
    refine ⟨fuel, ?_⟩
    rwa [HardwareAdequacy.selectPath_apply_encode]
  · rintro ⟨fuel, hfuel⟩
    rw [interp_recLam_apply, HardwareAdequacy.selectPath_apply_encode]
    rw [mem_recLambdaValue_iff_exists_iterateBot]
    refine ⟨fuel, ?_⟩
    rwa [HardwareAdequacy.selectPath_apply_encode] at hfuel

/-- At a related empty-stack recursive closure, the path result is the
final continuation at the recursive value, hence the supremum of its
finite unfoldings. -/
theorem mem_path_recClosure_iff_exists_iterateBot {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {self arg : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    (hc : s.control = .value (.recClosure self arg body closureEnv))
    (hstack : s.stack = [])
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result)
    (hscoped : ChannelConfig.WellScoped s)
    (token : TTObservationToken 2) :
    token ∈ result ↔
      ∃ (semanticEnv : Env (HSemanticValue D₀ j₀)) (fuel : ℕ),
        EnvRel D₀ j₀ realize closureEnv semanticEnv ∧
          token ∈
            semanticUnit (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀)
              (ScottFixApproximation.iterateBot
                (recFunctional (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) self arg
                  (interp (hardwarePrimitive D₀ j₀ realize) body)
                  semanticEnv) fuel) active finalK := by
  rcases hrel with ⟨herase, current, currentK, hcontrol, hstackRel, hresult⟩
  have hobserved : observedStack = [] := by
    cases observedStack with
    | nil => rfl
    | cons frame rest =>
        rw [ObservedStack.erase_cons, hstack] at herase
        cases herase
  subst observedStack
  cases hstackRel
  rw [hc] at hcontrol
  cases hcontrol with
  | value _ d _ hvalue =>
      cases hvalue with
      | recClosure _ _ _ _ semanticEnv henv =>
          have hvalueScoped : RuntimeValue.WellScoped
              (.recClosure self arg body closureEnv) := by
            have hctl := hscoped.left
            rw [hc] at hctl
            exact hctl.right
          rw [hresult]
          constructor
          · intro ht
            obtain ⟨fuel, hfuel⟩ :=
              (mem_recLambdaValue_iff_exists_iterateBot D₀ j₀ self arg
                (interp (hardwarePrimitive D₀ j₀ realize) body)
                semanticEnv active finalK token).mp ht
            exact ⟨semanticEnv, fuel, henv, hfuel⟩
          · rintro ⟨semanticEnv', fuel, henv', hfuel⟩
            have heq :
                recLambdaValue (Q := TTExternalContinuationPower 2)
                    (D₀ := D₀) (j₀ := j₀) self arg
                    (interp (hardwarePrimitive D₀ j₀ realize) body)
                    semanticEnv =
                  recLambdaValue (Q := TTExternalContinuationPower 2)
                    (D₀ := D₀) (j₀ := j₀) self arg
                    (interp (hardwarePrimitive D₀ j₀ realize) body)
                    semanticEnv' :=
              valueRel_functional D₀ j₀ realize hvalueScoped
                (ValueRel.recClosure self arg body closureEnv
                  semanticEnv henv)
                (ValueRel.recClosure self arg body closureEnv
                  semanticEnv' henv')
            have hlim :
                token ∈
                  semanticUnit (Q := TTExternalContinuationPower 2)
                    (D₀ := D₀) (j₀ := j₀)
                    (recLambdaValue (Q := TTExternalContinuationPower 2)
                      (D₀ := D₀) (j₀ := j₀) self arg
                      (interp (hardwarePrimitive D₀ j₀ realize) body)
                      semanticEnv') active finalK :=
              (semanticUnit (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀)).monotone
                (ScottFixApproximation.iterateBot_le_fix _ fuel)
                active finalK hfuel
            rwa [← heq] at hlim

/-- Selector-path form of the Scott unfolding of a recursive value. -/
theorem selectPath_recLambdaValue_eq_iSup_iterateBot
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (self arg : Name)
    (body : ScottMap (Env (HSemanticValue D₀ j₀)) (HSemanticComp D₀ j₀))
    (ρ : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    HardwareAdequacy.selectPath selectors
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (recLambdaValue (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self arg body ρ)) i k =
      ⨆ fuel,
        HardwareAdequacy.selectPath selectors
          (semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)
            (ScottFixApproximation.iterateBot
              (recFunctional (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀) self arg body ρ) fuel)) i k := by
  rw [HardwareAdequacy.selectPath_apply_encode,
    semanticUnit_recLambdaValue_eq_iSup_iterateBot]
  refine iSup_congr fun fuel => ?_
  rw [HardwareAdequacy.selectPath_apply_encode]

/-- A uniform upper bound for every finite unfolding is an upper bound
for the recursive fixed point.  This is the Scott-continuity half of
fuel induction. -/
theorem selectPath_recLambdaValue_le_of_iterateBot
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (self arg : Name)
    (body : ScottMap (Env (HSemanticValue D₀ j₀)) (HSemanticComp D₀ j₀))
    (ρ : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    {T : TTResult 2}
    (hle : ∀ fuel,
      HardwareAdequacy.selectPath selectors
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (ScottFixApproximation.iterateBot
            (recFunctional (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) self arg body ρ) fuel)) i k ≤ T) :
    HardwareAdequacy.selectPath selectors
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (recLambdaValue (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self arg body ρ)) i k ≤ T := by
  rw [selectPath_recLambdaValue_eq_iSup_iterateBot]
  exact iSup_le hle

/-- Presented completeness of the recursive fixed point from soundness
plus a fuel-indexed lower bound.  Each `iterateBot` stage remains a
finite denotation; no single tree is identified with the fixed point. -/
theorem presented_recLambdaValue_of_iterateBot {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (start : ChannelConfig C)
    (self arg : Name)
    (body : ScottMap (Env (HSemanticValue D₀ j₀)) (HSemanticComp D₀ j₀))
    (ρ : Env (HSemanticValue D₀ j₀))
    (hsound : ∀ selectors i
        (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
        (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)),
      (∀ d, k d = (ξ d).satisfiedTTTheory resultCode) →
        sSup (channelTreeResults D₀ j₀ realize start selectors i k) ≤
          HardwareAdequacy.selectPath selectors
            (semanticUnit (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀)
              (recLambdaValue (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀) self arg body ρ)) i k)
    (hlower : ∀ fuel selectors i
        (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
        (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)),
      (∀ d, k d = (ξ d).satisfiedTTTheory resultCode) →
        HardwareAdequacy.selectPath selectors
          (semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)
            (ScottFixApproximation.iterateBot
              (recFunctional (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀) self arg body ρ) fuel)) i k ≤
          sSup (channelTreeResults D₀ j₀ realize start selectors i k)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize start
      (semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (recLambdaValue (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) self arg body ρ)) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ k hk
    apply le_antisymm
    · exact selectPath_recLambdaValue_le_of_iterateBot D₀ j₀
        self arg body ρ selectors i k (fun fuel => hlower fuel selectors i ξ k hk)
    · exact hsound selectors i ξ k hk

/-- Finite unfolding of a related recursive closure at a chosen fuel. -/
noncomputable def recClosureFuelValue {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀)) (fuel : ℕ) :
    HSemanticValue D₀ j₀ :=
  ScottFixApproximation.iterateBot
    (recFunctional (Q := TTExternalContinuationPower 2)
      (D₀ := D₀) (j₀ := j₀) self arg
      (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv) fuel

/-- Fuel-indexed logical relation.  Ordinary values ignore the fuel.
Recursive closures are related to the `fuel`-fold `iterateBot` unfolding
rather than the Scott fixed point. -/
inductive FuelValueRel {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀) :
    ℕ → RuntimeValue C → HSemanticValue D₀ j₀ → Prop where
  | payload (fuel : ℕ) (c : C) :
      FuelValueRel D₀ j₀ realize fuel (.payload c) (realize c)
  | closure (fuel : ℕ) (x : Name) (body : Term (QubitPrimitive C))
      (runtimeEnv : RuntimeEnv C)
      (semanticEnv : Env (HSemanticValue D₀ j₀))
      (henv : ∀ y v, RuntimeEnv.lookup y runtimeEnv = some v →
        FuelValueRel D₀ j₀ realize fuel v (semanticEnv y)) :
      FuelValueRel D₀ j₀ realize fuel (.closure x body runtimeEnv)
        (lambdaValue (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) x
          (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv)
  | recClosure (fuel : ℕ) (self arg : Name)
      (body : Term (QubitPrimitive C))
      (runtimeEnv : RuntimeEnv C)
      (semanticEnv : Env (HSemanticValue D₀ j₀))
      (henv : ∀ y v, RuntimeEnv.lookup y runtimeEnv = some v →
        FuelValueRel D₀ j₀ realize fuel v (semanticEnv y)) :
      FuelValueRel D₀ j₀ realize fuel
        (.recClosure self arg body runtimeEnv)
        (recClosureFuelValue D₀ j₀ realize self arg body semanticEnv fuel)

/-- Agreement of a finite runtime environment with a fuel-truncated
semantic one. -/
def FuelEnvRel {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fuel : ℕ)
    (runtimeEnv : RuntimeEnv C)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) : Prop :=
  ∀ x v, RuntimeEnv.lookup x runtimeEnv = some v →
    FuelValueRel D₀ j₀ realize fuel v (semanticEnv x)

theorem recClosureFuelValue_zero {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    recClosureFuelValue D₀ j₀ realize self arg body semanticEnv 0 = ⊥ :=
  ScottFixApproximation.iterateBot_zero _

theorem recClosureFuelValue_succ {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀)) (fuel : ℕ) :
    recClosureFuelValue D₀ j₀ realize self arg body semanticEnv (fuel + 1) =
      recFunctional (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) self arg
        (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv
        (recClosureFuelValue D₀ j₀ realize self arg body semanticEnv fuel) :=
  ScottFixApproximation.iterateBot_succ _ _

theorem recClosureFuelValue_le_recLambdaValue {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀)) (fuel : ℕ) :
    recClosureFuelValue D₀ j₀ realize self arg body semanticEnv fuel ≤
      recLambdaValue (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) self arg
        (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv :=
  ScottFixApproximation.iterateBot_le_fix _ _

theorem recLambdaValue_eq_iSup_recClosureFuelValue {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    recLambdaValue (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) self arg
        (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv =
      ⨆ fuel, recClosureFuelValue D₀ j₀ realize self arg body
        semanticEnv fuel :=
  recLambdaValue_eq_iSup_channel_finite D₀ j₀ self arg
    (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv

/-- The zero unfolding is bottom, so a related recursive closure at fuel
zero contributes no token. -/
theorem fuelValueRel_recClosure_zero {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {self arg : Name} {body : Term (QubitPrimitive C)}
    {runtimeEnv : RuntimeEnv C}
    {semanticEnv : Env (HSemanticValue D₀ j₀)}
    (henv : FuelEnvRel D₀ j₀ realize 0 runtimeEnv semanticEnv) :
    FuelValueRel D₀ j₀ realize 0
        (.recClosure self arg body runtimeEnv) ⊥ := by
  have h := FuelValueRel.recClosure (D₀ := D₀) (j₀ := j₀)
    (realize := realize) 0 self arg body runtimeEnv semanticEnv henv
  rwa [recClosureFuelValue_zero] at h

/-- One successor unfolding is `recFunctional` at the previous fuel. -/
theorem fuelValueRel_recClosure_succ {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {self arg : Name} {body : Term (QubitPrimitive C)}
    {runtimeEnv : RuntimeEnv C}
    {semanticEnv : Env (HSemanticValue D₀ j₀)}
    {fuel : ℕ}
    (henv : FuelEnvRel D₀ j₀ realize (fuel + 1) runtimeEnv semanticEnv) :
    FuelValueRel D₀ j₀ realize (fuel + 1)
        (.recClosure self arg body runtimeEnv)
        (recFunctional (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) self arg
          (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv
          (recClosureFuelValue D₀ j₀ realize self arg body
            semanticEnv fuel)) := by
  have h := FuelValueRel.recClosure (D₀ := D₀) (j₀ := j₀)
    (realize := realize) (fuel + 1) self arg body runtimeEnv
    semanticEnv henv
  rwa [recClosureFuelValue_succ] at h

/-- Unfolding a finite recursive approximant applies the body with `self`
bound to the previous fuel.  This is the semantic `recBeta` step used by
fuel induction. -/
theorem applyComp_pure_recFunctional
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (self arg : Name)
    (body : ScottMap (Env (HSemanticValue D₀ j₀)) (HSemanticComp D₀ j₀))
    (ρ : Env (HSemanticValue D₀ j₀))
    (approx d : HSemanticValue D₀ j₀) :
    applyComp (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        ((semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)).comp
          (ScottMap.const
            (recFunctional (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) self arg body ρ approx)))
        ((semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)).comp
          (ScottMap.const d))
        ρ =
      body
        (envUpdate (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) arg
          (envUpdate (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self (ρ, approx), d)) := by
  rw [applyComp_apply]
  change
    semanticBind (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (applyContinuation (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          ((semanticUnit (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀)).comp
            (ScottMap.const d)) ρ)
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (recFunctional (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self arg body ρ approx)) =
      body
        (envUpdate (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) arg
          (envUpdate (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self (ρ, approx), d))
  have hOuter := congrArg
    (fun f : ScottMap (HSemanticValue D₀ j₀) (HSemanticComp D₀ j₀) =>
      f (recFunctional (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) self arg body ρ approx))
    (IsQuantumMonad.unit_bind (Q := TTExternalContinuationPower 2)
      (applyContinuation (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        ((semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)).comp
          (ScottMap.const d)) ρ))
  rw [ScottMap.comp_apply] at hOuter
  rw [hOuter, applyContinuation_apply]
  have harg :
      ((semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)).comp
        (ScottMap.const d)) ρ =
        semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) d :=
    rfl
  rw [harg]
  have hInner := congrArg
    (fun f : ScottMap (HSemanticValue D₀ j₀) (HSemanticComp D₀ j₀) =>
      f d)
    (IsQuantumMonad.unit_bind (Q := TTExternalContinuationPower 2)
      (semanticUnfold (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (recFunctional (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) self arg body ρ approx)))
  rw [ScottMap.comp_apply] at hInner
  refine hInner.trans ?_
  change
    qEmbInfInf (QModel (TTExternalContinuationPower 2)) D₀ j₀
        (qProjInfInf (QModel (TTExternalContinuationPower 2)) D₀ j₀
          (scottLambda
            (body.comp
              ((envUpdate (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) arg).comp
                (ScottMap.pairMap
                  ((envUpdate (Q := TTExternalContinuationPower 2)
                      (D₀ := D₀) (j₀ := j₀) self).comp
                    ScottMap.fstMap)
                  ScottMap.sndMap)))
            (ρ, approx)))
        d =
      body
        (envUpdate (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) arg
          (envUpdate (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self (ρ, approx), d))
  let f : ScottMap (HSemanticValue D₀ j₀) (HSemanticComp D₀ j₀) :=
    scottLambda
      (body.comp
        ((envUpdate (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) arg).comp
          (ScottMap.pairMap
            ((envUpdate (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀) self).comp
              ScottMap.fstMap)
            ScottMap.sndMap)))
      (ρ, approx)
  have hf := congrArg
    (fun g : ScottMap (HSemanticValue D₀ j₀) (HSemanticComp D₀ j₀) =>
      g d)
    (qEmbInfInf_qProjInfInf (QModel (TTExternalContinuationPower 2))
      D₀ j₀ f)
  simpa only [f, scottLambda_apply, ScottMap.comp_apply,
    ScottMap.pairMap_apply, ScottMap.fstMap_apply,
    ScottMap.sndMap_apply] using hf

/-- Applying the successor unfolding is exactly one semantic `recBeta`
into the previous fuel. -/
theorem applyComp_iterateBot_succ
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (self arg : Name)
    (body : ScottMap (Env (HSemanticValue D₀ j₀)) (HSemanticComp D₀ j₀))
    (ρ : Env (HSemanticValue D₀ j₀))
    (fuel : ℕ) (d : HSemanticValue D₀ j₀) :
    applyComp (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        ((semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)).comp
          (ScottMap.const
            (ScottFixApproximation.iterateBot
              (recFunctional (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀) self arg body ρ) (fuel + 1))))
        ((semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)).comp
          (ScottMap.const d))
        ρ =
      body
        (envUpdate (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) arg
          (envUpdate (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self
            (ρ, ScottFixApproximation.iterateBot
              (recFunctional (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀) self arg body ρ) fuel),
            d)) := by
  rw [ScottFixApproximation.iterateBot_succ]
  exact applyComp_pure_recFunctional D₀ j₀ self arg body ρ
    (ScottFixApproximation.iterateBot
      (recFunctional (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) self arg body ρ) fuel) d

/-- Syntax-level successor unfolding: applying the next `recClosureFuelValue`
evaluates the body with `self` bound to the previous fuel. -/
theorem applyComp_recClosureFuelValue_succ {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (fuel : ℕ) (d : HSemanticValue D₀ j₀) :
    applyComp (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        ((semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)).comp
          (ScottMap.const
            (recClosureFuelValue D₀ j₀ realize self arg body
              semanticEnv (fuel + 1))))
        ((semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)).comp
          (ScottMap.const d))
        semanticEnv =
      interp (hardwarePrimitive D₀ j₀ realize) body
        (envUpdate (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) arg
          (envUpdate (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self
            (semanticEnv,
              recClosureFuelValue D₀ j₀ realize self arg body
                semanticEnv fuel),
            d)) :=
  applyComp_iterateBot_succ D₀ j₀ self arg
    (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv fuel d

/-- A related recursive closure is the supremum of its fuel-indexed
unfoldings. -/
theorem valueRel_recClosure_eq_iSup_fuel {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {self arg : Name} {body : Term (QubitPrimitive C)}
    {runtimeEnv : RuntimeEnv C} {d : HSemanticValue D₀ j₀}
    (h : ValueRel D₀ j₀ realize
      (.recClosure self arg body runtimeEnv) d) :
    ∃ semanticEnv : Env (HSemanticValue D₀ j₀),
      EnvRel D₀ j₀ realize runtimeEnv semanticEnv ∧
        d = ⨆ fuel, recClosureFuelValue D₀ j₀ realize self arg body
          semanticEnv fuel := by
  cases h with
  | recClosure _ _ _ _ semanticEnv henv =>
      exact ⟨semanticEnv, henv,
        recLambdaValue_eq_iSup_recClosureFuelValue D₀ j₀ realize
          self arg body semanticEnv⟩

/-- Selector paths are monotone in the returned value. -/
theorem selectPath_semanticUnit_monotone
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {d d' : HSemanticValue D₀ j₀} (hle : d ≤ d')
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    HardwareAdequacy.selectPath selectors
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) d) i k ≤
      HardwareAdequacy.selectPath selectors
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) d') i k := by
  rw [HardwareAdequacy.selectPath_apply_encode,
    HardwareAdequacy.selectPath_apply_encode]
  exact
    (semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)).monotone hle
      (HardwareAdequacy.encodePath selectors i) k

/-- The zero unfolding contributes the bottom observation. -/
theorem selectPath_recClosureFuelValue_zero {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    HardwareAdequacy.selectPath selectors
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (recClosureFuelValue D₀ j₀ realize self arg body
            semanticEnv 0)) i k =
      k ⊥ := by
  rw [recClosureFuelValue_zero, HardwareAdequacy.selectPath_apply_encode]
  rfl

/-- Each finite unfolding is below the recursive value, after any
selector path. -/
theorem selectPath_recClosureFuelValue_le_recLambdaValue {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀)) (fuel : ℕ)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    HardwareAdequacy.selectPath selectors
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (recClosureFuelValue D₀ j₀ realize self arg body
            semanticEnv fuel)) i k ≤
      HardwareAdequacy.selectPath selectors
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (recLambdaValue (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self arg
            (interp (hardwarePrimitive D₀ j₀ realize) body)
            semanticEnv)) i k :=
  selectPath_semanticUnit_monotone D₀ j₀
    (recClosureFuelValue_le_recLambdaValue D₀ j₀ realize
      self arg body semanticEnv fuel)
    selectors i k

/-- The body at a finite `self` unfolding is below the operational
`recBeta` body, which binds the full recursive value. -/
theorem interp_body_fuel_le_recBeta {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (fuel : ℕ) (d : HSemanticValue D₀ j₀) :
    interp (hardwarePrimitive D₀ j₀ realize) body
        (envUpdate (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) arg
          (envUpdate (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self
            (semanticEnv,
              recClosureFuelValue D₀ j₀ realize self arg body
                semanticEnv fuel),
            d)) ≤
      interp (hardwarePrimitive D₀ j₀ realize) body
        (envUpdate (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) arg
          (envUpdate (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self
            (semanticEnv,
              recLambdaValue (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀) self arg
                (interp (hardwarePrimitive D₀ j₀ realize) body)
                semanticEnv),
            d)) := by
  refine (interp (hardwarePrimitive D₀ j₀ realize) body).monotone ?_
  refine (envUpdate (Q := TTExternalContinuationPower 2)
      (D₀ := D₀) (j₀ := j₀) arg).monotone ?_
  refine Prod.mk_le_mk.mpr ⟨?_, le_rfl⟩
  exact (envUpdate (Q := TTExternalContinuationPower 2)
      (D₀ := D₀) (j₀ := j₀) self).monotone
    (Prod.mk_le_mk.mpr ⟨le_rfl,
      recClosureFuelValue_le_recLambdaValue D₀ j₀ realize
        self arg body semanticEnv fuel⟩)

/-- Applying the successor unfolding is below the operational `recBeta`
denotation. -/
theorem applyComp_recClosureFuelValue_succ_le_recBeta {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self x : Name) (body : Term (QubitPrimitive C))
    (closureEnv : RuntimeEnv C)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (_henv : EnvRel D₀ j₀ realize closureEnv semanticEnv)
    (arg : RuntimeValue C) (d : HSemanticValue D₀ j₀)
    (_harg : ValueRel D₀ j₀ realize arg d)
    (fuel : ℕ) :
    applyComp (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        ((semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)).comp
          (ScottMap.const
            (recClosureFuelValue D₀ j₀ realize self x body
              semanticEnv (fuel + 1))))
        ((semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)).comp
          (ScottMap.const d))
        semanticEnv ≤
      interp (hardwarePrimitive D₀ j₀ realize) body
        (envUpdate (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) x
          (envUpdate (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self
            (semanticEnv,
              recLambdaValue (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀) self x
                (interp (hardwarePrimitive D₀ j₀ realize) body)
                semanticEnv),
            d)) := by
  rw [applyComp_recClosureFuelValue_succ]
  exact interp_body_fuel_le_recBeta D₀ j₀ realize self x body
    semanticEnv fuel d

/-- Fuel induction step: a lower bound for the body at fuel `n` is a
lower bound for applying the successor unfolding. -/
theorem selectPath_applyComp_recClosureFuelValue_succ_le_of_body {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (fuel : ℕ) (d : HSemanticValue D₀ j₀)
    (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    {T : TTResult 2}
    (hbody :
      HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize) body
          (envUpdate (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) arg
            (envUpdate (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) self
              (semanticEnv,
                recClosureFuelValue D₀ j₀ realize self arg body
                  semanticEnv fuel),
              d))) i k ≤ T) :
    HardwareAdequacy.selectPath selectors
        (applyComp (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          ((semanticUnit (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀)).comp
            (ScottMap.const
              (recClosureFuelValue D₀ j₀ realize self arg body
                semanticEnv (fuel + 1))))
          ((semanticUnit (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀)).comp
            (ScottMap.const d))
          semanticEnv) i k ≤ T := by
  rwa [applyComp_recClosureFuelValue_succ]

/-- Binding `self` to the current fuel unfolding and `arg` to a related
value preserves `FuelEnvRel`. -/
theorem recClosure_unfold_env_fuel {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {self arg : Name} {body : Term (QubitPrimitive C)}
    {runtimeEnv : RuntimeEnv C}
    {semanticEnv : Env (HSemanticValue D₀ j₀)}
    {value : RuntimeValue C} {d : HSemanticValue D₀ j₀}
    {fuel : ℕ}
    (henv : FuelEnvRel D₀ j₀ realize fuel runtimeEnv semanticEnv)
    (hvalue : FuelValueRel D₀ j₀ realize fuel value d) :
    FuelEnvRel D₀ j₀ realize fuel
      (RuntimeEnv.bind arg value
        (RuntimeEnv.bind self
          (.recClosure self arg body runtimeEnv) runtimeEnv))
      (envUpdate (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) arg
        (envUpdate (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) self
          (semanticEnv,
            recClosureFuelValue D₀ j₀ realize self arg body
              semanticEnv fuel),
          d)) := by
  intro y w hw
  by_cases hyarg : y = arg
  · subst y
    simp [RuntimeEnv.bind, RuntimeEnv.lookup] at hw
    cases hw
    simpa [envUpdate_apply] using hvalue
  · by_cases hyself : y = self
    · subst y
      simp [RuntimeEnv.bind, RuntimeEnv.lookup, hyarg] at hw
      cases hw
      simpa [envUpdate_apply, envUpdate_other hyarg] using
        FuelValueRel.recClosure (D₀ := D₀) (j₀ := j₀) (realize := realize)
          fuel self arg body runtimeEnv semanticEnv henv
    · simp [RuntimeEnv.bind, RuntimeEnv.lookup, hyarg, hyself] at hw
      have hy : y ≠ arg := hyarg
      have hy' : y ≠ self := hyself
      simpa [envUpdate_apply, envUpdate_other hy, envUpdate_other hy'] using
        henv y w hw

/-- A related empty-stack recursive closure denotes the unit of its
Scott value. -/
theorem recClosure_terminal_related {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {self arg : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    (hc : s.control = .value (.recClosure self arg body closureEnv))
    (hstack : s.stack = [])
    {semanticEnv : Env (HSemanticValue D₀ j₀)}
    (henv : EnvRel D₀ j₀ realize closureEnv semanticEnv) :
    ChannelConfigRel D₀ j₀ realize s
      (semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (recLambdaValue (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) self arg
          (interp (hardwarePrimitive D₀ j₀ realize) body)
          semanticEnv)) := by
  refine ⟨semanticUnit (Q := TTExternalContinuationPower 2)
      (D₀ := D₀) (j₀ := j₀)
      (recLambdaValue (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) self arg
        (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv),
    id, ?_, ?_, rfl⟩
  · exact hc.symm ▸ ControlRel.value _ _ s.env
      (recClosure_created D₀ j₀ realize self arg body
        closureEnv semanticEnv henv)
  · rw [hstack]
    exact StackRel.nil

/-- Operational fuel induction at a related empty-stack recursive closure:
each `iterateBot` stage is below the unique terminal tree, so the Scott
fixed point is presented-complete. -/
theorem recClosure_terminal_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {self arg : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    (hc : s.control = .value (.recClosure self arg body closureEnv))
    (hstack : s.stack = [])
    (hscoped : ChannelConfig.WellScoped s)
    {semanticEnv : Env (HSemanticValue D₀ j₀)}
    (henv : EnvRel D₀ j₀ realize closureEnv semanticEnv) :
    PresentedChannelTreeCompleteness D₀ j₀ realize s
      (semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (recLambdaValue (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) self arg
          (interp (hardwarePrimitive D₀ j₀ realize) body)
          semanticEnv)) := by
  have hrel := recClosure_terminal_related D₀ j₀ realize hc hstack henv
  have hterminal : ChannelTerminal s := ⟨.recClosure self arg body closureEnv, hc, hstack⟩
  have hd : ValueRel D₀ j₀ realize hterminal.value
      (recLambdaValue (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) self arg
        (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv) := by
    have hv : hterminal.value =
        .recClosure self arg body closureEnv := by
      have hctl := hterminal.control_eq
      rw [hc] at hctl
      injection hctl with h
      exact h.symm
    rw [hv]
    exact recClosure_created D₀ j₀ realize self arg body
      closureEnv semanticEnv henv
  let R := terminalValueRealization D₀ j₀ hterminal hd
  refine presented_recLambdaValue_of_iterateBot D₀ j₀ realize s
    self arg (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv
    ?hsound ?hlower
  · intro selectors i ξ k hk
    apply sSup_le
    rintro T ⟨_, tree, treeR, _, rfl⟩
    cases tree with
    | terminal hterm =>
        exact (terminal_channelTreePointwiseSound D₀ j₀ hterm hscoped
          hrel treeR).restricted_le_selected selectors i k
    | internal hstep next =>
        exact False.elim
          (ChannelInternalStep.not_value_nil hstep hc hstack)
    | external _ hex _ =>
        exact False.elim (by cases hex <;> cases hc)
    | probability _ _ _ _ =>
        cases hc
    | probabilityZero _ =>
        cases hc
    | probabilityOne _ =>
        cases hc
    | measurement _ _ =>
        cases hc
  · intro fuel selectors i ξ k hk
    refine (selectPath_recClosureFuelValue_le_recLambdaValue D₀ j₀
      realize self arg body semanticEnv fuel selectors i k).trans ?_
    have heq :=
      terminal_restrictedResult_eq D₀ j₀ hterminal hscoped hrel R
        selectors i k
    rw [← heq]
    apply le_sSup
    exact ⟨0, ChannelTree.terminal hterminal, R, le_rfl, rfl⟩

/-- Recursive abstraction at an empty stack is the identity wrap of the
related recursive closure, so operational fuel induction lifts through
`recLam`. -/
theorem recLam_terminal_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {self arg : Name}
    {body : Term (QubitPrimitive C)}
    (hc : s.control = .term (.recLam self arg body))
    (hstack : s.stack = [])
    (hscoped : ChannelConfig.WellScoped s)
    {semanticEnv : Env (HSemanticValue D₀ j₀)}
    (henv : EnvRel D₀ j₀ realize s.env semanticEnv) :
    PresentedChannelTreeCompleteness D₀ j₀ realize s
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.recLam self arg body) semanticEnv) := by
  have hvalueScoped : RuntimeValue.WellScoped
      (.recClosure self arg body s.env) := by
    have hctl := hscoped.left
    rw [hc] at hctl
    exact RuntimeValue.WellScoped.recClosure self arg body s.env
      hctl.left fun y hy => hctl.right y hy
  have henvScoped : RuntimeEnv.WellScoped s.env := by
    have hctl := hscoped.left
    rw [hc] at hctl
    exact hctl.left
  have hchild : PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .value (.recClosure self arg body s.env)}
      (semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (recLambdaValue (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) self arg
          (interp (hardwarePrimitive D₀ j₀ realize) body)
          semanticEnv)) :=
    recClosure_terminal_presentedChannelTreeCompleteness D₀ j₀ realize
      (s := {s with control := .value (.recClosure self arg body s.env)})
      rfl hstack
      ⟨⟨henvScoped, hvalueScoped⟩, hscoped.right⟩
      henv
  let t : ChannelConfig C :=
    {s with control := .value (.recClosure self arg body s.env)}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.recLam self arg body)} t :=
      ChannelInternalStep.recursive (s := s) (self := self) (arg := arg)
        (body := body)
    have hs : s = {s with control := .term (.recLam self arg body)} :=
      ChannelConfig.ext hc rfl rfl rfl
    exact hs.symm ▸ happ
  rw [interp_recLam_apply]
  exact identity_step_presentedChannelTreeCompleteness D₀ j₀ realize
    hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_of_recursive h' hc) hchild

/-- A syntactically closed `recLam` at a normalized start is
presented-complete: the unique empty-stack unfolding is the Scott
fixed point of its finite `iterateBot` stages. -/
theorem recLam_initial_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (hclosed : Closed (.recLam self arg body))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.recLam self arg body) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.recLam self arg body) semanticEnv) :=
  recLam_terminal_presentedChannelTreeCompleteness D₀ j₀ realize
    rfl rfl (initialChannelConfig_wellScoped hclosed quantum)
    (env_nil D₀ j₀ realize semanticEnv)

/-- Packaged presented completeness for a closed initial `recLam`. -/
theorem recLam_initial_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (hclosed : Closed (.recLam self arg body))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelConfigCompleteness D₀ j₀ realize
      (initialChannelConfig (.recLam self arg body) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.recLam self arg body) semanticEnv) where
  related := initialChannelConfig_related D₀ j₀ realize
    (.recLam self arg body) quantum semanticEnv
  complete := recLam_initial_presentedChannelTreeCompleteness D₀ j₀
    realize self arg body hclosed quantum semanticEnv

/-- Presented completeness is token adequacy at finitely represented
final continuations. -/
theorem presented_channel_tree_token_adequacy_iff {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (start : ChannelConfig C) (denotation : HSemanticComp D₀ j₀)
    (hcomplete : PresentedChannelTreeCompleteness D₀ j₀ realize
      start denotation)
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors denotation i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C start)
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) := by
  classical
  rw [hcomplete.selected_result_eq_channelTree_sup_presented
    selectors i ξ k hk, RoundedTheory.mem_sSup]
  constructor
  · rintro ⟨_, ⟨fuel, tree, R, hdepth, rfl⟩, htoken⟩
    by_cases havail : ResultAvailable tree selectors i
    · refine ⟨fuel, tree, R, hdepth, havail, ?_⟩
      apply (token_of_restrictedInstrument D₀ j₀ realize tree R selectors i
        ξ k (fun o => hk _) token).1
      rw [restrictedResult_eq_embed D₀ j₀ realize tree R selectors i k havail]
        at htoken
      exact htoken
    · rw [restrictedResult_eq_bot D₀ j₀ realize tree R selectors i k havail]
        at htoken
      have hfalse : False := by
        rw [← sSup_empty, RoundedTheory.mem_sSup] at htoken
        simp at htoken
      exact hfalse.elim
  · rintro ⟨fuel, tree, R, hdepth, havail, htoken⟩
    refine ⟨restrictedResult D₀ j₀ realize tree R selectors i k, ?_, ?_⟩
    · exact ⟨fuel, tree, R, hdepth, rfl⟩
    · rw [restrictedResult_eq_embed D₀ j₀ realize tree R selectors i k havail]
      exact (token_of_restrictedInstrument D₀ j₀ realize tree R selectors i
          ξ k (fun o => hk _) token).2 htoken

/-- Closed `recLam` tokens are finite channel-tree tokens: each
`iterateBot` stage is below the unique empty-stack tree. -/
theorem recLam_initial_presented_token_adequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (hclosed : Closed (.recLam self arg body))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize)
          (.recLam self arg body) semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig (.recLam self arg body) quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig (.recLam self arg body) quantum)
    (interp (hardwarePrimitive D₀ j₀ realize)
      (.recLam self arg body) semanticEnv)
    (recLam_initial_presentedChannelTreeCompleteness D₀ j₀ realize
      self arg body hclosed quantum semanticEnv)
    selectors ξ k hk i token

theorem closed_app {Prim : Type} {fn arg : Term Prim}
    (h : Closed (.app fn arg)) : Closed fn ∧ Closed arg := by
  simpa [Closed, free] using h

theorem closed_intern {Prim : Type} {left right : Term Prim}
    (h : Closed (.intern left right)) : Closed left ∧ Closed right := by
  simpa [Closed, free] using h

theorem closed_extern {Prim : Type} {left right : Term Prim}
    (h : Closed (.extern left right)) : Closed left ∧ Closed right := by
  simpa [Closed, free] using h

theorem closed_prob {Prim : Type} {p : Prob} {left right : Term Prim}
    (h : Closed (.prob p left right)) : Closed left ∧ Closed right := by
  simpa [Closed, free] using h

/-- A well-scoped related empty-stack value is presented-complete: the
unique tree is the terminal leaf, and functionality identifies it with
the related denotation. -/
theorem terminal_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} (hterminal : ChannelTerminal s)
    (hscoped : ChannelConfig.WellScoped s)
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelTreeCompleteness D₀ j₀ realize s answer where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ k hk
    obtain ⟨d, hd, _hanswer⟩ := terminal_related D₀ j₀ hterminal hrel
    let R := terminalValueRealization D₀ j₀ hterminal hd
    have heq :=
      terminal_restrictedResult_eq D₀ j₀ hterminal hscoped hrel R
        selectors i k
    apply le_antisymm
    · rw [← heq]
      apply le_sSup
      exact ⟨0, ChannelTree.terminal hterminal, R, le_rfl, rfl⟩
    · apply sSup_le
      rintro T ⟨_, tree, treeR, _, rfl⟩
      cases tree with
      | terminal hterm =>
          exact (terminal_channelTreePointwiseSound D₀ j₀ hterm hscoped
            hrel treeR).restricted_le_selected selectors i k
      | internal hstep next =>
          exact False.elim
            (ChannelInternalStep.not_value_nil hstep
              hterminal.control_eq hterminal.stack_eq)
      | external _ hex _ =>
          exact False.elim (ChannelExternalStep.not_value hex
            hterminal.control_eq)
      | probability _ _ _ _ =>
          cases hterminal.control_eq
      | probabilityZero _ =>
          cases hterminal.control_eq
      | probabilityOne _ =>
          cases hterminal.control_eq
      | measurement _ _ =>
          cases hterminal.control_eq

theorem closure_terminal_related {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    (hc : s.control = .value (.closure x body closureEnv))
    (hstack : s.stack = [])
    {semanticEnv : Env (HSemanticValue D₀ j₀)}
    (henv : EnvRel D₀ j₀ realize closureEnv semanticEnv) :
    ChannelConfigRel D₀ j₀ realize s
      (semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (lambdaValue (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) x
          (interp (hardwarePrimitive D₀ j₀ realize) body)
          semanticEnv)) := by
  refine ⟨semanticUnit (Q := TTExternalContinuationPower 2)
      (D₀ := D₀) (j₀ := j₀)
      (lambdaValue (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) x
        (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv),
    id, ?_, ?_, rfl⟩
  · exact hc.symm ▸ ControlRel.value _ _ s.env
      (closure_created D₀ j₀ realize x body
        closureEnv semanticEnv henv)
  · rw [hstack]
    exact StackRel.nil

theorem closure_terminal_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    (hc : s.control = .value (.closure x body closureEnv))
    (hstack : s.stack = [])
    (hscoped : ChannelConfig.WellScoped s)
    {semanticEnv : Env (HSemanticValue D₀ j₀)}
    (henv : EnvRel D₀ j₀ realize closureEnv semanticEnv) :
    PresentedChannelTreeCompleteness D₀ j₀ realize s
      (semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (lambdaValue (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) x
          (interp (hardwarePrimitive D₀ j₀ realize) body)
          semanticEnv)) :=
  terminal_presentedChannelTreeCompleteness D₀ j₀ realize
    ⟨.closure x body closureEnv, hc, hstack⟩ hscoped
    (closure_terminal_related D₀ j₀ realize hc hstack henv)

/-- Ordinary abstraction at an empty stack is the identity wrap of the
related closure. -/
theorem lam_terminal_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x : Name}
    {body : Term (QubitPrimitive C)}
    (hc : s.control = .term (.lam x body))
    (hstack : s.stack = [])
    (hscoped : ChannelConfig.WellScoped s)
    {semanticEnv : Env (HSemanticValue D₀ j₀)}
    (henv : EnvRel D₀ j₀ realize s.env semanticEnv) :
    PresentedChannelTreeCompleteness D₀ j₀ realize s
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.lam x body) semanticEnv) := by
  have hvalueScoped : RuntimeValue.WellScoped
      (.closure x body s.env) := by
    have hctl := hscoped.left
    rw [hc] at hctl
    exact RuntimeValue.WellScoped.closure x body s.env
      hctl.left fun y hy => hctl.right y hy
  have henvScoped : RuntimeEnv.WellScoped s.env := by
    have hctl := hscoped.left
    rw [hc] at hctl
    exact hctl.left
  have hchild : PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .value (.closure x body s.env)}
      (semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (lambdaValue (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) x
          (interp (hardwarePrimitive D₀ j₀ realize) body)
          semanticEnv)) :=
    closure_terminal_presentedChannelTreeCompleteness D₀ j₀ realize
      (s := {s with control := .value (.closure x body s.env)})
      rfl hstack
      ⟨⟨henvScoped, hvalueScoped⟩, hscoped.right⟩
      henv
  let t : ChannelConfig C :=
    {s with control := .value (.closure x body s.env)}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.lam x body)} t :=
      ChannelInternalStep.lambda (s := s) (x := x) (body := body)
    have hs : s = {s with control := .term (.lam x body)} :=
      ChannelConfig.ext hc rfl rfl rfl
    exact hs.symm ▸ happ
  rw [interp_lam_apply]
  exact identity_step_presentedChannelTreeCompleteness D₀ j₀ realize
    hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_of_lambda h' hc) hchild

/-- Internal choice of any two presented closed terms is the join of their
channel-tree suprema. -/
theorem intern_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hleft : PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig left quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv))
    (hright : PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig right quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.intern left right) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) (.intern left right)
        semanticEnv) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ k hk
    rw [selectPath_intern,
      hleft.selected_result_eq_channelTree_sup_presented selectors i ξ k hk,
      hright.selected_result_eq_channelTree_sup_presented selectors i ξ k hk]
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
        · exact
            (restrictedResult_internal_of_identity D₀ j₀ realize
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
              selectors i k).symm
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
        · exact
            (restrictedResult_internal_of_identity D₀ j₀ realize
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
              selectors i k).symm
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
            have := restrictedResult_internal_of_identity D₀ j₀ realize
              h hop next R selectors i k
            rw [this]
            apply le_sup_of_le_left
            apply le_sSup
            exact ⟨next.depth,
              next,
              internalChildRealization D₀ j₀ realize h next R,
              le_rfl, rfl⟩
          · cases ht
            have := restrictedResult_internal_of_identity D₀ j₀ realize
              h hop next R selectors i k
            rw [this]
            apply le_sup_of_le_right
            apply le_sSup
            exact ⟨next.depth,
              next,
              internalChildRealization D₀ j₀ realize h next R,
              le_rfl, rfl⟩
      | external _ hex _ =>
          exact False.elim (ChannelExternalStep.not_intern hex hctrl)

/-- External choice of any two presented closed terms is the selected
child-tree supremum. -/
theorem extern_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hleft : PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig left quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv))
    (hright : PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig right quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.extern left right) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) (.extern left right)
        semanticEnv) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ k hk
    cases selectors with
    | cons b selectors =>
        rw [selectPath_extern_cons]
        cases b
        · simp only [Bool.false_eq_true, if_false]
          rw [hleft.selected_result_eq_channelTree_sup_presented
            selectors i ξ k hk,
            external_cons_channelTreeSup]
          simp
        · simp only [if_true]
          rw [hright.selected_result_eq_channelTree_sup_presented
            selectors i ξ k hk,
            external_cons_channelTreeSup]
          simp
    | nil =>
        cases i with
        | zero =>
            rw [HardwareAdequacy.selectPath_nil, interp_extern_apply,
              external_root_channelTreeSup]
            change (TTContinuation.externalChoice
              (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv,
                interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)
              0) k = ⊥
            rw [TTContinuation.externalChoice_root_bot]
            exact ScottMap.bot_apply k
        | succ n =>
            by_cases heven : n % 2 = 0
            · have hi : n + 1 =
                  HardwareAdequacy.branchCoordinate false (n / 2) := by
                simp [HardwareAdequacy.branchCoordinate]
                omega
              rw [hi, HardwareAdequacy.selectPath_nil,
                selectPath_extern_coordinate]
              simp only [Bool.false_eq_true, if_false]
              have hc :=
                hleft.selected_result_eq_channelTree_sup_presented
                  [] (n / 2) ξ k hk
              have hc' :
                  interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv
                      (n / 2) k =
                    sSup (channelTreeResults D₀ j₀ realize
                      (initialChannelConfig left quantum) [] (n / 2) k) := by
                simpa using hc
              exact hc'.trans
                (external_coordinate_channelTreeSup D₀ j₀ realize left right
                  quantum false (n / 2) k).symm
            · have hodd : n % 2 = 1 := by omega
              have hi : n + 1 =
                  HardwareAdequacy.branchCoordinate true (n / 2) := by
                simp [HardwareAdequacy.branchCoordinate]
                omega
              rw [hi, HardwareAdequacy.selectPath_nil,
                selectPath_extern_coordinate]
              simp only [if_true]
              have hc :=
                hright.selected_result_eq_channelTree_sup_presented
                  [] (n / 2) ξ k hk
              have hc' :
                  interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv
                      (n / 2) k =
                    sSup (channelTreeResults D₀ j₀ realize
                      (initialChannelConfig right quantum) [] (n / 2) k) := by
                simpa using hc
              exact hc'.trans
                (external_coordinate_channelTreeSup D₀ j₀ realize left right
                  quantum true (n / 2) k).symm

/-- Endpoint completeness at weight zero, at a presented continuation. -/
theorem prob_zero_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hright : PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig right quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.prob 0 left right) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) (.prob 0 left right)
        semanticEnv) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ k hk
    have hright' :=
      PresentedChannelTreeCompleteness.congr
        (show
            { initialChannelConfig (.prob 0 left right) quantum with
              control := .term right
              quantum := applyOperation
                (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                (initialChannelConfig (.prob 0 left right) quantum).quantum } =
              initialChannelConfig right quantum from
          ChannelConfig.ext rfl rfl rfl
            (applyOperation_sourceProbability_one_initial left right quantum)).symm
        rfl hright
    rw [selectPath_prob_zero,
      hright'.selected_result_eq_channelTree_sup_presented
        selectors i ξ k hk]
    apply le_antisymm
    · apply sSup_le
      rintro T ⟨fuel, child, R, hdepth, rfl⟩
      apply le_sSup
      refine ⟨fuel + 1, wrapProbZero left right quantum child,
        wrapProbabilityZeroRealization D₀ j₀ realize
          (s := initialChannelConfig (.prob 0 left right) quantum)
          (leftTerm := left) (rightTerm := right) child R, ?_, ?_⟩
      · simpa [wrapProbZero_depth] using Nat.succ_le_succ hdepth
      · exact
          (restrictedResult_probabilityZero D₀ j₀ realize child
            (wrapProbabilityZeroRealization D₀ j₀ realize
              (s := initialChannelConfig (.prob 0 left right) quantum)
              (leftTerm := left) (rightTerm := right) child R)
            selectors i k).symm
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      have hle :=
        restrictedResult_of_control_prob_zero D₀ j₀ realize tree R rfl
          selectors i k
      exact hle

/-- Endpoint completeness at weight one, at a presented continuation. -/
theorem prob_one_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hleft : PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig left quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.prob 1 left right) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) (.prob 1 left right)
        semanticEnv) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ k hk
    have hleft' :=
      PresentedChannelTreeCompleteness.congr
        (show
            { initialChannelConfig (.prob 1 left right) quantum with
              control := .term left
              quantum := applyOperation
                (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                (initialChannelConfig (.prob 1 left right) quantum).quantum } =
              initialChannelConfig left quantum from
          ChannelConfig.ext rfl rfl rfl
            (by
            apply SubNormalizedDensity.ext
            rw [applyOperation_sourceProbability_one]
            rfl)).symm
        rfl hleft
    rw [selectPath_prob_one,
      hleft'.selected_result_eq_channelTree_sup_presented
        selectors i ξ k hk]
    apply le_antisymm
    · apply sSup_le
      rintro T ⟨fuel, child, R, hdepth, rfl⟩
      apply le_sSup
      refine ⟨fuel + 1, wrapProbOne left right quantum child,
        wrapProbabilityOneRealization D₀ j₀ realize
          (s := initialChannelConfig (.prob 1 left right) quantum)
          (leftTerm := left) (rightTerm := right) child R, ?_, ?_⟩
      · simpa [wrapProbOne_depth] using Nat.succ_le_succ hdepth
      · exact
          (restrictedResult_probabilityOne D₀ j₀ realize child
            (wrapProbabilityOneRealization D₀ j₀ realize
              (s := initialChannelConfig (.prob 1 left right) quantum)
              (leftTerm := left) (rightTerm := right) child R)
            selectors i k).symm
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      have hle :=
        restrictedResult_of_control_prob_one D₀ j₀ realize tree R rfl
          selectors i k
      exact hle

theorem no_channelTree_of_invalid_prob {C : Type}
    {s : ChannelConfig C} (tree : ChannelTree C s)
    {p : ℝ} {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.prob p left right))
    (hp : ¬ (0 ≤ p ∧ p ≤ 1)) : False := by
  cases tree with
  | terminal hterm =>
      have := hterm.control_eq.symm.trans hc
      cases this
  | internal h _ =>
      exact False.elim (ChannelInternalStep.not_prob h hc)
  | external _ h _ =>
      exact False.elim (ChannelExternalStep.not_prob h hc)
  | @probability s' p' left' right' hp₀ hp₁ _ _ =>
      have hctrl :
          s.control = .term (.prob p' left' right') := by
        change ({s' with
            control := .term (.prob p' left' right')}).control =
          .term (.prob p' left' right')
        rfl
      rw [hc] at hctrl
      injection hctrl with hterm
      injection hterm with hp' _ _
      subst p
      exact hp ⟨hp₀.le, hp₁.le⟩
  | @probabilityZero s' L R next =>
      have hctrl : s.control = .term (.prob 0 L R) := by
        change ({s' with control := .term (.prob 0 L R)}).control =
          .term (.prob 0 L R)
        rfl
      rw [hc] at hctrl
      injection hctrl with hterm
      injection hterm with hp0
      subst p
      exact hp ⟨le_rfl, zero_le_one⟩
  | @probabilityOne s' L R next =>
      have hctrl : s.control = .term (.prob 1 L R) := by
        change ({s' with control := .term (.prob 1 L R)}).control =
          .term (.prob 1 L R)
        rfl
      rw [hc] at hctrl
      injection hctrl with hterm
      injection hterm with hp1
      subst p
      exact hp ⟨zero_le_one, le_rfl⟩
  | measurement _ _ =>
      cases hc

/-- Invalid weights have no physical trees and denote bottom. -/
theorem prob_invalid_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (p : ℝ) (hp : ¬ (0 ≤ p ∧ p ≤ 1))
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.prob p left right) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) (.prob p left right)
        semanticEnv) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ k hk
    have hbot :
        HardwareAdequacy.selectPath selectors
          (interp (hardwarePrimitive D₀ j₀ realize) (.prob p left right)
            semanticEnv) i k = ⊥ := by
      rw [selectPath_prob, TTContinuation.probChoice_apply, dif_neg hp]
    rw [hbot]
    apply le_antisymm
    · exact bot_le
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      exact False.elim
        (no_channelTree_of_invalid_prob tree rfl hp)

/-- A syntactically closed `lam` at a normalized start is
presented-complete. -/
theorem lam_initial_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x : Name) (body : Term (QubitPrimitive C))
    (hclosed : Closed (.lam x body))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.lam x body) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.lam x body) semanticEnv) :=
  lam_terminal_presentedChannelTreeCompleteness D₀ j₀ realize
    rfl rfl (initialChannelConfig_wellScoped hclosed quantum)
    (env_nil D₀ j₀ realize semanticEnv)

/-- Interior probabilistic choice from presented children at the scaled
source-probability starts. -/
theorem prob_presented_of_presented_children {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1)
    (left right : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hleft : PresentedChannelTreeCompleteness D₀ j₀ realize
      (probLeftConfig p hp₀.le hp₁.le left right quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv))
    (hright : PresentedChannelTreeCompleteness D₀ j₀ realize
      (probRightConfig p hp₀.le hp₁.le left right quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.prob p left right) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) (.prob p left right)
        semanticEnv) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ k hk
    have hpI : 0 ≤ p ∧ p ≤ 1 := ⟨hp₀.le, hp₁.le⟩
    rw [selectPath_prob, TTContinuation.probChoice_apply, dif_pos hpI,
      hleft.selected_result_eq_channelTree_sup_presented selectors i ξ k hk,
      hright.selected_result_eq_channelTree_sup_presented selectors i ξ k hk]
    let SL :=
      channelTreeResults D₀ j₀ realize
        (probLeftConfig p hp₀.le hp₁.le left right quantum) selectors i k
    let SR :=
      channelTreeResults D₀ j₀ realize
        (probRightConfig p hp₀.le hp₁.le left right quantum) selectors i k
    refine le_antisymm ?_ ?_
    · by_cases hL : SL.Nonempty
      · by_cases hR : SR.Nonempty
        · rw [TTWeightedAggregation.weightedResultScott_sSup_product
            p hp₀.le hp₁.le SL SR hL hR]
          apply sSup_le
          rintro _ ⟨⟨TL, TR⟩, ⟨⟨fuelL, leftT, leftR, hdepthL, rfl⟩,
              ⟨fuelR, rightT, rightR, hdepthR, rfl⟩⟩, rfl⟩
          apply le_sSup
          refine ⟨max fuelL fuelR + 1,
            wrapProb hp₀ hp₁ left right quantum leftT rightT,
            wrapProbabilityRealization D₀ j₀ realize hp₀ hp₁ leftT rightT
              leftR rightR, ?_, ?_⟩
          · simp [wrapProb_depth]
            omega
          · exact
              (restrictedResult_probability_presented D₀ j₀ realize hp₀ hp₁
                leftT rightT
                (wrapProbabilityRealization D₀ j₀ realize hp₀ hp₁
                  leftT rightT leftR rightR)
                selectors i ξ k hk).symm
        · have hbot :
              TTWeightedAggregation.weightedResultScott p hp₀.le hp₁.le
                (sSup SL, sSup SR) = ⊥ := by
            have : sSup SR = ⊥ := by
              have hempty : SR = ∅ :=
                Set.not_nonempty_iff_eq_empty.mp hR
              rw [hempty, sSup_empty]
            rw [this, TTWeightedAggregation.weightedResultScott_bot_right
              p hp₀ hp₁]
          rw [hbot]
          exact bot_le
      · have hbot :
            TTWeightedAggregation.weightedResultScott p hp₀.le hp₁.le
              (sSup SL, sSup SR) = ⊥ := by
          have : sSup SL = ⊥ := by
            have hempty : SL = ∅ :=
              Set.not_nonempty_iff_eq_empty.mp hL
            rw [hempty, sSup_empty]
          rw [this, TTWeightedAggregation.weightedResultScott_bot_left
            p hp₀ hp₁]
        rw [hbot]
        exact bot_le
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      have hle :=
        restrictedResult_of_control_prob_presented D₀ j₀ realize tree R
          hp₀ hp₁ rfl selectors i ξ k hk
      have hL :
          { initialChannelConfig (.prob p left right) quantum with
              control := .term left
              quantum := applyOperation
                (sourceProbabilityOperation p hp₀.le hp₁.le)
                (initialChannelConfig (.prob p left right) quantum).quantum } =
            probLeftConfig p hp₀.le hp₁.le left right quantum := by
        apply ChannelConfig.ext <;> rfl
      have hR :
          { initialChannelConfig (.prob p left right) quantum with
              control := .term right
              quantum := applyOperation
                (sourceProbabilityOperation (1 - p)
                  (sub_nonneg.mpr hp₁.le) (by linarith))
                (initialChannelConfig (.prob p left right) quantum).quantum } =
            probRightConfig p hp₀.le hp₁.le left right quantum := by
        apply ChannelConfig.ext <;> rfl
      simpa [hL, hR] using hle

open Classical

def runtimeValueBodySize {C : Type} : RuntimeValue C → ℕ
  | .payload _ => 0
  | .closure _ body _ => termSize body
  | .recClosure _ _ body _ => termSize body

def valueProducedSize {C : Type} (value : RuntimeValue C)
    (runtimeEnv : RuntimeEnv C) : ℕ :=
  if ∃ x, RuntimeEnv.lookup x runtimeEnv = some value then
    0
  else
    runtimeValueBodySize value

def envCharge {C : Type} : RuntimeEnv C → ℕ
  | [] => 0
  | (_, value) :: rest => valueProducedSize value rest + envCharge rest

def stackCharge {C : Type} (runtimeEnv : RuntimeEnv C) : EvalStack C → ℕ
  | [] => 0
  | .argument arg _ :: rest =>
      termSize arg + stackCharge runtimeEnv rest
  | .function fn :: rest =>
      valueProducedSize fn runtimeEnv + stackCharge runtimeEnv rest

def controlCharge {C : Type} (s : ChannelConfig C) : ℕ :=
  match s.control with
  | .term code => termSize code
  | .value value => valueProducedSize value s.env

def controlPhase {C : Type} (s : ChannelConfig C) : ℕ :=
  match s.control with
  | .term _ => 0
  | .value _ => 1

def configMeasure {C : Type} (s : ChannelConfig C) : ℕ :=
  2 * (controlCharge s + stackCharge s.env s.stack + envCharge s.env) +
    controlPhase s

/-- Token adequacy for every closed term whose channel-tree completeness
theorem is already proved. -/
theorem closed_term_channel_tree_token_adequacy {C : Type}
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
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  initialConfig_channel_tree_token_adequacy_iff D₀ j₀ realize code quantum
    semanticEnv hcomplete selectors ξ k hk i token

/-! ## Path-indexed token adequacy -/

/-- One finite channel tree witnesses a token at the active path coordinate.
The final value continuation is supplied separately, so the same predicate can
be transported across administrative CEK steps. -/
def PathChannelTreeTokenWitness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (start : ChannelConfig C) (active : ℕ)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (token : TTObservationToken 2) : Prop :=
  ∃ (tree : ChannelTree C start)
      (R : ChannelTreeRealization D₀ j₀ realize tree),
    ResultAvailable tree [] active ∧
      TTObservationToken.Holds resultCode token
        ((restrictedInstrument D₀ j₀ realize tree R [] active).bind ξ)

/-- Token-level interface for the path-indexed fundamental theorem.

Besides retaining the logical relation for the current CEK state, it says
exactly that every token in the related result is witnessed by a finite
channel tree at the active coordinate, for every finitely represented final
continuation. -/
structure PathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (start : ChannelConfig C) (active : ℕ)
    (observedStack : ObservedStack C)
    (finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (result : TTResult 2) : Prop where
  related :
    PathChannelConfigRel D₀ j₀ realize start active observedStack finalK result
  token_iff :
    ∀ (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1}),
      (∀ d, finalK d = (ξ d).satisfiedTTTheory resultCode) →
      ∀ token,
        token ∈ result ↔
          PathChannelTreeTokenWitness D₀ j₀ realize start active ξ token

/-- At a related terminal state, token membership is exactly membership in
the restricted terminal instrument. -/
theorem path_terminal_token_of_restrictedInstrument {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} (hterminal : ChannelTerminal s)
    (hscoped : ChannelConfig.WellScoped s)
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result)
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.terminal hterminal))
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (hk : ∀ d, finalK d = (ξ d).satisfiedTTTheory resultCode)
    (token : TTObservationToken 2) :
    token ∈ result ↔
      TTObservationToken.Holds resultCode token
        ((restrictedInstrument D₀ j₀ realize
          (ChannelTree.terminal hterminal) R [] active).bind ξ) := by
  rcases hrel with
    ⟨herase, current, currentK, hcontrol, hstack, hresult⟩
  have hobserved : observedStack = [] := by
    cases observedStack with
    | nil => rfl
    | cons frame rest =>
        rw [ObservedStack.erase_cons, hterminal.stack_eq] at herase
        cases herase
  subst observedStack
  cases hstack
  have hnil : StackRel D₀ j₀ realize s.stack id := by
    rw [hterminal.stack_eq]
    exact StackRel.nil
  have hconfig : ChannelConfigRel D₀ j₀ realize s current :=
    ⟨current, id, hcontrol, hnil, rfl⟩
  obtain ⟨d, hcurrent, hrealized⟩ :=
    terminal_realized_eq_unit D₀ j₀ hterminal hscoped hconfig R
  have hall : ∀ o, OutcomeCompatible
      (ChannelTree.terminal hterminal) [] active o := by
    intro o
    rcases o with ⟨⟩
    exact List.nil_prefix
  have hresultEq :
      result =
        embed (restrictedInstrument D₀ j₀ realize
          (ChannelTree.terminal hterminal) R [] active) finalK := by
    rw [hresult, hcurrent]
    rw [congrArg (fun f : ScottMap
        (ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) (TTResult 2) =>
          f finalK)
      (embed_restricted_of_all_compatible D₀ j₀ realize
        (ChannelTree.terminal hterminal) R [] active hall)]
    rw [hrealized, embed_unit]
    rfl
  rw [hresultEq]
  exact token_of_restrictedInstrument D₀ j₀ realize
    (ChannelTree.terminal hterminal) R [] active ξ finalK
    (fun o => hk _) token

/-- A related terminal configuration is token-adequate.  The realization
argument supplies its canonical finite terminal witness. -/
theorem terminal_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} (hterminal : ChannelTerminal s)
    (hscoped : ChannelConfig.WellScoped s)
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result)
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.terminal hterminal)) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s active observedStack finalK result where
  related := hrel
  token_iff := by
    intro ξ hk token
    constructor
    · intro htoken
      refine ⟨ChannelTree.terminal hterminal, R, ?_, ?_⟩
      · simp [ResultAvailable, resultAvailableAt]
      · exact
          (path_terminal_token_of_restrictedInstrument D₀ j₀ realize
            hterminal hscoped hrel R ξ hk token).mp htoken
    · rintro ⟨tree, R', _, htoken⟩
      cases tree with
      | terminal hterminal' =>
          exact
            (path_terminal_token_of_restrictedInstrument D₀ j₀ realize
              hterminal' hscoped hrel R' ξ hk token).mpr htoken
      | internal hstep next =>
          exact False.elim
            (ChannelInternalStep.not_value_nil hstep hterminal.control_eq
              hterminal.stack_eq)
      | external _ hstep _ =>
          exact False.elim (by cases hstep <;> cases hterminal.control_eq)
      | probability _ _ _ _ =>
          cases hterminal.control_eq
      | probabilityZero _ =>
          cases hterminal.control_eq
      | probabilityOne _ =>
          cases hterminal.control_eq
      | measurement _ _ =>
          cases hterminal.control_eq

/-- Token adequacy transfers backwards across a unique-successor
identity-operation step.  Instrument observations are transported through the
unit-sigma outcome reindexing, rather than through lattice-level completeness. -/
theorem identity_step_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C}
    (hstep : ChannelInternalStep s t)
    (hop : channelInternalOperation s = QuantumOperation.identity 2)
    (hunq : ∀ {t'}, ChannelInternalStep s t' → t' = t)
    {active : ℕ} {sourceObserved childObserved : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s active sourceObserved finalK result)
    (hchild : PathChannelTreeTokenAdequacy D₀ j₀ realize
      t active childObserved finalK result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s active sourceObserved finalK result where
  related := hsource
  token_iff := by
    intro ξ hk token
    rw [hchild.token_iff ξ hk token]
    constructor
    · rintro ⟨tree, R, havail, htoken⟩
      let sourceTree := ChannelTree.internal hstep tree
      let sourceR :=
        wrapInternalRealization D₀ j₀ realize hstep tree R
      refine ⟨sourceTree, sourceR, havail, ?_⟩
      apply (token_of_restrictedInstrument D₀ j₀ realize
        sourceTree sourceR [] active ξ finalK (fun o => hk _) token).mp
      rw [embed_restricted_internal_of_identity D₀ j₀ realize
        hstep hop tree sourceR [] active]
      exact
        (token_of_restrictedInstrument D₀ j₀ realize
          tree
          (internalChildRealization D₀ j₀ realize hstep tree sourceR)
          [] active ξ finalK (fun o => hk _) token).mpr htoken
    · rintro ⟨tree, R, havail, htoken⟩
      cases tree with
      | terminal hterminal =>
          exact False.elim
            (ChannelInternalStep.not_value_nil hstep hterminal.control_eq
              hterminal.stack_eq)
      | @internal _ t' hstep' next =>
          have ht : t' = t := hunq hstep'
          subst t'
          let childR :=
            internalChildRealization D₀ j₀ realize hstep' next R
          refine ⟨next, childR, havail, ?_⟩
          apply (token_of_restrictedInstrument D₀ j₀ realize
            next childR [] active ξ finalK (fun o => hk _) token).mp
          rw [← embed_restricted_internal_of_identity D₀ j₀ realize
            hstep' hop next R [] active]
          exact
            (token_of_restrictedInstrument D₀ j₀ realize
              (ChannelTree.internal hstep' next) R [] active ξ finalK
              (fun o => hk _) token).mpr htoken
      | external _ hex _ =>
          exact False.elim (by cases hex <;> cases hstep)
      | probability _ _ _ _ =>
          cases hstep
      | probabilityZero _ =>
          cases hstep
      | probabilityOne _ =>
          cases hstep
      | measurement _ _ =>
          cases hstep

/-- Application is an identity step that installs the argument frame at the
active coordinate.  The child adequacy is taken at the same coordinate with
the pushed observed stack. -/
theorem application_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {fn arg : Term (QubitPrimitive C)}
    (hc : s.control = .term (.app fn arg))
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result)
    (hchild : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with
        control := .term fn
        stack := .argument arg s.env :: s.stack}
      active ((.argument arg s.env, active) :: observedStack)
      finalK result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s active observedStack finalK result := by
  let t : ChannelConfig C :=
    {s with
      control := .term fn
      stack := .argument arg s.env :: s.stack}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app fn arg)} t :=
      ChannelInternalStep.application (s := s) (fn := fn) (arg := arg)
    have hs : s = {s with control := .term (.app fn arg)} :=
      ChannelConfig.ext hc rfl rfl rfl
    exact hs.symm ▸ happ
  exact identity_step_pathChannelTreeTokenAdequacy D₀ j₀ realize
    hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_of_application h' hc)
    hsource hchild

/-- Argument evaluation restores the saved frame coordinate.  The function
value is coordinate-independent, so the parent may have descended through
an external branch; token restriction follows the restored coordinate. -/
theorem evaluateArgument_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {fn : RuntimeValue C}
    {arg : Term (QubitPrimitive C)} {callEnv : RuntimeEnv C}
    {rest : EvalStack C} {active saved : ℕ}
    {observedRest : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hc : s.control = .value fn)
    (hs : s.stack = .argument arg callEnv :: rest)
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s active ((.argument arg callEnv, saved) :: observedRest)
      finalK result)
    (hchild : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with
        control := .term arg
        env := callEnv
        stack := .function fn :: rest}
      saved ((.function fn, saved) :: observedRest) finalK result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s saved ((.argument arg callEnv, saved) :: observedRest)
      finalK result := by
  let t : ChannelConfig C :=
    {s with
      control := .term arg
      env := callEnv
      stack := .function fn :: rest}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with
            control := .value fn
            stack := .argument arg callEnv :: rest} t :=
      ChannelInternalStep.evaluateArgument
        (s := s) (fn := fn) (arg := arg) (callEnv := callEnv)
        (rest := rest)
    have hsrc :
        s = {s with
          control := .value fn
          stack := .argument arg callEnv :: rest} :=
      ChannelConfig.ext hc rfl hs rfl
    exact hsrc.symm ▸ happ
  exact identity_step_pathChannelTreeTokenAdequacy D₀ j₀ realize
    hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_of_evaluateArgument h' hc hs)
    (path_channel_config_value_reindex D₀ j₀ hc hsource) hchild

/-- Closure beta pops the function frame and resumes the body at the saved
coordinate.  The argument value is coordinate-independent, so the parent
may have a different active coordinate than the frame. -/
theorem beta_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    {arg : RuntimeValue C} {rest : EvalStack C}
    {active saved : ℕ} {observedRest : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hc : s.control = .value arg)
    (hs : s.stack = .function (.closure x body closureEnv) :: rest)
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s active
      ((.function (.closure x body closureEnv), saved) :: observedRest)
      finalK result)
    (hchild : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with
        control := .term body
        env := RuntimeEnv.bind x arg closureEnv
        stack := rest}
      saved observedRest finalK result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s saved
      ((.function (.closure x body closureEnv), saved) :: observedRest)
      finalK result := by
  let t : ChannelConfig C :=
    {s with
      control := .term body
      env := RuntimeEnv.bind x arg closureEnv
      stack := rest}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with
            control := .value arg
            stack := .function (.closure x body closureEnv) :: rest} t :=
      ChannelInternalStep.beta (s := s) (x := x) (body := body)
        (closureEnv := closureEnv) (arg := arg) (rest := rest)
    have hsrc :
        s = {s with
          control := .value arg
          stack := .function (.closure x body closureEnv) :: rest} :=
      ChannelConfig.ext hc rfl hs rfl
    exact hsrc.symm ▸ happ
  exact identity_step_pathChannelTreeTokenAdequacy D₀ j₀ realize
    hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_of_beta h' hc hs)
    (path_channel_config_value_reindex D₀ j₀ hc hsource) hchild

/-- Recursive-closure beta is the same identity wrap as ordinary beta, with
both recursive binders installed in the body environment. -/
theorem recBeta_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {self x : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    {arg : RuntimeValue C} {rest : EvalStack C}
    {active saved : ℕ} {observedRest : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hc : s.control = .value arg)
    (hs : s.stack =
      .function (.recClosure self x body closureEnv) :: rest)
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s active
      ((.function (.recClosure self x body closureEnv), saved) ::
        observedRest)
      finalK result)
    (hchild : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with
        control := .term body
        env :=
          RuntimeEnv.bind x arg
            (RuntimeEnv.bind self
              (.recClosure self x body closureEnv) closureEnv)
        stack := rest}
      saved observedRest finalK result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s saved
      ((.function (.recClosure self x body closureEnv), saved) ::
        observedRest)
      finalK result := by
  let t : ChannelConfig C :=
    {s with
      control := .term body
      env :=
        RuntimeEnv.bind x arg
          (RuntimeEnv.bind self
            (.recClosure self x body closureEnv) closureEnv)
      stack := rest}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with
            control := .value arg
            stack :=
              .function (.recClosure self x body closureEnv) :: rest} t :=
      ChannelInternalStep.recBeta (s := s) (self := self) (x := x)
        (body := body) (closureEnv := closureEnv) (arg := arg)
        (rest := rest)
    have hsrc :
        s = {s with
          control := .value arg
          stack :=
            .function (.recClosure self x body closureEnv) :: rest} :=
      ChannelConfig.ext hc rfl hs rfl
    exact hsrc.symm ▸ happ
  exact identity_step_pathChannelTreeTokenAdequacy D₀ j₀ realize
    hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_of_recBeta h' hc hs)
    (path_channel_config_value_reindex D₀ j₀ hc hsource) hchild

/-- Recursive abstraction is an identity step onto the related recursive
closure.  Finite `iterateBot` unfoldings describe that closure's tokens;
the operational tree is the identity wrap of the closure value. -/
theorem recursive_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {self arg : Name}
    {body : Term (QubitPrimitive C)}
    (hc : s.control = .term (.recLam self arg body))
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result)
    (hchild : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with control := .value (.recClosure self arg body s.env)}
      active observedStack finalK result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s active observedStack finalK result := by
  let t : ChannelConfig C :=
    {s with control := .value (.recClosure self arg body s.env)}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.recLam self arg body)} t :=
      ChannelInternalStep.recursive (s := s) (self := self) (arg := arg)
        (body := body)
    have hs : s = {s with control := .term (.recLam self arg body)} :=
      ChannelConfig.ext hc rfl rfl rfl
    exact hs.symm ▸ happ
  exact identity_step_pathChannelTreeTokenAdequacy D₀ j₀ realize
    hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_of_recursive h' hc)
    hsource hchild

/-- Ordinary abstraction is the same identity wrap onto a related closure. -/
theorem lambda_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x : Name} {body : Term (QubitPrimitive C)}
    (hc : s.control = .term (.lam x body))
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result)
    (hchild : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with control := .value (.closure x body s.env)}
      active observedStack finalK result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s active observedStack finalK result := by
  let t : ChannelConfig C :=
    {s with control := .value (.closure x body s.env)}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.lam x body)} t :=
      ChannelInternalStep.lambda (s := s) (x := x) (body := body)
    have hs : s = {s with control := .term (.lam x body)} :=
      ChannelConfig.ext hc rfl rfl rfl
    exact hs.symm ▸ happ
  exact identity_step_pathChannelTreeTokenAdequacy D₀ j₀ realize
    hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_of_lambda h' hc)
    hsource hchild

/-- Variable lookup is an identity step onto the related runtime value. -/
theorem variable_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x : Name} {v : RuntimeValue C}
    (hc : s.control = .term (.var x))
    (hlookup : RuntimeEnv.lookup x s.env = some v)
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result)
    (hchild : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with control := .value v}
      active observedStack finalK result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s active observedStack finalK result := by
  let t : ChannelConfig C := {s with control := .value v}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.var x)} t :=
      ChannelInternalStep.variable (s := s) (x := x) (v := v) hlookup
    have hs : s = {s with control := .term (.var x)} :=
      ChannelConfig.ext hc rfl rfl rfl
    exact hs.symm ▸ happ
  exact identity_step_pathChannelTreeTokenAdequacy D₀ j₀ realize
    hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_of_variable h' hc hlookup)
    hsource hchild

/-- Stacked fundamental lemma for `app (lam x body) arg`.
Application pushes the argument frame, abstraction installs the
closure, and argument evaluation restores that frame's coordinate.
The remaining obligation is adequacy of the argument under the
function frame. -/
theorem stacked_lam_app_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x : Name}
    {body arg : Term (QubitPrimitive C)}
    (hc : s.control = .term (.app (.lam x body) arg))
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result)
    (harg : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with
        control := .term arg
        stack := .function (.closure x body s.env) :: s.stack}
      active
      ((.function (.closure x body s.env), active) :: observedStack)
      finalK result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s active observedStack finalK result := by
  have hAppEq :
      {s with control := .term (.app (.lam x body) arg)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelLam :
      PathChannelConfigRel D₀ j₀ realize
        {s with
          control := .term (.lam x body)
          stack := .argument arg s.env :: s.stack}
        active ((.argument arg s.env, active) :: observedStack)
        finalK result :=
    path_channel_config_application D₀ j₀
      (hrel := hAppEq.symm ▸ hsource)
  have hrelClo :
      PathChannelConfigRel D₀ j₀ realize
        {s with
          control := .value (.closure x body s.env)
          stack := .argument arg s.env :: s.stack}
        active ((.argument arg s.env, active) :: observedStack)
        finalK result :=
    path_channel_config_lambda D₀ j₀
      (s := {s with stack := .argument arg s.env :: s.stack})
      (hrel := by
        simpa using hrelLam)
  have hClo :=
    evaluateArgument_pathChannelTreeTokenAdequacy D₀ j₀ realize
      (s := {s with
        control := .value (.closure x body s.env)
        stack := .argument arg s.env :: s.stack})
      (fn := .closure x body s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack)
      (active := active) (saved := active)
      (observedRest := observedStack)
      rfl rfl hrelClo harg
  have hLam :=
    lambda_pathChannelTreeTokenAdequacy D₀ j₀ realize
      (s := {s with
        control := .term (.lam x body)
        stack := .argument arg s.env :: s.stack})
      (x := x) (body := body) rfl hrelLam hClo
  exact application_pathChannelTreeTokenAdequacy D₀ j₀ realize hc
    hsource hLam

/-- Stacked fundamental lemma for `app (recLam self x body) arg`.
The same administrative sequence as ordinary abstraction, installing a
recursive closure. -/
theorem stacked_recLam_app_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {self x : Name}
    {body arg : Term (QubitPrimitive C)}
    (hc : s.control = .term (.app (.recLam self x body) arg))
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result)
    (harg : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with
        control := .term arg
        stack :=
          .function (.recClosure self x body s.env) :: s.stack}
      active
      ((.function (.recClosure self x body s.env), active) ::
        observedStack)
      finalK result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s active observedStack finalK result := by
  have hAppEq :
      {s with control := .term (.app (.recLam self x body) arg)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelRec :
      PathChannelConfigRel D₀ j₀ realize
        {s with
          control := .term (.recLam self x body)
          stack := .argument arg s.env :: s.stack}
        active ((.argument arg s.env, active) :: observedStack)
        finalK result :=
    path_channel_config_application D₀ j₀
      (hrel := hAppEq.symm ▸ hsource)
  have hrelClo :
      PathChannelConfigRel D₀ j₀ realize
        {s with
          control := .value (.recClosure self x body s.env)
          stack := .argument arg s.env :: s.stack}
        active ((.argument arg s.env, active) :: observedStack)
        finalK result :=
    path_channel_config_recursive D₀ j₀
      (s := {s with stack := .argument arg s.env :: s.stack})
      (hrel := by
        simpa using hrelRec)
  have hClo :=
    evaluateArgument_pathChannelTreeTokenAdequacy D₀ j₀ realize
      (s := {s with
        control := .value (.recClosure self x body s.env)
        stack := .argument arg s.env :: s.stack})
      (fn := .recClosure self x body s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack)
      (active := active) (saved := active)
      (observedRest := observedStack)
      rfl rfl hrelClo harg
  have hRec :=
    recursive_pathChannelTreeTokenAdequacy D₀ j₀ realize
      (s := {s with
        control := .term (.recLam self x body)
        stack := .argument arg s.env :: s.stack})
      (self := self) (arg := x) (body := body) rfl hrelRec hClo
  exact application_pathChannelTreeTokenAdequacy D₀ j₀ realize hc
    hsource hRec

/-- Token adequacy for a Pauli-X primitive at an empty stack.  The parent
result is the embedded physical operation, not the child's unit return. -/
theorem pauliX_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {value : C}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hstack : s.stack = [])
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s active observedStack finalK result := by
  refine
    { related := hsource
      token_iff := ?_ }
  intro ξ hk token
  rcases hsource with
    ⟨herase, current, currentK, hcontrol, hstackRel, hresult⟩
  have hobserved : observedStack = [] := by
    cases observedStack with
    | nil => rfl
    | cons frame rest =>
        rw [ObservedStack.erase_cons, hstack] at herase
        cases herase
  subst observedStack
  cases hstackRel
  rw [hc] at hcontrol
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      have hresultEq :
          result =
            embed (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
              (realize value)) finalK := by
        rw [hresult, interp_prim_apply, hardwarePrimitive_pauliX,
          taggedEmbed_apply]
      rcases s with ⟨control, env, stack, quantum⟩
      simp only at hc hstack
      subst control
      subst stack
      let child : ChannelConfig C :=
        { control := .value (.payload value)
          env := env
          stack := []
          quantum := applyOperation Qubit.pauliXOp quantum }
      let hterminal : ChannelTerminal child :=
        { value := .payload value
          control_eq := rfl
          stack_eq := rfl }
      let childTree : ChannelTree C child :=
        ChannelTree.terminal hterminal
      let hstep : ChannelInternalStep
          ⟨.term (.prim (.pauliX value)), env, [], quantum⟩ child :=
        ChannelInternalStep.pauliXPrimitive
          (s := ⟨.term (.prim (.pauliX value)), env, [], quantum⟩)
          (value := value)
      let sourceTree := ChannelTree.internal hstep childTree
      let childR : ChannelTreeRealization D₀ j₀ realize childTree :=
        { value := fun _ => realize value
          related := by
            intro o
            change ValueRel D₀ j₀ realize (.payload value) (realize value)
            exact ValueRel.payload value }
      let sourceR :=
        wrapInternalRealization D₀ j₀ realize hstep childTree childR
      have hembed :
          embed (restrictedInstrument D₀ j₀ realize sourceTree sourceR
              [] active) =
            embed (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
              (realize value)) := by
        rw [embed_restricted_internal D₀ j₀ realize hstep childTree sourceR
          [] active]
        let μ :=
          (FiniteInstrumentComp.ofOperation Qubit.pauliXOp ()).bind
            (fun _ =>
              restrictedInstrument D₀ j₀ realize childTree
                (internalChildRealization D₀ j₀ realize hstep childTree
                  sourceR)
                [] active)
        let _ : Unique μ.Outcome :=
          { default := ⟨⟨⟩, ⟨⟨⟩, List.nil_prefix⟩⟩
            uniq := by
              intro o
              rcases o with ⟨⟨⟩, ⟨⟨⟩, _⟩⟩
              rfl }
        refine embed_eq_ofOperation_of_unique μ Qubit.pauliXOp
          (realize value) ?_ ?_
        · intro o
          rfl
        · intro o
          change KrausFamily.comp (KrausFamily.identity 2)
              Qubit.pauliXOp.kraus =
            Qubit.pauliXOp.kraus
          simp
      constructor
      · intro htoken
        refine ⟨sourceTree, sourceR, trivial, ?_⟩
        apply (token_of_restrictedInstrument D₀ j₀ realize
          sourceTree sourceR [] active ξ finalK
          (fun o => hk _) token).mp
        rw [hembed, ← hresultEq]
        exact htoken
      · rintro ⟨tree, R, havail, htoken⟩
        cases tree with
        | terminal hterminal' =>
            cases hterminal'.control_eq
        | @internal _ t' hstep' next =>
            have ht :=
              ChannelInternalStep.eq_config_of_pauliX hstep' rfl
            subst t'
            cases next with
            | terminal hterm =>
                have hembed' :
                    embed (restrictedInstrument D₀ j₀ realize
                        (ChannelTree.internal hstep'
                          (ChannelTree.terminal hterm)) R [] active) =
                      embed (FiniteInstrumentComp.ofOperation
                        Qubit.pauliXOp (realize value)) := by
                  have hall' : ∀ o, OutcomeCompatible
                      (ChannelTree.internal hstep'
                        (ChannelTree.terminal hterm)) [] active o := by
                    intro o
                    exact List.nil_prefix
                  rw [embed_restricted_of_all_compatible D₀ j₀ realize
                    _ R [] active hall']
                  let μ := realizedInstrument D₀ j₀ realize
                    (ChannelTree.internal hstep'
                      (ChannelTree.terminal hterm)) R
                  let _ : Unique μ.Outcome :=
                    { default := ⟨⟨⟩, ⟨⟩⟩
                      uniq := by
                        intro o
                        rcases o with ⟨⟨⟩, ⟨⟩⟩
                        rfl }
                  refine embed_eq_ofOperation_of_unique μ Qubit.pauliXOp
                    (realize value) ?_ ?_
                  · intro o
                    have hrel := R.related o
                    have hpay :
                        ((ChannelTree.internal hstep'
                            (ChannelTree.terminal hterm)).instrument.value
                          o).isTerminal.value =
                          .payload value := by
                      have hv : hterm.value = .payload value := by
                        injection hterm.control_eq with h
                        exact h.symm
                      simp [ChannelTree.instrument]
                      exact hv
                    rw [hpay] at hrel
                    exact ValueRel.payload_eq D₀ j₀ hrel
                  · intro o
                    rcases o with ⟨⟨⟩, ⟨⟩⟩
                    change KrausFamily.comp (KrausFamily.identity 2)
                        (channelInternalOperation
                          ⟨.term (.prim (.pauliX value)), env, [],
                            quantum⟩).kraus =
                      Qubit.pauliXOp.kraus
                    simp [channelInternalOperation]
                rw [hresultEq, ← hembed']
                exact
                  (token_of_restrictedInstrument D₀ j₀ realize
                    (ChannelTree.internal hstep'
                      (ChannelTree.terminal hterm)) R [] active ξ finalK
                    (fun o => hk _) token).mpr htoken
            | internal h' _ =>
                exact False.elim
                  (ChannelInternalStep.not_value_nil h'
                    (ChannelInternalStep.eq_of_pauliX hstep' rfl).1
                    ((ChannelInternalStep.eq_of_pauliX hstep' rfl).2.2.1))
            | external _ hex _ =>
                exact False.elim
                  (ChannelExternalStep.not_value hex
                    (ChannelInternalStep.eq_of_pauliX hstep' rfl).1)
        | external _ hex _ =>
            exact False.elim (ChannelExternalStep.not_prim hex rfl)

/-- Token adequacy transfers backwards across one selected external edge.
Only the active coordinate descends into the selected child; coordinates
saved in pending frames remain unchanged. -/
theorem external_step_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s t : ChannelConfig C} {selected : Bool}
    {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.extern left right))
    (hstep : ChannelExternalStep s selected t)
    {childActive : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hsource : PathChannelConfigRel D₀ j₀ realize s
      (HardwareAdequacy.branchCoordinate selected childActive)
      observedStack finalK result)
    (hchild : PathChannelTreeTokenAdequacy D₀ j₀ realize
      t childActive observedStack finalK result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize s
      (HardwareAdequacy.branchCoordinate selected childActive)
      observedStack finalK result where
  related := hsource
  token_iff := by
    have ht :
        t = {s with
          control := .term (if selected then right else left)} :=
      ChannelExternalStep.eq_of_extern hstep hc
    subst t
    intro ξ hk token
    rw [hchild.token_iff ξ hk token]
    constructor
    · rintro ⟨tree, R, havail, htoken⟩
      let sourceTree := ChannelTree.external selected hstep tree
      let sourceR :=
        wrapExternalRealization D₀ j₀ realize selected hstep tree R
      refine ⟨sourceTree, sourceR, ?_, ?_⟩
      · cases selected
        · change ∃ rest,
            HardwareAdequacy.coordinatePath
                (HardwareAdequacy.branchCoordinate false childActive) =
              false :: rest ∧
              resultAvailableAt tree rest
          exact ⟨HardwareAdequacy.coordinatePath childActive, by simp, havail⟩
        · change ∃ rest,
            HardwareAdequacy.coordinatePath
                (HardwareAdequacy.branchCoordinate true childActive) =
              true :: rest ∧
              resultAvailableAt tree rest
          exact ⟨HardwareAdequacy.coordinatePath childActive, by simp, havail⟩
      · apply (token_of_restrictedInstrument D₀ j₀ realize
          sourceTree sourceR []
          (HardwareAdequacy.branchCoordinate selected childActive)
          ξ finalK (fun o => hk _) token).mp
        rw [embed_restricted_external_coordinate D₀ j₀ realize
          selected hstep tree sourceR childActive]
        exact
          (token_of_restrictedInstrument D₀ j₀ realize
            tree
            (externalChildRealization D₀ j₀ realize selected hstep tree sourceR)
            [] childActive ξ finalK (fun o => hk _) token).mpr htoken
    · rintro ⟨tree, R, havail, htoken⟩
      cases tree with
      | terminal hterminal =>
          have := hterminal.control_eq.symm.trans hc
          cases this
      | internal hinternal next =>
          exact False.elim (by cases hinternal <;> cases hc)
      | @external _ t' selected' hstep' next =>
          have hselected : selected' = selected := by
            cases selected' <;> cases selected
            · rfl
            · exfalso
              rcases havail with ⟨rest, hpath, _⟩
              rw [HardwareAdequacy.coordinatePath_right] at hpath
              cases hpath
            · exfalso
              rcases havail with ⟨rest, hpath, _⟩
              rw [HardwareAdequacy.coordinatePath_left] at hpath
              cases hpath
            · rfl
          subst selected'
          have ht' :
              t' = {s with
                control := .term (if selected then right else left)} :=
            ChannelExternalStep.eq_of_extern hstep' hc
          subst t'
          let childR :=
            externalChildRealization D₀ j₀ realize selected hstep' next R
          refine ⟨next, childR, ?_, ?_⟩
          · rcases havail with ⟨rest, hpath, havailChild⟩
            cases selected
            · rw [HardwareAdequacy.coordinatePath_left] at hpath
              injection hpath with hrest
              subst rest
              exact havailChild
            · rw [HardwareAdequacy.coordinatePath_right] at hpath
              injection hpath with hrest
              subst rest
              exact havailChild
          · apply (token_of_restrictedInstrument D₀ j₀ realize
              next childR [] childActive ξ finalK
              (fun o => hk _) token).mp
            rw [← embed_restricted_external_coordinate D₀ j₀ realize
              selected hstep' next R childActive]
            exact
              (token_of_restrictedInstrument D₀ j₀ realize
                (ChannelTree.external selected hstep' next) R []
                (HardwareAdequacy.branchCoordinate selected childActive)
                ξ finalK (fun o => hk _) token).mpr htoken
      | probability _ _ _ _ =>
          cases hc
      | probabilityZero _ =>
          cases hc
      | probabilityOne _ =>
          cases hc
      | measurement _ _ =>
          cases hc

/-- Token adequacy aggregates backwards through a strictly interior
probability node.  A parent token is assembled from potentially different
branch-local source tokens via `WeightedDerives` and `RoundedBelow`; no
independent-membership interpretation of the parent token is assumed. -/
theorem probability_step_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {p : ℝ}
    {left right : Term (QubitPrimitive C)}
    (hp₀ : 0 < p) (hp₁ : p < 1)
    (hc : s.control = .term (.prob p left right))
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {leftResult rightResult result : TTResult 2}
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result)
    (hleft : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with
        control := .term left
        quantum := applyOperation
          (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum}
      active observedStack finalK leftResult)
    (hright : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with
        control := .term right
        quantum := applyOperation
          (sourceProbabilityOperation (1 - p)
            (sub_nonneg.mpr hp₁.le) (by linarith)) s.quantum}
      active observedStack finalK rightResult)
    (hresult : result =
      TTWeightedAggregation.weightedResultScott p hp₀.le hp₁.le
        (leftResult, rightResult)) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s active observedStack finalK result := by
  refine
    { related := hsource
      token_iff := ?_ }
  intro ξ hk token
  rw [hresult, TTWeightedAggregation.weightedResultScott_interior
    p hp₀ hp₁]
  constructor
  · intro htoken
    obtain ⟨leftToken, hleftToken, rightToken, hrightToken,
        target, hderives, hrounded⟩ :=
      (TTWeightedAggregation.mem_core p hp₀.le hp₁.le
        leftResult rightResult token).mp htoken
    obtain ⟨leftTree, leftR, hleftAvail, hleftHolds⟩ :=
      (hleft.token_iff ξ hk leftToken).mp hleftToken
    obtain ⟨rightTree, rightR, hrightAvail, hrightHolds⟩ :=
      (hright.token_iff ξ hk rightToken).mp hrightToken
    rcases s with ⟨control, env, stack, quantum⟩
    simp only at hc
    subst control
    let sourceTree := ChannelTree.probability hp₀ hp₁ leftTree rightTree
    let sourceR := wrapProbabilityRealization D₀ j₀ realize
      hp₀ hp₁ leftTree rightTree leftR rightR
    refine ⟨sourceTree, sourceR, ⟨hleftAvail, hrightAvail⟩, ?_⟩
    have hleftRestricted :
        leftToken ∈ restrictedResult D₀ j₀ realize leftTree leftR
          [] active finalK := by
      rw [restrictedResult_eq_embed D₀ j₀ realize leftTree leftR
        [] active finalK hleftAvail]
      exact
        (token_of_restrictedInstrument D₀ j₀ realize leftTree leftR
          [] active ξ finalK (fun o => hk _) leftToken).mpr hleftHolds
    have hrightRestricted :
        rightToken ∈ restrictedResult D₀ j₀ realize rightTree rightR
          [] active finalK := by
      rw [restrictedResult_eq_embed D₀ j₀ realize rightTree rightR
        [] active finalK hrightAvail]
      exact
        (token_of_restrictedInstrument D₀ j₀ realize rightTree rightR
          [] active ξ finalK (fun o => hk _) rightToken).mpr hrightHolds
    have hparentRestricted :
        token ∈ restrictedResult D₀ j₀ realize sourceTree sourceR
          [] active finalK := by
      rw [restrictedResult_probability_presented D₀ j₀ realize
        hp₀ hp₁ leftTree rightTree sourceR [] active ξ finalK hk,
        TTWeightedAggregation.weightedResultScott_interior p hp₀ hp₁]
      exact
        (TTWeightedAggregation.mem_core p hp₀.le hp₁.le _ _ token).2
          ⟨leftToken, hleftRestricted, rightToken, hrightRestricted,
            target, hderives, hrounded⟩
    apply (token_of_restrictedInstrument D₀ j₀ realize
      sourceTree sourceR [] active ξ finalK (fun o => hk _) token).mp
    rw [← restrictedResult_eq_embed D₀ j₀ realize sourceTree sourceR
      [] active finalK ⟨hleftAvail, hrightAvail⟩]
    exact hparentRestricted
  · rintro ⟨tree, parentR, havail, htoken⟩
    cases tree with
    | terminal hterminal =>
        have := hterminal.control_eq.symm.trans hc
        cases this
    | internal hstep _ =>
        exact False.elim (ChannelInternalStep.not_prob hstep hc)
    | external _ hstep _ =>
        exact False.elim (ChannelExternalStep.not_prob hstep hc)
    | @probability source p' L rightTerm' hp₀' hp₁' leftTree rightTree =>
        injection hc with hterm
        injection hterm with hp hL hR
        subst p'
        subst L
        subst rightTerm'
        rcases havail with ⟨hleftAvail, hrightAvail⟩
        let leftR := probabilityLeftRealization D₀ j₀ realize
          hp₀' hp₁' leftTree rightTree parentR
        let rightR := probabilityRightRealization D₀ j₀ realize
          hp₀' hp₁' leftTree rightTree parentR
        have hparentRestricted :
            token ∈ restrictedResult D₀ j₀ realize
              (ChannelTree.probability hp₀' hp₁' leftTree rightTree) parentR
              [] active finalK := by
          rw [restrictedResult_eq_embed D₀ j₀ realize
            (ChannelTree.probability hp₀' hp₁' leftTree rightTree) parentR
            [] active finalK ⟨hleftAvail, hrightAvail⟩]
          exact
            (token_of_restrictedInstrument D₀ j₀ realize
              (ChannelTree.probability hp₀' hp₁' leftTree rightTree) parentR
              [] active ξ finalK (fun o => hk _) token).mpr htoken
        rw [restrictedResult_probability_presented D₀ j₀ realize
          hp₀' hp₁' leftTree rightTree parentR [] active ξ finalK hk,
          TTWeightedAggregation.weightedResultScott_interior p hp₀' hp₁']
          at hparentRestricted
        obtain ⟨leftToken, hleftRestricted, rightToken, hrightRestricted,
            target, hderives, hrounded⟩ :=
          (TTWeightedAggregation.mem_core p hp₀'.le hp₁'.le _ _ token).mp
            hparentRestricted
        have hleftHolds :
            TTObservationToken.Holds resultCode leftToken
              ((restrictedInstrument D₀ j₀ realize leftTree leftR
                [] active).bind ξ) := by
          apply (token_of_restrictedInstrument D₀ j₀ realize
            leftTree leftR [] active ξ finalK
            (fun o => hk _) leftToken).mp
          rw [← restrictedResult_eq_embed D₀ j₀ realize leftTree leftR
            [] active finalK hleftAvail]
          exact hleftRestricted
        have hrightHolds :
            TTObservationToken.Holds resultCode rightToken
              ((restrictedInstrument D₀ j₀ realize rightTree rightR
                [] active).bind ξ) := by
          apply (token_of_restrictedInstrument D₀ j₀ realize
            rightTree rightR [] active ξ finalK
            (fun o => hk _) rightToken).mp
          rw [← restrictedResult_eq_embed D₀ j₀ realize rightTree rightR
            [] active finalK hrightAvail]
          exact hrightRestricted
        have hleftMember : leftToken ∈ leftResult :=
          (hleft.token_iff ξ hk leftToken).mpr
            ⟨leftTree, leftR, hleftAvail, hleftHolds⟩
        have hrightMember : rightToken ∈ rightResult :=
          (hright.token_iff ξ hk rightToken).mpr
            ⟨rightTree, rightR, hrightAvail, hrightHolds⟩
        exact
          (TTWeightedAggregation.mem_core p hp₀.le hp₁.le
            leftResult rightResult token).2
            ⟨leftToken, hleftMember, rightToken, hrightMember,
              target, hderives, hrounded⟩
    | probabilityZero _ =>
        injection hc with hterm
        injection hterm with hp
        exact (ne_of_gt hp₀ hp.symm).elim
    | probabilityOne _ =>
        injection hc with hterm
        injection hterm with hp
        exact (ne_of_lt hp₁ hp.symm).elim
    | measurement _ _ =>
        cases hc

/-- Token adequacy transfers backwards through the endpoint `p = 0`.
The generic source and explicit control equality let tree inversion retain
the source environment, stack, and quantum state definitionally. -/
theorem probabilityZero_step_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.prob 0 left right))
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result)
    (hchild : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with
        control := .term right
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1)) s.quantum}
      active observedStack finalK result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s active observedStack finalK result := by
  refine
    { related := hsource
      token_iff := ?_ }
  intro ξ hk token
  rw [hchild.token_iff ξ hk token]
  constructor
  · rintro ⟨tree, R, havail, htoken⟩
    rcases s with ⟨control, env, stack, quantum⟩
    simp only at hc
    subst control
    let sourceTree := ChannelTree.probabilityZero
      (s := ⟨.term (.prob 0 left right), env, stack, quantum⟩)
      (left := left) tree
    let sourceR :=
      wrapProbabilityZeroRealization D₀ j₀ realize
        (leftTerm := left) (rightTerm := right) tree R
    refine ⟨sourceTree, sourceR, havail, ?_⟩
    apply (token_of_restrictedInstrument D₀ j₀ realize
      sourceTree sourceR [] active ξ finalK (fun o => hk _) token).mp
    rw [embed_restricted_probabilityZero D₀ j₀ realize tree sourceR]
    exact
      (token_of_restrictedInstrument D₀ j₀ realize
        tree
        (probabilityZeroRealization D₀ j₀ realize tree sourceR)
        [] active ξ finalK (fun o => hk _) token).mpr htoken
  · rintro ⟨tree, R, havail, htoken⟩
    cases tree with
    | terminal hterminal =>
        have := hterminal.control_eq.symm.trans hc
        cases this
    | internal hstep _ =>
        exact False.elim (ChannelInternalStep.not_prob hstep hc)
    | external _ hstep _ =>
        exact False.elim (ChannelExternalStep.not_prob hstep hc)
    | probability hp₀ hp₁ leftTree rightTree =>
        injection hc with hterm
        injection hterm with hp0
        exact (lt_irrefl (0 : ℝ) (hp0 ▸ hp₀)).elim
    | @probabilityZero _ L R next =>
        injection hc with hterm
        injection hterm with _ hL hR
        subst hL
        subst hR
        let childR :=
          probabilityZeroRealization D₀ j₀ realize next R
        refine ⟨next, childR, havail, ?_⟩
        apply (token_of_restrictedInstrument D₀ j₀ realize
          next childR [] active ξ finalK (fun o => hk _) token).mp
        rw [← embed_restricted_probabilityZero D₀ j₀ realize next R]
        exact
          (token_of_restrictedInstrument D₀ j₀ realize
            (ChannelTree.probabilityZero next) R [] active
            ξ finalK (fun o => hk _) token).mpr htoken
    | probabilityOne _ =>
        injection hc with hterm
        injection hterm with hp01
        exact (one_ne_zero hp01).elim
    | measurement _ _ =>
        cases hc

/-- Token adequacy transfers backwards through the endpoint `p = 1`. -/
theorem probabilityOne_step_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.prob 1 left right))
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result)
    (hchild : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with
        control := .term left
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1)) s.quantum}
      active observedStack finalK result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s active observedStack finalK result := by
  refine
    { related := hsource
      token_iff := ?_ }
  intro ξ hk token
  rw [hchild.token_iff ξ hk token]
  constructor
  · rintro ⟨tree, R, havail, htoken⟩
    rcases s with ⟨control, env, stack, quantum⟩
    simp only at hc
    subst control
    let sourceTree := ChannelTree.probabilityOne
      (s := ⟨.term (.prob 1 left right), env, stack, quantum⟩)
      (right := right) tree
    let sourceR :=
      wrapProbabilityOneRealization D₀ j₀ realize
        (leftTerm := left) (rightTerm := right) tree R
    refine ⟨sourceTree, sourceR, havail, ?_⟩
    apply (token_of_restrictedInstrument D₀ j₀ realize
      sourceTree sourceR [] active ξ finalK (fun o => hk _) token).mp
    rw [embed_restricted_probabilityOne D₀ j₀ realize tree sourceR]
    exact
      (token_of_restrictedInstrument D₀ j₀ realize
        tree
        (probabilityOneRealization D₀ j₀ realize tree sourceR)
        [] active ξ finalK (fun o => hk _) token).mpr htoken
  · rintro ⟨tree, R, havail, htoken⟩
    cases tree with
    | terminal hterminal =>
        have := hterminal.control_eq.symm.trans hc
        cases this
    | internal hstep _ =>
        exact False.elim (ChannelInternalStep.not_prob hstep hc)
    | external _ hstep _ =>
        exact False.elim (ChannelExternalStep.not_prob hstep hc)
    | probability hp₀ hp₁ leftTree rightTree =>
        injection hc with hterm
        injection hterm with hp1
        exact (lt_irrefl (1 : ℝ) (hp1 ▸ hp₁)).elim
    | probabilityZero _ =>
        injection hc with hterm
        injection hterm with hp10
        exact (zero_ne_one hp10).elim
    | @probabilityOne _ L R next =>
        injection hc with hterm
        injection hterm with _ hL hR
        subst hL
        subst hR
        let childR :=
          probabilityOneRealization D₀ j₀ realize next R
        refine ⟨next, childR, havail, ?_⟩
        apply (token_of_restrictedInstrument D₀ j₀ realize
          next childR [] active ξ finalK (fun o => hk _) token).mp
        rw [← embed_restricted_probabilityOne D₀ j₀ realize next R]
        exact
          (token_of_restrictedInstrument D₀ j₀ realize
            (ChannelTree.probabilityOne next) R [] active
            ξ finalK (fun o => hk _) token).mpr htoken
    | measurement _ _ =>
        cases hc

/-! ### Measurement aggregation -/

/-- Two branch-local observations force a target observation after a physical
computational-basis measurement.  The two source tokens are independent;
membership of one parent token in both branches is not assumed. -/
def MeasurementDerives
    (zero one target : TTObservationToken 2) : Prop :=
  ∀ μ ν : FiniteInstrumentComp 2 PUnit.{1},
    TTObservationToken.Holds resultCode zero μ →
    TTObservationToken.Holds resultCode one ν →
    TTObservationToken.Holds resultCode target
      (Qubit.measureZComp.bind (fun b => if b then ν else μ))

/-- Rounded token aggregation for computational-basis measurement.  This is
the measurement-specialized form of `TTTokenTheory.aggregateResult`; it takes
two unrelated branch theories rather than incorrectly requiring one token to
belong to both. -/
noncomputable def measurementResult
    (zeroResult oneResult : TTResult 2) : TTResult 2 :=
  sSup {T | ∃ zero ∈ zeroResult, ∃ one ∈ oneResult, ∃ target,
    MeasurementDerives zero one target ∧
    T = RoundedTheory.principal
      (TTObservationToken.roundedBasis resultCode) target}

theorem mem_measurementResult
    (zeroResult oneResult : TTResult 2) (token : TTObservationToken 2) :
    token ∈ measurementResult zeroResult oneResult ↔
      ∃ zero ∈ zeroResult, ∃ one ∈ oneResult, ∃ target,
        MeasurementDerives zero one target ∧
        TTObservationToken.RoundedBelow resultCode token target := by
  rw [measurementResult, RoundedTheory.mem_sSup]
  constructor
  · rintro ⟨T, ⟨zero, hzero, one, hone, target, hderives, rfl⟩, ht⟩
    exact ⟨zero, hzero, one, hone, target, hderives,
      (RoundedTheory.mem_principal
        (B := TTObservationToken.roundedBasis resultCode)).mp ht⟩
  · rintro ⟨zero, hzero, one, hone, target, hderives, ht⟩
    exact
      ⟨RoundedTheory.principal
          (TTObservationToken.roundedBasis resultCode) target,
        ⟨zero, hzero, one, hone, target, hderives, rfl⟩,
        (RoundedTheory.mem_principal
          (B := TTObservationToken.roundedBasis resultCode)).2 ht⟩

/-- The token-generated measurement aggregate agrees with physical
`measureZ` bind whenever both branches are finite result instruments. -/
theorem measurementResult_satisfied
    (μ ν : FiniteInstrumentComp 2 PUnit.{1}) :
    measurementResult
        (μ.satisfiedTTTheory resultCode)
        (ν.satisfiedTTTheory resultCode) =
      (Qubit.measureZComp.bind
        (fun b => if b then ν else μ)).satisfiedTTTheory resultCode := by
  apply RoundedTheory.ext
  ext t
  constructor
  · intro ht
    obtain ⟨zero, hzero, one, hone, target, hderives, httarget⟩ :=
      (mem_measurementResult _ _ t).mp ht
    have htarget :
        TTObservationToken.Holds resultCode target
          (Qubit.measureZComp.bind (fun b => if b then ν else μ)) :=
      hderives μ ν
        ((FiniteInstrumentComp.mem_satisfiedTTTheory resultCode μ zero).mp
          hzero)
        ((FiniteInstrumentComp.mem_satisfiedTTTheory resultCode ν one).mp
          hone)
    exact TTObservationToken.roundedBelow_entails resultCode httarget
      (Qubit.measureZComp.bind (fun b => if b then ν else μ)) htarget
  · intro ht
    obtain ⟨target, httarget, htarget⟩ :=
      TTObservationToken.exists_stronglyBelow_holds resultCode
        (Qubit.measureZComp.bind (fun b => if b then ν else μ)) ht
    obtain ⟨sources, hsources, hall⟩ :=
      TTResultApproximation.exists_bind_source_tokens
        Qubit.measureZComp target (fun b => if b then ν else μ) htarget
    let zero := sources false
    let one := sources true
    apply (mem_measurementResult _ _ t).2
    refine ⟨zero, ?_, one, ?_, target, ?_, ?_⟩
    · apply (FiniteInstrumentComp.mem_satisfiedTTTheory resultCode μ zero).2
      simpa [zero, resultCode, Qubit.measureZComp] using hsources false
    · apply (FiniteInstrumentComp.mem_satisfiedTTTheory resultCode ν one).2
      simpa [one, resultCode, Qubit.measureZComp] using hsources true
    · intro μ' ν' hzero hone
      apply hall (fun b => if b then ν' else μ')
      intro b
      cases b
      · exact hzero
      · exact hone
    · exact ⟨t, TTObservationToken.entails_refl resultCode t, httarget⟩

/-- At a finitely-presented continuation, an available measurement node is
exactly token aggregation of its restricted children. -/
theorem restrictedResult_measurement_eq_measurementResult {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {zeroValue oneValue : C}
    (zero : ChannelTree C
      { s with
        control := .value (.payload zeroValue)
        quantum := applyOperation (measurementOperation false) s.quantum })
    (one : ChannelTree C
      { s with
        control := .value (.payload oneValue)
        quantum := applyOperation (measurementOperation true) s.quantum })
    (R : ChannelTreeRealization D₀ j₀ realize
      (ChannelTree.measurement zero one))
    (selectors : List Bool) (i : ℕ)
    (hzero : ResultAvailable zero selectors i)
    (hone : ResultAvailable one selectors i)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode) :
    restrictedResult D₀ j₀ realize
        (ChannelTree.measurement zero one) R selectors i k =
      measurementResult
        (restrictedResult D₀ j₀ realize zero
          (measurementZeroRealization D₀ j₀ realize zero one R) selectors i k)
        (restrictedResult D₀ j₀ realize one
          (measurementOneRealization D₀ j₀ realize zero one R)
          selectors i k) := by
  classical
  let zeroR := measurementZeroRealization D₀ j₀ realize zero one R
  let oneR := measurementOneRealization D₀ j₀ realize zero one R
  let μZ := restrictedInstrument D₀ j₀ realize zero zeroR selectors i
  let μO := restrictedInstrument D₀ j₀ realize one oneR selectors i
  let μM := Qubit.measureZComp.bind
    (fun b => if b then μO else μZ)
  have havail_iff :
      ResultAvailable (ChannelTree.measurement zero one) selectors i ↔
        ResultAvailable zero selectors i ∧ ResultAvailable one selectors i :=
    Iff.rfl
  rw [restrictedResult_eq_embed D₀ j₀ realize
      (ChannelTree.measurement zero one) R selectors i k
      (havail_iff.mpr ⟨hzero, hone⟩),
    restrictedResult_eq_embed D₀ j₀ realize zero zeroR selectors i k hzero,
    restrictedResult_eq_embed D₀ j₀ realize one oneR selectors i k hone,
    embed_restricted_measurement D₀ j₀ realize zero one R selectors i]
  change embed μM k = measurementResult (embed μZ k) (embed μO k)
  calc
    embed μM k =
        (μM.bind ξ).satisfiedTTTheory resultCode :=
      TTPhysicalEmbedding.embed_satisfied μM ξ k (fun _ => hk _)
    _ = (Qubit.measureZComp.bind
          (fun b => (if b then μO else μZ).bind ξ)).satisfiedTTTheory
          resultCode := by
      have hassoc :=
        satisfiedTTTheory_bind_assoc Qubit.measureZComp
          (fun b => if b then μO else μZ) ξ
      exact hassoc
    _ = (Qubit.measureZComp.bind
          (fun b => if b then μO.bind ξ else μZ.bind ξ)).satisfiedTTTheory
          resultCode := by
      have hif : ∀ b : Bool,
          (if b then μO else μZ).bind ξ =
            if b then μO.bind ξ else μZ.bind ξ := by
        intro b
        split_ifs <;> rfl
      congr 1
      exact congrArg Qubit.measureZComp.bind (funext hif)
    _ = measurementResult
          ((μZ.bind ξ).satisfiedTTTheory resultCode)
          ((μO.bind ξ).satisfiedTTTheory resultCode) :=
      (measurementResult_satisfied (μZ.bind ξ) (μO.bind ξ)).symm
    _ = measurementResult (embed μZ k) (embed μO k) := by
      rw [TTPhysicalEmbedding.embed_satisfied μZ ξ k (fun _ => hk _),
        TTPhysicalEmbedding.embed_satisfied μO ξ k (fun _ => hk _)]

/-- Token adequacy aggregates backwards through computational-basis
measurement.  The branch results correspond to the two unnormalized child
states in `ChannelTree.measurement`; aggregation uses branch-local source
tokens and `MeasurementDerives`, not common-token intersection. -/
theorem measurement_step_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {zeroValue oneValue : C}
    (hc : s.control =
      .term (.prim (.measureZ zeroValue oneValue)))
    (hscoped : ChannelConfig.WellScoped s)
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {zeroResult oneResult result : TTResult 2}
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result)
    (hzero : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with
        control := .value (.payload zeroValue)
        quantum := applyOperation (measurementOperation false) s.quantum}
      active observedStack finalK zeroResult)
    (hone : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with
        control := .value (.payload oneValue)
        quantum := applyOperation (measurementOperation true) s.quantum}
      active observedStack finalK oneResult)
    (hresult : result = measurementResult zeroResult oneResult) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s active observedStack finalK result := by
  refine
    { related := hsource
      token_iff := ?_ }
  intro ξ hk token
  rw [hresult, mem_measurementResult]
  constructor
  · rintro ⟨zeroToken, hzeroToken, oneToken, honeToken,
        target, hderives, hrounded⟩
    obtain ⟨zeroTree, zeroR, hzeroAvail, hzeroHolds⟩ :=
      (hzero.token_iff ξ hk zeroToken).mp hzeroToken
    obtain ⟨oneTree, oneR, honeAvail, honeHolds⟩ :=
      (hone.token_iff ξ hk oneToken).mp honeToken
    rcases s with ⟨control, env, stack, quantum⟩
    simp only at hc
    subst control
    let sourceTree := ChannelTree.measurement zeroTree oneTree
    let sourceR := wrapMeasurementRealization D₀ j₀ realize
      zeroTree oneTree zeroR oneR
    let projectedZeroR :=
      measurementZeroRealization D₀ j₀ realize zeroTree oneTree sourceR
    let projectedOneR :=
      measurementOneRealization D₀ j₀ realize zeroTree oneTree sourceR
    have hzeroScoped : ChannelConfig.WellScoped
        (⟨.value (.payload zeroValue), env, stack,
          applyOperation (measurementOperation false) quantum⟩ :
          ChannelConfig C) := by
      rcases hscoped with ⟨⟨henv, _⟩, hstack⟩
      exact ⟨⟨henv, .payload zeroValue⟩, hstack⟩
    have honeScoped : ChannelConfig.WellScoped
        (⟨.value (.payload oneValue), env, stack,
          applyOperation (measurementOperation true) quantum⟩ :
          ChannelConfig C) := by
      rcases hscoped with ⟨⟨henv, _⟩, hstack⟩
      exact ⟨⟨henv, .payload oneValue⟩, hstack⟩
    have hzeroRestricted :
        zeroToken ∈ restrictedResult D₀ j₀ realize zeroTree zeroR
          [] active finalK := by
      rw [restrictedResult_eq_embed D₀ j₀ realize zeroTree zeroR
        [] active finalK hzeroAvail]
      exact
        (token_of_restrictedInstrument D₀ j₀ realize zeroTree zeroR
          [] active ξ finalK (fun o => hk _) zeroToken).mpr hzeroHolds
    have honeRestricted :
        oneToken ∈ restrictedResult D₀ j₀ realize oneTree oneR
          [] active finalK := by
      rw [restrictedResult_eq_embed D₀ j₀ realize oneTree oneR
        [] active finalK honeAvail]
      exact
        (token_of_restrictedInstrument D₀ j₀ realize oneTree oneR
          [] active ξ finalK (fun o => hk _) oneToken).mpr honeHolds
    refine ⟨sourceTree, sourceR, ⟨hzeroAvail, honeAvail⟩, ?_⟩
    have hparentRestricted :
        token ∈ restrictedResult D₀ j₀ realize sourceTree sourceR
          [] active finalK := by
      rw [restrictedResult_measurement_eq_measurementResult D₀ j₀ realize
        zeroTree oneTree sourceR [] active hzeroAvail honeAvail ξ finalK hk,
        ← restrictedResult_eq_of_wellScoped D₀ j₀ realize zeroTree hzeroScoped
          zeroR projectedZeroR [] active ξ finalK hk,
        ← restrictedResult_eq_of_wellScoped D₀ j₀ realize oneTree honeScoped
          oneR projectedOneR [] active ξ finalK hk]
      exact (mem_measurementResult _ _ token).2
        ⟨zeroToken, hzeroRestricted, oneToken, honeRestricted,
          target, hderives, hrounded⟩
    apply (token_of_restrictedInstrument D₀ j₀ realize
      sourceTree sourceR [] active ξ finalK (fun o => hk _) token).mp
    rw [← restrictedResult_eq_embed D₀ j₀ realize sourceTree sourceR
      [] active finalK ⟨hzeroAvail, honeAvail⟩]
    exact hparentRestricted
  · rintro ⟨tree, parentR, havail, htoken⟩
    cases tree with
    | terminal hterminal =>
        have := hterminal.control_eq.symm.trans hc
        cases this
    | internal hstep _ =>
        exact False.elim (ChannelInternalStep.not_measureZ hstep hc)
    | external _ hstep _ =>
        exact False.elim (by cases hstep <;> cases hc)
    | probability _ _ _ _ =>
        cases hc
    | probabilityZero _ =>
        cases hc
    | probabilityOne _ =>
        cases hc
    | @measurement source zeroValue' oneValue' zeroTree oneTree =>
        injection hc with hterm
        injection hterm with hmeasure
        injection hmeasure with hzeroValue honeValue
        subst zeroValue'
        subst oneValue'
        rcases havail with ⟨hzeroAvail, honeAvail⟩
        let zeroR :=
          measurementZeroRealization D₀ j₀ realize zeroTree oneTree parentR
        let oneR :=
          measurementOneRealization D₀ j₀ realize zeroTree oneTree parentR
        have hparentRestricted :
            token ∈ restrictedResult D₀ j₀ realize
              (ChannelTree.measurement zeroTree oneTree) parentR
              [] active finalK := by
          rw [restrictedResult_eq_embed D₀ j₀ realize
            (ChannelTree.measurement zeroTree oneTree) parentR
            [] active finalK ⟨hzeroAvail, honeAvail⟩]
          exact
            (token_of_restrictedInstrument D₀ j₀ realize
              (ChannelTree.measurement zeroTree oneTree) parentR
              [] active ξ finalK (fun o => hk _) token).mpr htoken
        rw [restrictedResult_measurement_eq_measurementResult D₀ j₀ realize
          zeroTree oneTree parentR [] active hzeroAvail honeAvail ξ finalK hk]
          at hparentRestricted
        obtain ⟨zeroToken, hzeroRestricted, oneToken, honeRestricted,
            target, hderives, hrounded⟩ :=
          (mem_measurementResult _ _ token).mp hparentRestricted
        have hzeroHolds :
            TTObservationToken.Holds resultCode zeroToken
              ((restrictedInstrument D₀ j₀ realize zeroTree zeroR
                [] active).bind ξ) := by
          apply (token_of_restrictedInstrument D₀ j₀ realize
            zeroTree zeroR [] active ξ finalK
            (fun o => hk _) zeroToken).mp
          rw [← restrictedResult_eq_embed D₀ j₀ realize zeroTree zeroR
            [] active finalK hzeroAvail]
          exact hzeroRestricted
        have honeHolds :
            TTObservationToken.Holds resultCode oneToken
              ((restrictedInstrument D₀ j₀ realize oneTree oneR
                [] active).bind ξ) := by
          apply (token_of_restrictedInstrument D₀ j₀ realize
            oneTree oneR [] active ξ finalK
            (fun o => hk _) oneToken).mp
          rw [← restrictedResult_eq_embed D₀ j₀ realize oneTree oneR
            [] active finalK honeAvail]
          exact honeRestricted
        have hzeroMember : zeroToken ∈ zeroResult :=
          (hzero.token_iff ξ hk zeroToken).mpr
            ⟨zeroTree, zeroR, hzeroAvail, hzeroHolds⟩
        have honeMember : oneToken ∈ oneResult :=
          (hone.token_iff ξ hk oneToken).mpr
            ⟨oneTree, oneR, honeAvail, honeHolds⟩
        exact ⟨zeroToken, hzeroMember, oneToken, honeMember,
          target, hderives, hrounded⟩

end HardwareChannelSemantics
end QLambda
