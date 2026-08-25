/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.HardwareOperational

/-!
# Finite observations of the hardware machine

This module records finite executions of the hardware CEK machine.  A trace
keeps probabilistic mass, the path of environment selectors, and a symbolic
Kraus history.  The Kraus history is ghost data: executable configurations
continue to contain only a normalized density matrix.

No claim relating these observations to the TT denotation is made here.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QLambda
namespace HardwareObservation

open HardwareOperational
open TTPhysicalPrimitives

/-- Symbolic quantum metadata for one machine transition.  Administrative and
external steps denote the identity operation.  A source probability is
represented physically by a square-root-scaled identity Kraus operator. -/
inductive QuantumAction where
  | identity
  | pauliX
  | measurement (outcome : Bool)
  | sourceProbability (weight : ℝ)

namespace QuantumAction

/-- Kraus family denoted by a symbolic transition action. -/
noncomputable def kraus : QuantumAction → KrausFamily 2 2
  | .identity => KrausFamily.identity 2
  | .pauliX => Qubit.pauliXOp.kraus
  | .measurement b => HardwareOperational.measureBranch b
  | .sourceProbability p =>
      KrausFamily.scale (Real.sqrt p) (KrausFamily.identity 2)

/-- Compose a chronological symbolic history into one Kraus family. -/
noncomputable def composeHistory : List QuantumAction → KrausFamily 2 2
  | [] => KrausFamily.identity 2
  | a :: as => KrausFamily.comp (composeHistory as) a.kraus

@[simp]
theorem composeHistory_nil :
    composeHistory [] = KrausFamily.identity 2 :=
  rfl

@[simp]
theorem composeHistory_cons (a : QuantumAction) (as : List QuantumAction) :
    composeHistory (a :: as) =
      KrausFamily.comp (composeHistory as) a.kraus :=
  rfl

/-- A source probability acts as scalar multiplication by its real weight. -/
theorem apply_sourceProbability (p : ℝ) (hp : 0 ≤ p)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    KrausFamily.applyMat (kraus (.sourceProbability p)) ρ =
      (p : ℂ) • ρ := by
  rw [kraus, KrausFamily.applyMat_scale, KrausFamily.applyMat_identity]
  have hsqrt :
      (Real.sqrt p : ℂ) * star (Real.sqrt p : ℂ) = p := by
    simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    norm_cast
    simpa [pow_two] using Real.sq_sqrt hp
  rw [hsqrt]

/-- A measurement action is the corresponding unnormalized Born branch. -/
theorem apply_measurement {C : Type} (s : Config C) (b : Bool)
    (hp : 0 < measureProbability s b) :
    KrausFamily.applyMat (kraus (.measurement b)) s.quantum.mat =
      (measureProbability s b : ℂ) • (measuredState s b hp).mat := by
  rw [kraus]
  unfold measureProbability at hp
  unfold measuredState measureProbability
  rw [HardwareOperational.NormalizedDensity.normalizeBranch_mat]
  ext i j
  simp [Matrix.smul_apply, ne_of_gt hp]

end QuantumAction

/-- Symbolic action determined by the source of an internal step.  This
definition inspects executable syntax rather than eliminating a proof into
data. -/
def internalAction {C : Type} (s : Config C) : QuantumAction :=
  match s.control with
  | .term (.prim (.pauliX _)) => .pauliX
  | _ => .identity

/-- One transition with all observational labels made explicit.  Internal,
weighted, and environment-selected transitions remain distinct constructors. -/
inductive MachineStep {C : Type} :
    Config C → ℝ → List Bool → QuantumAction → Config C → Prop where
  | internal {s t : Config C} (h : HardwareOperational.InternalStep s t) :
      MachineStep s 1 [] (internalAction s) t
  | probabilityLeft {s : Config C} {p : ℝ}
      {left right : Term (QubitPrimitive C)}
      (hp : 0 < p) (hp1 : p ≤ 1) :
      MachineStep
        {s with control := .term (.prob p left right)}
        p [] (.sourceProbability p)
        {s with control := .term left}
  | probabilityRight {s : Config C} {p : ℝ}
      {left right : Term (QubitPrimitive C)}
      (hp : 0 ≤ p) (hp1 : p < 1) :
      MachineStep
        {s with control := .term (.prob p left right)}
        (1 - p) [] (.sourceProbability (1 - p))
        {s with control := .term right}
  | measurement {s : Config C} {zeroValue oneValue : C} {b : Bool}
      (h : 0 < measureProbability s b) :
      MachineStep
        {s with control := .term (.prim (.measureZ zeroValue oneValue))}
        (measureProbability s b) [] (.measurement b)
        {s with
          control := .value (.payload (if b then oneValue else zeroValue))
          quantum := measuredState s b h}
  | external {s t : Config C} {selector : Bool}
      (h : HardwareOperational.ExternalStep s selector t) :
      MachineStep s 1 [selector] .identity t

/-- Erasure of symbolic Kraus metadata back to exactly one of the three
operational step relations. -/
inductive UnderlyingStep {C : Type} :
    Config C → ℝ → List Bool → Config C → Prop where
  | internal {s t : Config C} (h : HardwareOperational.InternalStep s t) :
      UnderlyingStep s 1 [] t
  | weighted {s t : Config C} {p : ℝ}
      (h : HardwareOperational.WeightedStep s p t) :
      UnderlyingStep s p [] t
  | external {s t : Config C} {selector : Bool}
      (h : HardwareOperational.ExternalStep s selector t) :
      UnderlyingStep s 1 [selector] t

namespace MachineStep

/-- Every labelled step is backed by one of the original operational
relations; the symbolic layer adds metadata but no transitions. -/
theorem underlying {C : Type} {s t : Config C} {p : ℝ}
    {selectors : List Bool} {action : QuantumAction}
    (h : MachineStep s p selectors action t) :
    UnderlyingStep s p selectors t := by
  cases h with
  | internal h => exact .internal h
  | probabilityLeft hp hp1 =>
      exact .weighted (.probabilityLeft hp hp1)
  | probabilityRight hp hp1 =>
      exact .weighted (.probabilityRight hp hp1)
  | measurement hp =>
      exact .weighted (.measurement hp)
  | external h => exact .external h

/-- Every original weighted transition admits its corresponding symbolic
label, so the labelled trace layer is complete for weighted steps. -/
theorem exists_of_weighted {C : Type} {s t : Config C} {p : ℝ}
    (h : HardwareOperational.WeightedStep s p t) :
    ∃ action, MachineStep s p [] action t := by
  cases h with
  | probabilityLeft hp hp1 =>
      exact ⟨.sourceProbability _, .probabilityLeft hp hp1⟩
  | probabilityRight hp hp1 =>
      exact ⟨.sourceProbability _, .probabilityRight hp hp1⟩
  | measurement hp =>
      exact ⟨.measurement _, .measurement hp⟩

theorem weight_pos {C : Type} {s t : Config C} {p : ℝ}
    {selectors : List Bool} {action : QuantumAction}
    (h : MachineStep s p selectors action t) : 0 < p := by
  cases h with
  | internal => norm_num
  | external => norm_num
  | probabilityLeft hp _ => exact hp
  | probabilityRight _ hp1 => linarith
  | measurement hp => exact hp

/-- A symbolic one-step Kraus action produces the weighted, unnormalized
target state from the normalized source state. -/
theorem apply_kraus_eq_weight_smul {C : Type} {s t : Config C} {p : ℝ}
    {selectors : List Bool} {action : QuantumAction}
    (h : MachineStep s p selectors action t) :
    KrausFamily.applyMat action.kraus s.quantum.mat =
      (p : ℂ) • t.quantum.mat := by
  cases h with
  | internal h =>
      cases h <;>
        simp [internalAction, QuantumAction.kraus,
          HardwareOperational.NormalizedDensity.pauliX]
  | external h =>
      cases h <;> simp [QuantumAction.kraus]
  | probabilityLeft hp hp1 =>
      exact QuantumAction.apply_sourceProbability _ (le_of_lt hp) _
  | probabilityRight hq hq1 =>
      exact QuantumAction.apply_sourceProbability _
        (sub_nonneg.mpr (le_of_lt hq1)) _
  | measurement hp =>
      exact QuantumAction.apply_measurement _ _ hp

end MachineStep

/-- A finite execution trace.  Histories and selector paths are chronological;
weights multiply along the trace. -/
inductive ExecutionTrace {C : Type} :
    Config C → Config C → ℝ → List Bool → List QuantumAction → ℕ → Prop where
  | refl (s : Config C) :
      ExecutionTrace s s 1 [] [] 0
  | cons {s u t : Config C} {p q : ℝ}
      {headSelectors tailSelectors : List Bool}
      {action : QuantumAction} {actions : List QuantumAction} {depth : ℕ}
      (head : MachineStep s p headSelectors action u)
      (tail : ExecutionTrace u t q tailSelectors actions depth) :
      ExecutionTrace s t (p * q) (headSelectors ++ tailSelectors)
        (action :: actions) (depth + 1)

namespace ExecutionTrace

theorem weight_pos {C : Type} {s t : Config C} {p : ℝ}
    {selectors : List Bool} {actions : List QuantumAction} {depth : ℕ}
    (h : ExecutionTrace s t p selectors actions depth) : 0 < p := by
  induction h with
  | refl => norm_num
  | cons head tail ih =>
      exact mul_pos head.weight_pos ih

/-- The composed symbolic Kraus history agrees with the concrete normalized
states after restoring the accumulated branch weight. -/
theorem apply_composeHistory_eq_weight_smul
    {C : Type} {s t : Config C} {p : ℝ}
    {selectors : List Bool} {actions : List QuantumAction} {depth : ℕ}
    (h : ExecutionTrace s t p selectors actions depth) :
    KrausFamily.applyMat (QuantumAction.composeHistory actions) s.quantum.mat =
      (p : ℂ) • t.quantum.mat := by
  induction h with
  | refl =>
      simp
  | @cons s u t p q hs ts action actions depth head tail ih =>
      rw [QuantumAction.composeHistory_cons, KrausFamily.applyMat_comp,
        head.apply_kraus_eq_weight_smul, KrausFamily.applyMat_smul, ih]
      rw [smul_smul]
      norm_cast

end ExecutionTrace

/-- A terminal CEK configuration has returned a value with no pending frames. -/
structure Terminal {C : Type} (s : Config C) where
  value : RuntimeValue C
  control_eq : s.control = .value value
  stack_eq : s.stack = []

/-- A completed finite observation from `start`.  It retains its terminal
configuration, positive accumulated mass, selector path, symbolic Kraus
history, and exact transition depth. -/
structure FiniteObservation {C : Type} (start : Config C) where
  terminal : Config C
  weight : ℝ
  selectors : List Bool
  actions : List QuantumAction
  depth : ℕ
  trace : ExecutionTrace start terminal weight selectors actions depth
  isTerminal : Terminal terminal

namespace FiniteObservation

theorem weight_pos {C : Type} {start : Config C}
    (o : FiniteObservation start) : 0 < o.weight :=
  o.trace.weight_pos

/-- Intrinsic Kraus family represented by this finite history. -/
noncomputable def kraus {C : Type} {start : Config C}
    (o : FiniteObservation start) : KrausFamily 2 2 :=
  QuantumAction.composeHistory o.actions

theorem apply_kraus_eq_weight_smul {C : Type} {start : Config C}
    (o : FiniteObservation start) :
    KrausFamily.applyMat o.kraus start.quantum.mat =
      (o.weight : ℂ) • o.terminal.quantum.mat :=
  o.trace.apply_composeHistory_eq_weight_smul

end FiniteObservation

/-- A depth/fuel-bounded witness packages a completed observation together
with the fact that it fits within the available fuel. -/
structure FuelWitness {C : Type} (start : Config C) (fuel : ℕ) where
  observation : FiniteObservation start
  depth_le : observation.depth ≤ fuel

namespace FuelWitness

/-- Increasing fuel preserves every existing observation witness. -/
def weaken {C : Type} {start : Config C} {fuel fuel' : ℕ}
    (h : fuel ≤ fuel') (w : FuelWitness start fuel) :
    FuelWitness start fuel' :=
  ⟨w.observation, w.depth_le.trans h⟩

end FuelWitness

/-- The set of completed observations visible at a given fuel. -/
def observationsAtFuel {C : Type} (start : Config C) (fuel : ℕ) :
    Set (FiniteObservation start) :=
  {o | o.depth ≤ fuel}

theorem observationsAtFuel_mono {C : Type} {start : Config C}
    {fuel fuel' : ℕ} (h : fuel ≤ fuel') :
    observationsAtFuel start fuel ⊆ observationsAtFuel start fuel' :=
  fun _ ho => ho.trans h

/-- A directed, exhaustive fuel presentation of operational observations.
This is the order-theoretic interface intended for later comparison with
finite TT tokens; it contains no denotational adequacy assertion. -/
structure DirectedOperationalObservation {C : Type} (start : Config C) where
  stage : ℕ → Set (FiniteObservation start)
  monotone : ∀ ⦃fuel fuel'⦄, fuel ≤ fuel' → stage fuel ⊆ stage fuel'
  exhaustive : ∀ o, ∃ fuel, o ∈ stage fuel

/-- Canonical directed observation object generated by trace depth. -/
def operationalObservation {C : Type} (start : Config C) :
    DirectedOperationalObservation start where
  stage := observationsAtFuel start
  monotone := fun _ _ h => observationsAtFuel_mono (start := start) h
  exhaustive := fun o => ⟨o.depth, show o.depth ≤ o.depth from le_rfl⟩

theorem operationalObservation_stage_directed {C : Type}
    (start : Config C) :
    Directed (· ⊆ ·) (operationalObservation start).stage := by
  change Directed (· ⊆ ·) (observationsAtFuel start)
  intro i j
  refine ⟨max i j, ?_, ?_⟩
  · exact observationsAtFuel_mono (start := start) (le_max_left i j)
  · exact observationsAtFuel_mono (start := start) (le_max_right i j)

/-! ## Branch-complete finite evaluation trees -/

/-- An empty physical computation, used only for a branch whose source or
Born weight is zero. -/
def emptyInstrument (n : ℕ) (D : Type) : FiniteInstrumentComp n D where
  Outcome := Empty
  branch := Empty.elim
  value := Empty.elim
  trace_nonincreasing := by
    intro ρ hρ
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    simpa [Matrix.trace] using
      (Finset.sum_nonneg fun x (_ : x ∈ Finset.univ) =>
        (Complex.nonneg_iff.mp hρ.diag_nonneg).1)

/-- The two source-probability branches as one physical instrument. -/
noncomputable def probabilityInstrument (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    FiniteInstrumentComp 2 Bool where
  Outcome := Bool
  branch := fun b =>
    QuantumAction.kraus (.sourceProbability (if b then 1 - p else p))
  value := id
  trace_nonincreasing := by
    intro ρ hρ
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [QuantumAction.apply_sourceProbability (1 - p)
        (sub_nonneg.mpr hp₁) ρ]
    rw [QuantumAction.apply_sourceProbability p hp₀ ρ]
    rw [Matrix.trace_smul, Matrix.trace_smul]
    have htr : 0 ≤ (Matrix.trace ρ).re := by
      change 0 ≤ ∑ x : Fin 2, (ρ x x).re
      exact Finset.sum_nonneg fun x _ =>
        (Complex.nonneg_iff.mp hρ.diag_nonneg).1
    change
      (((1 - p : ℝ) : ℂ) * Matrix.trace ρ).re +
          ((p : ℂ) * Matrix.trace ρ).re ≤
        (Matrix.trace ρ).re
    rw [Complex.mul_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    linarith

/-- One completed leaf, including the external selectors consumed on the
path to it. -/
structure TreeLeaf (C : Type) where
  terminal : Config C
  isTerminal : Terminal terminal
  selectors : List Bool

/-- A finite, scheduler-resolved evaluation tree. Internal choice chooses one
child. External choice chooses and records one selector. Probability and
measurement retain every nonzero physical branch together. Administrative
and deterministic quantum steps are unary. -/
inductive EvaluationTree (C : Type) :
    KrausFamily 2 2 → Config C → Type where
  | terminal {κ : KrausFamily 2 2} {s : Config C}
      (h : Terminal s) : EvaluationTree C κ s
  | internal {κ : KrausFamily 2 2} {s t : Config C}
      (h : HardwareOperational.InternalStep s t)
      (next : EvaluationTree C
        (KrausFamily.comp (internalAction s).kraus κ) t) :
      EvaluationTree C κ s
  | external {κ : KrausFamily 2 2} {s t : Config C} (selector : Bool)
      (h : HardwareOperational.ExternalStep s selector t)
      (next : EvaluationTree C κ t) : EvaluationTree C κ s
  | probabilityInterior {κ : KrausFamily 2 2}
      {s : Config C} {p : ℝ}
      {left right : Term (QubitPrimitive C)}
      (hp₀ : 0 < p) (hp₁ : p < 1)
      (leftTree : EvaluationTree C
        (KrausFamily.comp
          (QuantumAction.kraus (.sourceProbability p)) κ)
        {s with control := .term left})
      (rightTree : EvaluationTree C
        (KrausFamily.comp
          (QuantumAction.kraus (.sourceProbability (1 - p))) κ)
        {s with control := .term right}) :
      EvaluationTree C κ
        {s with control := .term (.prob p left right)}
  | probabilityZero {κ : KrausFamily 2 2} {s : Config C}
      {left right : Term (QubitPrimitive C)}
      (rightTree : EvaluationTree C
        (KrausFamily.comp
          (QuantumAction.kraus (.sourceProbability 1)) κ)
        {s with control := .term right}) :
      EvaluationTree C κ
        {s with control := .term (.prob 0 left right)}
  | probabilityOne {κ : KrausFamily 2 2} {s : Config C}
      {left right : Term (QubitPrimitive C)}
      (leftTree : EvaluationTree C
        (KrausFamily.comp
          (QuantumAction.kraus (.sourceProbability 1)) κ)
        {s with control := .term left}) :
      EvaluationTree C κ
        {s with control := .term (.prob 1 left right)}
  | measurementBoth {κ : KrausFamily 2 2}
      {s : Config C} {zeroValue oneValue : C}
      (h₀ : 0 < measureProbability s false)
      (h₁ : 0 < measureProbability s true)
      (zeroTree : EvaluationTree C
        (KrausFamily.comp (measureBranch false) κ)
        {s with control := .value (.payload zeroValue),
                 quantum := measuredState s false h₀})
      (oneTree : EvaluationTree C
        (KrausFamily.comp (measureBranch true) κ)
        {s with control := .value (.payload oneValue),
                 quantum := measuredState s true h₁}) :
      EvaluationTree C κ
        {s with control := .term (.prim (.measureZ zeroValue oneValue))}
  | measurementFalseOnly {κ : KrausFamily 2 2}
      {s : Config C} {zeroValue oneValue : C}
      (h₀ : 0 < measureProbability s false)
      (hzero : measureProbability s true = 0)
      (hglobal : KrausFamily.SemEq
        (KrausFamily.comp (measureBranch true) κ) KrausFamily.zero)
      (zeroTree : EvaluationTree C
        (KrausFamily.comp (measureBranch false) κ)
        {s with control := .value (.payload zeroValue),
                 quantum := measuredState s false h₀}) :
      EvaluationTree C κ
        {s with control := .term (.prim (.measureZ zeroValue oneValue))}
  | measurementTrueOnly {κ : KrausFamily 2 2}
      {s : Config C} {zeroValue oneValue : C}
      (hzero : measureProbability s false = 0)
      (h₁ : 0 < measureProbability s true)
      (hglobal : KrausFamily.SemEq
        (KrausFamily.comp (measureBranch false) κ) KrausFamily.zero)
      (oneTree : EvaluationTree C
        (KrausFamily.comp (measureBranch true) κ)
        {s with control := .value (.payload oneValue),
                 quantum := measuredState s true h₁}) :
      EvaluationTree C κ
        {s with control := .term (.prim (.measureZ zeroValue oneValue))}

namespace EvaluationTree

/-- A dead branch certificate is channel-level: the composite branch acts as
zero on every input matrix, not merely on the concrete state in the current
configuration. -/
theorem deadComposite_apply_eq_zero
    {κ : KrausFamily 2 2} (branch : KrausFamily 2 2)
    (hdead : KrausFamily.SemEq
      (KrausFamily.comp branch κ) KrausFamily.zero)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    KrausFamily.applyMat (KrausFamily.comp branch κ) ρ = 0 := by
  rw [hdead]
  exact KrausFamily.applyMat_zero ρ

/-- Source-probability endpoint branches are globally dead after every
symbolic prefix, so the endpoint tree constructors need no concrete target
state for the omitted branch. -/
theorem sourceProbability_zero_comp_semEq_zero
    (κ : KrausFamily 2 2) :
    KrausFamily.SemEq
      (KrausFamily.comp
        (QuantumAction.kraus (.sourceProbability 0)) κ)
      KrausFamily.zero := by
  intro ρ
  rw [KrausFamily.applyMat_comp,
    QuantumAction.apply_sourceProbability 0 (le_refl 0)]
  simp only [Complex.ofReal_zero, zero_smul, KrausFamily.applyMat_zero]

/-- Exact tree height, used as operational fuel. -/
noncomputable def depth {C : Type} {κ : KrausFamily 2 2}
    {s : Config C} : EvaluationTree C κ s → ℕ
  | .terminal _ => 0
  | .internal _ t => t.depth + 1
  | .external _ _ t => t.depth + 1
  | .probabilityInterior _ _ l r => max l.depth r.depth + 1
  | .probabilityZero r => r.depth + 1
  | .probabilityOne l => l.depth + 1
  | .measurementBoth _ _ l r => max l.depth r.depth + 1
  | .measurementFalseOnly _ _ _ t => t.depth + 1
  | .measurementTrueOnly _ _ _ t => t.depth + 1

/-- Prepend one consumed external selector to every terminal leaf. -/
def prependSelector {C : Type} (b : Bool) (leaf : TreeLeaf C) :
    TreeLeaf C :=
  { leaf with selectors := b :: leaf.selectors }

/-- Physical operation of an internal step, determined by executable source
syntax. -/
noncomputable def internalOperation {C : Type} {s t : Config C}
    (h : InternalStep s t) : QuantumOperation 2 2 where
  kraus := (internalAction s).kraus
  trace_nonincreasing := by
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

/-- Fold a completed tree into one finite physical instrument. Its outcomes
are exactly terminal leaves; probability and measurement are combined by
finite instrument bind before any TT embedding. -/
noncomputable def instrument {C : Type} {κ : KrausFamily 2 2}
    {s : Config C} :
    EvaluationTree C κ s → FiniteInstrumentComp 2 (TreeLeaf C)
  | .terminal h => FiniteInstrumentComp.unit
      ⟨s, h, []⟩
  | .internal h next =>
      (FiniteInstrumentComp.ofOperation (internalOperation h) Unit.unit).bind
        (fun _ => next.instrument)
  | .external selector _ next =>
      next.instrument.map (prependSelector selector)
  | .probabilityInterior hp₀ hp₁ leftTree rightTree =>
      (probabilityInstrument _ hp₀.le hp₁.le).bind
        (fun b => if b then rightTree.instrument else leftTree.instrument)
  | .probabilityZero rightTree =>
      (probabilityInstrument 0 (le_refl 0) zero_le_one).bind
        (fun b => if b then rightTree.instrument
          else emptyInstrument 2 (TreeLeaf C))
  | .probabilityOne leftTree =>
      (probabilityInstrument 1 zero_le_one (le_refl 1)).bind
        (fun b => if b then emptyInstrument 2 (TreeLeaf C)
          else leftTree.instrument)
  | .measurementBoth _ _ zeroTree oneTree =>
      Qubit.measureZComp.bind
        (fun b => if b then oneTree.instrument else zeroTree.instrument)
  | .measurementFalseOnly _ _ _ zeroTree =>
      Qubit.measureZComp.bind
        (fun b => if b then emptyInstrument 2 (TreeLeaf C)
          else zeroTree.instrument)
  | .measurementTrueOnly _ _ _ oneTree =>
      Qubit.measureZComp.bind
        (fun b => if b then oneTree.instrument
          else emptyInstrument 2 (TreeLeaf C))

/-- Structural trace nonincrease of the folded tree instrument. -/
theorem instrument_trace_nonincreasing {C : Type}
    {κ : KrausFamily 2 2} {s : Config C}
    (tree : EvaluationTree C κ s) :
    ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ, ρ.PosSemidef →
      (∑ o : tree.instrument.Outcome,
        (Matrix.trace
          (KrausFamily.applyMat (tree.instrument.branch o) ρ)).re) ≤
        (Matrix.trace ρ).re :=
  tree.instrument.trace_nonincreasing

/-- Completed trees available at a fuel bound. -/
def treesAtFuel {C : Type} (start : Config C) (fuel : ℕ) :
    Set (EvaluationTree C (KrausFamily.identity 2) start) :=
  {tree | tree.depth ≤ fuel}

theorem treesAtFuel_mono {C : Type} {start : Config C}
    {fuel fuel' : ℕ} (h : fuel ≤ fuel') :
    treesAtFuel start fuel ⊆ treesAtFuel start fuel' :=
  fun _ ht => ht.trans h

end EvaluationTree

end HardwareObservation
end QLambda
