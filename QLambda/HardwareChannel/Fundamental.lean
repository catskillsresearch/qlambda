/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.HardwareChannel.Closed

/-!
# Path-indexed fundamental theorem

Layer of the hardware channel-tree semantics.  All layers share the
`QLambda.HardwareChannelSemantics` namespace; import
`QLambda.HardwareChannelSemantics` for the full module.

The path transfer lemmas of `Spines` are assembled here into one
fundamental theorem.  The recursion is *not* a well-founded recursion on
`configMeasure`: the CEK machine of this language is Turing complete, so
no configuration measure decreases at `evaluateArgument` (the frame's
saved environment need not be the current one), at `beta` (freshness of
the popped closure is not an invariant), or at `recBeta` at all.  The
induction is therefore on an explicit branch-complete evaluation
derivation `PathChannelEvaluation`, whose constructors are exactly the
situations covered by a path transfer lemma.

Internal choice now has a two-child constructor, matching probability:
both successors are retained, so the unique-successor identity transfer
is not used.  A value under a payload function frame remains excluded
(stuck).  This file proves that the concrete closed example
`app (prim (ret c)) (prim (ret c'))` has no channel tree, and proves
failure of presented completeness whenever an explicit finitely presented
observation of its denotation is nonbottom.  It does not construct a
particular domain and `realize` satisfying that semantic hypothesis, so it
does not claim an unconditional model-specific counterexample.
-/

set_option maxHeartbeats 800000

namespace QLambda
namespace HardwareChannelSemantics

open Matrix
open scoped ComplexOrder MatrixOrder

open HardwareOperational
open HardwareObservation
open HardwareAdequacy
open HardwareLogicalRelation
open TTPhysicalPrimitives
open TTPhysicalEmbedding
open TTContinuation
open Scott1972.ContinuousLattice

/-! ## Small token-theory facts -/

/-- The empty observation theory has no tokens. -/
theorem not_mem_bot_result {n : ℕ} {token : TTObservationToken n}
    (h : token ∈ (⊥ : TTResult n)) : False := by
  have hbot : (⊥ : TTResult n) = sSup (∅ : Set (TTResult n)) :=
    sSup_empty.symm
  rw [hbot, RoundedTheory.mem_sSup] at h
  obtain ⟨_, ⟨⟩, _⟩ := h

/-! ## Missing path-indexed transfers -/

/-- Returning a classical payload is an identity step onto the related
payload value. -/
theorem path_channel_config_return {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {value : C}
    (hc : s.control = .term (.prim (.ret value)))
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result) :
    PathChannelConfigRel D₀ j₀ realize
      {s with control := .value (.payload value)}
      active observedStack finalK result := by
  rcases hrel with ⟨herase, current, currentK, hcontrol, hstack, hresult⟩
  rw [hc] at hcontrol
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨herase,
        semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) (realize value),
        currentK,
        ControlRel.value (.payload value) (realize value) s.env
          (payload_related D₀ j₀ realize value),
        hstack, ?_⟩
      rw [hresult, interp_prim_apply, hardwarePrimitive_ret]
      rfl

/-- Token adequacy transfers backwards across the `ret` primitive. -/
theorem return_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {value : C}
    (hc : s.control = .term (.prim (.ret value)))
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result)
    (hchild : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with control := .value (.payload value)}
      active observedStack finalK result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s active observedStack finalK result := by
  let t : ChannelConfig C := {s with control := .value (.payload value)}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.prim (.ret value))} t :=
      ChannelInternalStep.returnPrimitive (s := s) (value := value)
    have hs : s = {s with control := .term (.prim (.ret value))} :=
      ChannelConfig.ext hc rfl rfl rfl
    exact hs.symm ▸ happ
  exact identity_step_pathChannelTreeTokenAdequacy D₀ j₀ realize
    hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_config_of_return h' hc)
    hsource hchild

/-- A related terminal configuration is token-adequate; its canonical
finite witness is built from the value related by the relation itself. -/
theorem terminal_related_pathChannelTreeTokenAdequacy {C : Type}
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
      s active observedStack finalK result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s active observedStack finalK result := by
  have hvalue : ∃ d, ValueRel D₀ j₀ realize hterminal.value d := by
    rcases hrel with ⟨_, current, currentK, hcontrol, _, _⟩
    rw [hterminal.control_eq] at hcontrol
    cases hcontrol with
    | value _ d _ hd => exact ⟨d, hd⟩
  obtain ⟨d, hd⟩ := hvalue
  exact terminal_pathChannelTreeTokenAdequacy D₀ j₀ realize hterminal
    hscoped hrel (terminalValueRealization D₀ j₀ hterminal hd)

/-- At the unresolved root coordinate an external choice observes nothing,
and no finite tree is available there either. -/
theorem extern_root_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.extern left right))
    {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s 0 observedStack finalK result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s 0 observedStack finalK result := by
  have hbot : result = ⊥ := by
    rcases hsource with ⟨herase, current, currentK, hcontrol, hstack, hresult⟩
    rw [hc] at hcontrol
    cases hcontrol with
    | term _ _ semanticEnv henv =>
        rw [hresult]
        rw [show
            interp (hardwarePrimitive D₀ j₀ realize) (.extern left right)
                semanticEnv 0 =
              ⊥ from by
              rw [interp_extern_apply]
              exact TTContinuation.externalChoice_root_bot _ _]
        exact ScottMap.bot_apply currentK
  refine
    { related := hsource
      token_iff := ?_ }
  intro ξ hk token
  constructor
  · intro htoken
    rw [hbot] at htoken
    exact absurd htoken (fun h => not_mem_bot_result h)
  · rintro ⟨tree, R, havail, htoken⟩
    exfalso
    cases tree with
    | terminal hterminal =>
        have := hterminal.control_eq.symm.trans hc
        cases this
    | internal hstep _ =>
        exact ChannelInternalStep.not_extern hstep hc
    | @external _ t' selector hstep next =>
        have havail' :
            resultAvailableAt (ChannelTree.external selector hstep next) [] := by
          simpa [ResultAvailable, HardwareAdequacy.coordinatePath] using havail
        obtain ⟨rest, hpath, _⟩ := havail'
        exact absurd hpath (by simp)
    | probability _ _ _ _ =>
        cases hc
    | probabilityZero _ =>
        cases hc
    | probabilityOne _ =>
        cases hc
    | measurement _ _ =>
        cases hc

/-- Interior probabilistic choice at the path level: the two branch
observations exist and the parent observation is their weighted
aggregate. -/
theorem path_channel_config_probability {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {p : ℝ}
    {left right : Term (QubitPrimitive C)}
    (hp₀ : 0 < p) (hp₁ : p < 1)
    (hc : s.control = .term (.prob p left right))
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result) :
    ∃ leftResult rightResult,
      PathChannelConfigRel D₀ j₀ realize
        {s with
          control := .term left
          quantum := applyOperation
            (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum}
        active observedStack finalK leftResult ∧
      PathChannelConfigRel D₀ j₀ realize
        {s with
          control := .term right
          quantum := applyOperation
            (sourceProbabilityOperation (1 - p)
              (sub_nonneg.mpr hp₁.le) (by linarith)) s.quantum}
        active observedStack finalK rightResult ∧
      result =
        TTWeightedAggregation.weightedResultScott p hp₀.le hp₁.le
          (leftResult, rightResult) := by
  rcases hrel with ⟨herase, current, currentK, hcontrol, hstack, hresult⟩
  rw [hc] at hcontrol
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine
        ⟨interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv active
            currentK,
          interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv active
            currentK,
          ⟨herase,
            interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv,
            currentK, ControlRel.term left s.env semanticEnv henv,
            hstack, rfl⟩,
          ⟨herase,
            interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv,
            currentK, ControlRel.term right s.env semanticEnv henv,
            hstack, rfl⟩, ?_⟩
      have hsel :=
        selectPath_prob D₀ j₀ realize p left right semanticEnv [] active
          currentK
      simp only [HardwareAdequacy.selectPath_nil] at hsel
      rw [hresult, hsel, TTContinuation.probChoice_apply,
        dif_pos (⟨hp₀.le, hp₁.le⟩ : 0 ≤ p ∧ p ≤ 1)]

/-- Computational-basis measurement at the path level: the two payload
branches are related and the parent observation is their measurement
aggregate.  Distinctness of the realized payloads is what lets the two
branch instruments be interpolated independently. -/
theorem path_channel_config_measureZ {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {zeroValue oneValue : C}
    (hc : s.control = .term (.prim (.measureZ zeroValue oneValue)))
    (hne : realize zeroValue ≠ realize oneValue)
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result) :
    ∃ zeroResult oneResult,
      PathChannelConfigRel D₀ j₀ realize
        {s with
          control := .value (.payload zeroValue)
          quantum := applyOperation (measurementOperation false) s.quantum}
        active observedStack finalK zeroResult ∧
      PathChannelConfigRel D₀ j₀ realize
        {s with
          control := .value (.payload oneValue)
          quantum := applyOperation (measurementOperation true) s.quantum}
        active observedStack finalK oneResult ∧
      result = measurementResult zeroResult oneResult := by
  rcases hrel with ⟨herase, current, currentK, hcontrol, hstack, hresult⟩
  rw [hc] at hcontrol
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨currentK (realize zeroValue), currentK (realize oneValue),
        ⟨herase,
          semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) (realize zeroValue),
          currentK,
          ControlRel.value (.payload zeroValue) (realize zeroValue) s.env
            (payload_related D₀ j₀ realize zeroValue),
          hstack, rfl⟩,
        ⟨herase,
          semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) (realize oneValue),
          currentK,
          ControlRel.value (.payload oneValue) (realize oneValue) s.env
            (payload_related D₀ j₀ realize oneValue),
          hstack, rfl⟩, ?_⟩
      rw [hresult, interp_prim_apply, hardwarePrimitive_measureZ,
        taggedEmbed_apply]
      have h :=
        embed_measureZ_map_eq_measurementResult_of_ne
          (fun b : Bool => if b then realize oneValue else realize zeroValue)
          (by simpa using hne) currentK
      simpa using h

/-- Internal choice at the path level: both children are related at the
same coordinate and the parent observation is their join. -/
theorem path_channel_config_intern {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.intern left right))
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result) :
    ∃ leftResult rightResult,
      PathChannelConfigRel D₀ j₀ realize
        {s with control := .term left}
        active observedStack finalK leftResult ∧
      PathChannelConfigRel D₀ j₀ realize
        {s with control := .term right}
        active observedStack finalK rightResult ∧
      result = leftResult ⊔ rightResult := by
  rcases hrel with ⟨herase, current, currentK, hcontrol, hstack, hresult⟩
  rw [hc] at hcontrol
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine
        ⟨interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv active
            currentK,
          interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv active
            currentK,
          ⟨herase,
            interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv,
            currentK, ControlRel.term left s.env semanticEnv henv,
            hstack, rfl⟩,
          ⟨herase,
            interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv,
            currentK, ControlRel.term right s.env semanticEnv henv,
            hstack, rfl⟩, ?_⟩
      rw [hresult, interp_intern_apply,
        TTContinuation.computation_intern_apply,
        TTContinuation.internalChoice_apply]

/-! ## Steps recovered from a control equation -/

theorem channelInternalStep_of_application {C : Type} {s : ChannelConfig C}
    {fn arg : Term (QubitPrimitive C)}
    (hc : s.control = .term (.app fn arg)) :
    ChannelInternalStep s
      {s with
        control := .term fn
        stack := .argument arg s.env :: s.stack} := by
  have hstep :=
    ChannelInternalStep.application (s := s) (fn := fn) (arg := arg)
  have hs : s = {s with control := .term (.app fn arg)} :=
    ChannelConfig.ext hc rfl rfl rfl
  exact hs.symm ▸ hstep

theorem channelInternalStep_of_lambda {C : Type} {s : ChannelConfig C}
    {x : Name} {body : Term (QubitPrimitive C)}
    (hc : s.control = .term (.lam x body)) :
    ChannelInternalStep s
      {s with control := .value (.closure x body s.env)} := by
  have hstep := ChannelInternalStep.lambda (s := s) (x := x) (body := body)
  have hs : s = {s with control := .term (.lam x body)} :=
    ChannelConfig.ext hc rfl rfl rfl
  exact hs.symm ▸ hstep

theorem channelInternalStep_of_recursive {C : Type} {s : ChannelConfig C}
    {self x : Name} {body : Term (QubitPrimitive C)}
    (hc : s.control = .term (.recLam self x body)) :
    ChannelInternalStep s
      {s with control := .value (.recClosure self x body s.env)} := by
  have hstep :=
    ChannelInternalStep.recursive (s := s) (self := self) (arg := x)
      (body := body)
  have hs : s = {s with control := .term (.recLam self x body)} :=
    ChannelConfig.ext hc rfl rfl rfl
  exact hs.symm ▸ hstep

theorem channelInternalStep_of_variable {C : Type} {s : ChannelConfig C}
    {x : Name} {v : RuntimeValue C}
    (hc : s.control = .term (.var x))
    (hlookup : RuntimeEnv.lookup x s.env = some v) :
    ChannelInternalStep s {s with control := .value v} := by
  have hstep :=
    ChannelInternalStep.variable (s := s) (x := x) (v := v) hlookup
  have hs : s = {s with control := .term (.var x)} :=
    ChannelConfig.ext hc rfl rfl rfl
  exact hs.symm ▸ hstep

theorem channelInternalStep_of_return {C : Type} {s : ChannelConfig C}
    {value : C} (hc : s.control = .term (.prim (.ret value))) :
    ChannelInternalStep s {s with control := .value (.payload value)} := by
  have hstep :=
    ChannelInternalStep.returnPrimitive (s := s) (value := value)
  have hs : s = {s with control := .term (.prim (.ret value))} :=
    ChannelConfig.ext hc rfl rfl rfl
  exact hs.symm ▸ hstep

theorem channelInternalStep_of_evaluateArgument {C : Type}
    {s : ChannelConfig C} {fn : RuntimeValue C}
    {arg : Term (QubitPrimitive C)} {callEnv : RuntimeEnv C}
    {rest : EvalStack C}
    (hc : s.control = .value fn)
    (hs : s.stack = .argument arg callEnv :: rest) :
    ChannelInternalStep s
      {s with
        control := .term arg
        env := callEnv
        stack := .function fn :: rest} := by
  have hstep :=
    ChannelInternalStep.evaluateArgument (s := s) (fn := fn) (arg := arg)
      (callEnv := callEnv) (rest := rest)
  have hsrc :
      s = {s with
        control := .value fn
        stack := .argument arg callEnv :: rest} :=
    ChannelConfig.ext hc rfl hs rfl
  exact hsrc.symm ▸ hstep

theorem channelInternalStep_of_beta {C : Type} {s : ChannelConfig C}
    {x : Name} {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    {arg : RuntimeValue C} {rest : EvalStack C}
    (hc : s.control = .value arg)
    (hs : s.stack = .function (.closure x body closureEnv) :: rest) :
    ChannelInternalStep s
      {s with
        control := .term body
        env := RuntimeEnv.bind x arg closureEnv
        stack := rest} := by
  have hstep :=
    ChannelInternalStep.beta (s := s) (x := x) (body := body)
      (closureEnv := closureEnv) (arg := arg) (rest := rest)
  have hsrc :
      s = {s with
        control := .value arg
        stack := .function (.closure x body closureEnv) :: rest} :=
    ChannelConfig.ext hc rfl hs rfl
  exact hsrc.symm ▸ hstep

theorem channelInternalStep_of_recBeta {C : Type} {s : ChannelConfig C}
    {self x : Name} {body : Term (QubitPrimitive C)}
    {closureEnv : RuntimeEnv C} {arg : RuntimeValue C} {rest : EvalStack C}
    (hc : s.control = .value arg)
    (hs : s.stack =
      .function (.recClosure self x body closureEnv) :: rest) :
    ChannelInternalStep s
      {s with
        control := .term body
        env :=
          RuntimeEnv.bind x arg
            (RuntimeEnv.bind self
              (.recClosure self x body closureEnv) closureEnv)
        stack := rest} := by
  have hstep :=
    ChannelInternalStep.recBeta (s := s) (self := self) (x := x)
      (body := body) (closureEnv := closureEnv) (arg := arg) (rest := rest)
  have hsrc :
      s = {s with
        control := .value arg
        stack := .function (.recClosure self x body closureEnv) :: rest} :=
    ChannelConfig.ext hc rfl hs rfl
  exact hsrc.symm ▸ hstep

/-! ## Well-scopedness of branch children -/

theorem wellScoped_congr_quantum {C : Type} {s : ChannelConfig C}
    (quantum : SubNormalizedDensity 2)
    (h : ChannelConfig.WellScoped s) :
    ChannelConfig.WellScoped {s with quantum := quantum} :=
  h

theorem wellScoped_prob_left {C : Type} {s : ChannelConfig C} {p : ℝ}
    {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.prob p left right))
    (hscoped : ChannelConfig.WellScoped s)
    (quantum : SubNormalizedDensity 2) :
    ChannelConfig.WellScoped
      {s with control := .term left, quantum := quantum} :=
  wellScoped_congr_quantum quantum
    (wellScoped_term_child hc hscoped (fun x hx => by simp [free, hx]))

theorem wellScoped_prob_right {C : Type} {s : ChannelConfig C} {p : ℝ}
    {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.prob p left right))
    (hscoped : ChannelConfig.WellScoped s)
    (quantum : SubNormalizedDensity 2) :
    ChannelConfig.WellScoped
      {s with control := .term right, quantum := quantum} :=
  wellScoped_congr_quantum quantum
    (wellScoped_term_child hc hscoped (fun x hx => by simp [free, hx]))

theorem wellScoped_payload_child {C : Type} {s : ChannelConfig C}
    {code : Term (QubitPrimitive C)}
    (hc : s.control = .term code)
    (hscoped : ChannelConfig.WellScoped s)
    (value : C) (quantum : SubNormalizedDensity 2) :
    ChannelConfig.WellScoped
      {s with control := .value (.payload value), quantum := quantum} := by
  rcases hscoped with ⟨hctl, hstack⟩
  rw [hc] at hctl
  exact ⟨⟨hctl.left, .payload value⟩, hstack⟩

theorem wellScoped_intern_left {C : Type} {s : ChannelConfig C}
    {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.intern left right))
    (hscoped : ChannelConfig.WellScoped s) :
    ChannelConfig.WellScoped {s with control := .term left} :=
  wellScoped_term_child hc hscoped (fun x hx => by simp [free, hx])

theorem wellScoped_intern_right {C : Type} {s : ChannelConfig C}
    {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.intern left right))
    (hscoped : ChannelConfig.WellScoped s) :
    ChannelConfig.WellScoped {s with control := .term right} :=
  wellScoped_term_child hc hscoped (fun x hx => by simp [free, hx])

theorem channelExternalStep_of_extern {C : Type} {s : ChannelConfig C}
    {left right : Term (QubitPrimitive C)} {selected : Bool}
    (hc : s.control = .term (.extern left right)) :
    ChannelExternalStep s selected
      {s with control := .term (if selected then right else left)} := by
  have hsrc : s = {s with control := .term (.extern left right)} :=
    ChannelConfig.ext hc rfl rfl rfl
  cases selected with
  | false =>
      exact hsrc.symm ▸
        ChannelExternalStep.selectFalse (s := s) (left := left)
          (right := right)
  | true =>
      exact hsrc.symm ▸
        ChannelExternalStep.selectTrue (s := s) (left := left)
          (right := right)

theorem branchCoordinate_succ (i : ℕ) :
    HardwareAdequacy.branchCoordinate (i % 2 ≠ 0) (i / 2) = i + 1 := by
  unfold HardwareAdequacy.branchCoordinate
  split_ifs with hsel
  · have : i % 2 = 1 := by
      have hmod := Nat.mod_two_eq_zero_or_one i
      rcases hmod with h0 | h1
      · simp [h0] at hsel
      · exact h1
    omega
  · have : i % 2 = 0 := by
      have hmod := Nat.mod_two_eq_zero_or_one i
      rcases hmod with h0 | h1
      · exact h0
      · simp [h1] at hsel
    omega

/-- Token adequacy of internal choice is the join of the two identity-wrapped
children.  Both successors are retained, matching the denotation. -/
theorem intern_step_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.intern left right))
    {active : ℕ} {observedStack : ObservedStack C}
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {leftResult rightResult result : TTResult 2}
    (hsource : PathChannelConfigRel D₀ j₀ realize
      s active observedStack finalK result)
    (hleft : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with control := .term left}
      active observedStack finalK leftResult)
    (hright : PathChannelTreeTokenAdequacy D₀ j₀ realize
      {s with control := .term right}
      active observedStack finalK rightResult)
    (hresult : result = leftResult ⊔ rightResult) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize
      s active observedStack finalK result := by
  refine
    { related := hsource
      token_iff := ?_ }
  intro ξ hk token
  rw [hresult, Adequacy.mem_sup_iff]
  have hop :
      channelInternalOperation
        {s with control := .term (.intern left right)} =
        QuantumOperation.identity 2 :=
    rfl
  constructor
  · intro htoken
    rcases s with ⟨control, env, stack, quantum⟩
    simp only at hc
    subst control
    rcases htoken with hL | hR
    · obtain ⟨tree, R, havail, hholds⟩ :=
        (hleft.token_iff ξ hk token).mp hL
      let hstep :=
        ChannelInternalStep.internalLeft
          (s := ⟨.term (.intern left right), env, stack, quantum⟩)
          (left := left) (right := right)
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
          [] active ξ finalK (fun o => hk _) token).mpr hholds
    · obtain ⟨tree, R, havail, hholds⟩ :=
        (hright.token_iff ξ hk token).mp hR
      let hstep :=
        ChannelInternalStep.internalRight
          (s := ⟨.term (.intern left right), env, stack, quantum⟩)
          (left := left) (right := right)
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
          [] active ξ finalK (fun o => hk _) token).mpr hholds
  · rintro ⟨tree, parentR, havail, hholds⟩
    cases tree with
    | terminal hterminal =>
        have := hterminal.control_eq.symm.trans hc
        cases this
    | @internal _ t hstep next =>
        have hop' : channelInternalOperation s = QuantumOperation.identity 2 := by
          simp [channelInternalOperation, hc]
        rcases ChannelInternalStep.eq_of_intern hstep hc with ht | ht
        · subst t
          let childR :=
            internalChildRealization D₀ j₀ realize hstep next parentR
          refine Or.inl ((hleft.token_iff ξ hk token).mpr ⟨next, childR, havail, ?_⟩)
          apply (token_of_restrictedInstrument D₀ j₀ realize
            next childR [] active ξ finalK (fun o => hk _) token).mp
          rw [← embed_restricted_internal_of_identity D₀ j₀ realize
            hstep hop' next parentR [] active]
          exact
            (token_of_restrictedInstrument D₀ j₀ realize
              (ChannelTree.internal hstep next) parentR [] active ξ finalK
              (fun o => hk _) token).mpr hholds
        · subst t
          let childR :=
            internalChildRealization D₀ j₀ realize hstep next parentR
          refine Or.inr ((hright.token_iff ξ hk token).mpr ⟨next, childR, havail, ?_⟩)
          apply (token_of_restrictedInstrument D₀ j₀ realize
            next childR [] active ξ finalK (fun o => hk _) token).mp
          rw [← embed_restricted_internal_of_identity D₀ j₀ realize
            hstep hop' next parentR [] active]
          exact
            (token_of_restrictedInstrument D₀ j₀ realize
              (ChannelTree.internal hstep next) parentR [] active ξ finalK
              (fun o => hk _) token).mpr hholds
    | external _ hex _ =>
        exact False.elim (ChannelExternalStep.not_intern hex hc)
    | probability _ _ _ _ =>
        cases hc
    | probabilityZero _ =>
        cases hc
    | probabilityOne _ =>
        cases hc
    | measurement _ _ =>
        cases hc

/-! ## Branch-complete evaluation derivations

Each constructor is one situation for which a path transfer lemma exists,
together with the coordinate and observed-stack bookkeeping that lemma
performs.  Values under payload function frames have no constructor
(they are stuck), and `pauliX` has one only at the empty stack (its
physical operation is not aggregated through a pending stack). -/
inductive PathChannelEvaluation {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀) :
    ChannelConfig C → ℕ → ObservedStack C → Prop where
  | terminal {s : ChannelConfig C} {active : ℕ}
      {observed : ObservedStack C}
      (hterminal : ChannelTerminal s) :
      PathChannelEvaluation D₀ j₀ realize s active observed
  | application {s : ChannelConfig C} {fn arg : Term (QubitPrimitive C)}
      {active : ℕ} {observed : ObservedStack C}
      (hc : s.control = .term (.app fn arg))
      (hnext : PathChannelEvaluation D₀ j₀ realize
        {s with
          control := .term fn
          stack := .argument arg s.env :: s.stack}
        active ((.argument arg s.env, active) :: observed)) :
      PathChannelEvaluation D₀ j₀ realize s active observed
  | lambda {s : ChannelConfig C} {x : Name} {body : Term (QubitPrimitive C)}
      {active : ℕ} {observed : ObservedStack C}
      (hc : s.control = .term (.lam x body))
      (hnext : PathChannelEvaluation D₀ j₀ realize
        {s with control := .value (.closure x body s.env)}
        active observed) :
      PathChannelEvaluation D₀ j₀ realize s active observed
  | recursive {s : ChannelConfig C} {self x : Name}
      {body : Term (QubitPrimitive C)}
      {active : ℕ} {observed : ObservedStack C}
      (hc : s.control = .term (.recLam self x body))
      (hnext : PathChannelEvaluation D₀ j₀ realize
        {s with control := .value (.recClosure self x body s.env)}
        active observed) :
      PathChannelEvaluation D₀ j₀ realize s active observed
  | varLookup {s : ChannelConfig C} {x : Name} {v : RuntimeValue C}
      {active : ℕ} {observed : ObservedStack C}
      (hc : s.control = .term (.var x))
      (hlookup : RuntimeEnv.lookup x s.env = some v)
      (hnext : PathChannelEvaluation D₀ j₀ realize
        {s with control := .value v} active observed) :
      PathChannelEvaluation D₀ j₀ realize s active observed
  | returnPayload {s : ChannelConfig C} {value : C}
      {active : ℕ} {observed : ObservedStack C}
      (hc : s.control = .term (.prim (.ret value)))
      (hnext : PathChannelEvaluation D₀ j₀ realize
        {s with control := .value (.payload value)} active observed) :
      PathChannelEvaluation D₀ j₀ realize s active observed
  | evaluateArgument {s : ChannelConfig C} {fn : RuntimeValue C}
      {arg : Term (QubitPrimitive C)} {callEnv : RuntimeEnv C}
      {rest : EvalStack C} {saved : ℕ} {observedRest : ObservedStack C}
      (hc : s.control = .value fn)
      (hs : s.stack = .argument arg callEnv :: rest)
      (hnext : PathChannelEvaluation D₀ j₀ realize
        {s with
          control := .term arg
          env := callEnv
          stack := .function fn :: rest}
        saved ((.function fn, saved) :: observedRest)) :
      PathChannelEvaluation D₀ j₀ realize s saved
        ((.argument arg callEnv, saved) :: observedRest)
  | beta {s : ChannelConfig C} {x : Name}
      {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
      {arg : RuntimeValue C} {rest : EvalStack C} {saved : ℕ}
      {observedRest : ObservedStack C}
      (hc : s.control = .value arg)
      (hs : s.stack = .function (.closure x body closureEnv) :: rest)
      (hnext : PathChannelEvaluation D₀ j₀ realize
        {s with
          control := .term body
          env := RuntimeEnv.bind x arg closureEnv
          stack := rest}
        saved observedRest) :
      PathChannelEvaluation D₀ j₀ realize s saved
        ((.function (.closure x body closureEnv), saved) :: observedRest)
  | recBeta {s : ChannelConfig C} {self x : Name}
      {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
      {arg : RuntimeValue C} {rest : EvalStack C} {saved : ℕ}
      {observedRest : ObservedStack C}
      (hc : s.control = .value arg)
      (hs : s.stack =
        .function (.recClosure self x body closureEnv) :: rest)
      (hnext : PathChannelEvaluation D₀ j₀ realize
        {s with
          control := .term body
          env :=
            RuntimeEnv.bind x arg
              (RuntimeEnv.bind self
                (.recClosure self x body closureEnv) closureEnv)
          stack := rest}
        saved observedRest) :
      PathChannelEvaluation D₀ j₀ realize s saved
        ((.function (.recClosure self x body closureEnv), saved) ::
          observedRest)
  | pauliX {s : ChannelConfig C} {value : C} {active : ℕ}
      {observed : ObservedStack C}
      (hc : s.control = .term (.prim (.pauliX value)))
      (hstack : s.stack = []) :
      PathChannelEvaluation D₀ j₀ realize s active observed
  | externBranch {s t : ChannelConfig C}
      {left right : Term (QubitPrimitive C)} {selected : Bool}
      {childActive : ℕ} {observed : ObservedStack C}
      (hc : s.control = .term (.extern left right))
      (hstep : ChannelExternalStep s selected t)
      (hnext : PathChannelEvaluation D₀ j₀ realize t childActive observed) :
      PathChannelEvaluation D₀ j₀ realize s
        (HardwareAdequacy.branchCoordinate selected childActive) observed
  | externRoot {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
      {observed : ObservedStack C}
      (hc : s.control = .term (.extern left right)) :
      PathChannelEvaluation D₀ j₀ realize s 0 observed
  | probZero {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
      {active : ℕ} {observed : ObservedStack C}
      (hc : s.control = .term (.prob 0 left right))
      (hnext : PathChannelEvaluation D₀ j₀ realize
        {s with
          control := .term right
          quantum := applyOperation
            (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
            s.quantum}
        active observed) :
      PathChannelEvaluation D₀ j₀ realize s active observed
  | probOne {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
      {active : ℕ} {observed : ObservedStack C}
      (hc : s.control = .term (.prob 1 left right))
      (hnext : PathChannelEvaluation D₀ j₀ realize
        {s with
          control := .term left
          quantum := applyOperation
            (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
            s.quantum}
        active observed) :
      PathChannelEvaluation D₀ j₀ realize s active observed
  | probability {s : ChannelConfig C} {p : ℝ}
      {left right : Term (QubitPrimitive C)}
      {active : ℕ} {observed : ObservedStack C}
      (hp₀ : 0 < p) (hp₁ : p < 1)
      (hc : s.control = .term (.prob p left right))
      (hleft : PathChannelEvaluation D₀ j₀ realize
        {s with
          control := .term left
          quantum := applyOperation
            (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum}
        active observed)
      (hright : PathChannelEvaluation D₀ j₀ realize
        {s with
          control := .term right
          quantum := applyOperation
            (sourceProbabilityOperation (1 - p)
              (sub_nonneg.mpr hp₁.le) (by linarith)) s.quantum}
        active observed) :
      PathChannelEvaluation D₀ j₀ realize s active observed
  | measurement {s : ChannelConfig C} {zeroValue oneValue : C}
      {active : ℕ} {observed : ObservedStack C}
      (hc : s.control = .term (.prim (.measureZ zeroValue oneValue)))
      (hne : realize zeroValue ≠ realize oneValue)
      (hzero : PathChannelEvaluation D₀ j₀ realize
        {s with
          control := .value (.payload zeroValue)
          quantum := applyOperation (measurementOperation false) s.quantum}
        active observed)
      (hone : PathChannelEvaluation D₀ j₀ realize
        {s with
          control := .value (.payload oneValue)
          quantum := applyOperation (measurementOperation true) s.quantum}
        active observed) :
      PathChannelEvaluation D₀ j₀ realize s active observed
  | intern {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
      {active : ℕ} {observed : ObservedStack C}
      (hc : s.control = .term (.intern left right))
      (hleft : PathChannelEvaluation D₀ j₀ realize
        {s with control := .term left} active observed)
      (hright : PathChannelEvaluation D₀ j₀ realize
        {s with control := .term right} active observed) :
      PathChannelEvaluation D₀ j₀ realize s active observed

/-! ## The path-indexed fundamental theorem -/

/-- Every branch-complete evaluation derivation at a related well-scoped
state is token-adequate: at the active coordinate, the observations of the
denotation are exactly those witnessed by finite channel trees. -/
theorem pathChannelEvaluation_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {active : ℕ} {observedStack : ObservedStack C}
    (heval : PathChannelEvaluation D₀ j₀ realize s active observedStack) :
    ∀ (_ : ChannelConfig.WellScoped s)
      (finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
      (result : TTResult 2),
      PathChannelConfigRel D₀ j₀ realize s active observedStack finalK
        result →
      PathChannelTreeTokenAdequacy D₀ j₀ realize s active observedStack
        finalK result := by
  induction heval with
  | @terminal s active observed hterminal =>
      intro hscoped finalK result hrel
      exact terminal_related_pathChannelTreeTokenAdequacy D₀ j₀ realize
        hterminal hscoped hrel
  | @application s fn arg active observed hc _ ih =>
      intro hscoped finalK result hrel
      have hEq : {s with control := .term (.app fn arg)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hchild :=
        path_channel_config_application D₀ j₀ (hrel := hEq.symm ▸ hrel)
      exact application_pathChannelTreeTokenAdequacy D₀ j₀ realize hc hrel
        (ih ((channelInternalStep_of_application hc).preserve_wellScoped
          hscoped) finalK result hchild)
  | @lambda s x body active observed hc _ ih =>
      intro hscoped finalK result hrel
      have hEq : {s with control := .term (.lam x body)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hchild :=
        path_channel_config_lambda D₀ j₀ (hrel := hEq.symm ▸ hrel)
      exact lambda_pathChannelTreeTokenAdequacy D₀ j₀ realize hc hrel
        (ih ((channelInternalStep_of_lambda hc).preserve_wellScoped hscoped)
          finalK result hchild)
  | @recursive s self x body active observed hc _ ih =>
      intro hscoped finalK result hrel
      have hEq : {s with control := .term (.recLam self x body)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hchild :=
        path_channel_config_recursive D₀ j₀ (hrel := hEq.symm ▸ hrel)
      exact recursive_pathChannelTreeTokenAdequacy D₀ j₀ realize hc hrel
        (ih ((channelInternalStep_of_recursive hc).preserve_wellScoped
          hscoped) finalK result hchild)
  | @varLookup s x v active observed hc hlookup _ ih =>
      intro hscoped finalK result hrel
      exact variable_pathChannelTreeTokenAdequacy D₀ j₀ realize hc hlookup
        hrel
        (ih ((channelInternalStep_of_variable hc hlookup).preserve_wellScoped
          hscoped) finalK result
          (path_channel_config_variable D₀ j₀ hc hlookup hrel))
  | @returnPayload s value active observed hc _ ih =>
      intro hscoped finalK result hrel
      exact return_pathChannelTreeTokenAdequacy D₀ j₀ realize hc hrel
        (ih ((channelInternalStep_of_return hc).preserve_wellScoped hscoped)
          finalK result (path_channel_config_return D₀ j₀ hc hrel))
  | @evaluateArgument s fn arg callEnv rest saved observedRest hc hs _ ih =>
      intro hscoped finalK result hrel
      have hEq :
          {s with
            control := .value fn
            stack := .argument arg callEnv :: rest} = s :=
        ChannelConfig.ext hc.symm rfl hs.symm rfl
      have hchild :=
        path_channel_config_evaluateArgument D₀ j₀
          (hrel := hEq.symm ▸ hrel)
      exact evaluateArgument_pathChannelTreeTokenAdequacy D₀ j₀ realize hc hs
        hrel
        (ih ((channelInternalStep_of_evaluateArgument hc hs).preserve_wellScoped
          hscoped) finalK result hchild)
  | @beta s x body closureEnv arg rest saved observedRest hc hs _ ih =>
      intro hscoped finalK result hrel
      have hEq :
          {s with
            control := .value arg
            stack := .function (.closure x body closureEnv) :: rest} = s :=
        ChannelConfig.ext hc.symm rfl hs.symm rfl
      have hchild :=
        path_channel_config_beta D₀ j₀ (hrel := hEq.symm ▸ hrel)
      exact beta_pathChannelTreeTokenAdequacy D₀ j₀ realize hc hs hrel
        (ih ((channelInternalStep_of_beta hc hs).preserve_wellScoped hscoped)
          finalK result hchild)
  | @recBeta s self x body closureEnv arg rest saved observedRest hc hs _
      ih =>
      intro hscoped finalK result hrel
      have hEq :
          {s with
            control := .value arg
            stack :=
              .function (.recClosure self x body closureEnv) :: rest} = s :=
        ChannelConfig.ext hc.symm rfl hs.symm rfl
      have hchild :=
        path_channel_config_recBeta D₀ j₀ (hrel := hEq.symm ▸ hrel)
      exact recBeta_pathChannelTreeTokenAdequacy D₀ j₀ realize hc hs hrel
        (ih ((channelInternalStep_of_recBeta hc hs).preserve_wellScoped
          hscoped) finalK result hchild)
  | @pauliX s value active observed hc hstack =>
      intro hscoped finalK result hrel
      exact pauliX_pathChannelTreeTokenAdequacy D₀ j₀ realize hc hstack hrel
  | @externBranch s t left right selected childActive observed hc hstep _
      ih =>
      intro hscoped finalK result hrel
      have hEq : {s with control := .term (.extern left right)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hchild :
          PathChannelConfigRel D₀ j₀ realize
            {s with control := .term (if selected then right else left)}
            childActive observed finalK result :=
        path_channel_config_externalSelect D₀ j₀ (hrel := hEq.symm ▸ hrel)
      have ht : t = {s with
          control := .term (if selected then right else left)} :=
        ChannelExternalStep.eq_of_extern hstep hc
      subst ht
      exact external_step_pathChannelTreeTokenAdequacy D₀ j₀ realize hc hstep
        hrel
        (ih (hstep.preserve_wellScoped hscoped) finalK result hchild)
  | @externRoot s left right observed hc =>
      intro hscoped finalK result hrel
      exact extern_root_pathChannelTreeTokenAdequacy D₀ j₀ realize hc hrel
  | @probZero s left right active observed hc _ ih =>
      intro hscoped finalK result hrel
      have hEq : {s with control := .term (.prob 0 left right)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hchild :=
        path_channel_config_probabilityZero D₀ j₀ (hrel := hEq.symm ▸ hrel)
      exact probabilityZero_step_pathChannelTreeTokenAdequacy D₀ j₀ realize hc
        hrel
        (ih (wellScoped_prob_right hc hscoped _) finalK result hchild)
  | @probOne s left right active observed hc _ ih =>
      intro hscoped finalK result hrel
      have hEq : {s with control := .term (.prob 1 left right)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hchild :=
        path_channel_config_probabilityOne D₀ j₀ (hrel := hEq.symm ▸ hrel)
      exact probabilityOne_step_pathChannelTreeTokenAdequacy D₀ j₀ realize hc
        hrel
        (ih (wellScoped_prob_left hc hscoped _) finalK result hchild)
  | @probability s p left right active observed hp₀ hp₁ hc _ _ ihL ihR =>
      intro hscoped finalK result hrel
      obtain ⟨leftResult, rightResult, hrelL, hrelR, hres⟩ :=
        path_channel_config_probability D₀ j₀ hp₀ hp₁ hc hrel
      exact probability_step_pathChannelTreeTokenAdequacy D₀ j₀ realize hp₀
        hp₁ hc hrel
        (ihL (wellScoped_prob_left hc hscoped _) finalK leftResult hrelL)
        (ihR (wellScoped_prob_right hc hscoped _) finalK rightResult hrelR)
        hres
  | @measurement s zeroValue oneValue active observed hc hne _ _ ihZ ihO =>
      intro hscoped finalK result hrel
      obtain ⟨zeroResult, oneResult, hrelZ, hrelO, hres⟩ :=
        path_channel_config_measureZ D₀ j₀ hc hne hrel
      exact measurement_step_pathChannelTreeTokenAdequacy D₀ j₀ realize hc
        hscoped hrel
        (ihZ (wellScoped_payload_child hc hscoped zeroValue _) finalK
          zeroResult hrelZ)
        (ihO (wellScoped_payload_child hc hscoped oneValue _) finalK
          oneResult hrelO)
        hres
  | @intern s left right active observed hc _ _ ihL ihR =>
      intro hscoped finalK result hrel
      obtain ⟨leftResult, rightResult, hrelL, hrelR, hres⟩ :=
        path_channel_config_intern D₀ j₀ hc hrel
      exact intern_step_pathChannelTreeTokenAdequacy D₀ j₀ realize hc
        hrel
        (ihL (wellScoped_intern_left hc hscoped) finalK leftResult hrelL)
        (ihR (wellScoped_intern_right hc hscoped) finalK rightResult hrelR)
        hres

/-- Path-indexed fundamental theorem, in applied form. -/
theorem related_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C}
    {active : ℕ} {observedStack : ObservedStack C}
    (heval : PathChannelEvaluation D₀ j₀ realize s active observedStack)
    (hscoped : ChannelConfig.WellScoped s)
    {finalK : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)}
    {result : TTResult 2}
    (hrel : PathChannelConfigRel D₀ j₀ realize s active observedStack finalK
      result) :
    PathChannelTreeTokenAdequacy D₀ j₀ realize s active observedStack finalK
      result :=
  pathChannelEvaluation_pathChannelTreeTokenAdequacy D₀ j₀ realize heval
    hscoped finalK result hrel

/-! ## From token adequacy back to channel-tree completeness -/

/-- Coordinatewise token adequacy at the empty observed stack is exactly
coordinate-presented channel-tree completeness. -/
theorem coordinatePresented_of_pathChannelTreeTokenAdequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {denotation : HSemanticComp D₀ j₀}
    (hadq : ∀ (i : ℕ) (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)),
      PathChannelTreeTokenAdequacy D₀ j₀ realize s i [] k
        (denotation i k)) :
    CoordinatePresentedChannelTreeCompleteness D₀ j₀ realize s denotation where
  coordinate_result_eq_channelTree_sup_presented := by
    classical
    intro i ξ k hk
    apply RoundedTheory.ext
    ext token
    have hiff := (hadq i k).token_iff ξ hk token
    have hsup :
        token ∈ (sSup (channelTreeResults D₀ j₀ realize s [] i k) :
            TTResult 2) ↔
          ∃ T ∈ channelTreeResults D₀ j₀ realize s [] i k, token ∈ T :=
      RoundedTheory.mem_sSup _
    constructor
    · intro hmem
      obtain ⟨tree, R, havail, htoken⟩ := hiff.mp hmem
      refine hsup.mpr ⟨restrictedResult D₀ j₀ realize tree R [] i k,
        ⟨tree.depth, tree, R, le_rfl, rfl⟩, ?_⟩
      rw [restrictedResult_eq_embed D₀ j₀ realize tree R [] i k havail]
      exact (token_of_restrictedInstrument D₀ j₀ realize tree R [] i ξ k
        (fun o => hk _) token).mpr htoken
    · intro hmem
      obtain ⟨T, ⟨fuel, tree, R, hdepth, rfl⟩, htoken⟩ := hsup.mp hmem
      by_cases havail : ResultAvailable tree [] i
      · refine hiff.mpr ⟨tree, R, havail, ?_⟩
        rw [restrictedResult_eq_embed D₀ j₀ realize tree R [] i k havail]
          at htoken
        exact (token_of_restrictedInstrument D₀ j₀ realize tree R [] i ξ k
          (fun o => hk _) token).mp htoken
      · rw [restrictedResult_eq_bot D₀ j₀ realize tree R [] i k havail]
          at htoken
        exact absurd htoken (fun h => not_mem_bot_result h)

/-- At an empty CEK stack the classical relation gives the path-indexed
relation at every coordinate and every final continuation. -/
theorem pathChannelConfigRel_of_channelConfigRel_nil {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} (hs : s.stack = [])
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize s answer)
    (active : ℕ) (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    PathChannelConfigRel D₀ j₀ realize s active [] k (answer active k) := by
  rcases hrel with ⟨current, stackK, hcontrol, hstack, rfl⟩
  rw [hs] at hstack
  cases hstack
  exact ⟨hs.symm, current, k, hcontrol, PathStackRel.nil, rfl⟩

/-- Bridge from the classical relation to presented channel-tree
completeness at an empty stack, for a state with a branch-complete
evaluation derivation at every coordinate. -/
theorem related_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} (hs : s.stack = [])
    (heval : ∀ i, PathChannelEvaluation D₀ j₀ realize s i [])
    (hscoped : ChannelConfig.WellScoped s)
    {answer : HSemanticComp D₀ j₀}
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer where
  related := hrel
  complete :=
    (coordinatePresented_of_pathChannelTreeTokenAdequacy D₀ j₀ realize
      (fun i k =>
        related_pathChannelTreeTokenAdequacy D₀ j₀ realize (heval i) hscoped
          (pathChannelConfigRel_of_channelConfigRel_nil D₀ j₀ hs hrel
            i k))).toPresented

/-! ## Closed programs -/

/-- Channel-tree completeness for a closed program with a branch-complete
evaluation derivation at every coordinate.  No syntactic `NoApp`,
`FunAppFrag` or `Produces` restriction is imposed; the derivation is the
only hypothesis, and it is exactly the operational content that stuck
states and internal choice fail to provide. -/
theorem closed_term_presented_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (hclosed : Closed code)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (heval : ∀ i, PathChannelEvaluation D₀ j₀ realize
      (initialChannelConfig code quantum) i []) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig code quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
  (related_presentedChannelConfigCompleteness D₀ j₀ realize rfl heval
    (initialChannelConfig_wellScoped hclosed quantum)
    (initialChannelConfig_related D₀ j₀ realize code quantum
      semanticEnv)).complete

/-- Token adequacy for a closed program with a branch-complete evaluation
derivation at every coordinate. -/
theorem closed_term_presented_token_adequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (hclosed : Closed code)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (heval : ∀ i, PathChannelEvaluation D₀ j₀ realize
      (initialChannelConfig code quantum) i [])
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv)
        i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig code quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig code quantum)
    (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv)
    (closed_term_presented_channelTreeCompleteness D₀ j₀ realize code hclosed
      quantum semanticEnv heval)
    selectors ξ k hk i token

/-! ## Stuck payload frames and the NoApp bridge -/

/-- A value under a payload function frame has no CEK successor: beta and
recBeta require a closure, and every other internal step expects a
different control or stack shape. -/
theorem stuck_payload_under_function_no_internal_step {C : Type}
    {s : ChannelConfig C} {arg : RuntimeValue C} {value : C}
    {rest : EvalStack C}
    (hc : s.control = .value arg)
    (hs : s.stack = .function (.payload value) :: rest) :
    ∀ {t : ChannelConfig C}, ¬ ChannelInternalStep s t := by
  intro t hstep
  cases hstep with
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

/-- A payload used as a function is not merely unable to take an internal
step: no branch-complete channel tree can start there.  Terminality is
excluded by the pending function frame, external stepping by value control,
and all physical branching constructors require term control. -/
theorem stuck_payload_under_function_no_channelTree {C : Type}
    {s : ChannelConfig C} {arg : RuntimeValue C} {value : C}
    {rest : EvalStack C}
    (hc : s.control = .value arg)
    (hs : s.stack = .function (.payload value) :: rest) :
    ChannelTree C s → False := by
  intro tree
  cases tree with
  | terminal hterminal =>
      have hne := hs.symm.trans hterminal.stack_eq
      cases hne
  | internal hstep _ =>
      exact stuck_payload_under_function_no_internal_step hc hs hstep
  | external _ hstep _ =>
      exact ChannelExternalStep.not_value hstep hc
  | probability _ _ _ _ => cases hc
  | probabilityZero _ => cases hc
  | probabilityOne _ => cases hc
  | measurement _ _ => cases hc

/-- The concrete closed program `app (ret f) (ret a)` has no branch-complete
channel tree.  Its unique administrative prefix evaluates both returns and
ends with payload `a` under a function frame containing payload `f`. -/
theorem closed_payload_application_no_channelTree {C : Type}
    (functionValue argumentValue : C) (quantum : NormalizedDensity 2) :
    ChannelTree C
      (initialChannelConfig
        (.app (.prim (.ret functionValue)) (.prim (.ret argumentValue)))
        quantum) →
      False := by
  let s₀ : ChannelConfig C :=
    initialChannelConfig
      (.app (.prim (.ret functionValue)) (.prim (.ret argumentValue)))
      quantum
  intro tree₀
  have hc₀ :
      s₀.control =
        .term
          (.app (.prim (.ret functionValue)) (.prim (.ret argumentValue))) :=
    rfl
  cases tree₀ with
  | terminal hterminal =>
      have := hterminal.control_eq.symm.trans hc₀
      cases this
  | @internal _ s₁ h₀ tree₁ =>
      have hs₁ := ChannelInternalStep.eq_of_application h₀ hc₀
      subst s₁
      have hc₁ :
          ({s₀ with
            control := .term (.prim (.ret functionValue))
            stack :=
              .argument (.prim (.ret argumentValue)) s₀.env :: s₀.stack}).control =
            .term (.prim (.ret functionValue)) :=
        rfl
      cases tree₁ with
      | terminal hterminal =>
          have := hterminal.control_eq.symm.trans hc₁
          cases this
      | @internal _ s₂ h₁ tree₂ =>
          have hs₂ := ChannelInternalStep.eq_config_of_return h₁ hc₁
          subst s₂
          have hc₂ :
              ({s₀ with
                control := .value (.payload functionValue)
                stack :=
                  .argument (.prim (.ret argumentValue)) s₀.env ::
                    s₀.stack}).control =
                .value (.payload functionValue) :=
            rfl
          have hstack₂ :
              ({s₀ with
                control := .value (.payload functionValue)
                stack :=
                  .argument (.prim (.ret argumentValue)) s₀.env ::
                    s₀.stack}).stack =
                .argument (.prim (.ret argumentValue)) s₀.env :: s₀.stack :=
            rfl
          cases tree₂ with
          | terminal hterminal =>
              have hne := hstack₂.symm.trans hterminal.stack_eq
              cases hne
          | @internal _ s₃ h₂ tree₃ =>
              have hs₃ :=
                ChannelInternalStep.eq_of_evaluateArgument h₂ hc₂ hstack₂
              subst s₃
              have hc₃ :
                  ({s₀ with
                    control := .term (.prim (.ret argumentValue))
                    stack := [.function (.payload functionValue)]}).control =
                    .term (.prim (.ret argumentValue)) :=
                rfl
              cases tree₃ with
              | terminal hterminal =>
                  have := hterminal.control_eq.symm.trans hc₃
                  cases this
              | @internal _ s₄ h₃ tree₄ =>
                  have hs₄ :=
                    ChannelInternalStep.eq_config_of_return h₃ hc₃
                  subst s₄
                  exact stuck_payload_under_function_no_channelTree
                    (s :=
                      {s₀ with
                        control := .value (.payload argumentValue)
                        stack := [.function (.payload functionValue)]})
                    rfl rfl tree₄
              | external _ hstep _ =>
                  exact ChannelExternalStep.not_prim hstep hc₃
          | external _ hstep _ =>
              exact ChannelExternalStep.not_value hstep hc₂
      | external _ hstep _ =>
          exact ChannelExternalStep.not_prim hstep hc₁
  | external _ hstep _ =>
      cases hstep

/-- Concrete semantic boundary for unrestricted closed-term completeness.

If one finitely presented continuation observes the denotation of the closed
stuck program `app (ret f) (ret a)` as nonbottom, then presented channel-tree
completeness for that program is contradictory: the preceding theorem shows
that its operational channel-tree result set is empty.  The nonbottom
hypothesis is explicit because constructing a particular recursive domain,
projection, realization, and separating finite instrument is intentionally
not part of this theorem. -/
theorem
    closed_payload_application_not_presented_channelTreeComplete_of_nonbottom
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (functionValue argumentValue : C)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool) (i : ℕ)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (hnonbottom :
      HardwareAdequacy.selectPath selectors
          (interp (hardwarePrimitive D₀ j₀ realize)
            (.app (.prim (.ret functionValue)) (.prim (.ret argumentValue)))
            semanticEnv)
          i k ≠
        ⊥) :
    ¬ PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.app (.prim (.ret functionValue)) (.prim (.ret argumentValue)))
        quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.prim (.ret functionValue)) (.prim (.ret argumentValue)))
        semanticEnv) := by
  intro hcomplete
  apply hnonbottom
  rw [hcomplete.selected_result_eq_channelTree_sup_presented
    selectors i ξ k hk]
  apply le_antisymm
  · apply sSup_le
    rintro result ⟨fuel, tree, realization, hdepth, hresult⟩
    exact False.elim
      (closed_payload_application_no_channelTree functionValue argumentValue
        quantum tree)
  · exact bot_le

/-- Application-free closed terms are presented-complete with no
`PathChannelEvaluation` hypothesis: they are already covered by the
empty-stack NoApp induction. -/
theorem closed_term_presented_channelTreeCompleteness_of_noApp {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (hclosed : Closed code) (hnoapp : NoApp code)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig code quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
  closed_lambda_choice_presented_channelTreeCompleteness D₀ j₀ realize
    code hclosed hnoapp quantum semanticEnv

/-- Token adequacy for application-free closed terms. -/
theorem closed_term_presented_token_adequacy_of_noApp {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (hclosed : Closed code) (hnoapp : NoApp code)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv)
        i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig code quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  closed_lambda_choice_presented_token_adequacy D₀ j₀ realize
    code hclosed hnoapp quantum semanticEnv selectors ξ k hk i token

end HardwareChannelSemantics
end QLambda
