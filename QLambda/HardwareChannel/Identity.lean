/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.HardwareChannel.Config

/-!
# Identity-step presented completeness transfers

Layer of the hardware channel-tree semantics.  All layers share the
`QLambda.HardwareChannelSemantics` namespace; import
`QLambda.HardwareChannelSemantics` for the full module.
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

/-- Presented completeness transfers across a hardware return. -/
theorem return_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {value : C}
    (hc : s.control = .term (.prim (.ret value)))
    {denotation : HSemanticComp D₀ j₀}
    (hsource : ChannelConfigRel D₀ j₀ realize s denotation)
    (hchild : PresentedChannelConfigCompleteness D₀ j₀ realize
      {s with control := .value (.payload value)}
      denotation) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s denotation := by
  let t : ChannelConfig C :=
    {s with control := .value (.payload value)}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.prim (.ret value))} t :=
      ChannelInternalStep.returnPrimitive (s := s) (value := value)
    have hs : s = {s with control := .term (.prim (.ret value))} :=
      ChannelConfig.ext hc rfl rfl rfl
    exact hs.symm ▸ happ
  exact PresentedChannelConfigCompleteness.ofIdentityStep D₀ j₀ realize
    hsource hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelInternalStep.eq_config_of_return h' hc) hchild

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
  | @probability _ p' _ _ hp₀ hp₁ _ _ =>
      injection hc with hterm
      injection hterm with hp' _ _
      subst p
      exact hp ⟨hp₀.le, hp₁.le⟩
  | @probabilityZero _ _ _ _ =>
      injection hc with hterm
      injection hterm with hp0
      subst p
      exact hp ⟨le_rfl, zero_le_one⟩
  | @probabilityOne _ _ _ _ =>
      injection hc with hterm
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


end HardwareChannelSemantics
end QLambda
