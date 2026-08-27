/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.HardwareChannel.Spines

/-!
# Under-frame completeness and closed special cases

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

/-- List-of-frames completeness: a lambda under leftover argument
frames, a value under the corresponding function frame, and
administrative NoApp at that same function frame. -/
theorem argument_spine_presented
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : ∀ p ∈ frames, AdminNoApp p.1) :
    (∀ {s : ChannelConfig C} {x : Name}
        {body : Term (QubitPrimitive C)} {answer : HSemanticComp D₀ j₀},
      s.control = .term (.lam x body) →
      s.stack = argumentStack frames →
      LamAbsorbs frames.length body →
      ChannelConfig.WellScoped s →
      ChannelConfigRel D₀ j₀ realize s answer →
      PresentedChannelConfigCompleteness D₀ j₀ realize s answer)
    ∧
    ValueUnderFunctionArgumentFrames D₀ j₀ realize frames
    ∧
    (∀ {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
        {x : Name} {body : Term (QubitPrimitive C)}
        {cloX : RuntimeEnv C} {answer : HSemanticComp D₀ j₀},
      AdminNoApp code →
      s.control = .term code →
      s.stack =
        .function (.closure x body cloX) :: argumentStack frames →
      BodyUnderArgs frames.length body →
      ChannelConfig.WellScoped s →
      ChannelConfigRel D₀ j₀ realize s answer →
      PresentedChannelConfigCompleteness D₀ j₀ realize s answer) := by
  induction frames with
  | nil =>
      refine ⟨?hlam, ?hval, ?hadmin⟩
      · intro s x body answer hc hs _habs hscoped hrel
        obtain ⟨semanticEnv, k, henv, hstack, heq⟩ :=
          channelConfigRel_term_inv D₀ j₀ hc hrel
        rw [hs] at hstack
        cases hstack
        exact
          { related := hrel
            complete :=
              PresentedChannelTreeCompleteness.congr rfl heq.symm
                (lam_terminal_presentedChannelTreeCompleteness
                  D₀ j₀ realize hc (by simpa using hs) hscoped
                  henv) }
      · intro s arg x body cloX answer hc hs hbody hscoped hrel
        have hs' : s.stack = [.function (.closure x body cloX)] := by
          simpa [argumentStack] using hs
        exact
          value_under_closure_nil_presentedChannelConfigCompleteness
            D₀ j₀ realize hc hs' (BodyUnderArgs_zero.mp hbody)
            hscoped hrel
      · intro s code x body cloX answer hadmin hc hs hbody hscoped
          hrel
        have hs' : s.stack = [.function (.closure x body cloX)] := by
          simpa [argumentStack] using hs
        exact
          admin_noapp_under_closure_nil_presentedChannelConfigCompleteness
            D₀ j₀ realize hadmin hc hs' (BodyUnderArgs_zero.mp hbody)
            hscoped hrel
  | cons p rest ih =>
      rcases p with ⟨arg, callEnv⟩
      have hadminArg : AdminNoApp arg :=
        hok (arg, callEnv) (by simp)
      have hokRest : ∀ q ∈ rest, AdminNoApp q.1 :=
        fun q hq => hok q (by simp [hq])
      obtain ⟨ihLam, ihVal, ihAdmin⟩ := ih hokRest
      have hlam :
          ∀ {s : ChannelConfig C} {x : Name}
            {body : Term (QubitPrimitive C)}
            {answer : HSemanticComp D₀ j₀},
          s.control = .term (.lam x body) →
          s.stack = argumentStack ((arg, callEnv) :: rest) →
          LamAbsorbs ((arg, callEnv) :: rest).length body →
          ChannelConfig.WellScoped s →
          ChannelConfigRel D₀ j₀ realize s answer →
          PresentedChannelConfigCompleteness D₀ j₀ realize s
            answer := by
        intro s x body answer hc hs habs hscoped hrel
        have hsLam :
            {s with control := .term (.lam x body)} = s :=
          ChannelConfig.ext hc.symm rfl rfl rfl
        have hrelLam : ChannelConfigRel D₀ j₀ realize
            {s with control := .term (.lam x body)} answer :=
          hsLam.symm ▸ hrel
        have hrelClo :=
          channel_config_lambda D₀ j₀ (s := s) hrelLam
        have hsrcClo :
            {s with control := .value (.closure x body s.env)} =
              {s with
                control := .value (.closure x body s.env)
                stack :=
                  .argument arg callEnv :: argumentStack rest} :=
          ChannelConfig.ext rfl rfl hs rfl
        have hrelFn :=
          channel_config_evaluateArgument D₀ j₀
            (s := {s with control := .value (.closure x body s.env)})
            (fn := .closure x body s.env) (arg := arg)
            (callEnv := callEnv) (rest := argumentStack rest)
            (hsrcClo ▸ hrelClo)
        have hstepLam : ChannelInternalStep s
            {s with control := .value (.closure x body s.env)} := by
          have happ :
              ChannelInternalStep
                {s with control := .term (.lam x body)}
                {s with control := .value (.closure x body s.env)} :=
            ChannelInternalStep.lambda (s := s) (x := x) (body := body)
          exact hsLam.symm ▸ happ
        have hstepArg : ChannelInternalStep
            {s with control := .value (.closure x body s.env)}
            {s with
              control := .term arg
              env := callEnv
              stack :=
                .function (.closure x body s.env) ::
                  argumentStack rest} := by
          have happ :
              ChannelInternalStep
                {s with
                  control := .value (.closure x body s.env)
                  stack :=
                    .argument arg callEnv :: argumentStack rest}
                {s with
                  control := .term arg
                  env := callEnv
                  stack :=
                    .function (.closure x body s.env) ::
                      argumentStack rest} :=
            ChannelInternalStep.evaluateArgument
              (s := {s with control := .value (.closure x body s.env)})
              (fn := .closure x body s.env) (arg := arg)
              (callEnv := callEnv) (rest := argumentStack rest)
          exact hsrcClo.symm ▸ happ
        have hscopedFn : ChannelConfig.WellScoped
            {s with
              control := .term arg
              env := callEnv
              stack :=
                .function (.closure x body s.env) ::
                  argumentStack rest} :=
          ChannelInternalStep.preserve_wellScoped hstepArg
            (ChannelInternalStep.preserve_wellScoped hstepLam hscoped)
        have hbodyRest : BodyUnderArgs rest.length body := by
          simpa [LamAbsorbs] using habs
        have harg :
            PresentedChannelConfigCompleteness D₀ j₀ realize
              {s with
                control := .term arg
                env := callEnv
                stack :=
                  .function (.closure x body s.env) ::
                    argumentStack rest}
              answer :=
          ihAdmin hadminArg rfl rfl hbodyRest hscopedFn hrelFn
        have hClo :=
          evaluateArgument_presentedChannelConfigCompleteness
            D₀ j₀ realize
            (s := {s with control := .value (.closure x body s.env)})
            (fn := .closure x body s.env) (arg := arg)
            (callEnv := callEnv) (rest := argumentStack rest)
            rfl hs hrelClo harg
        exact lambda_presentedChannelConfigCompleteness D₀ j₀ realize
          hc hrel hClo
      have hval : ValueUnderFunctionArgumentFrames D₀ j₀ realize
          ((arg, callEnv) :: rest) := by
        intro s v x body cloX answer hc hs hbody hscoped hrel
        obtain ⟨y, body', rfl, hbody'⟩ :=
          BodyUnderArgs_succ_inv (n := rest.length) hbody
        have hsEq :
            {s with
              control := .value v
              stack :=
                .function (.closure x (.lam y body') cloX) ::
                  argumentStack ((arg, callEnv) :: rest)} = s :=
          ChannelConfig.ext hc.symm rfl hs.symm rfl
        have hrel' : ChannelConfigRel D₀ j₀ realize
            {s with
              control := .value v
              stack :=
                .function (.closure x (.lam y body') cloX) ::
                  argumentStack ((arg, callEnv) :: rest)}
            answer :=
          hsEq.symm ▸ hrel
        have hrelBody :=
          channel_config_beta D₀ j₀ (s := s) (x := x)
            (body := .lam y body') (closureEnv := cloX) (arg := v)
            (rest := argumentStack ((arg, callEnv) :: rest)) hrel'
        let sBody : ChannelConfig C :=
          {s with
            control := .term (.lam y body')
            env := RuntimeEnv.bind x v cloX
            stack := argumentStack ((arg, callEnv) :: rest)}
        have hstepBeta : ChannelInternalStep s sBody := by
          have happ :
              ChannelInternalStep
                {s with
                  control := .value v
                  stack :=
                    .function (.closure x (.lam y body') cloX) ::
                      argumentStack ((arg, callEnv) :: rest)}
                sBody :=
            ChannelInternalStep.beta (s := s) (x := x)
              (body := .lam y body') (closureEnv := cloX) (arg := v)
              (rest := argumentStack ((arg, callEnv) :: rest))
          exact hsEq.symm ▸ happ
        have hscopedBody : ChannelConfig.WellScoped sBody :=
          ChannelInternalStep.preserve_wellScoped hstepBeta hscoped
        have habs : LamAbsorbs ((arg, callEnv) :: rest).length body' :=
          hbody'
        have hchild :=
          hlam (s := sBody) (x := y) (body := body') rfl rfl habs
            hscopedBody hrelBody
        exact beta_presentedChannelConfigCompleteness D₀ j₀ realize
          (s := s) (x := x) (body := .lam y body')
          (closureEnv := cloX) (arg := v)
          (rest := argumentStack ((arg, callEnv) :: rest))
          hc hs hrel hchild
      exact ⟨hlam, hval,
        fun {s} {code} {x} {body} {cloX} {answer} =>
          admin_noapp_under_function_argument_frames_of_value
            D₀ j₀ realize ((arg, callEnv) :: rest) hval⟩

theorem lam_under_argument_frames_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : ∀ p ∈ frames, AdminNoApp p.1)
    {s : ChannelConfig C} {x : Name}
    {body : Term (QubitPrimitive C)} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.lam x body))
    (hs : s.stack = argumentStack frames)
    (habs : LamAbsorbs frames.length body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer :=
  (argument_spine_presented D₀ j₀ realize frames hok).1
    hc hs habs hscoped hrel

theorem value_under_function_argument_frames_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : ∀ p ∈ frames, AdminNoApp p.1)
    {s : ChannelConfig C} {arg : RuntimeValue C} {x : Name}
    {body : Term (QubitPrimitive C)} {cloX : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .value arg)
    (hs : s.stack =
      .function (.closure x body cloX) :: argumentStack frames)
    (hbody : BodyUnderArgs frames.length body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer :=
  (argument_spine_presented D₀ j₀ realize frames hok).2.1
    hc hs hbody hscoped hrel

theorem admin_noapp_under_function_argument_frames_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : ∀ p ∈ frames, AdminNoApp p.1)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {x : Name} {body : Term (QubitPrimitive C)} {cloX : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack =
      .function (.closure x body cloX) :: argumentStack frames)
    (hbody : BodyUnderArgs frames.length body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer :=
  (argument_spine_presented D₀ j₀ realize frames hok).2.2
    hadmin hc hs hbody hscoped hrel

/-- Inner `app (lam x body) arg` under leftover argument frames. -/
theorem app_lam_under_argument_frames_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : ∀ p ∈ frames, AdminNoApp p.1)
    {s : ChannelConfig C} {x : Name}
    {body arg : Term (QubitPrimitive C)} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.app (.lam x body) arg))
    (hs : s.stack = argumentStack frames)
    (hadminArg : AdminNoApp arg)
    (hbody : BodyUnderArgs frames.length body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsApp :
      {s with control := .term (.app (.lam x body) arg)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app (.lam x body) arg)} answer :=
    hsApp.symm ▸ hrel
  have hrelLam :=
    channel_config_application D₀ j₀ (s := s) (fn := .lam x body)
      (arg := arg) hrelApp
  have hrelClo :=
    channel_config_lambda D₀ j₀
      (s := {s with stack := .argument arg s.env :: s.stack})
      hrelLam
  have hrelArg :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {s with
          control := .value (.closure x body s.env)
          stack := .argument arg s.env :: s.stack})
      (fn := .closure x body s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack) hrelClo
  let sArg : ChannelConfig C :=
    {s with
      control := .term arg
      stack := .function (.closure x body s.env) :: s.stack}
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.lam x body)
        stack := .argument arg s.env :: s.stack} := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app (.lam x body) arg)}
          {s with
            control := .term (.lam x body)
            stack := .argument arg s.env :: s.stack} :=
      ChannelInternalStep.application (s := s)
        (fn := .lam x body) (arg := arg)
    exact hsApp.symm ▸ happ
  have hstepLam : ChannelInternalStep
      {s with
        control := .term (.lam x body)
        stack := .argument arg s.env :: s.stack}
      {s with
        control := .value (.closure x body s.env)
        stack := .argument arg s.env :: s.stack} :=
    ChannelInternalStep.lambda
      (s := {s with stack := .argument arg s.env :: s.stack})
      (x := x) (body := body)
  have hstepArg : ChannelInternalStep
      {s with
        control := .value (.closure x body s.env)
        stack := .argument arg s.env :: s.stack}
      sArg :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {s with
          control := .value (.closure x body s.env)
          stack := .argument arg s.env :: s.stack})
      (fn := .closure x body s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack)
  have hscopedArg : ChannelConfig.WellScoped sArg :=
    ChannelInternalStep.preserve_wellScoped hstepArg
      (ChannelInternalStep.preserve_wellScoped hstepLam
        (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
  have hsArg :
      sArg.stack =
        .function (.closure x body s.env) :: argumentStack frames := by
    simp [sArg, hs]
  have harg :
      PresentedChannelConfigCompleteness D₀ j₀ realize sArg answer :=
    admin_noapp_under_function_argument_frames_presentedChannelConfigCompleteness
      D₀ j₀ realize frames hok (s := sArg) (code := arg) (x := x)
      (body := body) (cloX := s.env) hadminArg rfl hsArg hbody
      hscopedArg
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term arg
              env := s.env
              stack :=
                .function (.closure x body s.env) :: s.stack}
            _
        exact hrelArg)
  exact stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := x) (body := body) (arg := arg) hc hrel harg

/-- Closed triple curried
`app (app (app (lam x (lam y (lam z body))) arg1) arg2) arg3`. -/
theorem closed_app_app_app_lam_lam_lam_admin_noapp_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x y z : Name) (body arg1 arg2 arg3 : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.app (.app (.lam x (.lam y (.lam z body))) arg1) arg2)
        arg3))
    (hnoapp : NoApp body)
    (hadmin1 : AdminNoApp arg1) (hadmin2 : AdminNoApp arg2)
    (hadmin3 : AdminNoApp arg3)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.app (.app (.app (.lam x (.lam y (.lam z body))) arg1) arg2)
          arg3)
        quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.app (.app (.lam x (.lam y (.lam z body))) arg1) arg2)
          arg3)
        semanticEnv) := by
  let inner2 : Term (QubitPrimitive C) :=
    .app (.app (.lam x (.lam y (.lam z body))) arg1) arg2
  let code : Term (QubitPrimitive C) := .app inner2 arg3
  let s : ChannelConfig C := initialChannelConfig code quantum
  have hc : s.control = .term code := rfl
  have hrel :=
    initialChannelConfig_related D₀ j₀ realize code quantum semanticEnv
  have hscoped :=
    initialChannelConfig_wellScoped hclosed quantum
  have hsApp :
      {s with control := .term (.app inner2 arg3)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app inner2 arg3)}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    hsApp.symm ▸ hrel
  have hrelInner :=
    channel_config_application D₀ j₀ (s := s) (fn := inner2)
      (arg := arg3) hrelApp
  let sInner : ChannelConfig C :=
    {s with
      control := .term inner2
      stack := .argument arg3 s.env :: s.stack}
  have hstepApp : ChannelInternalStep s sInner := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app inner2 arg3)} sInner :=
      ChannelInternalStep.application (s := s) (fn := inner2)
        (arg := arg3)
    exact hsApp.symm ▸ happ
  have hscopedInner : ChannelConfig.WellScoped sInner :=
    ChannelInternalStep.preserve_wellScoped hstepApp hscoped
  have hsInner : sInner.stack = argumentStack [(arg3, s.env)] := by
    simp [sInner, s, initialChannelConfig, ofConfig, initialConfig,
      argumentStack]
  let inner1 : Term (QubitPrimitive C) :=
    .app (.lam x (.lam y (.lam z body))) arg1
  have hsApp2 :
      {sInner with control := .term (.app inner1 arg2)} = sInner :=
    ChannelConfig.ext rfl rfl rfl rfl
  have hrelApp2 : ChannelConfigRel D₀ j₀ realize
      {sInner with control := .term (.app inner1 arg2)}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) := by
    change ChannelConfigRel D₀ j₀ realize
        {s with
          control := .term inner2
          env := s.env
          stack := .argument arg3 s.env :: s.stack}
        _
    exact hrelInner
  have hrelInner1 :=
    channel_config_application D₀ j₀ (s := sInner) (fn := inner1)
      (arg := arg2) hrelApp2
  let sInner1 : ChannelConfig C :=
    {sInner with
      control := .term inner1
      stack := .argument arg2 sInner.env :: sInner.stack}
  have hstepApp2 : ChannelInternalStep sInner sInner1 := by
    have happ :
        ChannelInternalStep
          {sInner with control := .term (.app inner1 arg2)}
          sInner1 :=
      ChannelInternalStep.application (s := sInner) (fn := inner1)
        (arg := arg2)
    exact hsApp2.symm ▸ happ
  have hscopedInner1 : ChannelConfig.WellScoped sInner1 :=
    ChannelInternalStep.preserve_wellScoped hstepApp2 hscopedInner
  have hsInner1 :
      sInner1.stack = argumentStack [(arg2, s.env), (arg3, s.env)] := by
    simp [sInner1, sInner, s, initialChannelConfig, ofConfig,
      initialConfig, argumentStack]
  have hok : ∀ p ∈ [(arg2, s.env), (arg3, s.env)], AdminNoApp p.1 := by
    intro p hp
    simp at hp
    rcases hp with h | h <;> cases h <;> assumption
  have hbody :
      BodyUnderArgs
        ([(arg2, s.env), (arg3, s.env)] : List
          (Term (QubitPrimitive C) × RuntimeEnv C)).length
        (.lam y (.lam z body)) := by
    simpa [BodyUnderArgs] using hnoapp
  have hinner1 :
      PresentedChannelConfigCompleteness D₀ j₀ realize sInner1
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    app_lam_under_argument_frames_presentedChannelConfigCompleteness
      D₀ j₀ realize [(arg2, s.env), (arg3, s.env)] hok
      (s := sInner1) (x := x) (body := .lam y (.lam z body))
      (arg := arg1) rfl hsInner1 hadmin1 hbody hscopedInner1
      (by
        change ChannelConfigRel D₀ j₀ realize
            {sInner with
              control := .term inner1
              env := sInner.env
              stack := .argument arg2 sInner.env :: sInner.stack}
            _
        exact hrelInner1)
  have hinner :
      PresentedChannelConfigCompleteness D₀ j₀ realize sInner
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    application_presentedChannelConfigCompleteness D₀ j₀ realize
      (s := sInner) (fn := inner1) (arg := arg2) rfl
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term inner2
              env := s.env
              stack := .argument arg3 s.env :: s.stack}
            _
        exact hrelInner)
      hinner1
  exact (application_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (fn := inner2) (arg := arg3) hc hrel hinner).complete

/-- Token adequacy for closed triple curried
`app (app (app (lam x (lam y (lam z body))) arg1) arg2) arg3`. -/
theorem closed_app_app_app_lam_lam_lam_admin_noapp_presented_token_adequacy
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x y z : Name) (body arg1 arg2 arg3 : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.app (.app (.lam x (.lam y (.lam z body))) arg1) arg2)
        arg3))
    (hnoapp : NoApp body)
    (hadmin1 : AdminNoApp arg1) (hadmin2 : AdminNoApp arg2)
    (hadmin3 : AdminNoApp arg3)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize)
          (.app (.app (.app (.lam x (.lam y (.lam z body))) arg1) arg2)
            arg3)
          semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig
            (.app (.app (.app (.lam x (.lam y (.lam z body))) arg1)
              arg2) arg3)
            quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig
      (.app (.app (.app (.lam x (.lam y (.lam z body))) arg1) arg2)
        arg3)
      quantum)
    (interp (hardwarePrimitive D₀ j₀ realize)
      (.app (.app (.app (.lam x (.lam y (.lam z body))) arg1) arg2)
        arg3)
      semanticEnv)
    (closed_app_app_app_lam_lam_lam_admin_noapp_presented_channelTreeCompleteness
      D₀ j₀ realize x y z body arg1 arg2 arg3 hclosed hnoapp
      hadmin1 hadmin2 hadmin3 quantum semanticEnv)
    selectors ξ k hk i token

/-- Value completeness under a right-nested ordinary-closure spine. -/
def ValueUnderFunctionSpine {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)) :
    Prop :=
  ∀ {s : ChannelConfig C} {arg : RuntimeValue C}
    {answer : HSemanticComp D₀ j₀},
    s.control = .value arg →
    s.stack = functionStack frames →
    FunctionSpineOk frames →
    ChannelConfig.WellScoped s →
    ChannelConfigRel D₀ j₀ realize s answer →
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer

/-- Pauli-X under a nonempty function-frame spine, given value
completeness at that stack. -/
theorem pauliX_under_function_spine_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderFunctionSpine D₀ j₀ realize frames)
    {s : ChannelConfig C} {value : C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack = functionStack frames)
    (hok : FunctionSpineOk frames)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsPx :
      {s with control := .term (.prim (.pauliX value))} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  obtain ⟨semanticEnv, kStack, henv, hstack, rfl⟩ :=
    channelConfigRel_term_inv D₀ j₀ hc hrel
  let sVal : ChannelConfig C :=
    {s with
      control := .value (.payload value)
      quantum := applyOperation Qubit.pauliXOp s.quantum}
  have hstep : ChannelInternalStep s sVal := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.prim (.pauliX value))}
          sVal :=
      ChannelInternalStep.pauliXPrimitive (s := s) (value := value)
    exact hsPx.symm ▸ happ
  have hscopedVal : ChannelConfig.WellScoped sVal :=
    ChannelInternalStep.preserve_wellScoped hstep hscoped
  have hrelVal : ChannelConfigRel D₀ j₀ realize sVal
      (kStack
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) (realize value))) :=
    ⟨semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (realize value),
      kStack,
      ControlRel.value _ _ s.env
        (payload_related D₀ j₀ realize value),
      hstack, rfl⟩
  have hval :=
    hVal (s := sVal) (arg := .payload value) rfl hs hok hscopedVal
      hrelVal
  refine
    { related := hrel
      complete := ?_ }
  constructor
  intro selectors i ξ kξ hk
  have hchildEq :=
    hval.complete.selected_result_eq_channelTree_sup_presented
      selectors i ξ kξ hk
  have hden :
      interp (hardwarePrimitive D₀ j₀ realize)
          (.prim (.pauliX value)) semanticEnv =
        taggedEmbed
          (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
            (realize value)) := by
    simp [hardwarePrimitive_pauliX]
  have hne : s.stack ≠ [] := by
    rw [hs]
    exact hok.stack_ne_nil
  let unitVal : HSemanticComp D₀ j₀ :=
    semanticUnit (Q := TTExternalContinuationPower 2)
      (D₀ := D₀) (j₀ := j₀) (realize value)
  let opVal : HSemanticComp D₀ j₀ :=
    taggedEmbed
      (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
        (realize value))
  have hchildCoord :
      kStack unitVal (HardwareAdequacy.encodePath selectors i) kξ =
        sSup (channelTreeResults D₀ j₀ realize sVal selectors i
          kξ) := by
    have hsel :
        HardwareAdequacy.selectPath selectors (kStack unitVal) i kξ =
          kStack unitVal (HardwareAdequacy.encodePath selectors i)
            kξ :=
      congrArg (fun f => f kξ)
        (HardwareAdequacy.selectPath_apply_encode selectors
          (kStack unitVal) i)
    exact hsel.symm.trans hchildEq
  have hselParent :
      HardwareAdequacy.selectPath selectors (kStack opVal) i kξ =
        kStack opVal (HardwareAdequacy.encodePath selectors i) kξ :=
    congrArg (fun f => f kξ)
      (HardwareAdequacy.selectPath_apply_encode selectors
        (kStack opVal) i)
  have hop :
      kStack opVal (HardwareAdequacy.encodePath selectors i) kξ =
        embed (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
            (realize value))
          (ScottMap.const
            (kStack unitVal (HardwareAdequacy.encodePath selectors i)
              kξ)) :=
    stackRel_ofOperation_eval D₀ j₀ hstack hne
      Qubit.pauliXOp (realize value)
      (HardwareAdequacy.encodePath selectors i) kξ
  rw [hden, hselParent, hop, hchildCoord, embed_ofOperation_const_sSup]
  apply le_antisymm
  · apply sSup_le
    rintro T ⟨r, ⟨fuel, child, R, hdepth, rfl⟩, rfl⟩
    apply le_sSup
    refine ⟨fuel + 1, ChannelTree.internal hstep child,
      wrapInternalRealization D₀ j₀ realize hstep child R, ?_, ?_⟩
    · change child.depth + 1 ≤ fuel + 1
      omega
    · exact
        (restrictedResult_internal_pauliX D₀ j₀ realize hstep hc
          child
          (wrapInternalRealization D₀ j₀ realize hstep child R)
          selectors i ξ kξ hk).symm
  · apply sSup_le
    rintro T ⟨_, tree, R, _, rfl⟩
    cases tree with
    | terminal hterm =>
        cases hterm.control_eq.symm.trans hc
    | @internal _ t' h next =>
        have ht : t' = sVal :=
          ChannelInternalStep.eq_config_of_pauliX h hc
        subst t'
        rw [restrictedResult_internal_pauliX D₀ j₀ realize h hc
          next R selectors i ξ kξ hk]
        apply le_sSup
        refine ⟨restrictedResult D₀ j₀ realize next
            (internalChildRealization D₀ j₀ realize h next R)
            selectors i kξ,
          ⟨next.depth, next,
            internalChildRealization D₀ j₀ realize h next R,
            le_rfl, rfl⟩, rfl⟩
    | external _ hex _ =>
        exact False.elim (ChannelExternalStep.not_prim hex hc)
    | probability _ _ _ _ =>
        cases hc
    | probabilityZero _ =>
        cases hc
    | probabilityOne _ =>
        cases hc
    | measurement _ _ =>
        cases hc

/-- Administrative NoApp under a function-frame spine, given value
completeness at that stack. -/
theorem admin_noapp_under_function_spine_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderFunctionSpine D₀ j₀ realize frames)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack = functionStack frames)
    (hok : FunctionSpineOk frames)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  induction code generalizing s answer with
  | var z =>
      have hctl := hscoped.left
      rw [hc] at hctl
      obtain ⟨v, hlookup⟩ := hctl.right z (by simp [free])
      have hsVar :
          {s with control := .term (.var z)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelVar : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.var z)} answer :=
        hsVar.symm ▸ hrel
      have hrelVal :=
        channel_config_variable D₀ j₀ hlookup hrelVar
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value v} :=
        ⟨⟨hctl.left, hctl.left z v hlookup⟩, hscoped.right⟩
      have hval :=
        hVal (s := {s with control := .value v}) (arg := v)
          rfl hs hok hscopedVal hrelVal
      exact variable_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hlookup hrel hval
  | app _ _ =>
      exact False.elim hadmin
  | lam z M _ih =>
      have hsLam :
          {s with control := .term (.lam z M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelLam : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.lam z M)} answer :=
        hsLam.symm ▸ hrel
      have hrelVal :=
        channel_config_lambda D₀ j₀ (s := s) hrelLam
      have hstepLam : ChannelInternalStep s
          {s with control := .value (.closure z M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.lam z M)}
              {s with control := .value (.closure z M s.env)} :=
          ChannelInternalStep.lambda (s := s) (x := z) (body := M)
        exact hsLam.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.closure z M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepLam hscoped
      have hval :=
        hVal (s := {s with control := .value (.closure z M s.env)})
          (arg := .closure z M s.env) rfl hs hok hscopedVal hrelVal
      exact lambda_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hrel hval
  | recLam self z M _ih =>
      have hsRec :
          {s with control := .term (.recLam self z M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelRec : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.recLam self z M)} answer :=
        hsRec.symm ▸ hrel
      have hrelVal :=
        channel_config_recursive D₀ j₀ (s := s) hrelRec
      have hstepRec : ChannelInternalStep s
          {s with control := .value (.recClosure self z M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.recLam self z M)}
              {s with
                control := .value (.recClosure self z M s.env)} :=
          ChannelInternalStep.recursive (s := s) (self := self)
            (arg := z) (body := M)
        exact hsRec.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.recClosure self z M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepRec hscoped
      have hval :=
        hVal
          (s :=
            {s with control := .value (.recClosure self z M s.env)})
          (arg := .recClosure self z M s.env) rfl hs hok hscopedVal
          hrelVal
      exact recLam_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hrel hval
  | intern left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hadmin
      have hscopedL :=
        wellScoped_term_child (child := left) hc hscoped
          (fun z hz => by simp [free, hz])
      have hscopedR :=
        wellScoped_term_child (child := right) hc hscoped
          (fun z hz => by simp [free, hz])
      refine intern_related_presentedChannelConfigCompleteness
        D₀ j₀ realize hc hrel ?_ ?_
      · intro semanticEnv k henv hstack
        exact ihL hnaL (s := {s with control := .term left}) rfl hs
          hscopedL
          ⟨interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv, k,
            ControlRel.term left s.env semanticEnv henv, hstack, rfl⟩
      · intro semanticEnv k henv hstack
        exact ihR hnaR (s := {s with control := .term right}) rfl hs
          hscopedR
          ⟨interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv, k,
            ControlRel.term right s.env semanticEnv henv, hstack, rfl⟩
  | extern _ _ _ _ =>
      exact False.elim hadmin
  | prob p left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hadmin
      have hscopedL :=
        wellScoped_term_child (child := left) hc hscoped
          (fun z hz => by simp [free, hz])
      have hscopedR :=
        wellScoped_term_child (child := right) hc hscoped
          (fun z hz => by simp [free, hz])
      refine prob_related_presentedChannelConfigCompleteness
        D₀ j₀ realize hc hrel ?_ ?_
      · intro semanticEnv k quantum henv hstack
        exact ihL hnaL
          (s := {s with control := .term left, quantum := quantum})
          rfl hs ⟨hscopedL.left, hscopedL.right⟩
          ⟨interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv, k,
            ControlRel.term left s.env semanticEnv henv, hstack, rfl⟩
      · intro semanticEnv k quantum henv hstack
        exact ihR hnaR
          (s := {s with control := .term right, quantum := quantum})
          rfl hs ⟨hscopedR.left, hscopedR.right⟩
          ⟨interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv, k,
            ControlRel.term right s.env semanticEnv henv, hstack, rfl⟩
  | prim prim =>
      cases prim with
      | ret value =>
          have hsRet :
              {s with control := .term (.prim (.ret value))} = s :=
            ChannelConfig.ext hc.symm rfl rfl rfl
          have hrelRet : ChannelConfigRel D₀ j₀ realize
              {s with control := .term (.prim (.ret value))} answer :=
            hsRet.symm ▸ hrel
          have hrelVal :=
            channel_config_return D₀ j₀ hrelRet
          have hstepRet : ChannelInternalStep s
              {s with control := .value (.payload value)} := by
            have happ :
                ChannelInternalStep
                  {s with control := .term (.prim (.ret value))}
                  {s with control := .value (.payload value)} :=
              ChannelInternalStep.returnPrimitive (s := s)
                (value := value)
            exact hsRet.symm ▸ happ
          have hscopedVal : ChannelConfig.WellScoped
              {s with control := .value (.payload value)} :=
            ChannelInternalStep.preserve_wellScoped hstepRet hscoped
          have hval :=
            hVal (s := {s with control := .value (.payload value)})
              (arg := .payload value) rfl hs hok hscopedVal hrelVal
          exact return_presentedChannelConfigCompleteness D₀ j₀ realize
            hc hrel hval
      | pauliX value =>
          exact
            pauliX_under_function_spine_of_value
              D₀ j₀ realize frames hVal hc hs hok hscoped hrel
      | measureZ _ _ =>
          exact False.elim hadmin

/-- List-of-frames completeness for a right-nested ordinary-closure
spine: a value, then administrative NoApp, at that stack. -/
theorem function_spine_presented
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : FunctionSpineOk frames) :
    ValueUnderFunctionSpine D₀ j₀ realize frames ∧
      (∀ {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
          {answer : HSemanticComp D₀ j₀},
        AdminNoApp code →
        s.control = .term code →
        s.stack = functionStack frames →
        FunctionSpineOk frames →
        ChannelConfig.WellScoped s →
        ChannelConfigRel D₀ j₀ realize s answer →
        PresentedChannelConfigCompleteness D₀ j₀ realize s answer) := by
  induction frames with
  | nil => exact False.elim hok
  | cons p rest ih =>
      rcases p with ⟨x, body, clo⟩
      cases rest with
      | nil =>
          have hnoapp : NoApp body := FunctionSpineOk_singleton.mp hok
          have hval : ValueUnderFunctionSpine D₀ j₀ realize
              [(x, body, clo)] := by
            intro s arg answer hc hs _hok hscoped hrel
            have hs' : s.stack = [.function (.closure x body clo)] := by
              simpa [functionStack] using hs
            exact
              value_under_closure_nil_presentedChannelConfigCompleteness
                D₀ j₀ realize hc hs' hnoapp hscoped hrel
          exact ⟨hval,
            fun {s} {code} {answer} =>
              admin_noapp_under_function_spine_of_value
                D₀ j₀ realize [(x, body, clo)] hval⟩
      | cons q rest' =>
          have ⟨hadminY, hokRest⟩ :=
            (FunctionSpineOk_cons_cons
              (x := x) (body := body) (clo := clo) (y := q)
              (rest := rest')).mp hok
          obtain ⟨ihVal, ihAdmin⟩ := ih hokRest
          have hval : ValueUnderFunctionSpine D₀ j₀ realize
              ((x, body, clo) :: q :: rest') := by
            intro s arg answer hc hs _hok' hscoped hrel
            have hsEq :
                {s with
                  control := .value arg
                  stack :=
                    .function (.closure x body clo) ::
                      functionStack (q :: rest')} = s :=
              ChannelConfig.ext hc.symm rfl hs.symm rfl
            have hrel' : ChannelConfigRel D₀ j₀ realize
                {s with
                  control := .value arg
                  stack :=
                    .function (.closure x body clo) ::
                      functionStack (q :: rest')}
                answer :=
              hsEq.symm ▸ hrel
            have hrelBody :=
              channel_config_beta D₀ j₀ (s := s) (x := x)
                (body := body) (closureEnv := clo) (arg := arg)
                (rest := functionStack (q :: rest')) hrel'
            let sBody : ChannelConfig C :=
              {s with
                control := .term body
                env := RuntimeEnv.bind x arg clo
                stack := functionStack (q :: rest')}
            have hstepBeta : ChannelInternalStep s sBody := by
              have happ :
                  ChannelInternalStep
                    {s with
                      control := .value arg
                      stack :=
                        .function (.closure x body clo) ::
                          functionStack (q :: rest')}
                    sBody :=
                ChannelInternalStep.beta (s := s) (x := x)
                  (body := body) (closureEnv := clo) (arg := arg)
                  (rest := functionStack (q :: rest'))
              exact hsEq.symm ▸ happ
            have hscopedBody : ChannelConfig.WellScoped sBody :=
              ChannelInternalStep.preserve_wellScoped hstepBeta hscoped
            have hchild :=
              ihAdmin (s := sBody) (code := body) hadminY rfl rfl
                hokRest hscopedBody hrelBody
            exact beta_presentedChannelConfigCompleteness D₀ j₀ realize
              (s := s) (x := x) (body := body) (closureEnv := clo)
              (arg := arg) (rest := functionStack (q :: rest'))
              hc hs hrel hchild
          exact ⟨hval,
            fun {s} {code} {answer} =>
              admin_noapp_under_function_spine_of_value
                D₀ j₀ realize ((x, body, clo) :: q :: rest') hval⟩

theorem value_under_function_spine_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : FunctionSpineOk frames)
    {s : ChannelConfig C} {arg : RuntimeValue C}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .value arg)
    (hs : s.stack = functionStack frames)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer :=
  (function_spine_presented D₀ j₀ realize frames hok).1
    hc hs hok hscoped hrel

theorem admin_noapp_under_function_spine_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : FunctionSpineOk frames)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack = functionStack frames)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer :=
  (function_spine_presented D₀ j₀ realize frames hok).2
    hadmin hc hs hok hscoped hrel

/-- Inner `app (lam y bodyY) arg` under a residual function-frame
spine. -/
theorem app_lam_under_function_spine_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : FunctionSpineOk rest)
    {s : ChannelConfig C} {y : Name}
    {bodyY arg : Term (QubitPrimitive C)} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.app (.lam y bodyY) arg))
    (hs : s.stack = functionStack rest)
    (hadminY : AdminNoApp bodyY) (hadminArg : AdminNoApp arg)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsApp :
      {s with control := .term (.app (.lam y bodyY) arg)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app (.lam y bodyY) arg)} answer :=
    hsApp.symm ▸ hrel
  have hrelLam :=
    channel_config_application D₀ j₀ (s := s)
      (fn := .lam y bodyY) (arg := arg) hrelApp
  have hrelClo :=
    channel_config_lambda D₀ j₀
      (s := {s with stack := .argument arg s.env :: s.stack})
      hrelLam
  have hrelArg :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {s with
          control := .value (.closure y bodyY s.env)
          stack := .argument arg s.env :: s.stack})
      (fn := .closure y bodyY s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack) hrelClo
  let sArg : ChannelConfig C :=
    {s with
      control := .term arg
      stack := .function (.closure y bodyY s.env) :: s.stack}
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.lam y bodyY)
        stack := .argument arg s.env :: s.stack} := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app (.lam y bodyY) arg)}
          {s with
            control := .term (.lam y bodyY)
            stack := .argument arg s.env :: s.stack} :=
      ChannelInternalStep.application (s := s)
        (fn := .lam y bodyY) (arg := arg)
    exact hsApp.symm ▸ happ
  have hstepLam : ChannelInternalStep
      {s with
        control := .term (.lam y bodyY)
        stack := .argument arg s.env :: s.stack}
      {s with
        control := .value (.closure y bodyY s.env)
        stack := .argument arg s.env :: s.stack} :=
    ChannelInternalStep.lambda
      (s := {s with stack := .argument arg s.env :: s.stack})
      (x := y) (body := bodyY)
  have hstepArg : ChannelInternalStep
      {s with
        control := .value (.closure y bodyY s.env)
        stack := .argument arg s.env :: s.stack}
      sArg :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {s with
          control := .value (.closure y bodyY s.env)
          stack := .argument arg s.env :: s.stack})
      (fn := .closure y bodyY s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack)
  have hscopedArg : ChannelConfig.WellScoped sArg :=
    ChannelInternalStep.preserve_wellScoped hstepArg
      (ChannelInternalStep.preserve_wellScoped hstepLam
        (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
  have hsArg :
      sArg.stack = functionStack ((y, bodyY, s.env) :: rest) := by
    simp [sArg, hs]
  have hokFull : FunctionSpineOk ((y, bodyY, s.env) :: rest) :=
    FunctionSpineOk.cons hok.ne_nil hadminY hok
  have harg :
      PresentedChannelConfigCompleteness D₀ j₀ realize sArg answer :=
    admin_noapp_under_function_spine_presentedChannelConfigCompleteness
      D₀ j₀ realize ((y, bodyY, s.env) :: rest) hokFull
      (s := sArg) (code := arg) hadminArg rfl hsArg hscopedArg
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term arg
              env := s.env
              stack :=
                .function (.closure y bodyY s.env) :: s.stack}
            _
        exact hrelArg)
  exact stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := y) (body := bodyY) (arg := arg) hc hrel harg

/-- Closed right-nested
`app (lam x bodyX) (app (lam y bodyY) (app (lam z bodyZ) arg))`. -/
theorem closed_nested3_lam_admin_noapp_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x y z : Name) (bodyX bodyY bodyZ arg : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.lam x bodyX)
        (.app (.lam y bodyY) (.app (.lam z bodyZ) arg))))
    (hnoappX : NoApp bodyX)
    (hadminY : AdminNoApp bodyY) (hadminZ : AdminNoApp bodyZ)
    (hadminArg : AdminNoApp arg)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.app (.lam x bodyX)
          (.app (.lam y bodyY) (.app (.lam z bodyZ) arg)))
        quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.lam x bodyX)
          (.app (.lam y bodyY) (.app (.lam z bodyZ) arg)))
        semanticEnv) := by
  let inner2 : Term (QubitPrimitive C) := .app (.lam z bodyZ) arg
  let inner1 : Term (QubitPrimitive C) := .app (.lam y bodyY) inner2
  let code : Term (QubitPrimitive C) := .app (.lam x bodyX) inner1
  let s : ChannelConfig C := initialChannelConfig code quantum
  have hc : s.control = .term code := rfl
  have hrel :=
    initialChannelConfig_related D₀ j₀ realize code quantum semanticEnv
  have hscoped :=
    initialChannelConfig_wellScoped hclosed quantum
  have hsApp :
      {s with control := .term (.app (.lam x bodyX) inner1)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app (.lam x bodyX) inner1)}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    hsApp.symm ▸ hrel
  have hrelLam :=
    channel_config_application D₀ j₀ (s := s)
      (fn := .lam x bodyX) (arg := inner1) hrelApp
  have hrelClo :=
    channel_config_lambda D₀ j₀
      (s := {s with stack := .argument inner1 s.env :: s.stack})
      hrelLam
  have hrelInner :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {s with
          control := .value (.closure x bodyX s.env)
          stack := .argument inner1 s.env :: s.stack})
      (fn := .closure x bodyX s.env) (arg := inner1)
      (callEnv := s.env) (rest := s.stack) hrelClo
  let sInner : ChannelConfig C :=
    {s with
      control := .term inner1
      stack := .function (.closure x bodyX s.env) :: s.stack}
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.lam x bodyX)
        stack := .argument inner1 s.env :: s.stack} := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app (.lam x bodyX) inner1)}
          {s with
            control := .term (.lam x bodyX)
            stack := .argument inner1 s.env :: s.stack} :=
      ChannelInternalStep.application (s := s)
        (fn := .lam x bodyX) (arg := inner1)
    exact hsApp.symm ▸ happ
  have hstepLam : ChannelInternalStep
      {s with
        control := .term (.lam x bodyX)
        stack := .argument inner1 s.env :: s.stack}
      {s with
        control := .value (.closure x bodyX s.env)
        stack := .argument inner1 s.env :: s.stack} :=
    ChannelInternalStep.lambda
      (s := {s with stack := .argument inner1 s.env :: s.stack})
      (x := x) (body := bodyX)
  have hstepInner : ChannelInternalStep
      {s with
        control := .value (.closure x bodyX s.env)
        stack := .argument inner1 s.env :: s.stack}
      sInner :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {s with
          control := .value (.closure x bodyX s.env)
          stack := .argument inner1 s.env :: s.stack})
      (fn := .closure x bodyX s.env) (arg := inner1)
      (callEnv := s.env) (rest := s.stack)
  have hscopedInner : ChannelConfig.WellScoped sInner :=
    ChannelInternalStep.preserve_wellScoped hstepInner
      (ChannelInternalStep.preserve_wellScoped hstepLam
        (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
  have hsInner :
      sInner.stack = functionStack [(x, bodyX, s.env)] := by
    simp [sInner, s, initialChannelConfig, ofConfig, initialConfig]
  have hokX : FunctionSpineOk [(x, bodyX, s.env)] := hnoappX
  have hsApp1 :
      {sInner with control := .term (.app (.lam y bodyY) inner2)} =
        sInner :=
    ChannelConfig.ext rfl rfl rfl rfl
  have hrelApp1 : ChannelConfigRel D₀ j₀ realize
      {sInner with control := .term (.app (.lam y bodyY) inner2)}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) := by
    change ChannelConfigRel D₀ j₀ realize
        {s with
          control := .term inner1
          env := s.env
          stack := .function (.closure x bodyX s.env) :: s.stack}
        _
    exact hrelInner
  have hrelLam1 :=
    channel_config_application D₀ j₀ (s := sInner)
      (fn := .lam y bodyY) (arg := inner2) hrelApp1
  have hrelClo1 :=
    channel_config_lambda D₀ j₀
      (s := {sInner with stack := .argument inner2 sInner.env :: sInner.stack})
      hrelLam1
  have hrelInner2 :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {sInner with
          control := .value (.closure y bodyY sInner.env)
          stack := .argument inner2 sInner.env :: sInner.stack})
      (fn := .closure y bodyY sInner.env) (arg := inner2)
      (callEnv := sInner.env) (rest := sInner.stack) hrelClo1
  let sInner2 : ChannelConfig C :=
    {sInner with
      control := .term inner2
      stack := .function (.closure y bodyY sInner.env) :: sInner.stack}
  have hstepApp1 : ChannelInternalStep sInner
      {sInner with
        control := .term (.lam y bodyY)
        stack := .argument inner2 sInner.env :: sInner.stack} := by
    have happ :
        ChannelInternalStep
          {sInner with control := .term (.app (.lam y bodyY) inner2)}
          {sInner with
            control := .term (.lam y bodyY)
            stack := .argument inner2 sInner.env :: sInner.stack} :=
      ChannelInternalStep.application (s := sInner)
        (fn := .lam y bodyY) (arg := inner2)
    exact hsApp1.symm ▸ happ
  have hstepLam1 : ChannelInternalStep
      {sInner with
        control := .term (.lam y bodyY)
        stack := .argument inner2 sInner.env :: sInner.stack}
      {sInner with
        control := .value (.closure y bodyY sInner.env)
        stack := .argument inner2 sInner.env :: sInner.stack} :=
    ChannelInternalStep.lambda
      (s := {sInner with stack := .argument inner2 sInner.env :: sInner.stack})
      (x := y) (body := bodyY)
  have hstepInner2 : ChannelInternalStep
      {sInner with
        control := .value (.closure y bodyY sInner.env)
        stack := .argument inner2 sInner.env :: sInner.stack}
      sInner2 :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {sInner with
          control := .value (.closure y bodyY sInner.env)
          stack := .argument inner2 sInner.env :: sInner.stack})
      (fn := .closure y bodyY sInner.env) (arg := inner2)
      (callEnv := sInner.env) (rest := sInner.stack)
  have hscopedInner2 : ChannelConfig.WellScoped sInner2 :=
    ChannelInternalStep.preserve_wellScoped hstepInner2
      (ChannelInternalStep.preserve_wellScoped hstepLam1
        (ChannelInternalStep.preserve_wellScoped hstepApp1
          hscopedInner))
  have hsInner2 :
      sInner2.stack =
        functionStack [(y, bodyY, s.env), (x, bodyX, s.env)] := by
    simp [sInner2, sInner, s, initialChannelConfig, ofConfig,
      initialConfig]
  have hokXY : FunctionSpineOk [(y, bodyY, s.env), (x, bodyX, s.env)] :=
    ⟨hadminY, hokX⟩
  have hinner2 :
      PresentedChannelConfigCompleteness D₀ j₀ realize sInner2
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    app_lam_under_function_spine_presentedChannelConfigCompleteness
      D₀ j₀ realize [(y, bodyY, s.env), (x, bodyX, s.env)] hokXY
      (s := sInner2) (y := z) (bodyY := bodyZ) (arg := arg)
      rfl hsInner2 hadminZ hadminArg hscopedInner2
      (by
        change ChannelConfigRel D₀ j₀ realize
            {sInner with
              control := .term inner2
              env := sInner.env
              stack :=
                .function (.closure y bodyY sInner.env) ::
                  sInner.stack}
            _
        exact hrelInner2)
  have hinner1 :
      PresentedChannelConfigCompleteness D₀ j₀ realize sInner
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
      (s := sInner) (x := y) (body := bodyY) (arg := inner2) rfl
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term inner1
              env := s.env
              stack := .function (.closure x bodyX s.env) :: s.stack}
            _
        exact hrelInner)
      hinner2
  exact (stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := x) (body := bodyX) (arg := inner1) hc hrel
    hinner1).complete

/-- Token adequacy for closed right-nested
`app (lam x bodyX) (app (lam y bodyY) (app (lam z bodyZ) arg))`. -/
theorem closed_nested3_lam_admin_noapp_presented_token_adequacy
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x y z : Name) (bodyX bodyY bodyZ arg : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.lam x bodyX)
        (.app (.lam y bodyY) (.app (.lam z bodyZ) arg))))
    (hnoappX : NoApp bodyX)
    (hadminY : AdminNoApp bodyY) (hadminZ : AdminNoApp bodyZ)
    (hadminArg : AdminNoApp arg)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize)
          (.app (.lam x bodyX)
            (.app (.lam y bodyY) (.app (.lam z bodyZ) arg)))
          semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig
            (.app (.lam x bodyX)
              (.app (.lam y bodyY) (.app (.lam z bodyZ) arg)))
            quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig
      (.app (.lam x bodyX)
        (.app (.lam y bodyY) (.app (.lam z bodyZ) arg)))
      quantum)
    (interp (hardwarePrimitive D₀ j₀ realize)
      (.app (.lam x bodyX)
        (.app (.lam y bodyY) (.app (.lam z bodyZ) arg)))
      semanticEnv)
    (closed_nested3_lam_admin_noapp_presented_channelTreeCompleteness
      D₀ j₀ realize x y z bodyX bodyY bodyZ arg hclosed hnoappX
      hadminY hadminZ hadminArg quantum semanticEnv)
    selectors ξ k hk i token

/-- Value completeness under a function spine over leftover argument
frames. -/
def ValueUnderMixedSpine {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C)) : Prop :=
  ∀ {s : ChannelConfig C} {arg : RuntimeValue C}
    {answer : HSemanticComp D₀ j₀},
    s.control = .value arg →
    s.stack = mixedStack fns args →
    MixedSpineOk fns args →
    ArgumentFramesOk args →
    ChannelConfig.WellScoped s →
    ChannelConfigRel D₀ j₀ realize s answer →
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer

/-- Pauli-X under a mixed function/argument spine, given value
completeness at that stack. -/
theorem pauliX_under_mixed_spine_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderMixedSpine D₀ j₀ realize fns args)
    {s : ChannelConfig C} {value : C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack = mixedStack fns args)
    (hok : MixedSpineOk fns args) (hargs : ArgumentFramesOk args)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsPx :
      {s with control := .term (.prim (.pauliX value))} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  obtain ⟨semanticEnv, kStack, henv, hstack, rfl⟩ :=
    channelConfigRel_term_inv D₀ j₀ hc hrel
  let sVal : ChannelConfig C :=
    {s with
      control := .value (.payload value)
      quantum := applyOperation Qubit.pauliXOp s.quantum}
  have hstep : ChannelInternalStep s sVal := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.prim (.pauliX value))}
          sVal :=
      ChannelInternalStep.pauliXPrimitive (s := s) (value := value)
    exact hsPx.symm ▸ happ
  have hscopedVal : ChannelConfig.WellScoped sVal :=
    ChannelInternalStep.preserve_wellScoped hstep hscoped
  have hrelVal : ChannelConfigRel D₀ j₀ realize sVal
      (kStack
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) (realize value))) :=
    ⟨semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (realize value),
      kStack,
      ControlRel.value _ _ s.env
        (payload_related D₀ j₀ realize value),
      hstack, rfl⟩
  have hval :=
    hVal (s := sVal) (arg := .payload value) rfl hs hok hargs
      hscopedVal hrelVal
  refine
    { related := hrel
      complete := ?_ }
  constructor
  intro selectors i ξ kξ hk
  have hchildEq :=
    hval.complete.selected_result_eq_channelTree_sup_presented
      selectors i ξ kξ hk
  have hden :
      interp (hardwarePrimitive D₀ j₀ realize)
          (.prim (.pauliX value)) semanticEnv =
        taggedEmbed
          (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
            (realize value)) := by
    simp [hardwarePrimitive_pauliX]
  have hne : s.stack ≠ [] := by
    rw [hs]
    exact hok.stack_ne_nil
  let unitVal : HSemanticComp D₀ j₀ :=
    semanticUnit (Q := TTExternalContinuationPower 2)
      (D₀ := D₀) (j₀ := j₀) (realize value)
  let opVal : HSemanticComp D₀ j₀ :=
    taggedEmbed
      (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
        (realize value))
  have hchildCoord :
      kStack unitVal (HardwareAdequacy.encodePath selectors i) kξ =
        sSup (channelTreeResults D₀ j₀ realize sVal selectors i
          kξ) := by
    have hsel :
        HardwareAdequacy.selectPath selectors (kStack unitVal) i kξ =
          kStack unitVal (HardwareAdequacy.encodePath selectors i)
            kξ :=
      congrArg (fun f => f kξ)
        (HardwareAdequacy.selectPath_apply_encode selectors
          (kStack unitVal) i)
    exact hsel.symm.trans hchildEq
  have hselParent :
      HardwareAdequacy.selectPath selectors (kStack opVal) i kξ =
        kStack opVal (HardwareAdequacy.encodePath selectors i) kξ :=
    congrArg (fun f => f kξ)
      (HardwareAdequacy.selectPath_apply_encode selectors
        (kStack opVal) i)
  have hop :
      kStack opVal (HardwareAdequacy.encodePath selectors i) kξ =
        embed (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
            (realize value))
          (ScottMap.const
            (kStack unitVal (HardwareAdequacy.encodePath selectors i)
              kξ)) :=
    stackRel_ofOperation_eval D₀ j₀ hstack hne
      Qubit.pauliXOp (realize value)
      (HardwareAdequacy.encodePath selectors i) kξ
  rw [hden, hselParent, hop, hchildCoord, embed_ofOperation_const_sSup]
  apply le_antisymm
  · apply sSup_le
    rintro T ⟨r, ⟨fuel, child, R, hdepth, rfl⟩, rfl⟩
    apply le_sSup
    refine ⟨fuel + 1, ChannelTree.internal hstep child,
      wrapInternalRealization D₀ j₀ realize hstep child R, ?_, ?_⟩
    · change child.depth + 1 ≤ fuel + 1
      omega
    · exact
        (restrictedResult_internal_pauliX D₀ j₀ realize hstep hc
          child
          (wrapInternalRealization D₀ j₀ realize hstep child R)
          selectors i ξ kξ hk).symm
  · apply sSup_le
    rintro T ⟨_, tree, R, _, rfl⟩
    cases tree with
    | terminal hterm =>
        cases hterm.control_eq.symm.trans hc
    | @internal _ t' h next =>
        have ht : t' = sVal :=
          ChannelInternalStep.eq_config_of_pauliX h hc
        subst t'
        rw [restrictedResult_internal_pauliX D₀ j₀ realize h hc
          next R selectors i ξ kξ hk]
        apply le_sSup
        refine ⟨restrictedResult D₀ j₀ realize next
            (internalChildRealization D₀ j₀ realize h next R)
            selectors i kξ,
          ⟨next.depth, next,
            internalChildRealization D₀ j₀ realize h next R,
            le_rfl, rfl⟩, rfl⟩
    | external _ hex _ =>
        exact False.elim (ChannelExternalStep.not_prim hex hc)
    | probability _ _ _ _ =>
        cases hc
    | probabilityZero _ =>
        cases hc
    | probabilityOne _ =>
        cases hc
    | measurement _ _ =>
        cases hc

/-- Administrative NoApp under a mixed spine, given value completeness
at that stack. -/
theorem admin_noapp_under_mixed_spine_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderMixedSpine D₀ j₀ realize fns args)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack = mixedStack fns args)
    (hok : MixedSpineOk fns args) (hargs : ArgumentFramesOk args)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  induction code generalizing s answer with
  | var z =>
      have hctl := hscoped.left
      rw [hc] at hctl
      obtain ⟨v, hlookup⟩ := hctl.right z (by simp [free])
      have hsVar :
          {s with control := .term (.var z)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelVar : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.var z)} answer :=
        hsVar.symm ▸ hrel
      have hrelVal :=
        channel_config_variable D₀ j₀ hlookup hrelVar
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value v} :=
        ⟨⟨hctl.left, hctl.left z v hlookup⟩, hscoped.right⟩
      have hval :=
        hVal (s := {s with control := .value v}) (arg := v)
          rfl hs hok hargs hscopedVal hrelVal
      exact variable_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hlookup hrel hval
  | app _ _ =>
      exact False.elim hadmin
  | lam z M _ih =>
      have hsLam :
          {s with control := .term (.lam z M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelLam : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.lam z M)} answer :=
        hsLam.symm ▸ hrel
      have hrelVal :=
        channel_config_lambda D₀ j₀ (s := s) hrelLam
      have hstepLam : ChannelInternalStep s
          {s with control := .value (.closure z M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.lam z M)}
              {s with control := .value (.closure z M s.env)} :=
          ChannelInternalStep.lambda (s := s) (x := z) (body := M)
        exact hsLam.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.closure z M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepLam hscoped
      have hval :=
        hVal (s := {s with control := .value (.closure z M s.env)})
          (arg := .closure z M s.env) rfl hs hok hargs hscopedVal
          hrelVal
      exact lambda_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hrel hval
  | recLam self z M _ih =>
      have hsRec :
          {s with control := .term (.recLam self z M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelRec : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.recLam self z M)} answer :=
        hsRec.symm ▸ hrel
      have hrelVal :=
        channel_config_recursive D₀ j₀ (s := s) hrelRec
      have hstepRec : ChannelInternalStep s
          {s with control := .value (.recClosure self z M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.recLam self z M)}
              {s with
                control := .value (.recClosure self z M s.env)} :=
          ChannelInternalStep.recursive (s := s) (self := self)
            (arg := z) (body := M)
        exact hsRec.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.recClosure self z M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepRec hscoped
      have hval :=
        hVal
          (s :=
            {s with control := .value (.recClosure self z M s.env)})
          (arg := .recClosure self z M s.env) rfl hs hok hargs
          hscopedVal hrelVal
      exact recLam_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hrel hval
  | intern left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hadmin
      have hscopedL :=
        wellScoped_term_child (child := left) hc hscoped
          (fun z hz => by simp [free, hz])
      have hscopedR :=
        wellScoped_term_child (child := right) hc hscoped
          (fun z hz => by simp [free, hz])
      refine intern_related_presentedChannelConfigCompleteness
        D₀ j₀ realize hc hrel ?_ ?_
      · intro semanticEnv k henv hstack
        exact ihL hnaL (s := {s with control := .term left}) rfl hs
          hscopedL
          ⟨interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv, k,
            ControlRel.term left s.env semanticEnv henv, hstack, rfl⟩
      · intro semanticEnv k henv hstack
        exact ihR hnaR (s := {s with control := .term right}) rfl hs
          hscopedR
          ⟨interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv, k,
            ControlRel.term right s.env semanticEnv henv, hstack, rfl⟩
  | extern _ _ _ _ =>
      exact False.elim hadmin
  | prob p left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hadmin
      have hscopedL :=
        wellScoped_term_child (child := left) hc hscoped
          (fun z hz => by simp [free, hz])
      have hscopedR :=
        wellScoped_term_child (child := right) hc hscoped
          (fun z hz => by simp [free, hz])
      refine prob_related_presentedChannelConfigCompleteness
        D₀ j₀ realize hc hrel ?_ ?_
      · intro semanticEnv k quantum henv hstack
        exact ihL hnaL
          (s := {s with control := .term left, quantum := quantum})
          rfl hs ⟨hscopedL.left, hscopedL.right⟩
          ⟨interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv, k,
            ControlRel.term left s.env semanticEnv henv, hstack, rfl⟩
      · intro semanticEnv k quantum henv hstack
        exact ihR hnaR
          (s := {s with control := .term right, quantum := quantum})
          rfl hs ⟨hscopedR.left, hscopedR.right⟩
          ⟨interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv, k,
            ControlRel.term right s.env semanticEnv henv, hstack, rfl⟩
  | prim prim =>
      cases prim with
      | ret value =>
          have hsRet :
              {s with control := .term (.prim (.ret value))} = s :=
            ChannelConfig.ext hc.symm rfl rfl rfl
          have hrelRet : ChannelConfigRel D₀ j₀ realize
              {s with control := .term (.prim (.ret value))} answer :=
            hsRet.symm ▸ hrel
          have hrelVal :=
            channel_config_return D₀ j₀ hrelRet
          have hstepRet : ChannelInternalStep s
              {s with control := .value (.payload value)} := by
            have happ :
                ChannelInternalStep
                  {s with control := .term (.prim (.ret value))}
                  {s with control := .value (.payload value)} :=
              ChannelInternalStep.returnPrimitive (s := s)
                (value := value)
            exact hsRet.symm ▸ happ
          have hscopedVal : ChannelConfig.WellScoped
              {s with control := .value (.payload value)} :=
            ChannelInternalStep.preserve_wellScoped hstepRet hscoped
          have hval :=
            hVal (s := {s with control := .value (.payload value)})
              (arg := .payload value) rfl hs hok hargs hscopedVal
              hrelVal
          exact return_presentedChannelConfigCompleteness D₀ j₀ realize
            hc hrel hval
      | pauliX value =>
          exact
            pauliX_under_mixed_spine_of_value
              D₀ j₀ realize fns args hVal hc hs hok hargs hscoped hrel
      | measureZ _ _ =>
          exact False.elim hadmin

/-- List-of-frames completeness for a function spine over leftover
argument frames. -/
theorem mixed_spine_presented
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : MixedSpineOk fns args) (hargs : ArgumentFramesOk args) :
    ValueUnderMixedSpine D₀ j₀ realize fns args ∧
      (∀ {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
          {answer : HSemanticComp D₀ j₀},
        AdminNoApp code →
        s.control = .term code →
        s.stack = mixedStack fns args →
        MixedSpineOk fns args →
        ArgumentFramesOk args →
        ChannelConfig.WellScoped s →
        ChannelConfigRel D₀ j₀ realize s answer →
        PresentedChannelConfigCompleteness D₀ j₀ realize s answer) := by
  induction fns with
  | nil => exact False.elim hok
  | cons p rest ih =>
      rcases p with ⟨x, body, clo⟩
      cases rest with
      | nil =>
          have hbody : BodyUnderArgs args.length body :=
            MixedSpineOk_singleton.mp hok
          have hval : ValueUnderMixedSpine D₀ j₀ realize
              [(x, body, clo)] args := by
            intro s arg answer hc hs _hok hargs' hscoped hrel
            have hs' : s.stack =
                .function (.closure x body clo) ::
                  argumentStack args := by
              simpa [mixedStack] using hs
            exact
              value_under_function_argument_frames_presentedChannelConfigCompleteness
                D₀ j₀ realize args hargs' hc hs' hbody hscoped hrel
          exact ⟨hval,
            fun {s} {code} {answer} =>
              admin_noapp_under_mixed_spine_of_value
                D₀ j₀ realize [(x, body, clo)] args hval⟩
      | cons q rest' =>
          have ⟨hadminY, hokRest⟩ :=
            (MixedSpineOk_cons_cons
              (x := x) (body := body) (clo := clo) (y := q)
              (rest := rest') (args := args)).mp hok
          obtain ⟨ihVal, ihAdmin⟩ := ih hokRest
          have hval : ValueUnderMixedSpine D₀ j₀ realize
              ((x, body, clo) :: q :: rest') args := by
            intro s arg answer hc hs _hok' hargs' hscoped hrel
            have hsEq :
                {s with
                  control := .value arg
                  stack :=
                    .function (.closure x body clo) ::
                      mixedStack (q :: rest') args} = s :=
              ChannelConfig.ext hc.symm rfl hs.symm rfl
            have hrel' : ChannelConfigRel D₀ j₀ realize
                {s with
                  control := .value arg
                  stack :=
                    .function (.closure x body clo) ::
                      mixedStack (q :: rest') args}
                answer :=
              hsEq.symm ▸ hrel
            have hrelBody :=
              channel_config_beta D₀ j₀ (s := s) (x := x)
                (body := body) (closureEnv := clo) (arg := arg)
                (rest := mixedStack (q :: rest') args) hrel'
            let sBody : ChannelConfig C :=
              {s with
                control := .term body
                env := RuntimeEnv.bind x arg clo
                stack := mixedStack (q :: rest') args}
            have hstepBeta : ChannelInternalStep s sBody := by
              have happ :
                  ChannelInternalStep
                    {s with
                      control := .value arg
                      stack :=
                        .function (.closure x body clo) ::
                          mixedStack (q :: rest') args}
                    sBody :=
                ChannelInternalStep.beta (s := s) (x := x)
                  (body := body) (closureEnv := clo) (arg := arg)
                  (rest := mixedStack (q :: rest') args)
              exact hsEq.symm ▸ happ
            have hscopedBody : ChannelConfig.WellScoped sBody :=
              ChannelInternalStep.preserve_wellScoped hstepBeta hscoped
            have hchild :=
              ihAdmin (s := sBody) (code := body) hadminY rfl rfl
                hokRest hargs' hscopedBody hrelBody
            exact beta_presentedChannelConfigCompleteness D₀ j₀ realize
              (s := s) (x := x) (body := body) (closureEnv := clo)
              (arg := arg) (rest := mixedStack (q :: rest') args)
              hc hs hrel hchild
          exact ⟨hval,
            fun {s} {code} {answer} =>
              admin_noapp_under_mixed_spine_of_value
                D₀ j₀ realize ((x, body, clo) :: q :: rest') args
                hval⟩

theorem admin_noapp_under_mixed_spine_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : MixedSpineOk fns args) (hargs : ArgumentFramesOk args)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack = mixedStack fns args)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer :=
  (mixed_spine_presented D₀ j₀ realize fns args hok hargs).2
    hadmin hc hs hok hargs hscoped hrel

/-- Inner `app (lam y bodyY) arg` under a mixed function/argument
spine. -/
theorem app_lam_under_mixed_spine_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : MixedSpineOk fns args) (hargs : ArgumentFramesOk args)
    {s : ChannelConfig C} {y : Name}
    {bodyY arg : Term (QubitPrimitive C)} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.app (.lam y bodyY) arg))
    (hs : s.stack = mixedStack fns args)
    (hadminY : AdminNoApp bodyY) (hadminArg : AdminNoApp arg)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsApp :
      {s with control := .term (.app (.lam y bodyY) arg)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app (.lam y bodyY) arg)} answer :=
    hsApp.symm ▸ hrel
  have hrelLam :=
    channel_config_application D₀ j₀ (s := s)
      (fn := .lam y bodyY) (arg := arg) hrelApp
  have hrelClo :=
    channel_config_lambda D₀ j₀
      (s := {s with stack := .argument arg s.env :: s.stack})
      hrelLam
  have hrelArg :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {s with
          control := .value (.closure y bodyY s.env)
          stack := .argument arg s.env :: s.stack})
      (fn := .closure y bodyY s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack) hrelClo
  let sArg : ChannelConfig C :=
    {s with
      control := .term arg
      stack := .function (.closure y bodyY s.env) :: s.stack}
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.lam y bodyY)
        stack := .argument arg s.env :: s.stack} := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app (.lam y bodyY) arg)}
          {s with
            control := .term (.lam y bodyY)
            stack := .argument arg s.env :: s.stack} :=
      ChannelInternalStep.application (s := s)
        (fn := .lam y bodyY) (arg := arg)
    exact hsApp.symm ▸ happ
  have hstepLam : ChannelInternalStep
      {s with
        control := .term (.lam y bodyY)
        stack := .argument arg s.env :: s.stack}
      {s with
        control := .value (.closure y bodyY s.env)
        stack := .argument arg s.env :: s.stack} :=
    ChannelInternalStep.lambda
      (s := {s with stack := .argument arg s.env :: s.stack})
      (x := y) (body := bodyY)
  have hstepArg : ChannelInternalStep
      {s with
        control := .value (.closure y bodyY s.env)
        stack := .argument arg s.env :: s.stack}
      sArg :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {s with
          control := .value (.closure y bodyY s.env)
          stack := .argument arg s.env :: s.stack})
      (fn := .closure y bodyY s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack)
  have hscopedArg : ChannelConfig.WellScoped sArg :=
    ChannelInternalStep.preserve_wellScoped hstepArg
      (ChannelInternalStep.preserve_wellScoped hstepLam
        (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
  have hsArg :
      sArg.stack = mixedStack ((y, bodyY, s.env) :: fns) args := by
    simp [sArg, hs, mixedStack]
  have hokFull : MixedSpineOk ((y, bodyY, s.env) :: fns) args :=
    MixedSpineOk.cons hok.ne_nil hadminY hok
  have harg :
      PresentedChannelConfigCompleteness D₀ j₀ realize sArg answer :=
    admin_noapp_under_mixed_spine_presentedChannelConfigCompleteness
      D₀ j₀ realize ((y, bodyY, s.env) :: fns) args hokFull hargs
      (s := sArg) (code := arg) hadminArg rfl hsArg hscopedArg
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term arg
              env := s.env
              stack :=
                .function (.closure y bodyY s.env) :: s.stack}
            _
        exact hrelArg)
  exact stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := y) (body := bodyY) (arg := arg) hc hrel harg

/-- Closed mixed
`app (app (lam x (lam y body)) (app (lam z bodyZ) arg)) arg2`. -/
theorem closed_mixed_lam_app_lam_admin_noapp_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x y z : Name) (body bodyZ arg arg2 : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.app (.lam x (.lam y body)) (.app (.lam z bodyZ) arg))
        arg2))
    (hnoapp : NoApp body)
    (hadminZ : AdminNoApp bodyZ)
    (hadminArg : AdminNoApp arg) (hadmin2 : AdminNoApp arg2)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.app (.app (.lam x (.lam y body)) (.app (.lam z bodyZ) arg))
          arg2)
        quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.app (.lam x (.lam y body)) (.app (.lam z bodyZ) arg))
          arg2)
        semanticEnv) := by
  let innerApp : Term (QubitPrimitive C) := .app (.lam z bodyZ) arg
  let inner : Term (QubitPrimitive C) :=
    .app (.lam x (.lam y body)) innerApp
  let code : Term (QubitPrimitive C) := .app inner arg2
  let s : ChannelConfig C := initialChannelConfig code quantum
  have hc : s.control = .term code := rfl
  have hrel :=
    initialChannelConfig_related D₀ j₀ realize code quantum semanticEnv
  have hscoped :=
    initialChannelConfig_wellScoped hclosed quantum
  have hsApp :
      {s with control := .term (.app inner arg2)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app inner arg2)}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    hsApp.symm ▸ hrel
  have hrelInner :=
    channel_config_application D₀ j₀ (s := s) (fn := inner)
      (arg := arg2) hrelApp
  let sInner : ChannelConfig C :=
    {s with
      control := .term inner
      stack := .argument arg2 s.env :: s.stack}
  have hstepApp : ChannelInternalStep s sInner := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app inner arg2)} sInner :=
      ChannelInternalStep.application (s := s) (fn := inner)
        (arg := arg2)
    exact hsApp.symm ▸ happ
  have hscopedInner : ChannelConfig.WellScoped sInner :=
    ChannelInternalStep.preserve_wellScoped hstepApp hscoped
  have hsInner : sInner.stack = argumentStack [(arg2, s.env)] := by
    simp [sInner, s, initialChannelConfig, ofConfig, initialConfig]
  have hsApp1 :
      {sInner with
          control := .term (.app (.lam x (.lam y body)) innerApp)} =
        sInner :=
    ChannelConfig.ext rfl rfl rfl rfl
  have hrelApp1 : ChannelConfigRel D₀ j₀ realize
      {sInner with
        control := .term (.app (.lam x (.lam y body)) innerApp)}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) := by
    change ChannelConfigRel D₀ j₀ realize
        {s with
          control := .term inner
          env := s.env
          stack := .argument arg2 s.env :: s.stack}
        _
    exact hrelInner
  have hrelLam :=
    channel_config_application D₀ j₀ (s := sInner)
      (fn := .lam x (.lam y body)) (arg := innerApp) hrelApp1
  have hrelClo :=
    channel_config_lambda D₀ j₀
      (s :=
        {sInner with
          stack := .argument innerApp sInner.env :: sInner.stack})
      hrelLam
  have hrelArg :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {sInner with
          control := .value (.closure x (.lam y body) sInner.env)
          stack := .argument innerApp sInner.env :: sInner.stack})
      (fn := .closure x (.lam y body) sInner.env) (arg := innerApp)
      (callEnv := sInner.env) (rest := sInner.stack) hrelClo
  let sArg : ChannelConfig C :=
    {sInner with
      control := .term innerApp
      stack :=
        .function (.closure x (.lam y body) sInner.env) ::
          sInner.stack}
  have hstepApp1 : ChannelInternalStep sInner
      {sInner with
        control := .term (.lam x (.lam y body))
        stack := .argument innerApp sInner.env :: sInner.stack} := by
    have happ :
        ChannelInternalStep
          {sInner with
            control := .term (.app (.lam x (.lam y body)) innerApp)}
          {sInner with
            control := .term (.lam x (.lam y body))
            stack := .argument innerApp sInner.env :: sInner.stack} :=
      ChannelInternalStep.application (s := sInner)
        (fn := .lam x (.lam y body)) (arg := innerApp)
    exact hsApp1.symm ▸ happ
  have hstepLam : ChannelInternalStep
      {sInner with
        control := .term (.lam x (.lam y body))
        stack := .argument innerApp sInner.env :: sInner.stack}
      {sInner with
        control := .value (.closure x (.lam y body) sInner.env)
        stack := .argument innerApp sInner.env :: sInner.stack} :=
    ChannelInternalStep.lambda
      (s :=
        {sInner with
          stack := .argument innerApp sInner.env :: sInner.stack})
      (x := x) (body := .lam y body)
  have hstepArg : ChannelInternalStep
      {sInner with
        control := .value (.closure x (.lam y body) sInner.env)
        stack := .argument innerApp sInner.env :: sInner.stack}
      sArg :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {sInner with
          control := .value (.closure x (.lam y body) sInner.env)
          stack := .argument innerApp sInner.env :: sInner.stack})
      (fn := .closure x (.lam y body) sInner.env) (arg := innerApp)
      (callEnv := sInner.env) (rest := sInner.stack)
  have hscopedArg : ChannelConfig.WellScoped sArg :=
    ChannelInternalStep.preserve_wellScoped hstepArg
      (ChannelInternalStep.preserve_wellScoped hstepLam
        (ChannelInternalStep.preserve_wellScoped hstepApp1
          hscopedInner))
  have hsArg :
      sArg.stack =
        mixedStack [(x, .lam y body, s.env)] [(arg2, s.env)] := by
    simp [sArg, sInner, s, initialChannelConfig, ofConfig,
      initialConfig, mixedStack]
  have hok : MixedSpineOk [(x, .lam y body, s.env)] [(arg2, s.env)] := by
    simpa [MixedSpineOk, BodyUnderArgs] using hnoapp
  have hargs : ArgumentFramesOk [(arg2, s.env)] := by
    intro p hp
    simp at hp
    cases hp
    exact hadmin2
  have hinnerApp :
      PresentedChannelConfigCompleteness D₀ j₀ realize sArg
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    app_lam_under_mixed_spine_presentedChannelConfigCompleteness
      D₀ j₀ realize [(x, .lam y body, s.env)] [(arg2, s.env)]
      hok hargs (s := sArg) (y := z) (bodyY := bodyZ) (arg := arg)
      rfl hsArg hadminZ hadminArg hscopedArg
      (by
        change ChannelConfigRel D₀ j₀ realize
            {sInner with
              control := .term innerApp
              env := sInner.env
              stack :=
                .function (.closure x (.lam y body) sInner.env) ::
                  sInner.stack}
            _
        exact hrelArg)
  have hinner :
      PresentedChannelConfigCompleteness D₀ j₀ realize sInner
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
      (s := sInner) (x := x) (body := .lam y body) (arg := innerApp)
      rfl
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term inner
              env := s.env
              stack := .argument arg2 s.env :: s.stack}
            _
        exact hrelInner)
      hinnerApp
  exact (application_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (fn := inner) (arg := arg2) hc hrel hinner).complete

/-- Token adequacy for closed mixed
`app (app (lam x (lam y body)) (app (lam z bodyZ) arg)) arg2`. -/
theorem closed_mixed_lam_app_lam_admin_noapp_presented_token_adequacy
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x y z : Name) (body bodyZ arg arg2 : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.app (.lam x (.lam y body)) (.app (.lam z bodyZ) arg))
        arg2))
    (hnoapp : NoApp body)
    (hadminZ : AdminNoApp bodyZ)
    (hadminArg : AdminNoApp arg) (hadmin2 : AdminNoApp arg2)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize)
          (.app (.app (.lam x (.lam y body))
            (.app (.lam z bodyZ) arg)) arg2)
          semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig
            (.app (.app (.lam x (.lam y body))
              (.app (.lam z bodyZ) arg)) arg2)
            quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig
      (.app (.app (.lam x (.lam y body)) (.app (.lam z bodyZ) arg))
        arg2)
      quantum)
    (interp (hardwarePrimitive D₀ j₀ realize)
      (.app (.app (.lam x (.lam y body)) (.app (.lam z bodyZ) arg))
        arg2)
      semanticEnv)
    (closed_mixed_lam_app_lam_admin_noapp_presented_channelTreeCompleteness
      D₀ j₀ realize x y z body bodyZ arg arg2 hclosed hnoapp
      hadminZ hadminArg hadmin2 quantum semanticEnv)
    selectors ξ k hk i token

/-- A lambda under one leftover argument frame over a residual
function-frame spine. -/
theorem lam_under_argument_function_spine_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : FunctionSpineOk rest)
    {s : ChannelConfig C} {x : Name}
    {body arg : Term (QubitPrimitive C)} {callEnv : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.lam x body))
    (hs : s.stack = .argument arg callEnv :: functionStack rest)
    (hadminBody : AdminNoApp body) (hadminArg : AdminNoApp arg)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsLam :
      {s with control := .term (.lam x body)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelLam : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.lam x body)} answer :=
    hsLam.symm ▸ hrel
  have hrelClo :=
    channel_config_lambda D₀ j₀ (s := s) hrelLam
  have hsrcClo :
      {s with control := .value (.closure x body s.env)} =
        {s with
          control := .value (.closure x body s.env)
          stack := .argument arg callEnv :: functionStack rest} :=
    ChannelConfig.ext rfl rfl hs rfl
  have hrelFn :=
    channel_config_evaluateArgument D₀ j₀
      (s := {s with control := .value (.closure x body s.env)})
      (fn := .closure x body s.env) (arg := arg)
      (callEnv := callEnv) (rest := functionStack rest)
      (hsrcClo ▸ hrelClo)
  have hstepLam : ChannelInternalStep s
      {s with control := .value (.closure x body s.env)} := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.lam x body)}
          {s with control := .value (.closure x body s.env)} :=
      ChannelInternalStep.lambda (s := s) (x := x) (body := body)
    exact hsLam.symm ▸ happ
  have hstepArg : ChannelInternalStep
      {s with control := .value (.closure x body s.env)}
      {s with
        control := .term arg
        env := callEnv
        stack :=
          .function (.closure x body s.env) :: functionStack rest} := by
    have happ :
        ChannelInternalStep
          {s with
            control := .value (.closure x body s.env)
            stack := .argument arg callEnv :: functionStack rest}
          {s with
            control := .term arg
            env := callEnv
            stack :=
              .function (.closure x body s.env) ::
                functionStack rest} :=
      ChannelInternalStep.evaluateArgument
        (s := {s with control := .value (.closure x body s.env)})
        (fn := .closure x body s.env) (arg := arg)
        (callEnv := callEnv) (rest := functionStack rest)
    exact hsrcClo.symm ▸ happ
  have hscopedFn : ChannelConfig.WellScoped
      {s with
        control := .term arg
        env := callEnv
        stack :=
          .function (.closure x body s.env) :: functionStack rest} :=
    ChannelInternalStep.preserve_wellScoped hstepArg
      (ChannelInternalStep.preserve_wellScoped hstepLam hscoped)
  have hokFull : FunctionSpineOk ((x, body, s.env) :: rest) :=
    FunctionSpineOk.cons hok.ne_nil hadminBody hok
  have hsFn :
      ({s with
          control := .term arg
          env := callEnv
          stack :=
            .function (.closure x body s.env) ::
              functionStack rest}).stack =
        functionStack ((x, body, s.env) :: rest) := by
    simp
  have harg :
      PresentedChannelConfigCompleteness D₀ j₀ realize
        {s with
          control := .term arg
          env := callEnv
          stack :=
            .function (.closure x body s.env) :: functionStack rest}
        answer :=
    admin_noapp_under_function_spine_presentedChannelConfigCompleteness
      D₀ j₀ realize ((x, body, s.env) :: rest) hokFull
      hadminArg rfl hsFn hscopedFn hrelFn
  have hClo :=
    evaluateArgument_presentedChannelConfigCompleteness D₀ j₀ realize
      (s := {s with control := .value (.closure x body s.env)})
      (fn := .closure x body s.env) (arg := arg)
      (callEnv := callEnv) (rest := functionStack rest)
      rfl hs hrelClo harg
  exact lambda_presentedChannelConfigCompleteness D₀ j₀ realize
    hc hrel hClo

/-- Value completeness under one function frame, one leftover argument
frame, and a residual function-frame spine. -/
def ValueUnderFunctionArgumentFunctionSpine {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (y : Name) (bodyY arg2 : Term (QubitPrimitive C))
    (cloY callEnv : RuntimeEnv C) : Prop :=
  ∀ {s : ChannelConfig C} {arg : RuntimeValue C}
    {answer : HSemanticComp D₀ j₀},
    s.control = .value arg →
    s.stack =
      .function (.closure y bodyY cloY) ::
        .argument arg2 callEnv :: functionStack rest →
    ChannelConfig.WellScoped s →
    ChannelConfigRel D₀ j₀ realize s answer →
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer

theorem value_under_function_argument_function_spine_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : FunctionSpineOk rest)
    {s : ChannelConfig C} {arg : RuntimeValue C}
    {y z : Name} {body arg2 : Term (QubitPrimitive C)}
    {cloY callEnv : RuntimeEnv C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .value arg)
    (hs : s.stack =
      [.function (.closure y (.lam z body) cloY),
        .argument arg2 callEnv] ++ functionStack rest)
    (hadminBody : AdminNoApp body) (hadminArg2 : AdminNoApp arg2)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsEq :
      {s with
        control := .value arg
        stack :=
          .function (.closure y (.lam z body) cloY) ::
            .argument arg2 callEnv :: functionStack rest} = s :=
    ChannelConfig.ext hc.symm rfl (by simpa using hs.symm) rfl
  have hrel' : ChannelConfigRel D₀ j₀ realize
      {s with
        control := .value arg
        stack :=
          .function (.closure y (.lam z body) cloY) ::
            .argument arg2 callEnv :: functionStack rest}
      answer :=
    hsEq.symm ▸ hrel
  have hrelBody :=
    channel_config_beta D₀ j₀ (s := s) (x := y)
      (body := .lam z body) (closureEnv := cloY) (arg := arg)
      (rest := .argument arg2 callEnv :: functionStack rest) hrel'
  let sBody : ChannelConfig C :=
    {s with
      control := .term (.lam z body)
      env := RuntimeEnv.bind y arg cloY
      stack := .argument arg2 callEnv :: functionStack rest}
  have hstepBeta : ChannelInternalStep s sBody := by
    have happ :
        ChannelInternalStep
          {s with
            control := .value arg
            stack :=
              .function (.closure y (.lam z body) cloY) ::
                .argument arg2 callEnv :: functionStack rest}
          sBody :=
      ChannelInternalStep.beta (s := s) (x := y)
        (body := .lam z body) (closureEnv := cloY) (arg := arg)
        (rest := .argument arg2 callEnv :: functionStack rest)
    exact hsEq.symm ▸ happ
  have hscopedBody : ChannelConfig.WellScoped sBody :=
    ChannelInternalStep.preserve_wellScoped hstepBeta hscoped
  have hchild :=
    lam_under_argument_function_spine_presentedChannelConfigCompleteness
      D₀ j₀ realize rest hok (s := sBody) (x := z) (body := body)
      (arg := arg2) (callEnv := callEnv) rfl rfl hadminBody hadminArg2
      hscopedBody hrelBody
  have hs' : s.stack =
      .function (.closure y (.lam z body) cloY) ::
        .argument arg2 callEnv :: functionStack rest := by
    simpa using hs
  exact beta_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := y) (body := .lam z body) (closureEnv := cloY)
    (arg := arg) (rest := .argument arg2 callEnv :: functionStack rest)
    hc hs' hrel hchild

theorem pauliX_under_function_argument_function_spine_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    {y : Name} {bodyY arg2 : Term (QubitPrimitive C)}
    {cloY callEnv : RuntimeEnv C}
    (hVal : ValueUnderFunctionArgumentFunctionSpine D₀ j₀ realize
      rest y bodyY arg2 cloY callEnv)
    {s : ChannelConfig C} {value : C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack =
      .function (.closure y bodyY cloY) ::
        .argument arg2 callEnv :: functionStack rest)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsPx :
      {s with control := .term (.prim (.pauliX value))} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  obtain ⟨semanticEnv, kStack, henv, hstack, rfl⟩ :=
    channelConfigRel_term_inv D₀ j₀ hc hrel
  let sVal : ChannelConfig C :=
    {s with
      control := .value (.payload value)
      quantum := applyOperation Qubit.pauliXOp s.quantum}
  have hstep : ChannelInternalStep s sVal := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.prim (.pauliX value))}
          sVal :=
      ChannelInternalStep.pauliXPrimitive (s := s) (value := value)
    exact hsPx.symm ▸ happ
  have hscopedVal : ChannelConfig.WellScoped sVal :=
    ChannelInternalStep.preserve_wellScoped hstep hscoped
  have hrelVal : ChannelConfigRel D₀ j₀ realize sVal
      (kStack
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) (realize value))) :=
    ⟨semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (realize value),
      kStack,
      ControlRel.value _ _ s.env
        (payload_related D₀ j₀ realize value),
      hstack, rfl⟩
  have hval :=
    hVal (s := sVal) (arg := .payload value) rfl hs hscopedVal hrelVal
  refine
    { related := hrel
      complete := ?_ }
  constructor
  intro selectors i ξ kξ hk
  have hchildEq :=
    hval.complete.selected_result_eq_channelTree_sup_presented
      selectors i ξ kξ hk
  have hden :
      interp (hardwarePrimitive D₀ j₀ realize)
          (.prim (.pauliX value)) semanticEnv =
        taggedEmbed
          (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
            (realize value)) := by
    simp [hardwarePrimitive_pauliX]
  have hne : s.stack ≠ [] := by
    rw [hs]
    exact List.cons_ne_nil _ _
  let unitVal : HSemanticComp D₀ j₀ :=
    semanticUnit (Q := TTExternalContinuationPower 2)
      (D₀ := D₀) (j₀ := j₀) (realize value)
  let opVal : HSemanticComp D₀ j₀ :=
    taggedEmbed
      (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
        (realize value))
  have hchildCoord :
      kStack unitVal (HardwareAdequacy.encodePath selectors i) kξ =
        sSup (channelTreeResults D₀ j₀ realize sVal selectors i
          kξ) := by
    have hsel :
        HardwareAdequacy.selectPath selectors (kStack unitVal) i kξ =
          kStack unitVal (HardwareAdequacy.encodePath selectors i)
            kξ :=
      congrArg (fun f => f kξ)
        (HardwareAdequacy.selectPath_apply_encode selectors
          (kStack unitVal) i)
    exact hsel.symm.trans hchildEq
  have hselParent :
      HardwareAdequacy.selectPath selectors (kStack opVal) i kξ =
        kStack opVal (HardwareAdequacy.encodePath selectors i) kξ :=
    congrArg (fun f => f kξ)
      (HardwareAdequacy.selectPath_apply_encode selectors
        (kStack opVal) i)
  have hop :
      kStack opVal (HardwareAdequacy.encodePath selectors i) kξ =
        embed (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
            (realize value))
          (ScottMap.const
            (kStack unitVal (HardwareAdequacy.encodePath selectors i)
              kξ)) :=
    stackRel_ofOperation_eval D₀ j₀ hstack hne
      Qubit.pauliXOp (realize value)
      (HardwareAdequacy.encodePath selectors i) kξ
  rw [hden, hselParent, hop, hchildCoord, embed_ofOperation_const_sSup]
  apply le_antisymm
  · apply sSup_le
    rintro T ⟨r, ⟨fuel, child, R, hdepth, rfl⟩, rfl⟩
    apply le_sSup
    refine ⟨fuel + 1, ChannelTree.internal hstep child,
      wrapInternalRealization D₀ j₀ realize hstep child R, ?_, ?_⟩
    · change child.depth + 1 ≤ fuel + 1
      omega
    · exact
        (restrictedResult_internal_pauliX D₀ j₀ realize hstep hc
          child
          (wrapInternalRealization D₀ j₀ realize hstep child R)
          selectors i ξ kξ hk).symm
  · apply sSup_le
    rintro T ⟨_, tree, R, _, rfl⟩
    cases tree with
    | terminal hterm =>
        cases hterm.control_eq.symm.trans hc
    | @internal _ t' h next =>
        have ht : t' = sVal :=
          ChannelInternalStep.eq_config_of_pauliX h hc
        subst t'
        rw [restrictedResult_internal_pauliX D₀ j₀ realize h hc
          next R selectors i ξ kξ hk]
        apply le_sSup
        refine ⟨restrictedResult D₀ j₀ realize next
            (internalChildRealization D₀ j₀ realize h next R)
            selectors i kξ,
          ⟨next.depth, next,
            internalChildRealization D₀ j₀ realize h next R,
            le_rfl, rfl⟩, rfl⟩
    | external _ hex _ =>
        exact False.elim (ChannelExternalStep.not_prim hex hc)
    | probability _ _ _ _ =>
        cases hc
    | probabilityZero _ =>
        cases hc
    | probabilityOne _ =>
        cases hc
    | measurement _ _ =>
        cases hc

theorem admin_noapp_under_function_argument_function_spine_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    {y : Name} {bodyY arg2 : Term (QubitPrimitive C)}
    {cloY callEnv : RuntimeEnv C}
    (hVal : ValueUnderFunctionArgumentFunctionSpine D₀ j₀ realize
      rest y bodyY arg2 cloY callEnv)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack =
      .function (.closure y bodyY cloY) ::
        .argument arg2 callEnv :: functionStack rest)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  induction code generalizing s answer with
  | var z =>
      have hctl := hscoped.left
      rw [hc] at hctl
      obtain ⟨v, hlookup⟩ := hctl.right z (by simp [free])
      have hsVar :
          {s with control := .term (.var z)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelVar : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.var z)} answer :=
        hsVar.symm ▸ hrel
      have hrelVal :=
        channel_config_variable D₀ j₀ hlookup hrelVar
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value v} :=
        ⟨⟨hctl.left, hctl.left z v hlookup⟩, hscoped.right⟩
      have hval :=
        hVal (s := {s with control := .value v}) (arg := v)
          rfl hs hscopedVal hrelVal
      exact variable_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hlookup hrel hval
  | app _ _ =>
      exact False.elim hadmin
  | lam w M _ih =>
      have hsLam :
          {s with control := .term (.lam w M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelLam : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.lam w M)} answer :=
        hsLam.symm ▸ hrel
      have hrelVal :=
        channel_config_lambda D₀ j₀ (s := s) hrelLam
      have hstepLam : ChannelInternalStep s
          {s with control := .value (.closure w M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.lam w M)}
              {s with control := .value (.closure w M s.env)} :=
          ChannelInternalStep.lambda (s := s) (x := w) (body := M)
        exact hsLam.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.closure w M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepLam hscoped
      have hval :=
        hVal (s := {s with control := .value (.closure w M s.env)})
          (arg := .closure w M s.env) rfl hs hscopedVal hrelVal
      exact lambda_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hrel hval
  | recLam self w M _ih =>
      have hsRec :
          {s with control := .term (.recLam self w M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelRec : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.recLam self w M)} answer :=
        hsRec.symm ▸ hrel
      have hrelVal :=
        channel_config_recursive D₀ j₀ (s := s) hrelRec
      have hstepRec : ChannelInternalStep s
          {s with control := .value (.recClosure self w M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.recLam self w M)}
              {s with
                control := .value (.recClosure self w M s.env)} :=
          ChannelInternalStep.recursive (s := s) (self := self)
            (arg := w) (body := M)
        exact hsRec.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.recClosure self w M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepRec hscoped
      have hval :=
        hVal
          (s :=
            {s with control := .value (.recClosure self w M s.env)})
          (arg := .recClosure self w M s.env) rfl hs hscopedVal hrelVal
      exact recLam_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hrel hval
  | intern left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hadmin
      have hscopedL :=
        wellScoped_term_child (child := left) hc hscoped
          (fun z hz => by simp [free, hz])
      have hscopedR :=
        wellScoped_term_child (child := right) hc hscoped
          (fun z hz => by simp [free, hz])
      refine intern_related_presentedChannelConfigCompleteness
        D₀ j₀ realize hc hrel ?_ ?_
      · intro semanticEnv k henv hstack
        exact ihL hnaL (s := {s with control := .term left}) rfl hs
          hscopedL
          ⟨interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv, k,
            ControlRel.term left s.env semanticEnv henv, hstack, rfl⟩
      · intro semanticEnv k henv hstack
        exact ihR hnaR (s := {s with control := .term right}) rfl hs
          hscopedR
          ⟨interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv, k,
            ControlRel.term right s.env semanticEnv henv, hstack, rfl⟩
  | extern _ _ _ _ =>
      exact False.elim hadmin
  | prob p left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hadmin
      have hscopedL :=
        wellScoped_term_child (child := left) hc hscoped
          (fun z hz => by simp [free, hz])
      have hscopedR :=
        wellScoped_term_child (child := right) hc hscoped
          (fun z hz => by simp [free, hz])
      refine prob_related_presentedChannelConfigCompleteness
        D₀ j₀ realize hc hrel ?_ ?_
      · intro semanticEnv k quantum henv hstack
        exact ihL hnaL
          (s := {s with control := .term left, quantum := quantum})
          rfl hs ⟨hscopedL.left, hscopedL.right⟩
          ⟨interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv, k,
            ControlRel.term left s.env semanticEnv henv, hstack, rfl⟩
      · intro semanticEnv k quantum henv hstack
        exact ihR hnaR
          (s := {s with control := .term right, quantum := quantum})
          rfl hs ⟨hscopedR.left, hscopedR.right⟩
          ⟨interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv, k,
            ControlRel.term right s.env semanticEnv henv, hstack, rfl⟩
  | prim prim =>
      cases prim with
      | ret value =>
          have hsRet :
              {s with control := .term (.prim (.ret value))} = s :=
            ChannelConfig.ext hc.symm rfl rfl rfl
          have hrelRet : ChannelConfigRel D₀ j₀ realize
              {s with control := .term (.prim (.ret value))} answer :=
            hsRet.symm ▸ hrel
          have hrelVal :=
            channel_config_return D₀ j₀ hrelRet
          have hstepRet : ChannelInternalStep s
              {s with control := .value (.payload value)} := by
            have happ :
                ChannelInternalStep
                  {s with control := .term (.prim (.ret value))}
                  {s with control := .value (.payload value)} :=
              ChannelInternalStep.returnPrimitive (s := s)
                (value := value)
            exact hsRet.symm ▸ happ
          have hscopedVal : ChannelConfig.WellScoped
              {s with control := .value (.payload value)} :=
            ChannelInternalStep.preserve_wellScoped hstepRet hscoped
          have hval :=
            hVal (s := {s with control := .value (.payload value)})
              (arg := .payload value) rfl hs hscopedVal hrelVal
          exact return_presentedChannelConfigCompleteness D₀ j₀ realize
            hc hrel hval
      | pauliX value =>
          exact
            pauliX_under_function_argument_function_spine_of_value
              D₀ j₀ realize rest hVal hc hs hscoped hrel
      | measureZ _ _ =>
          exact False.elim hadmin

theorem admin_noapp_under_function_argument_function_spine_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : FunctionSpineOk rest)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {y z : Name} {body arg2 : Term (QubitPrimitive C)}
    {cloY callEnv : RuntimeEnv C} {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack =
      [.function (.closure y (.lam z body) cloY),
        .argument arg2 callEnv] ++ functionStack rest)
    (hadminBody : AdminNoApp body) (hadminArg2 : AdminNoApp arg2)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hVal : ValueUnderFunctionArgumentFunctionSpine D₀ j₀ realize
      rest y (.lam z body) arg2 cloY callEnv := by
    intro s' arg answer' hc' hs' hscoped' hrel'
    exact
      value_under_function_argument_function_spine_presentedChannelConfigCompleteness
        D₀ j₀ realize rest hok hc' (by simpa using hs')
        hadminBody hadminArg2 hscoped' hrel'
  have hs' : s.stack =
      .function (.closure y (.lam z body) cloY) ::
        .argument arg2 callEnv :: functionStack rest := by
    simpa using hs
  exact admin_noapp_under_function_argument_function_spine_of_value
    D₀ j₀ realize rest hVal hadmin hc hs' hscoped hrel

/-- Inner `app (lam y (lam z body)) arg1` under one leftover argument
frame over a residual function-frame spine. -/
theorem app_lam_under_argument_function_spine_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : FunctionSpineOk rest)
    {s : ChannelConfig C} {y z : Name}
    {body arg1 arg2 : Term (QubitPrimitive C)} {callEnv : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.app (.lam y (.lam z body)) arg1))
    (hs : s.stack = .argument arg2 callEnv :: functionStack rest)
    (hadminBody : AdminNoApp body)
    (hadmin1 : AdminNoApp arg1) (hadmin2 : AdminNoApp arg2)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsApp :
      {s with control := .term (.app (.lam y (.lam z body)) arg1)} =
        s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app (.lam y (.lam z body)) arg1)}
      answer :=
    hsApp.symm ▸ hrel
  have hrelLam :=
    channel_config_application D₀ j₀ (s := s)
      (fn := .lam y (.lam z body)) (arg := arg1) hrelApp
  have hrelClo :=
    channel_config_lambda D₀ j₀
      (s := {s with stack := .argument arg1 s.env :: s.stack})
      hrelLam
  have hrelArg :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {s with
          control := .value (.closure y (.lam z body) s.env)
          stack := .argument arg1 s.env :: s.stack})
      (fn := .closure y (.lam z body) s.env) (arg := arg1)
      (callEnv := s.env) (rest := s.stack) hrelClo
  let sArg : ChannelConfig C :=
    {s with
      control := .term arg1
      stack := .function (.closure y (.lam z body) s.env) :: s.stack}
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.lam y (.lam z body))
        stack := .argument arg1 s.env :: s.stack} := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app (.lam y (.lam z body)) arg1)}
          {s with
            control := .term (.lam y (.lam z body))
            stack := .argument arg1 s.env :: s.stack} :=
      ChannelInternalStep.application (s := s)
        (fn := .lam y (.lam z body)) (arg := arg1)
    exact hsApp.symm ▸ happ
  have hstepLam : ChannelInternalStep
      {s with
        control := .term (.lam y (.lam z body))
        stack := .argument arg1 s.env :: s.stack}
      {s with
        control := .value (.closure y (.lam z body) s.env)
        stack := .argument arg1 s.env :: s.stack} :=
    ChannelInternalStep.lambda
      (s := {s with stack := .argument arg1 s.env :: s.stack})
      (x := y) (body := .lam z body)
  have hstepArg : ChannelInternalStep
      {s with
        control := .value (.closure y (.lam z body) s.env)
        stack := .argument arg1 s.env :: s.stack}
      sArg :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {s with
          control := .value (.closure y (.lam z body) s.env)
          stack := .argument arg1 s.env :: s.stack})
      (fn := .closure y (.lam z body) s.env) (arg := arg1)
      (callEnv := s.env) (rest := s.stack)
  have hscopedArg : ChannelConfig.WellScoped sArg :=
    ChannelInternalStep.preserve_wellScoped hstepArg
      (ChannelInternalStep.preserve_wellScoped hstepLam
        (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
  have hsArg :
      sArg.stack =
        [.function (.closure y (.lam z body) s.env),
          .argument arg2 callEnv] ++ functionStack rest := by
    simp [sArg, hs]
  have harg :
      PresentedChannelConfigCompleteness D₀ j₀ realize sArg answer :=
    admin_noapp_under_function_argument_function_spine_presentedChannelConfigCompleteness
      D₀ j₀ realize rest hok (s := sArg) (code := arg1)
      (y := y) (z := z) (body := body) (arg2 := arg2)
      (cloY := s.env) (callEnv := callEnv) hadmin1 rfl hsArg
      hadminBody hadmin2 hscopedArg
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term arg1
              env := s.env
              stack :=
                .function (.closure y (.lam z body) s.env) ::
                  s.stack}
            _
        exact hrelArg)
  exact stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := y) (body := .lam z body) (arg := arg1) hc hrel harg

/-- Closed curry under an outer lambda:
`app (lam x bodyX) (app (app (lam y (lam z body)) arg1) arg2)`. -/
theorem closed_lam_app_app_lam_lam_admin_noapp_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x y z : Name) (bodyX body arg1 arg2 : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.lam x bodyX)
        (.app (.app (.lam y (.lam z body)) arg1) arg2)))
    (hnoappX : NoApp bodyX)
    (hadminBody : AdminNoApp body)
    (hadmin1 : AdminNoApp arg1) (hadmin2 : AdminNoApp arg2)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.app (.lam x bodyX)
          (.app (.app (.lam y (.lam z body)) arg1) arg2))
        quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.lam x bodyX)
          (.app (.app (.lam y (.lam z body)) arg1) arg2))
        semanticEnv) := by
  let inner : Term (QubitPrimitive C) :=
    .app (.app (.lam y (.lam z body)) arg1) arg2
  let code : Term (QubitPrimitive C) := .app (.lam x bodyX) inner
  let s : ChannelConfig C := initialChannelConfig code quantum
  have hc : s.control = .term code := rfl
  have hrel :=
    initialChannelConfig_related D₀ j₀ realize code quantum semanticEnv
  have hscoped :=
    initialChannelConfig_wellScoped hclosed quantum
  have hsApp :
      {s with control := .term (.app (.lam x bodyX) inner)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app (.lam x bodyX) inner)}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    hsApp.symm ▸ hrel
  have hrelLam :=
    channel_config_application D₀ j₀ (s := s)
      (fn := .lam x bodyX) (arg := inner) hrelApp
  have hrelClo :=
    channel_config_lambda D₀ j₀
      (s := {s with stack := .argument inner s.env :: s.stack})
      hrelLam
  have hrelInner :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {s with
          control := .value (.closure x bodyX s.env)
          stack := .argument inner s.env :: s.stack})
      (fn := .closure x bodyX s.env) (arg := inner)
      (callEnv := s.env) (rest := s.stack) hrelClo
  let sInner : ChannelConfig C :=
    {s with
      control := .term inner
      stack := .function (.closure x bodyX s.env) :: s.stack}
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.lam x bodyX)
        stack := .argument inner s.env :: s.stack} := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app (.lam x bodyX) inner)}
          {s with
            control := .term (.lam x bodyX)
            stack := .argument inner s.env :: s.stack} :=
      ChannelInternalStep.application (s := s)
        (fn := .lam x bodyX) (arg := inner)
    exact hsApp.symm ▸ happ
  have hstepLam : ChannelInternalStep
      {s with
        control := .term (.lam x bodyX)
        stack := .argument inner s.env :: s.stack}
      {s with
        control := .value (.closure x bodyX s.env)
        stack := .argument inner s.env :: s.stack} :=
    ChannelInternalStep.lambda
      (s := {s with stack := .argument inner s.env :: s.stack})
      (x := x) (body := bodyX)
  have hstepInner : ChannelInternalStep
      {s with
        control := .value (.closure x bodyX s.env)
        stack := .argument inner s.env :: s.stack}
      sInner :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {s with
          control := .value (.closure x bodyX s.env)
          stack := .argument inner s.env :: s.stack})
      (fn := .closure x bodyX s.env) (arg := inner)
      (callEnv := s.env) (rest := s.stack)
  have hscopedInner : ChannelConfig.WellScoped sInner :=
    ChannelInternalStep.preserve_wellScoped hstepInner
      (ChannelInternalStep.preserve_wellScoped hstepLam
        (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
  have hsInner :
      sInner.stack = functionStack [(x, bodyX, s.env)] := by
    simp [sInner, s, initialChannelConfig, ofConfig, initialConfig]
  have hokX : FunctionSpineOk [(x, bodyX, s.env)] := hnoappX
  let inner1 : Term (QubitPrimitive C) :=
    .app (.lam y (.lam z body)) arg1
  have hsApp1 :
      {sInner with control := .term (.app inner1 arg2)} = sInner :=
    ChannelConfig.ext rfl rfl rfl rfl
  have hrelApp1 : ChannelConfigRel D₀ j₀ realize
      {sInner with control := .term (.app inner1 arg2)}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) := by
    change ChannelConfigRel D₀ j₀ realize
        {s with
          control := .term inner
          env := s.env
          stack := .function (.closure x bodyX s.env) :: s.stack}
        _
    exact hrelInner
  have hrelInner1 :=
    channel_config_application D₀ j₀ (s := sInner) (fn := inner1)
      (arg := arg2) hrelApp1
  let sInner1 : ChannelConfig C :=
    {sInner with
      control := .term inner1
      stack := .argument arg2 sInner.env :: sInner.stack}
  have hstepApp1 : ChannelInternalStep sInner sInner1 := by
    have happ :
        ChannelInternalStep
          {sInner with control := .term (.app inner1 arg2)}
          sInner1 :=
      ChannelInternalStep.application (s := sInner) (fn := inner1)
        (arg := arg2)
    exact hsApp1.symm ▸ happ
  have hscopedInner1 : ChannelConfig.WellScoped sInner1 :=
    ChannelInternalStep.preserve_wellScoped hstepApp1 hscopedInner
  have hsInner1 :
      sInner1.stack =
        .argument arg2 s.env :: functionStack [(x, bodyX, s.env)] := by
    simp [sInner1, sInner, s, initialChannelConfig, ofConfig,
      initialConfig]
  have hinner1 :
      PresentedChannelConfigCompleteness D₀ j₀ realize sInner1
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    app_lam_under_argument_function_spine_presentedChannelConfigCompleteness
      D₀ j₀ realize [(x, bodyX, s.env)] hokX (s := sInner1)
      (y := y) (z := z) (body := body) (arg1 := arg1) (arg2 := arg2)
      (callEnv := s.env) rfl hsInner1 hadminBody hadmin1 hadmin2
      hscopedInner1
      (by
        change ChannelConfigRel D₀ j₀ realize
            {sInner with
              control := .term inner1
              env := sInner.env
              stack := .argument arg2 sInner.env :: sInner.stack}
            _
        exact hrelInner1)
  have hinner :
      PresentedChannelConfigCompleteness D₀ j₀ realize sInner
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    application_presentedChannelConfigCompleteness D₀ j₀ realize
      (s := sInner) (fn := inner1) (arg := arg2) rfl
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term inner
              env := s.env
              stack := .function (.closure x bodyX s.env) :: s.stack}
            _
        exact hrelInner)
      hinner1
  exact (stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := x) (body := bodyX) (arg := inner) hc hrel
    hinner).complete

/-- Token adequacy for closed curry under an outer lambda. -/
theorem closed_lam_app_app_lam_lam_admin_noapp_presented_token_adequacy
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x y z : Name) (bodyX body arg1 arg2 : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.lam x bodyX)
        (.app (.app (.lam y (.lam z body)) arg1) arg2)))
    (hnoappX : NoApp bodyX)
    (hadminBody : AdminNoApp body)
    (hadmin1 : AdminNoApp arg1) (hadmin2 : AdminNoApp arg2)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize)
          (.app (.lam x bodyX)
            (.app (.app (.lam y (.lam z body)) arg1) arg2))
          semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig
            (.app (.lam x bodyX)
              (.app (.app (.lam y (.lam z body)) arg1) arg2))
            quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig
      (.app (.lam x bodyX)
        (.app (.app (.lam y (.lam z body)) arg1) arg2))
      quantum)
    (interp (hardwarePrimitive D₀ j₀ realize)
      (.app (.lam x bodyX)
        (.app (.app (.lam y (.lam z body)) arg1) arg2))
      semanticEnv)
    (closed_lam_app_app_lam_lam_admin_noapp_presented_channelTreeCompleteness
      D₀ j₀ realize x y z bodyX body arg1 arg2 hclosed hnoappX
      hadminBody hadmin1 hadmin2 quantum semanticEnv)
    selectors ξ k hk i token

/-- Value completeness under one function frame, leftover argument
frames, and a residual function-frame spine. -/
def ValueUnderFunctionArgumentThenFunctionSpine {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)) :
    Prop :=
  ∀ {s : ChannelConfig C} {arg : RuntimeValue C} {x : Name}
    {body : Term (QubitPrimitive C)} {cloX : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀},
    s.control = .value arg →
    s.stack =
      .function (.closure x body cloX) ::
        argumentThenFunctionStack args rest →
    BodyUnderArgsThenAdmin args.length body →
    ChannelConfig.WellScoped s →
    ChannelConfigRel D₀ j₀ realize s answer →
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer

theorem pauliX_under_function_argument_then_function_spine_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderFunctionArgumentThenFunctionSpine D₀ j₀ realize
      args rest)
    {s : ChannelConfig C} {value : C} {x : Name}
    {body : Term (QubitPrimitive C)} {cloX : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack =
      .function (.closure x body cloX) ::
        argumentThenFunctionStack args rest)
    (hbody : BodyUnderArgsThenAdmin args.length body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsPx :
      {s with control := .term (.prim (.pauliX value))} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  obtain ⟨semanticEnv, kStack, henv, hstack, rfl⟩ :=
    channelConfigRel_term_inv D₀ j₀ hc hrel
  let sVal : ChannelConfig C :=
    {s with
      control := .value (.payload value)
      quantum := applyOperation Qubit.pauliXOp s.quantum}
  have hstep : ChannelInternalStep s sVal := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.prim (.pauliX value))}
          sVal :=
      ChannelInternalStep.pauliXPrimitive (s := s) (value := value)
    exact hsPx.symm ▸ happ
  have hscopedVal : ChannelConfig.WellScoped sVal :=
    ChannelInternalStep.preserve_wellScoped hstep hscoped
  have hrelVal : ChannelConfigRel D₀ j₀ realize sVal
      (kStack
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) (realize value))) :=
    ⟨semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (realize value),
      kStack,
      ControlRel.value _ _ s.env
        (payload_related D₀ j₀ realize value),
      hstack, rfl⟩
  have hval :=
    hVal (s := sVal) (arg := .payload value) (x := x) (body := body)
      (cloX := cloX) rfl hs hbody hscopedVal hrelVal
  refine
    { related := hrel
      complete := ?_ }
  constructor
  intro selectors i ξ kξ hk
  have hchildEq :=
    hval.complete.selected_result_eq_channelTree_sup_presented
      selectors i ξ kξ hk
  have hden :
      interp (hardwarePrimitive D₀ j₀ realize)
          (.prim (.pauliX value)) semanticEnv =
        taggedEmbed
          (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
            (realize value)) := by
    simp [hardwarePrimitive_pauliX]
  have hne : s.stack ≠ [] := by
    rw [hs]
    exact List.cons_ne_nil _ _
  let unitVal : HSemanticComp D₀ j₀ :=
    semanticUnit (Q := TTExternalContinuationPower 2)
      (D₀ := D₀) (j₀ := j₀) (realize value)
  let opVal : HSemanticComp D₀ j₀ :=
    taggedEmbed
      (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
        (realize value))
  have hchildCoord :
      kStack unitVal (HardwareAdequacy.encodePath selectors i) kξ =
        sSup (channelTreeResults D₀ j₀ realize sVal selectors i
          kξ) := by
    have hsel :
        HardwareAdequacy.selectPath selectors (kStack unitVal) i kξ =
          kStack unitVal (HardwareAdequacy.encodePath selectors i)
            kξ :=
      congrArg (fun f => f kξ)
        (HardwareAdequacy.selectPath_apply_encode selectors
          (kStack unitVal) i)
    exact hsel.symm.trans hchildEq
  have hselParent :
      HardwareAdequacy.selectPath selectors (kStack opVal) i kξ =
        kStack opVal (HardwareAdequacy.encodePath selectors i) kξ :=
    congrArg (fun f => f kξ)
      (HardwareAdequacy.selectPath_apply_encode selectors
        (kStack opVal) i)
  have hop :
      kStack opVal (HardwareAdequacy.encodePath selectors i) kξ =
        embed (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
            (realize value))
          (ScottMap.const
            (kStack unitVal (HardwareAdequacy.encodePath selectors i)
              kξ)) :=
    stackRel_ofOperation_eval D₀ j₀ hstack hne
      Qubit.pauliXOp (realize value)
      (HardwareAdequacy.encodePath selectors i) kξ
  rw [hden, hselParent, hop, hchildCoord, embed_ofOperation_const_sSup]
  apply le_antisymm
  · apply sSup_le
    rintro T ⟨r, ⟨fuel, child, R, hdepth, rfl⟩, rfl⟩
    apply le_sSup
    refine ⟨fuel + 1, ChannelTree.internal hstep child,
      wrapInternalRealization D₀ j₀ realize hstep child R, ?_, ?_⟩
    · change child.depth + 1 ≤ fuel + 1
      omega
    · exact
        (restrictedResult_internal_pauliX D₀ j₀ realize hstep hc
          child
          (wrapInternalRealization D₀ j₀ realize hstep child R)
          selectors i ξ kξ hk).symm
  · apply sSup_le
    rintro T ⟨_, tree, R, _, rfl⟩
    cases tree with
    | terminal hterm =>
        cases hterm.control_eq.symm.trans hc
    | @internal _ t' h next =>
        have ht : t' = sVal :=
          ChannelInternalStep.eq_config_of_pauliX h hc
        subst t'
        rw [restrictedResult_internal_pauliX D₀ j₀ realize h hc
          next R selectors i ξ kξ hk]
        apply le_sSup
        refine ⟨restrictedResult D₀ j₀ realize next
            (internalChildRealization D₀ j₀ realize h next R)
            selectors i kξ,
          ⟨next.depth, next,
            internalChildRealization D₀ j₀ realize h next R,
            le_rfl, rfl⟩, rfl⟩
    | external _ hex _ =>
        exact False.elim (ChannelExternalStep.not_prim hex hc)
    | probability _ _ _ _ =>
        cases hc
    | probabilityZero _ =>
        cases hc
    | probabilityOne _ =>
        cases hc
    | measurement _ _ =>
        cases hc

theorem admin_noapp_under_function_argument_then_function_spine_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderFunctionArgumentThenFunctionSpine D₀ j₀ realize
      args rest)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {x : Name} {body : Term (QubitPrimitive C)} {cloX : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack =
      .function (.closure x body cloX) ::
        argumentThenFunctionStack args rest)
    (hbody : BodyUnderArgsThenAdmin args.length body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  induction code generalizing s answer with
  | var z =>
      have hctl := hscoped.left
      rw [hc] at hctl
      obtain ⟨v, hlookup⟩ := hctl.right z (by simp [free])
      have hsVar :
          {s with control := .term (.var z)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelVar : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.var z)} answer :=
        hsVar.symm ▸ hrel
      have hrelVal :=
        channel_config_variable D₀ j₀ hlookup hrelVar
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value v} :=
        ⟨⟨hctl.left, hctl.left z v hlookup⟩, hscoped.right⟩
      have hval :=
        hVal (s := {s with control := .value v}) (arg := v)
          (x := x) (body := body) (cloX := cloX)
          rfl hs hbody hscopedVal hrelVal
      exact variable_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hlookup hrel hval
  | app _ _ =>
      exact False.elim hadmin
  | lam z M _ih =>
      have hsLam :
          {s with control := .term (.lam z M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelLam : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.lam z M)} answer :=
        hsLam.symm ▸ hrel
      have hrelVal :=
        channel_config_lambda D₀ j₀ (s := s) hrelLam
      have hstepLam : ChannelInternalStep s
          {s with control := .value (.closure z M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.lam z M)}
              {s with control := .value (.closure z M s.env)} :=
          ChannelInternalStep.lambda (s := s) (x := z) (body := M)
        exact hsLam.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.closure z M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepLam hscoped
      have hval :=
        hVal (s := {s with control := .value (.closure z M s.env)})
          (arg := .closure z M s.env) (x := x) (body := body)
          (cloX := cloX) rfl hs hbody hscopedVal hrelVal
      exact lambda_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hrel hval
  | recLam self z M _ih =>
      have hsRec :
          {s with control := .term (.recLam self z M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelRec : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.recLam self z M)} answer :=
        hsRec.symm ▸ hrel
      have hrelVal :=
        channel_config_recursive D₀ j₀ (s := s) hrelRec
      have hstepRec : ChannelInternalStep s
          {s with control := .value (.recClosure self z M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.recLam self z M)}
              {s with
                control := .value (.recClosure self z M s.env)} :=
          ChannelInternalStep.recursive (s := s) (self := self)
            (arg := z) (body := M)
        exact hsRec.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.recClosure self z M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepRec hscoped
      have hval :=
        hVal
          (s :=
            {s with control := .value (.recClosure self z M s.env)})
          (arg := .recClosure self z M s.env) (x := x) (body := body)
          (cloX := cloX) rfl hs hbody hscopedVal hrelVal
      exact recLam_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hrel hval
  | intern left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hadmin
      have hscopedL :=
        wellScoped_term_child (child := left) hc hscoped
          (fun z hz => by simp [free, hz])
      have hscopedR :=
        wellScoped_term_child (child := right) hc hscoped
          (fun z hz => by simp [free, hz])
      refine intern_related_presentedChannelConfigCompleteness
        D₀ j₀ realize hc hrel ?_ ?_
      · intro semanticEnv k henv hstack
        exact ihL hnaL (s := {s with control := .term left}) rfl hs
          hscopedL
          ⟨interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv, k,
            ControlRel.term left s.env semanticEnv henv, hstack, rfl⟩
      · intro semanticEnv k henv hstack
        exact ihR hnaR (s := {s with control := .term right}) rfl hs
          hscopedR
          ⟨interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv, k,
            ControlRel.term right s.env semanticEnv henv, hstack, rfl⟩
  | extern _ _ _ _ =>
      exact False.elim hadmin
  | prob p left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hadmin
      have hscopedL :=
        wellScoped_term_child (child := left) hc hscoped
          (fun z hz => by simp [free, hz])
      have hscopedR :=
        wellScoped_term_child (child := right) hc hscoped
          (fun z hz => by simp [free, hz])
      refine prob_related_presentedChannelConfigCompleteness
        D₀ j₀ realize hc hrel ?_ ?_
      · intro semanticEnv k quantum henv hstack
        exact ihL hnaL
          (s := {s with control := .term left, quantum := quantum})
          rfl hs ⟨hscopedL.left, hscopedL.right⟩
          ⟨interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv, k,
            ControlRel.term left s.env semanticEnv henv, hstack, rfl⟩
      · intro semanticEnv k quantum henv hstack
        exact ihR hnaR
          (s := {s with control := .term right, quantum := quantum})
          rfl hs ⟨hscopedR.left, hscopedR.right⟩
          ⟨interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv, k,
            ControlRel.term right s.env semanticEnv henv, hstack, rfl⟩
  | prim prim =>
      cases prim with
      | ret value =>
          have hsRet :
              {s with control := .term (.prim (.ret value))} = s :=
            ChannelConfig.ext hc.symm rfl rfl rfl
          have hrelRet : ChannelConfigRel D₀ j₀ realize
              {s with control := .term (.prim (.ret value))} answer :=
            hsRet.symm ▸ hrel
          have hrelVal :=
            channel_config_return D₀ j₀ hrelRet
          have hstepRet : ChannelInternalStep s
              {s with control := .value (.payload value)} := by
            have happ :
                ChannelInternalStep
                  {s with control := .term (.prim (.ret value))}
                  {s with control := .value (.payload value)} :=
              ChannelInternalStep.returnPrimitive (s := s)
                (value := value)
            exact hsRet.symm ▸ happ
          have hscopedVal : ChannelConfig.WellScoped
              {s with control := .value (.payload value)} :=
            ChannelInternalStep.preserve_wellScoped hstepRet hscoped
          have hval :=
            hVal (s := {s with control := .value (.payload value)})
              (arg := .payload value) (x := x) (body := body)
              (cloX := cloX) rfl hs hbody hscopedVal hrelVal
          exact return_presentedChannelConfigCompleteness D₀ j₀ realize
            hc hrel hval
      | pauliX value =>
          exact
            pauliX_under_function_argument_then_function_spine_of_value
              D₀ j₀ realize args rest hVal hc hs hbody hscoped hrel
      | measureZ _ _ =>
          exact False.elim hadmin

/-- Leftover argument frames over a residual function-frame spine. -/
theorem argument_then_function_spine_presented
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hargs : ArgumentFramesOk args) (hok : FunctionSpineOk rest) :
    (∀ {s : ChannelConfig C} {x : Name}
        {body : Term (QubitPrimitive C)} {answer : HSemanticComp D₀ j₀},
      s.control = .term (.lam x body) →
      s.stack = argumentThenFunctionStack args rest →
      LamAbsorbsThenAdmin args.length body →
      ChannelConfig.WellScoped s →
      ChannelConfigRel D₀ j₀ realize s answer →
      PresentedChannelConfigCompleteness D₀ j₀ realize s answer)
    ∧
    ValueUnderFunctionArgumentThenFunctionSpine D₀ j₀ realize args rest
    ∧
    (∀ {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
        {x : Name} {body : Term (QubitPrimitive C)}
        {cloX : RuntimeEnv C} {answer : HSemanticComp D₀ j₀},
      AdminNoApp code →
      s.control = .term code →
      s.stack =
        .function (.closure x body cloX) ::
          argumentThenFunctionStack args rest →
      BodyUnderArgsThenAdmin args.length body →
      ChannelConfig.WellScoped s →
      ChannelConfigRel D₀ j₀ realize s answer →
      PresentedChannelConfigCompleteness D₀ j₀ realize s answer) := by
  induction args with
  | nil =>
      refine ⟨?hlam, ?hval, ?hadmin⟩
      · intro s x body answer hc hs _habs hscoped hrel
        have hsLam :
            {s with control := .term (.lam x body)} = s :=
          ChannelConfig.ext hc.symm rfl rfl rfl
        have hrelLam : ChannelConfigRel D₀ j₀ realize
            {s with control := .term (.lam x body)} answer :=
          hsLam.symm ▸ hrel
        have hrelVal :=
          channel_config_lambda D₀ j₀ (s := s) hrelLam
        have hstepLam : ChannelInternalStep s
            {s with control := .value (.closure x body s.env)} := by
          have happ :
              ChannelInternalStep
                {s with control := .term (.lam x body)}
                {s with control := .value (.closure x body s.env)} :=
            ChannelInternalStep.lambda (s := s) (x := x) (body := body)
          exact hsLam.symm ▸ happ
        have hscopedVal : ChannelConfig.WellScoped
            {s with control := .value (.closure x body s.env)} :=
          ChannelInternalStep.preserve_wellScoped hstepLam hscoped
        have hs' : ({s with
              control := .value (.closure x body s.env)}).stack =
            functionStack rest := by
          simpa [argumentThenFunctionStack] using hs
        have hval :=
          value_under_function_spine_presentedChannelConfigCompleteness
            D₀ j₀ realize rest hok
            (s := {s with control := .value (.closure x body s.env)})
            rfl hs' hscopedVal hrelVal
        exact lambda_presentedChannelConfigCompleteness D₀ j₀ realize
          hc hrel hval
      · intro s arg x body cloX answer hc hs hbody hscoped hrel
        have hs' : s.stack =
            functionStack ((x, body, cloX) :: rest) := by
          simpa [argumentThenFunctionStack, functionStack] using hs
        have hokFull : FunctionSpineOk ((x, body, cloX) :: rest) :=
          FunctionSpineOk.cons hok.ne_nil hbody hok
        exact
          value_under_function_spine_presentedChannelConfigCompleteness
            D₀ j₀ realize ((x, body, cloX) :: rest) hokFull hc hs'
            hscoped hrel
      · intro s code x body cloX answer hadmin hc hs hbody hscoped
          hrel
        have hs' : s.stack =
            functionStack ((x, body, cloX) :: rest) := by
          simpa [argumentThenFunctionStack, functionStack] using hs
        have hokFull : FunctionSpineOk ((x, body, cloX) :: rest) :=
          FunctionSpineOk.cons hok.ne_nil hbody hok
        exact
          admin_noapp_under_function_spine_presentedChannelConfigCompleteness
            D₀ j₀ realize ((x, body, cloX) :: rest) hokFull hadmin hc
            hs' hscoped hrel
  | cons p restArgs ih =>
      rcases p with ⟨arg, callEnv⟩
      have hadminArg : AdminNoApp arg :=
        hargs (arg, callEnv) (by simp)
      have hargsRest : ArgumentFramesOk restArgs :=
        fun q hq => hargs q (by simp [hq])
      obtain ⟨ihLam, ihVal, ihAdmin⟩ := ih hargsRest
      have hlam :
          ∀ {s : ChannelConfig C} {x : Name}
            {body : Term (QubitPrimitive C)}
            {answer : HSemanticComp D₀ j₀},
          s.control = .term (.lam x body) →
          s.stack =
            argumentThenFunctionStack ((arg, callEnv) :: restArgs)
              rest →
          LamAbsorbsThenAdmin
            ((arg, callEnv) :: restArgs).length body →
          ChannelConfig.WellScoped s →
          ChannelConfigRel D₀ j₀ realize s answer →
          PresentedChannelConfigCompleteness D₀ j₀ realize s
            answer := by
        intro s x body answer hc hs habs hscoped hrel
        have hsLam :
            {s with control := .term (.lam x body)} = s :=
          ChannelConfig.ext hc.symm rfl rfl rfl
        have hrelLam : ChannelConfigRel D₀ j₀ realize
            {s with control := .term (.lam x body)} answer :=
          hsLam.symm ▸ hrel
        have hrelClo :=
          channel_config_lambda D₀ j₀ (s := s) hrelLam
        have hsrcClo :
            {s with control := .value (.closure x body s.env)} =
              {s with
                control := .value (.closure x body s.env)
                stack :=
                  .argument arg callEnv ::
                    argumentThenFunctionStack restArgs rest} :=
          ChannelConfig.ext rfl rfl hs rfl
        have hrelFn :=
          channel_config_evaluateArgument D₀ j₀
            (s := {s with control := .value (.closure x body s.env)})
            (fn := .closure x body s.env) (arg := arg)
            (callEnv := callEnv)
            (rest := argumentThenFunctionStack restArgs rest)
            (hsrcClo ▸ hrelClo)
        have hstepLam : ChannelInternalStep s
            {s with control := .value (.closure x body s.env)} := by
          have happ :
              ChannelInternalStep
                {s with control := .term (.lam x body)}
                {s with control := .value (.closure x body s.env)} :=
            ChannelInternalStep.lambda (s := s) (x := x) (body := body)
          exact hsLam.symm ▸ happ
        have hstepArg : ChannelInternalStep
            {s with control := .value (.closure x body s.env)}
            {s with
              control := .term arg
              env := callEnv
              stack :=
                .function (.closure x body s.env) ::
                  argumentThenFunctionStack restArgs rest} := by
          have happ :
              ChannelInternalStep
                {s with
                  control := .value (.closure x body s.env)
                  stack :=
                    .argument arg callEnv ::
                      argumentThenFunctionStack restArgs rest}
                {s with
                  control := .term arg
                  env := callEnv
                  stack :=
                    .function (.closure x body s.env) ::
                      argumentThenFunctionStack restArgs rest} :=
            ChannelInternalStep.evaluateArgument
              (s := {s with control := .value (.closure x body s.env)})
              (fn := .closure x body s.env) (arg := arg)
              (callEnv := callEnv)
              (rest := argumentThenFunctionStack restArgs rest)
          exact hsrcClo.symm ▸ happ
        have hscopedFn : ChannelConfig.WellScoped
            {s with
              control := .term arg
              env := callEnv
              stack :=
                .function (.closure x body s.env) ::
                  argumentThenFunctionStack restArgs rest} :=
          ChannelInternalStep.preserve_wellScoped hstepArg
            (ChannelInternalStep.preserve_wellScoped hstepLam hscoped)
        have hbodyRest : BodyUnderArgsThenAdmin restArgs.length body :=
          by simpa [LamAbsorbsThenAdmin] using habs
        have harg :
            PresentedChannelConfigCompleteness D₀ j₀ realize
              {s with
                control := .term arg
                env := callEnv
                stack :=
                  .function (.closure x body s.env) ::
                    argumentThenFunctionStack restArgs rest}
              answer :=
          ihAdmin hadminArg rfl rfl hbodyRest hscopedFn hrelFn
        have hClo :=
          evaluateArgument_presentedChannelConfigCompleteness
            D₀ j₀ realize
            (s := {s with control := .value (.closure x body s.env)})
            (fn := .closure x body s.env) (arg := arg)
            (callEnv := callEnv)
            (rest := argumentThenFunctionStack restArgs rest)
            rfl hs hrelClo harg
        exact lambda_presentedChannelConfigCompleteness D₀ j₀ realize
          hc hrel hClo
      have hval : ValueUnderFunctionArgumentThenFunctionSpine
          D₀ j₀ realize ((arg, callEnv) :: restArgs) rest := by
        intro s v x body cloX answer hc hs hbody hscoped hrel
        obtain ⟨y, body', rfl, hbody'⟩ :=
          BodyUnderArgsThenAdmin_succ_inv (n := restArgs.length) hbody
        have hsEq :
            {s with
              control := .value v
              stack :=
                .function (.closure x (.lam y body') cloX) ::
                  argumentThenFunctionStack
                    ((arg, callEnv) :: restArgs) rest} = s :=
          ChannelConfig.ext hc.symm rfl hs.symm rfl
        have hrel' : ChannelConfigRel D₀ j₀ realize
            {s with
              control := .value v
              stack :=
                .function (.closure x (.lam y body') cloX) ::
                  argumentThenFunctionStack
                    ((arg, callEnv) :: restArgs) rest}
            answer :=
          hsEq.symm ▸ hrel
        have hrelBody :=
          channel_config_beta D₀ j₀ (s := s) (x := x)
            (body := .lam y body') (closureEnv := cloX) (arg := v)
            (rest :=
              argumentThenFunctionStack
                ((arg, callEnv) :: restArgs) rest)
            hrel'
        let sBody : ChannelConfig C :=
          {s with
            control := .term (.lam y body')
            env := RuntimeEnv.bind x v cloX
            stack :=
              argumentThenFunctionStack
                ((arg, callEnv) :: restArgs) rest}
        have hstepBeta : ChannelInternalStep s sBody := by
          have happ :
              ChannelInternalStep
                {s with
                  control := .value v
                  stack :=
                    .function (.closure x (.lam y body') cloX) ::
                      argumentThenFunctionStack
                        ((arg, callEnv) :: restArgs) rest}
                sBody :=
            ChannelInternalStep.beta (s := s) (x := x)
              (body := .lam y body') (closureEnv := cloX) (arg := v)
              (rest :=
                argumentThenFunctionStack
                  ((arg, callEnv) :: restArgs) rest)
          exact hsEq.symm ▸ happ
        have hscopedBody : ChannelConfig.WellScoped sBody :=
          ChannelInternalStep.preserve_wellScoped hstepBeta hscoped
        have habs : LamAbsorbsThenAdmin
            ((arg, callEnv) :: restArgs).length body' :=
          hbody'
        have hchild :=
          hlam (s := sBody) (x := y) (body := body') rfl rfl habs
            hscopedBody hrelBody
        exact beta_presentedChannelConfigCompleteness D₀ j₀ realize
          (s := s) (x := x) (body := .lam y body')
          (closureEnv := cloX) (arg := v)
          (rest :=
            argumentThenFunctionStack
              ((arg, callEnv) :: restArgs) rest)
          hc hs hrel hchild
      exact ⟨hlam, hval,
        fun {s} {code} {x} {body} {cloX} {answer} =>
          admin_noapp_under_function_argument_then_function_spine_of_value
            D₀ j₀ realize ((arg, callEnv) :: restArgs) rest hval⟩

theorem lam_under_argument_then_function_spine_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hargs : ArgumentFramesOk args) (hok : FunctionSpineOk rest)
    {s : ChannelConfig C} {x : Name}
    {body : Term (QubitPrimitive C)} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.lam x body))
    (hs : s.stack = argumentThenFunctionStack args rest)
    (habs : LamAbsorbsThenAdmin args.length body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer :=
  (argument_then_function_spine_presented D₀ j₀ realize args rest
    hargs hok).1 hc hs habs hscoped hrel

theorem value_under_function_argument_then_function_spine_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hargs : ArgumentFramesOk args) (hok : FunctionSpineOk rest)
    {s : ChannelConfig C} {arg : RuntimeValue C} {x : Name}
    {body : Term (QubitPrimitive C)} {cloX : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .value arg)
    (hs : s.stack =
      .function (.closure x body cloX) ::
        argumentThenFunctionStack args rest)
    (hbody : BodyUnderArgsThenAdmin args.length body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer :=
  (argument_then_function_spine_presented D₀ j₀ realize args rest
    hargs hok).2.1 hc hs hbody hscoped hrel

theorem admin_noapp_under_function_argument_then_function_spine_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hargs : ArgumentFramesOk args) (hok : FunctionSpineOk rest)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {x : Name} {body : Term (QubitPrimitive C)} {cloX : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack =
      .function (.closure x body cloX) ::
        argumentThenFunctionStack args rest)
    (hbody : BodyUnderArgsThenAdmin args.length body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer :=
  (argument_then_function_spine_presented D₀ j₀ realize args rest
    hargs hok).2.2 hadmin hc hs hbody hscoped hrel

/-- Inner `app (lam x body) arg` under leftover argument frames over a
residual function-frame spine. -/
theorem app_lam_under_argument_then_function_spine_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hargs : ArgumentFramesOk args) (hok : FunctionSpineOk rest)
    {s : ChannelConfig C} {x : Name}
    {body arg : Term (QubitPrimitive C)} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.app (.lam x body) arg))
    (hs : s.stack = argumentThenFunctionStack args rest)
    (hadminArg : AdminNoApp arg)
    (hbody : BodyUnderArgsThenAdmin args.length body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsApp :
      {s with control := .term (.app (.lam x body) arg)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app (.lam x body) arg)} answer :=
    hsApp.symm ▸ hrel
  have hrelLam :=
    channel_config_application D₀ j₀ (s := s) (fn := .lam x body)
      (arg := arg) hrelApp
  have hrelClo :=
    channel_config_lambda D₀ j₀
      (s := {s with stack := .argument arg s.env :: s.stack})
      hrelLam
  have hrelArg :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {s with
          control := .value (.closure x body s.env)
          stack := .argument arg s.env :: s.stack})
      (fn := .closure x body s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack) hrelClo
  let sArg : ChannelConfig C :=
    {s with
      control := .term arg
      stack := .function (.closure x body s.env) :: s.stack}
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.lam x body)
        stack := .argument arg s.env :: s.stack} := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app (.lam x body) arg)}
          {s with
            control := .term (.lam x body)
            stack := .argument arg s.env :: s.stack} :=
      ChannelInternalStep.application (s := s)
        (fn := .lam x body) (arg := arg)
    exact hsApp.symm ▸ happ
  have hstepLam : ChannelInternalStep
      {s with
        control := .term (.lam x body)
        stack := .argument arg s.env :: s.stack}
      {s with
        control := .value (.closure x body s.env)
        stack := .argument arg s.env :: s.stack} :=
    ChannelInternalStep.lambda
      (s := {s with stack := .argument arg s.env :: s.stack})
      (x := x) (body := body)
  have hstepArg : ChannelInternalStep
      {s with
        control := .value (.closure x body s.env)
        stack := .argument arg s.env :: s.stack}
      sArg :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {s with
          control := .value (.closure x body s.env)
          stack := .argument arg s.env :: s.stack})
      (fn := .closure x body s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack)
  have hscopedArg : ChannelConfig.WellScoped sArg :=
    ChannelInternalStep.preserve_wellScoped hstepArg
      (ChannelInternalStep.preserve_wellScoped hstepLam
        (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
  have hsArg :
      sArg.stack =
        .function (.closure x body s.env) ::
          argumentThenFunctionStack args rest := by
    simp [sArg, hs]
  have harg :
      PresentedChannelConfigCompleteness D₀ j₀ realize sArg answer :=
    admin_noapp_under_function_argument_then_function_spine_presentedChannelConfigCompleteness
      D₀ j₀ realize args rest hargs hok (s := sArg) (code := arg)
      (x := x) (body := body) (cloX := s.env) hadminArg rfl hsArg
      hbody hscopedArg
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term arg
              env := s.env
              stack :=
                .function (.closure x body s.env) :: s.stack}
            _
        exact hrelArg)
  exact stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := x) (body := body) (arg := arg) hc hrel harg

/-- Closed triple curry under an outer lambda:
`app (lam x bodyX) (app (app (app (lam y (lam z (lam w body))) arg1) arg2) arg3)`. -/
theorem closed_lam_app_app_app_lam_lam_lam_admin_noapp_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x y z w : Name) (bodyX body arg1 arg2 arg3 : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.lam x bodyX)
        (.app (.app (.app (.lam y (.lam z (.lam w body))) arg1) arg2)
          arg3)))
    (hnoappX : NoApp bodyX)
    (hadminBody : AdminNoApp body)
    (hadmin1 : AdminNoApp arg1) (hadmin2 : AdminNoApp arg2)
    (hadmin3 : AdminNoApp arg3)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.app (.lam x bodyX)
          (.app (.app (.app (.lam y (.lam z (.lam w body))) arg1) arg2)
            arg3))
        quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.lam x bodyX)
          (.app (.app (.app (.lam y (.lam z (.lam w body))) arg1) arg2)
            arg3))
        semanticEnv) := by
  let inner : Term (QubitPrimitive C) :=
    .app (.app (.app (.lam y (.lam z (.lam w body))) arg1) arg2) arg3
  let code : Term (QubitPrimitive C) := .app (.lam x bodyX) inner
  let s : ChannelConfig C := initialChannelConfig code quantum
  have hc : s.control = .term code := rfl
  have hrel :=
    initialChannelConfig_related D₀ j₀ realize code quantum semanticEnv
  have hscoped :=
    initialChannelConfig_wellScoped hclosed quantum
  have hsApp :
      {s with control := .term (.app (.lam x bodyX) inner)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app (.lam x bodyX) inner)}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    hsApp.symm ▸ hrel
  have hrelLam :=
    channel_config_application D₀ j₀ (s := s)
      (fn := .lam x bodyX) (arg := inner) hrelApp
  have hrelClo :=
    channel_config_lambda D₀ j₀
      (s := {s with stack := .argument inner s.env :: s.stack})
      hrelLam
  have hrelInner :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {s with
          control := .value (.closure x bodyX s.env)
          stack := .argument inner s.env :: s.stack})
      (fn := .closure x bodyX s.env) (arg := inner)
      (callEnv := s.env) (rest := s.stack) hrelClo
  let sInner : ChannelConfig C :=
    {s with
      control := .term inner
      stack := .function (.closure x bodyX s.env) :: s.stack}
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.lam x bodyX)
        stack := .argument inner s.env :: s.stack} := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app (.lam x bodyX) inner)}
          {s with
            control := .term (.lam x bodyX)
            stack := .argument inner s.env :: s.stack} :=
      ChannelInternalStep.application (s := s)
        (fn := .lam x bodyX) (arg := inner)
    exact hsApp.symm ▸ happ
  have hstepLam : ChannelInternalStep
      {s with
        control := .term (.lam x bodyX)
        stack := .argument inner s.env :: s.stack}
      {s with
        control := .value (.closure x bodyX s.env)
        stack := .argument inner s.env :: s.stack} :=
    ChannelInternalStep.lambda
      (s := {s with stack := .argument inner s.env :: s.stack})
      (x := x) (body := bodyX)
  have hstepInner : ChannelInternalStep
      {s with
        control := .value (.closure x bodyX s.env)
        stack := .argument inner s.env :: s.stack}
      sInner :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {s with
          control := .value (.closure x bodyX s.env)
          stack := .argument inner s.env :: s.stack})
      (fn := .closure x bodyX s.env) (arg := inner)
      (callEnv := s.env) (rest := s.stack)
  have hscopedInner : ChannelConfig.WellScoped sInner :=
    ChannelInternalStep.preserve_wellScoped hstepInner
      (ChannelInternalStep.preserve_wellScoped hstepLam
        (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
  have hokX : FunctionSpineOk [(x, bodyX, s.env)] := hnoappX
  let inner2 : Term (QubitPrimitive C) :=
    .app (.app (.lam y (.lam z (.lam w body))) arg1) arg2
  have hsApp2 :
      {sInner with control := .term (.app inner2 arg3)} = sInner :=
    ChannelConfig.ext rfl rfl rfl rfl
  have hrelApp2 : ChannelConfigRel D₀ j₀ realize
      {sInner with control := .term (.app inner2 arg3)}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) := by
    change ChannelConfigRel D₀ j₀ realize
        {s with
          control := .term inner
          env := s.env
          stack := .function (.closure x bodyX s.env) :: s.stack}
        _
    exact hrelInner
  have hrelInner2 :=
    channel_config_application D₀ j₀ (s := sInner) (fn := inner2)
      (arg := arg3) hrelApp2
  let sInner2 : ChannelConfig C :=
    {sInner with
      control := .term inner2
      stack := .argument arg3 sInner.env :: sInner.stack}
  have hstepApp2 : ChannelInternalStep sInner sInner2 := by
    have happ :
        ChannelInternalStep
          {sInner with control := .term (.app inner2 arg3)}
          sInner2 :=
      ChannelInternalStep.application (s := sInner) (fn := inner2)
        (arg := arg3)
    exact hsApp2.symm ▸ happ
  have hscopedInner2 : ChannelConfig.WellScoped sInner2 :=
    ChannelInternalStep.preserve_wellScoped hstepApp2 hscopedInner
  let inner1 : Term (QubitPrimitive C) :=
    .app (.lam y (.lam z (.lam w body))) arg1
  have hsApp1 :
      {sInner2 with control := .term (.app inner1 arg2)} = sInner2 :=
    ChannelConfig.ext rfl rfl rfl rfl
  have hrelApp1 : ChannelConfigRel D₀ j₀ realize
      {sInner2 with control := .term (.app inner1 arg2)}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) := by
    change ChannelConfigRel D₀ j₀ realize
        {sInner with
          control := .term inner2
          env := sInner.env
          stack := .argument arg3 sInner.env :: sInner.stack}
        _
    exact hrelInner2
  have hrelInner1 :=
    channel_config_application D₀ j₀ (s := sInner2) (fn := inner1)
      (arg := arg2) hrelApp1
  let sInner1 : ChannelConfig C :=
    {sInner2 with
      control := .term inner1
      stack := .argument arg2 sInner2.env :: sInner2.stack}
  have hstepApp1 : ChannelInternalStep sInner2 sInner1 := by
    have happ :
        ChannelInternalStep
          {sInner2 with control := .term (.app inner1 arg2)}
          sInner1 :=
      ChannelInternalStep.application (s := sInner2) (fn := inner1)
        (arg := arg2)
    exact hsApp1.symm ▸ happ
  have hscopedInner1 : ChannelConfig.WellScoped sInner1 :=
    ChannelInternalStep.preserve_wellScoped hstepApp1 hscopedInner2
  have hsInner1 :
      sInner1.stack =
        argumentThenFunctionStack
          [(arg2, s.env), (arg3, s.env)] [(x, bodyX, s.env)] := by
    simp [sInner1, sInner2, sInner, s, argumentThenFunctionStack,
      initialChannelConfig, ofConfig, initialConfig]
  have hargs23 : ArgumentFramesOk [(arg2, s.env), (arg3, s.env)] := by
    intro p hp
    simp at hp
    rcases hp with h | h <;> cases h <;> assumption
  have hbodyYZ : BodyUnderArgsThenAdmin 2 (.lam z (.lam w body)) :=
    hadminBody
  have hinner1 :
      PresentedChannelConfigCompleteness D₀ j₀ realize sInner1
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    app_lam_under_argument_then_function_spine_presentedChannelConfigCompleteness
      D₀ j₀ realize [(arg2, s.env), (arg3, s.env)]
      [(x, bodyX, s.env)] hargs23 hokX (s := sInner1)
      (x := y) (body := .lam z (.lam w body)) (arg := arg1)
      rfl hsInner1 hadmin1 hbodyYZ hscopedInner1
      (by
        change ChannelConfigRel D₀ j₀ realize
            {sInner2 with
              control := .term inner1
              env := sInner2.env
              stack := .argument arg2 sInner2.env :: sInner2.stack}
            _
        exact hrelInner1)
  have hinner2 :
      PresentedChannelConfigCompleteness D₀ j₀ realize sInner2
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    application_presentedChannelConfigCompleteness D₀ j₀ realize
      (s := sInner2) (fn := inner1) (arg := arg2) rfl
      (by
        change ChannelConfigRel D₀ j₀ realize
            {sInner with
              control := .term inner2
              env := sInner.env
              stack := .argument arg3 sInner.env :: sInner.stack}
            _
        exact hrelInner2)
      hinner1
  have hinner :
      PresentedChannelConfigCompleteness D₀ j₀ realize sInner
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    application_presentedChannelConfigCompleteness D₀ j₀ realize
      (s := sInner) (fn := inner2) (arg := arg3) rfl
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term inner
              env := s.env
              stack := .function (.closure x bodyX s.env) :: s.stack}
            _
        exact hrelInner)
      hinner2
  exact (stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := x) (body := bodyX) (arg := inner) hc hrel
    hinner).complete

/-- Token adequacy for closed triple curry under an outer lambda. -/
theorem closed_lam_app_app_app_lam_lam_lam_admin_noapp_presented_token_adequacy
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x y z w : Name) (bodyX body arg1 arg2 arg3 : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.lam x bodyX)
        (.app (.app (.app (.lam y (.lam z (.lam w body))) arg1) arg2)
          arg3)))
    (hnoappX : NoApp bodyX)
    (hadminBody : AdminNoApp body)
    (hadmin1 : AdminNoApp arg1) (hadmin2 : AdminNoApp arg2)
    (hadmin3 : AdminNoApp arg3)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize)
          (.app (.lam x bodyX)
            (.app (.app (.app (.lam y (.lam z (.lam w body))) arg1)
                arg2)
              arg3))
          semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig
            (.app (.lam x bodyX)
              (.app (.app (.app (.lam y (.lam z (.lam w body))) arg1)
                  arg2)
                arg3))
            quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig
      (.app (.lam x bodyX)
        (.app (.app (.app (.lam y (.lam z (.lam w body))) arg1) arg2)
          arg3))
      quantum)
    (interp (hardwarePrimitive D₀ j₀ realize)
      (.app (.lam x bodyX)
        (.app (.app (.app (.lam y (.lam z (.lam w body))) arg1) arg2)
          arg3))
      semanticEnv)
    (closed_lam_app_app_app_lam_lam_lam_admin_noapp_presented_channelTreeCompleteness
      D₀ j₀ realize x y z w bodyX body arg1 arg2 arg3 hclosed hnoappX
      hadminBody hadmin1 hadmin2 hadmin3 quantum semanticEnv)
    selectors ξ k hk i token

/-- Value completeness under a mixed function/argument spine over a
residual function-frame spine. -/
def ValueUnderMixedThenFn {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)) :
    Prop :=
  ∀ {s : ChannelConfig C} {arg : RuntimeValue C}
    {answer : HSemanticComp D₀ j₀},
    s.control = .value arg →
    s.stack = mixedThenFunctionStack fns args rest →
    MixedThenFnOk fns args rest →
    ArgumentFramesOk args →
    ChannelConfig.WellScoped s →
    ChannelConfigRel D₀ j₀ realize s answer →
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer

theorem pauliX_under_mixed_then_fn_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderMixedThenFn D₀ j₀ realize fns args rest)
    {s : ChannelConfig C} {value : C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack = mixedThenFunctionStack fns args rest)
    (hok : MixedThenFnOk fns args rest) (hargs : ArgumentFramesOk args)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsPx :
      {s with control := .term (.prim (.pauliX value))} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  obtain ⟨semanticEnv, kStack, henv, hstack, rfl⟩ :=
    channelConfigRel_term_inv D₀ j₀ hc hrel
  let sVal : ChannelConfig C :=
    {s with
      control := .value (.payload value)
      quantum := applyOperation Qubit.pauliXOp s.quantum}
  have hstep : ChannelInternalStep s sVal := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.prim (.pauliX value))}
          sVal :=
      ChannelInternalStep.pauliXPrimitive (s := s) (value := value)
    exact hsPx.symm ▸ happ
  have hscopedVal : ChannelConfig.WellScoped sVal :=
    ChannelInternalStep.preserve_wellScoped hstep hscoped
  have hrelVal : ChannelConfigRel D₀ j₀ realize sVal
      (kStack
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) (realize value))) :=
    ⟨semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (realize value),
      kStack,
      ControlRel.value _ _ s.env
        (payload_related D₀ j₀ realize value),
      hstack, rfl⟩
  have hval :=
    hVal (s := sVal) (arg := .payload value) rfl hs hok hargs
      hscopedVal hrelVal
  refine
    { related := hrel
      complete := ?_ }
  constructor
  intro selectors i ξ kξ hk
  have hchildEq :=
    hval.complete.selected_result_eq_channelTree_sup_presented
      selectors i ξ kξ hk
  have hden :
      interp (hardwarePrimitive D₀ j₀ realize)
          (.prim (.pauliX value)) semanticEnv =
        taggedEmbed
          (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
            (realize value)) := by
    simp [hardwarePrimitive_pauliX]
  have hne : s.stack ≠ [] := by
    rw [hs]
    exact hok.stack_ne_nil
  let unitVal : HSemanticComp D₀ j₀ :=
    semanticUnit (Q := TTExternalContinuationPower 2)
      (D₀ := D₀) (j₀ := j₀) (realize value)
  let opVal : HSemanticComp D₀ j₀ :=
    taggedEmbed
      (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
        (realize value))
  have hchildCoord :
      kStack unitVal (HardwareAdequacy.encodePath selectors i) kξ =
        sSup (channelTreeResults D₀ j₀ realize sVal selectors i
          kξ) := by
    have hsel :
        HardwareAdequacy.selectPath selectors (kStack unitVal) i kξ =
          kStack unitVal (HardwareAdequacy.encodePath selectors i)
            kξ :=
      congrArg (fun f => f kξ)
        (HardwareAdequacy.selectPath_apply_encode selectors
          (kStack unitVal) i)
    exact hsel.symm.trans hchildEq
  have hselParent :
      HardwareAdequacy.selectPath selectors (kStack opVal) i kξ =
        kStack opVal (HardwareAdequacy.encodePath selectors i) kξ :=
    congrArg (fun f => f kξ)
      (HardwareAdequacy.selectPath_apply_encode selectors
        (kStack opVal) i)
  have hop :
      kStack opVal (HardwareAdequacy.encodePath selectors i) kξ =
        embed (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
            (realize value))
          (ScottMap.const
            (kStack unitVal (HardwareAdequacy.encodePath selectors i)
              kξ)) :=
    stackRel_ofOperation_eval D₀ j₀ hstack hne
      Qubit.pauliXOp (realize value)
      (HardwareAdequacy.encodePath selectors i) kξ
  rw [hden, hselParent, hop, hchildCoord, embed_ofOperation_const_sSup]
  apply le_antisymm
  · apply sSup_le
    rintro T ⟨r, ⟨fuel, child, R, hdepth, rfl⟩, rfl⟩
    apply le_sSup
    refine ⟨fuel + 1, ChannelTree.internal hstep child,
      wrapInternalRealization D₀ j₀ realize hstep child R, ?_, ?_⟩
    · change child.depth + 1 ≤ fuel + 1
      omega
    · exact
        (restrictedResult_internal_pauliX D₀ j₀ realize hstep hc
          child
          (wrapInternalRealization D₀ j₀ realize hstep child R)
          selectors i ξ kξ hk).symm
  · apply sSup_le
    rintro T ⟨_, tree, R, _, rfl⟩
    cases tree with
    | terminal hterm =>
        cases hterm.control_eq.symm.trans hc
    | @internal _ t' h next =>
        have ht : t' = sVal :=
          ChannelInternalStep.eq_config_of_pauliX h hc
        subst t'
        rw [restrictedResult_internal_pauliX D₀ j₀ realize h hc
          next R selectors i ξ kξ hk]
        apply le_sSup
        refine ⟨restrictedResult D₀ j₀ realize next
            (internalChildRealization D₀ j₀ realize h next R)
            selectors i kξ,
          ⟨next.depth, next,
            internalChildRealization D₀ j₀ realize h next R,
            le_rfl, rfl⟩, rfl⟩
    | external _ hex _ =>
        exact False.elim (ChannelExternalStep.not_prim hex hc)
    | probability _ _ _ _ =>
        cases hc
    | probabilityZero _ =>
        cases hc
    | probabilityOne _ =>
        cases hc
    | measurement _ _ =>
        cases hc

theorem admin_noapp_under_mixed_then_fn_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderMixedThenFn D₀ j₀ realize fns args rest)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack = mixedThenFunctionStack fns args rest)
    (hok : MixedThenFnOk fns args rest) (hargs : ArgumentFramesOk args)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  induction code generalizing s answer with
  | var z =>
      have hctl := hscoped.left
      rw [hc] at hctl
      obtain ⟨v, hlookup⟩ := hctl.right z (by simp [free])
      have hsVar :
          {s with control := .term (.var z)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelVar : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.var z)} answer :=
        hsVar.symm ▸ hrel
      have hrelVal :=
        channel_config_variable D₀ j₀ hlookup hrelVar
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value v} :=
        ⟨⟨hctl.left, hctl.left z v hlookup⟩, hscoped.right⟩
      have hval :=
        hVal (s := {s with control := .value v}) (arg := v)
          rfl hs hok hargs hscopedVal hrelVal
      exact variable_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hlookup hrel hval
  | app _ _ =>
      exact False.elim hadmin
  | lam z M _ih =>
      have hsLam :
          {s with control := .term (.lam z M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelLam : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.lam z M)} answer :=
        hsLam.symm ▸ hrel
      have hrelVal :=
        channel_config_lambda D₀ j₀ (s := s) hrelLam
      have hstepLam : ChannelInternalStep s
          {s with control := .value (.closure z M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.lam z M)}
              {s with control := .value (.closure z M s.env)} :=
          ChannelInternalStep.lambda (s := s) (x := z) (body := M)
        exact hsLam.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.closure z M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepLam hscoped
      have hval :=
        hVal (s := {s with control := .value (.closure z M s.env)})
          (arg := .closure z M s.env) rfl hs hok hargs hscopedVal
          hrelVal
      exact lambda_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hrel hval
  | recLam self z M _ih =>
      have hsRec :
          {s with control := .term (.recLam self z M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelRec : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.recLam self z M)} answer :=
        hsRec.symm ▸ hrel
      have hrelVal :=
        channel_config_recursive D₀ j₀ (s := s) hrelRec
      have hstepRec : ChannelInternalStep s
          {s with control := .value (.recClosure self z M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.recLam self z M)}
              {s with
                control := .value (.recClosure self z M s.env)} :=
          ChannelInternalStep.recursive (s := s) (self := self)
            (arg := z) (body := M)
        exact hsRec.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.recClosure self z M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepRec hscoped
      have hval :=
        hVal
          (s :=
            {s with control := .value (.recClosure self z M s.env)})
          (arg := .recClosure self z M s.env) rfl hs hok hargs
          hscopedVal hrelVal
      exact recLam_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hrel hval
  | intern left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hadmin
      have hscopedL :=
        wellScoped_term_child (child := left) hc hscoped
          (fun z hz => by simp [free, hz])
      have hscopedR :=
        wellScoped_term_child (child := right) hc hscoped
          (fun z hz => by simp [free, hz])
      refine intern_related_presentedChannelConfigCompleteness
        D₀ j₀ realize hc hrel ?_ ?_
      · intro semanticEnv k henv hstack
        exact ihL hnaL (s := {s with control := .term left}) rfl hs
          hscopedL
          ⟨interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv, k,
            ControlRel.term left s.env semanticEnv henv, hstack, rfl⟩
      · intro semanticEnv k henv hstack
        exact ihR hnaR (s := {s with control := .term right}) rfl hs
          hscopedR
          ⟨interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv, k,
            ControlRel.term right s.env semanticEnv henv, hstack, rfl⟩
  | extern _ _ _ _ =>
      exact False.elim hadmin
  | prob p left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hadmin
      have hscopedL :=
        wellScoped_term_child (child := left) hc hscoped
          (fun z hz => by simp [free, hz])
      have hscopedR :=
        wellScoped_term_child (child := right) hc hscoped
          (fun z hz => by simp [free, hz])
      refine prob_related_presentedChannelConfigCompleteness
        D₀ j₀ realize hc hrel ?_ ?_
      · intro semanticEnv k quantum henv hstack
        exact ihL hnaL
          (s := {s with control := .term left, quantum := quantum})
          rfl hs ⟨hscopedL.left, hscopedL.right⟩
          ⟨interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv, k,
            ControlRel.term left s.env semanticEnv henv, hstack, rfl⟩
      · intro semanticEnv k quantum henv hstack
        exact ihR hnaR
          (s := {s with control := .term right, quantum := quantum})
          rfl hs ⟨hscopedR.left, hscopedR.right⟩
          ⟨interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv, k,
            ControlRel.term right s.env semanticEnv henv, hstack, rfl⟩
  | prim prim =>
      cases prim with
      | ret value =>
          have hsRet :
              {s with control := .term (.prim (.ret value))} = s :=
            ChannelConfig.ext hc.symm rfl rfl rfl
          have hrelRet : ChannelConfigRel D₀ j₀ realize
              {s with control := .term (.prim (.ret value))} answer :=
            hsRet.symm ▸ hrel
          have hrelVal :=
            channel_config_return D₀ j₀ hrelRet
          have hstepRet : ChannelInternalStep s
              {s with control := .value (.payload value)} := by
            have happ :
                ChannelInternalStep
                  {s with control := .term (.prim (.ret value))}
                  {s with control := .value (.payload value)} :=
              ChannelInternalStep.returnPrimitive (s := s)
                (value := value)
            exact hsRet.symm ▸ happ
          have hscopedVal : ChannelConfig.WellScoped
              {s with control := .value (.payload value)} :=
            ChannelInternalStep.preserve_wellScoped hstepRet hscoped
          have hval :=
            hVal (s := {s with control := .value (.payload value)})
              (arg := .payload value) rfl hs hok hargs hscopedVal
              hrelVal
          exact return_presentedChannelConfigCompleteness D₀ j₀ realize
            hc hrel hval
      | pauliX value =>
          exact
            pauliX_under_mixed_then_fn_of_value
              D₀ j₀ realize fns args rest hVal hc hs hok hargs
              hscoped hrel
      | measureZ _ _ =>
          exact False.elim hadmin

theorem mixed_then_fn_spine_presented
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : MixedThenFnOk fns args rest)
    (_hargs : ArgumentFramesOk args) :
    ValueUnderMixedThenFn D₀ j₀ realize fns args rest ∧
      (∀ {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
          {answer : HSemanticComp D₀ j₀},
        AdminNoApp code →
        s.control = .term code →
        s.stack = mixedThenFunctionStack fns args rest →
        MixedThenFnOk fns args rest →
        ArgumentFramesOk args →
        ChannelConfig.WellScoped s →
        ChannelConfigRel D₀ j₀ realize s answer →
        PresentedChannelConfigCompleteness D₀ j₀ realize s answer) := by
  induction fns with
  | nil => exact False.elim hok
  | cons p restFns ih =>
      rcases p with ⟨x, body, clo⟩
      cases restFns with
      | nil =>
          have ⟨hbody, hokRest⟩ := MixedThenFnOk_singleton.mp hok
          have hval : ValueUnderMixedThenFn D₀ j₀ realize
              [(x, body, clo)] args rest := by
            intro s arg answer hc hs _hok hargs' hscoped hrel
            have hs' : s.stack =
                .function (.closure x body clo) ::
                  argumentThenFunctionStack args rest := by
              simpa [mixedThenFunctionStack] using hs
            exact
              value_under_function_argument_then_function_spine_presentedChannelConfigCompleteness
                D₀ j₀ realize args rest hargs' hokRest hc hs' hbody
                hscoped hrel
          exact ⟨hval,
            fun {s} {code} {answer} =>
              admin_noapp_under_mixed_then_fn_of_value
                D₀ j₀ realize [(x, body, clo)] args rest hval⟩
      | cons q rest' =>
          have ⟨hadminY, hokRest⟩ :=
            (MixedThenFnOk_cons_cons
              (x := x) (body := body) (clo := clo) (y := q)
              (restFns := rest') (args := args) (rest := rest)).mp hok
          obtain ⟨ihVal, ihAdmin⟩ := ih hokRest
          have hval : ValueUnderMixedThenFn D₀ j₀ realize
              ((x, body, clo) :: q :: rest') args rest := by
            intro s arg answer hc hs _hok' hargs' hscoped hrel
            have hsEq :
                {s with
                  control := .value arg
                  stack :=
                    .function (.closure x body clo) ::
                      mixedThenFunctionStack (q :: rest') args
                        rest} = s :=
              ChannelConfig.ext hc.symm rfl hs.symm rfl
            have hrel' : ChannelConfigRel D₀ j₀ realize
                {s with
                  control := .value arg
                  stack :=
                    .function (.closure x body clo) ::
                      mixedThenFunctionStack (q :: rest') args
                        rest}
                answer :=
              hsEq.symm ▸ hrel
            have hrelBody :=
              channel_config_beta D₀ j₀ (s := s) (x := x)
                (body := body) (closureEnv := clo) (arg := arg)
                (rest :=
                  mixedThenFunctionStack (q :: rest') args rest)
                hrel'
            let sBody : ChannelConfig C :=
              {s with
                control := .term body
                env := RuntimeEnv.bind x arg clo
                stack :=
                  mixedThenFunctionStack (q :: rest') args rest}
            have hstepBeta : ChannelInternalStep s sBody := by
              have happ :
                  ChannelInternalStep
                    {s with
                      control := .value arg
                      stack :=
                        .function (.closure x body clo) ::
                          mixedThenFunctionStack (q :: rest') args
                            rest}
                    sBody :=
                ChannelInternalStep.beta (s := s) (x := x)
                  (body := body) (closureEnv := clo) (arg := arg)
                  (rest :=
                    mixedThenFunctionStack (q :: rest') args rest)
              exact hsEq.symm ▸ happ
            have hscopedBody : ChannelConfig.WellScoped sBody :=
              ChannelInternalStep.preserve_wellScoped hstepBeta hscoped
            have hchild :=
              ihAdmin (s := sBody) (code := body) hadminY rfl rfl
                hokRest hargs' hscopedBody hrelBody
            exact beta_presentedChannelConfigCompleteness D₀ j₀ realize
              (s := s) (x := x) (body := body) (closureEnv := clo)
              (arg := arg)
              (rest :=
                mixedThenFunctionStack (q :: rest') args rest)
              hc hs hrel hchild
          exact ⟨hval,
            fun {s} {code} {answer} =>
              admin_noapp_under_mixed_then_fn_of_value
                D₀ j₀ realize ((x, body, clo) :: q :: rest') args
                rest hval⟩

theorem admin_noapp_under_mixed_then_fn_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : MixedThenFnOk fns args rest)
    (hargs : ArgumentFramesOk args)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack = mixedThenFunctionStack fns args rest)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer :=
  (mixed_then_fn_spine_presented D₀ j₀ realize fns args rest hok
    hargs).2 hadmin hc hs hok hargs hscoped hrel

theorem app_lam_under_mixed_then_fn_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hok : MixedThenFnOk fns args rest)
    (hargs : ArgumentFramesOk args)
    {s : ChannelConfig C} {y : Name}
    {bodyY arg : Term (QubitPrimitive C)} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.app (.lam y bodyY) arg))
    (hs : s.stack = mixedThenFunctionStack fns args rest)
    (hadminY : AdminNoApp bodyY) (hadminArg : AdminNoApp arg)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsApp :
      {s with control := .term (.app (.lam y bodyY) arg)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app (.lam y bodyY) arg)} answer :=
    hsApp.symm ▸ hrel
  have hrelLam :=
    channel_config_application D₀ j₀ (s := s)
      (fn := .lam y bodyY) (arg := arg) hrelApp
  have hrelClo :=
    channel_config_lambda D₀ j₀
      (s := {s with stack := .argument arg s.env :: s.stack})
      hrelLam
  have hrelArg :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {s with
          control := .value (.closure y bodyY s.env)
          stack := .argument arg s.env :: s.stack})
      (fn := .closure y bodyY s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack) hrelClo
  let sArg : ChannelConfig C :=
    {s with
      control := .term arg
      stack := .function (.closure y bodyY s.env) :: s.stack}
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.lam y bodyY)
        stack := .argument arg s.env :: s.stack} := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app (.lam y bodyY) arg)}
          {s with
            control := .term (.lam y bodyY)
            stack := .argument arg s.env :: s.stack} :=
      ChannelInternalStep.application (s := s)
        (fn := .lam y bodyY) (arg := arg)
    exact hsApp.symm ▸ happ
  have hstepLam : ChannelInternalStep
      {s with
        control := .term (.lam y bodyY)
        stack := .argument arg s.env :: s.stack}
      {s with
        control := .value (.closure y bodyY s.env)
        stack := .argument arg s.env :: s.stack} :=
    ChannelInternalStep.lambda
      (s := {s with stack := .argument arg s.env :: s.stack})
      (x := y) (body := bodyY)
  have hstepArg : ChannelInternalStep
      {s with
        control := .value (.closure y bodyY s.env)
        stack := .argument arg s.env :: s.stack}
      sArg :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {s with
          control := .value (.closure y bodyY s.env)
          stack := .argument arg s.env :: s.stack})
      (fn := .closure y bodyY s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack)
  have hscopedArg : ChannelConfig.WellScoped sArg :=
    ChannelInternalStep.preserve_wellScoped hstepArg
      (ChannelInternalStep.preserve_wellScoped hstepLam
        (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
  have hsArg :
      sArg.stack =
        mixedThenFunctionStack ((y, bodyY, s.env) :: fns) args
          rest := by
    simp [sArg, hs, mixedThenFunctionStack]
  have hokFull : MixedThenFnOk ((y, bodyY, s.env) :: fns) args rest :=
    MixedThenFnOk.cons hok.ne_nil hadminY hok
  have harg :
      PresentedChannelConfigCompleteness D₀ j₀ realize sArg answer :=
    admin_noapp_under_mixed_then_fn_presentedChannelConfigCompleteness
      D₀ j₀ realize ((y, bodyY, s.env) :: fns) args rest hokFull
      hargs (s := sArg) (code := arg) hadminArg rfl hsArg hscopedArg
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term arg
              env := s.env
              stack :=
                .function (.closure y bodyY s.env) :: s.stack}
            _
        exact hrelArg)
  exact stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := y) (body := bodyY) (arg := arg) hc hrel harg

/-- Closed mixed left-and-right nest under an outer lambda. -/
theorem closed_lam_mixed_lam_app_lam_admin_noapp_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (a x y z : Name)
    (bodyA body bodyZ arg arg2 : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.lam a bodyA)
        (.app (.app (.lam x (.lam y body)) (.app (.lam z bodyZ) arg))
          arg2)))
    (hnoappA : NoApp bodyA)
    (hadminBody : AdminNoApp body)
    (hadminZ : AdminNoApp bodyZ)
    (hadminArg : AdminNoApp arg) (hadmin2 : AdminNoApp arg2)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.app (.lam a bodyA)
          (.app (.app (.lam x (.lam y body)) (.app (.lam z bodyZ) arg))
            arg2))
        quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.lam a bodyA)
          (.app (.app (.lam x (.lam y body)) (.app (.lam z bodyZ) arg))
            arg2))
        semanticEnv) := by
  let innerApp : Term (QubitPrimitive C) := .app (.lam z bodyZ) arg
  let inner : Term (QubitPrimitive C) :=
    .app (.lam x (.lam y body)) innerApp
  let mixed : Term (QubitPrimitive C) := .app inner arg2
  let code : Term (QubitPrimitive C) := .app (.lam a bodyA) mixed
  let s : ChannelConfig C := initialChannelConfig code quantum
  have hc : s.control = .term code := rfl
  have hrel :=
    initialChannelConfig_related D₀ j₀ realize code quantum semanticEnv
  have hscoped :=
    initialChannelConfig_wellScoped hclosed quantum
  have hsApp :
      {s with control := .term (.app (.lam a bodyA) mixed)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app (.lam a bodyA) mixed)}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    hsApp.symm ▸ hrel
  have hrelLamA :=
    channel_config_application D₀ j₀ (s := s)
      (fn := .lam a bodyA) (arg := mixed) hrelApp
  have hrelCloA :=
    channel_config_lambda D₀ j₀
      (s := {s with stack := .argument mixed s.env :: s.stack})
      hrelLamA
  have hrelMixed :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {s with
          control := .value (.closure a bodyA s.env)
          stack := .argument mixed s.env :: s.stack})
      (fn := .closure a bodyA s.env) (arg := mixed)
      (callEnv := s.env) (rest := s.stack) hrelCloA
  let sMixed : ChannelConfig C :=
    {s with
      control := .term mixed
      stack := .function (.closure a bodyA s.env) :: s.stack}
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.lam a bodyA)
        stack := .argument mixed s.env :: s.stack} := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app (.lam a bodyA) mixed)}
          {s with
            control := .term (.lam a bodyA)
            stack := .argument mixed s.env :: s.stack} :=
      ChannelInternalStep.application (s := s)
        (fn := .lam a bodyA) (arg := mixed)
    exact hsApp.symm ▸ happ
  have hstepLamA : ChannelInternalStep
      {s with
        control := .term (.lam a bodyA)
        stack := .argument mixed s.env :: s.stack}
      {s with
        control := .value (.closure a bodyA s.env)
        stack := .argument mixed s.env :: s.stack} :=
    ChannelInternalStep.lambda
      (s := {s with stack := .argument mixed s.env :: s.stack})
      (x := a) (body := bodyA)
  have hstepMixed : ChannelInternalStep
      {s with
        control := .value (.closure a bodyA s.env)
        stack := .argument mixed s.env :: s.stack}
      sMixed :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {s with
          control := .value (.closure a bodyA s.env)
          stack := .argument mixed s.env :: s.stack})
      (fn := .closure a bodyA s.env) (arg := mixed)
      (callEnv := s.env) (rest := s.stack)
  have hscopedMixed : ChannelConfig.WellScoped sMixed :=
    ChannelInternalStep.preserve_wellScoped hstepMixed
      (ChannelInternalStep.preserve_wellScoped hstepLamA
        (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
  have hokA : FunctionSpineOk [(a, bodyA, s.env)] := hnoappA
  have hsApp2 :
      {sMixed with control := .term (.app inner arg2)} = sMixed :=
    ChannelConfig.ext rfl rfl rfl rfl
  have hrelApp2 : ChannelConfigRel D₀ j₀ realize
      {sMixed with control := .term (.app inner arg2)}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) := by
    change ChannelConfigRel D₀ j₀ realize
        {s with
          control := .term mixed
          env := s.env
          stack := .function (.closure a bodyA s.env) :: s.stack}
        _
    exact hrelMixed
  have hrelInner :=
    channel_config_application D₀ j₀ (s := sMixed) (fn := inner)
      (arg := arg2) hrelApp2
  let sInner : ChannelConfig C :=
    {sMixed with
      control := .term inner
      stack := .argument arg2 sMixed.env :: sMixed.stack}
  have hstepApp2 : ChannelInternalStep sMixed sInner := by
    have happ :
        ChannelInternalStep
          {sMixed with control := .term (.app inner arg2)} sInner :=
      ChannelInternalStep.application (s := sMixed) (fn := inner)
        (arg := arg2)
    exact hsApp2.symm ▸ happ
  have hscopedInner : ChannelConfig.WellScoped sInner :=
    ChannelInternalStep.preserve_wellScoped hstepApp2 hscopedMixed
  have hsApp1 :
      {sInner with
          control := .term (.app (.lam x (.lam y body)) innerApp)} =
        sInner :=
    ChannelConfig.ext rfl rfl rfl rfl
  have hrelApp1 : ChannelConfigRel D₀ j₀ realize
      {sInner with
        control := .term (.app (.lam x (.lam y body)) innerApp)}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) := by
    change ChannelConfigRel D₀ j₀ realize
        {sMixed with
          control := .term inner
          env := sMixed.env
          stack := .argument arg2 sMixed.env :: sMixed.stack}
        _
    exact hrelInner
  have hrelLam :=
    channel_config_application D₀ j₀ (s := sInner)
      (fn := .lam x (.lam y body)) (arg := innerApp) hrelApp1
  have hrelClo :=
    channel_config_lambda D₀ j₀
      (s :=
        {sInner with
          stack := .argument innerApp sInner.env :: sInner.stack})
      hrelLam
  have hrelArg :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {sInner with
          control := .value (.closure x (.lam y body) sInner.env)
          stack := .argument innerApp sInner.env :: sInner.stack})
      (fn := .closure x (.lam y body) sInner.env) (arg := innerApp)
      (callEnv := sInner.env) (rest := sInner.stack) hrelClo
  let sArg : ChannelConfig C :=
    {sInner with
      control := .term innerApp
      stack :=
        .function (.closure x (.lam y body) sInner.env) ::
          sInner.stack}
  have hstepApp1 : ChannelInternalStep sInner
      {sInner with
        control := .term (.lam x (.lam y body))
        stack := .argument innerApp sInner.env :: sInner.stack} := by
    have happ :
        ChannelInternalStep
          {sInner with
            control := .term (.app (.lam x (.lam y body)) innerApp)}
          {sInner with
            control := .term (.lam x (.lam y body))
            stack := .argument innerApp sInner.env :: sInner.stack} :=
      ChannelInternalStep.application (s := sInner)
        (fn := .lam x (.lam y body)) (arg := innerApp)
    exact hsApp1.symm ▸ happ
  have hstepLam : ChannelInternalStep
      {sInner with
        control := .term (.lam x (.lam y body))
        stack := .argument innerApp sInner.env :: sInner.stack}
      {sInner with
        control := .value (.closure x (.lam y body) sInner.env)
        stack := .argument innerApp sInner.env :: sInner.stack} :=
    ChannelInternalStep.lambda
      (s :=
        {sInner with
          stack := .argument innerApp sInner.env :: sInner.stack})
      (x := x) (body := .lam y body)
  have hstepArg : ChannelInternalStep
      {sInner with
        control := .value (.closure x (.lam y body) sInner.env)
        stack := .argument innerApp sInner.env :: sInner.stack}
      sArg :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {sInner with
          control := .value (.closure x (.lam y body) sInner.env)
          stack := .argument innerApp sInner.env :: sInner.stack})
      (fn := .closure x (.lam y body) sInner.env) (arg := innerApp)
      (callEnv := sInner.env) (rest := sInner.stack)
  have hscopedArg : ChannelConfig.WellScoped sArg :=
    ChannelInternalStep.preserve_wellScoped hstepArg
      (ChannelInternalStep.preserve_wellScoped hstepLam
        (ChannelInternalStep.preserve_wellScoped hstepApp1
          hscopedInner))
  have hsArg :
      sArg.stack =
        mixedThenFunctionStack [(x, .lam y body, s.env)]
          [(arg2, s.env)] [(a, bodyA, s.env)] := by
    simp [sArg, sInner, sMixed, s, initialChannelConfig, ofConfig,
      initialConfig, mixedThenFunctionStack, argumentThenFunctionStack]
  have hok : MixedThenFnOk [(x, .lam y body, s.env)]
      [(arg2, s.env)] [(a, bodyA, s.env)] :=
    ⟨hadminBody, hokA⟩
  have hargs : ArgumentFramesOk [(arg2, s.env)] := by
    intro p hp
    simp at hp
    cases hp
    exact hadmin2
  have hinnerApp :
      PresentedChannelConfigCompleteness D₀ j₀ realize sArg
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    app_lam_under_mixed_then_fn_presentedChannelConfigCompleteness
      D₀ j₀ realize [(x, .lam y body, s.env)] [(arg2, s.env)]
      [(a, bodyA, s.env)] hok hargs (s := sArg) (y := z)
      (bodyY := bodyZ) (arg := arg) rfl hsArg hadminZ hadminArg
      hscopedArg
      (by
        change ChannelConfigRel D₀ j₀ realize
            {sInner with
              control := .term innerApp
              env := sInner.env
              stack :=
                .function (.closure x (.lam y body) sInner.env) ::
                  sInner.stack}
            _
        exact hrelArg)
  have hinner :
      PresentedChannelConfigCompleteness D₀ j₀ realize sInner
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
      (s := sInner) (x := x) (body := .lam y body) (arg := innerApp)
      rfl
      (by
        change ChannelConfigRel D₀ j₀ realize
            {sMixed with
              control := .term inner
              env := sMixed.env
              stack := .argument arg2 sMixed.env :: sMixed.stack}
            _
        exact hrelInner)
      hinnerApp
  have hmixed :
      PresentedChannelConfigCompleteness D₀ j₀ realize sMixed
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    application_presentedChannelConfigCompleteness D₀ j₀ realize
      (s := sMixed) (fn := inner) (arg := arg2) rfl
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term mixed
              env := s.env
              stack := .function (.closure a bodyA s.env) :: s.stack}
            _
        exact hrelMixed)
      hinner
  exact (stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := a) (body := bodyA) (arg := mixed) hc hrel
    hmixed).complete

theorem closed_lam_mixed_lam_app_lam_admin_noapp_presented_token_adequacy
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (a x y z : Name)
    (bodyA body bodyZ arg arg2 : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.lam a bodyA)
        (.app (.app (.lam x (.lam y body)) (.app (.lam z bodyZ) arg))
          arg2)))
    (hnoappA : NoApp bodyA)
    (hadminBody : AdminNoApp body)
    (hadminZ : AdminNoApp bodyZ)
    (hadminArg : AdminNoApp arg) (hadmin2 : AdminNoApp arg2)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize)
          (.app (.lam a bodyA)
            (.app (.app (.lam x (.lam y body))
                (.app (.lam z bodyZ) arg))
              arg2))
          semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig
            (.app (.lam a bodyA)
              (.app (.app (.lam x (.lam y body))
                  (.app (.lam z bodyZ) arg))
                arg2))
            quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig
      (.app (.lam a bodyA)
        (.app (.app (.lam x (.lam y body)) (.app (.lam z bodyZ) arg))
          arg2))
      quantum)
    (interp (hardwarePrimitive D₀ j₀ realize)
      (.app (.lam a bodyA)
        (.app (.app (.lam x (.lam y body)) (.app (.lam z bodyZ) arg))
          arg2))
      semanticEnv)
    (closed_lam_mixed_lam_app_lam_admin_noapp_presented_channelTreeCompleteness
      D₀ j₀ realize a x y z bodyA body bodyZ arg arg2 hclosed hnoappA
      hadminBody hadminZ hadminArg hadmin2 quantum semanticEnv)
    selectors ξ k hk i token

/-- Value completeness under one ordinary closure over a residual
recursive-closure frame. -/
def ValueUnderFunctionRecClosureNil {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (y : Name) (bodyY : Term (QubitPrimitive C))
    (cloY : RuntimeEnv C) (self x : Name)
    (body : Term (QubitPrimitive C)) (clo : RuntimeEnv C) : Prop :=
  ∀ {s : ChannelConfig C} {arg : RuntimeValue C}
    {answer : HSemanticComp D₀ j₀},
    s.control = .value arg →
    s.stack =
      [.function (.closure y bodyY cloY),
        .function (.recClosure self x body clo)] →
    ChannelConfig.WellScoped s →
    ChannelConfigRel D₀ j₀ realize s answer →
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer

theorem value_under_function_recClosure_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {arg : RuntimeValue C}
    {y self x : Name} {bodyY body : Term (QubitPrimitive C)}
    {cloY clo : RuntimeEnv C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .value arg)
    (hs : s.stack =
      [.function (.closure y bodyY cloY),
        .function (.recClosure self x body clo)])
    (hadminY : AdminNoApp bodyY) (hnoapp : NoApp body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsEq :
      {s with
        control := .value arg
        stack :=
          .function (.closure y bodyY cloY) ::
            [.function (.recClosure self x body clo)]} = s :=
    ChannelConfig.ext hc.symm rfl hs.symm rfl
  have hrel' : ChannelConfigRel D₀ j₀ realize
      {s with
        control := .value arg
        stack :=
          .function (.closure y bodyY cloY) ::
            [.function (.recClosure self x body clo)]}
      answer :=
    hsEq.symm ▸ hrel
  have hrelBody :=
    channel_config_beta D₀ j₀ (s := s) (x := y) (body := bodyY)
      (closureEnv := cloY) (arg := arg)
      (rest := [.function (.recClosure self x body clo)]) hrel'
  let sBody : ChannelConfig C :=
    {s with
      control := .term bodyY
      env := RuntimeEnv.bind y arg cloY
      stack := [.function (.recClosure self x body clo)]}
  have hstepBeta : ChannelInternalStep s sBody := by
    have happ :
        ChannelInternalStep
          {s with
            control := .value arg
            stack :=
              .function (.closure y bodyY cloY) ::
                [.function (.recClosure self x body clo)]}
          sBody :=
      ChannelInternalStep.beta (s := s) (x := y) (body := bodyY)
        (closureEnv := cloY) (arg := arg)
        (rest := [.function (.recClosure self x body clo)])
    exact hsEq.symm ▸ happ
  have hscopedBody : ChannelConfig.WellScoped sBody :=
    ChannelInternalStep.preserve_wellScoped hstepBeta hscoped
  have hchild :=
    admin_noapp_under_recClosure_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize (s := sBody) (code := bodyY) (self := self)
      (x := x) (body := body) (cloEnv := clo) hadminY rfl rfl hnoapp
      hscopedBody hrelBody
  exact beta_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := y) (body := bodyY) (closureEnv := cloY)
    (arg := arg) (rest := [.function (.recClosure self x body clo)])
    hc hs hrel hchild

theorem pauliX_under_function_recClosure_nil_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {y : Name} {bodyY : Term (QubitPrimitive C)}
    {cloY : RuntimeEnv C} {self x : Name}
    {body : Term (QubitPrimitive C)} {clo : RuntimeEnv C}
    (hVal : ValueUnderFunctionRecClosureNil D₀ j₀ realize
      y bodyY cloY self x body clo)
    {s : ChannelConfig C} {value : C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack =
      [.function (.closure y bodyY cloY),
        .function (.recClosure self x body clo)])
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsPx :
      {s with control := .term (.prim (.pauliX value))} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  obtain ⟨semanticEnv, kStack, henv, hstack, rfl⟩ :=
    channelConfigRel_term_inv D₀ j₀ hc hrel
  let sVal : ChannelConfig C :=
    {s with
      control := .value (.payload value)
      quantum := applyOperation Qubit.pauliXOp s.quantum}
  have hstep : ChannelInternalStep s sVal := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.prim (.pauliX value))}
          sVal :=
      ChannelInternalStep.pauliXPrimitive (s := s) (value := value)
    exact hsPx.symm ▸ happ
  have hscopedVal : ChannelConfig.WellScoped sVal :=
    ChannelInternalStep.preserve_wellScoped hstep hscoped
  have hrelVal : ChannelConfigRel D₀ j₀ realize sVal
      (kStack
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) (realize value))) :=
    ⟨semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (realize value),
      kStack,
      ControlRel.value _ _ s.env
        (payload_related D₀ j₀ realize value),
      hstack, rfl⟩
  have hval :=
    hVal (s := sVal) (arg := .payload value) rfl hs hscopedVal hrelVal
  refine
    { related := hrel
      complete := ?_ }
  constructor
  intro selectors i ξ kξ hk
  have hchildEq :=
    hval.complete.selected_result_eq_channelTree_sup_presented
      selectors i ξ kξ hk
  have hden :
      interp (hardwarePrimitive D₀ j₀ realize)
          (.prim (.pauliX value)) semanticEnv =
        taggedEmbed
          (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
            (realize value)) := by
    simp [hardwarePrimitive_pauliX]
  have hne : s.stack ≠ [] := by
    rw [hs]
    exact List.cons_ne_nil _ _
  let unitVal : HSemanticComp D₀ j₀ :=
    semanticUnit (Q := TTExternalContinuationPower 2)
      (D₀ := D₀) (j₀ := j₀) (realize value)
  let opVal : HSemanticComp D₀ j₀ :=
    taggedEmbed
      (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
        (realize value))
  have hchildCoord :
      kStack unitVal (HardwareAdequacy.encodePath selectors i) kξ =
        sSup (channelTreeResults D₀ j₀ realize sVal selectors i
          kξ) := by
    have hsel :
        HardwareAdequacy.selectPath selectors (kStack unitVal) i kξ =
          kStack unitVal (HardwareAdequacy.encodePath selectors i)
            kξ :=
      congrArg (fun f => f kξ)
        (HardwareAdequacy.selectPath_apply_encode selectors
          (kStack unitVal) i)
    exact hsel.symm.trans hchildEq
  have hselParent :
      HardwareAdequacy.selectPath selectors (kStack opVal) i kξ =
        kStack opVal (HardwareAdequacy.encodePath selectors i) kξ :=
    congrArg (fun f => f kξ)
      (HardwareAdequacy.selectPath_apply_encode selectors
        (kStack opVal) i)
  have hop :
      kStack opVal (HardwareAdequacy.encodePath selectors i) kξ =
        embed (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
            (realize value))
          (ScottMap.const
            (kStack unitVal (HardwareAdequacy.encodePath selectors i)
              kξ)) :=
    stackRel_ofOperation_eval D₀ j₀ hstack hne
      Qubit.pauliXOp (realize value)
      (HardwareAdequacy.encodePath selectors i) kξ
  rw [hden, hselParent, hop, hchildCoord, embed_ofOperation_const_sSup]
  apply le_antisymm
  · apply sSup_le
    rintro T ⟨r, ⟨fuel, child, R, hdepth, rfl⟩, rfl⟩
    apply le_sSup
    refine ⟨fuel + 1, ChannelTree.internal hstep child,
      wrapInternalRealization D₀ j₀ realize hstep child R, ?_, ?_⟩
    · change child.depth + 1 ≤ fuel + 1
      omega
    · exact
        (restrictedResult_internal_pauliX D₀ j₀ realize hstep hc
          child
          (wrapInternalRealization D₀ j₀ realize hstep child R)
          selectors i ξ kξ hk).symm
  · apply sSup_le
    rintro T ⟨_, tree, R, _, rfl⟩
    cases tree with
    | terminal hterm =>
        cases hterm.control_eq.symm.trans hc
    | @internal _ t' h next =>
        have ht : t' = sVal :=
          ChannelInternalStep.eq_config_of_pauliX h hc
        subst t'
        rw [restrictedResult_internal_pauliX D₀ j₀ realize h hc
          next R selectors i ξ kξ hk]
        apply le_sSup
        refine ⟨restrictedResult D₀ j₀ realize next
            (internalChildRealization D₀ j₀ realize h next R)
            selectors i kξ,
          ⟨next.depth, next,
            internalChildRealization D₀ j₀ realize h next R,
            le_rfl, rfl⟩, rfl⟩
    | external _ hex _ =>
        exact False.elim (ChannelExternalStep.not_prim hex hc)
    | probability _ _ _ _ =>
        cases hc
    | probabilityZero _ =>
        cases hc
    | probabilityOne _ =>
        cases hc
    | measurement _ _ =>
        cases hc

theorem admin_noapp_under_function_recClosure_nil_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {y : Name} {bodyY : Term (QubitPrimitive C)}
    {cloY : RuntimeEnv C} {self x : Name}
    {body : Term (QubitPrimitive C)} {clo : RuntimeEnv C}
    (hVal : ValueUnderFunctionRecClosureNil D₀ j₀ realize
      y bodyY cloY self x body clo)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack =
      [.function (.closure y bodyY cloY),
        .function (.recClosure self x body clo)])
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  induction code generalizing s answer with
  | var z =>
      have hctl := hscoped.left
      rw [hc] at hctl
      obtain ⟨v, hlookup⟩ := hctl.right z (by simp [free])
      have hsVar :
          {s with control := .term (.var z)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelVar : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.var z)} answer :=
        hsVar.symm ▸ hrel
      have hrelVal :=
        channel_config_variable D₀ j₀ hlookup hrelVar
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value v} :=
        ⟨⟨hctl.left, hctl.left z v hlookup⟩, hscoped.right⟩
      have hval :=
        hVal (s := {s with control := .value v}) (arg := v)
          rfl hs hscopedVal hrelVal
      exact variable_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hlookup hrel hval
  | app _ _ =>
      exact False.elim hadmin
  | lam z M _ih =>
      have hsLam :
          {s with control := .term (.lam z M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelLam : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.lam z M)} answer :=
        hsLam.symm ▸ hrel
      have hrelVal :=
        channel_config_lambda D₀ j₀ (s := s) hrelLam
      have hstepLam : ChannelInternalStep s
          {s with control := .value (.closure z M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.lam z M)}
              {s with control := .value (.closure z M s.env)} :=
          ChannelInternalStep.lambda (s := s) (x := z) (body := M)
        exact hsLam.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.closure z M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepLam hscoped
      have hval :=
        hVal (s := {s with control := .value (.closure z M s.env)})
          (arg := .closure z M s.env) rfl hs hscopedVal hrelVal
      exact lambda_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hrel hval
  | recLam recSelf z M _ih =>
      have hsRec :
          {s with control := .term (.recLam recSelf z M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelRec : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.recLam recSelf z M)} answer :=
        hsRec.symm ▸ hrel
      have hrelVal :=
        channel_config_recursive D₀ j₀ (s := s) hrelRec
      have hstepRec : ChannelInternalStep s
          {s with
            control := .value (.recClosure recSelf z M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.recLam recSelf z M)}
              {s with
                control := .value (.recClosure recSelf z M s.env)} :=
          ChannelInternalStep.recursive (s := s) (self := recSelf)
            (arg := z) (body := M)
        exact hsRec.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with
            control := .value (.recClosure recSelf z M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepRec hscoped
      have hval :=
        hVal
          (s :=
            {s with
              control := .value (.recClosure recSelf z M s.env)})
          (arg := .recClosure recSelf z M s.env) rfl hs hscopedVal
          hrelVal
      exact recLam_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hrel hval
  | intern left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hadmin
      have hscopedL :=
        wellScoped_term_child (child := left) hc hscoped
          (fun z hz => by simp [free, hz])
      have hscopedR :=
        wellScoped_term_child (child := right) hc hscoped
          (fun z hz => by simp [free, hz])
      refine intern_related_presentedChannelConfigCompleteness
        D₀ j₀ realize hc hrel ?_ ?_
      · intro semanticEnv k henv hstack
        exact ihL hnaL (s := {s with control := .term left}) rfl hs
          hscopedL
          ⟨interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv, k,
            ControlRel.term left s.env semanticEnv henv, hstack, rfl⟩
      · intro semanticEnv k henv hstack
        exact ihR hnaR (s := {s with control := .term right}) rfl hs
          hscopedR
          ⟨interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv, k,
            ControlRel.term right s.env semanticEnv henv, hstack, rfl⟩
  | extern _ _ _ _ =>
      exact False.elim hadmin
  | prob p left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hadmin
      have hscopedL :=
        wellScoped_term_child (child := left) hc hscoped
          (fun z hz => by simp [free, hz])
      have hscopedR :=
        wellScoped_term_child (child := right) hc hscoped
          (fun z hz => by simp [free, hz])
      refine prob_related_presentedChannelConfigCompleteness
        D₀ j₀ realize hc hrel ?_ ?_
      · intro semanticEnv k quantum henv hstack
        exact ihL hnaL
          (s := {s with control := .term left, quantum := quantum})
          rfl hs ⟨hscopedL.left, hscopedL.right⟩
          ⟨interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv, k,
            ControlRel.term left s.env semanticEnv henv, hstack, rfl⟩
      · intro semanticEnv k quantum henv hstack
        exact ihR hnaR
          (s := {s with control := .term right, quantum := quantum})
          rfl hs ⟨hscopedR.left, hscopedR.right⟩
          ⟨interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv, k,
            ControlRel.term right s.env semanticEnv henv, hstack, rfl⟩
  | prim prim =>
      cases prim with
      | ret value =>
          have hsRet :
              {s with control := .term (.prim (.ret value))} = s :=
            ChannelConfig.ext hc.symm rfl rfl rfl
          have hrelRet : ChannelConfigRel D₀ j₀ realize
              {s with control := .term (.prim (.ret value))} answer :=
            hsRet.symm ▸ hrel
          have hrelVal :=
            channel_config_return D₀ j₀ hrelRet
          have hstepRet : ChannelInternalStep s
              {s with control := .value (.payload value)} := by
            have happ :
                ChannelInternalStep
                  {s with control := .term (.prim (.ret value))}
                  {s with control := .value (.payload value)} :=
              ChannelInternalStep.returnPrimitive (s := s)
                (value := value)
            exact hsRet.symm ▸ happ
          have hscopedVal : ChannelConfig.WellScoped
              {s with control := .value (.payload value)} :=
            ChannelInternalStep.preserve_wellScoped hstepRet hscoped
          have hval :=
            hVal (s := {s with control := .value (.payload value)})
              (arg := .payload value) rfl hs hscopedVal hrelVal
          exact return_presentedChannelConfigCompleteness D₀ j₀ realize
            hc hrel hval
      | pauliX value =>
          exact
            pauliX_under_function_recClosure_nil_of_value
              D₀ j₀ realize hVal hc hs hscoped hrel
      | measureZ _ _ =>
          exact False.elim hadmin

theorem admin_noapp_under_function_recClosure_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {y self x : Name} {bodyY body : Term (QubitPrimitive C)}
    {cloY clo : RuntimeEnv C} {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack =
      [.function (.closure y bodyY cloY),
        .function (.recClosure self x body clo)])
    (hadminY : AdminNoApp bodyY) (hnoapp : NoApp body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hVal : ValueUnderFunctionRecClosureNil D₀ j₀ realize
      y bodyY cloY self x body clo := by
    intro s' arg answer' hc' hs' hscoped' hrel'
    exact
      value_under_function_recClosure_nil_presentedChannelConfigCompleteness
        D₀ j₀ realize hc' hs' hadminY hnoapp hscoped' hrel'
  exact admin_noapp_under_function_recClosure_nil_of_value
    D₀ j₀ realize hVal hadmin hc hs hscoped hrel

/-- Inner `app (lam y bodyY) arg` under one residual recursive-closure
frame. -/
theorem app_lam_under_recClosure_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {y self x : Name}
    {bodyY body arg : Term (QubitPrimitive C)}
    {clo : RuntimeEnv C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.app (.lam y bodyY) arg))
    (hs : s.stack = [.function (.recClosure self x body clo)])
    (hadminY : AdminNoApp bodyY) (hadminArg : AdminNoApp arg)
    (hnoapp : NoApp body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsApp :
      {s with control := .term (.app (.lam y bodyY) arg)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app (.lam y bodyY) arg)} answer :=
    hsApp.symm ▸ hrel
  have hrelLam :=
    channel_config_application D₀ j₀ (s := s)
      (fn := .lam y bodyY) (arg := arg) hrelApp
  have hrelClo :=
    channel_config_lambda D₀ j₀
      (s := {s with stack := .argument arg s.env :: s.stack})
      hrelLam
  have hrelArg :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {s with
          control := .value (.closure y bodyY s.env)
          stack := .argument arg s.env :: s.stack})
      (fn := .closure y bodyY s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack) hrelClo
  let sArg : ChannelConfig C :=
    {s with
      control := .term arg
      stack := .function (.closure y bodyY s.env) :: s.stack}
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.lam y bodyY)
        stack := .argument arg s.env :: s.stack} := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app (.lam y bodyY) arg)}
          {s with
            control := .term (.lam y bodyY)
            stack := .argument arg s.env :: s.stack} :=
      ChannelInternalStep.application (s := s)
        (fn := .lam y bodyY) (arg := arg)
    exact hsApp.symm ▸ happ
  have hstepLam : ChannelInternalStep
      {s with
        control := .term (.lam y bodyY)
        stack := .argument arg s.env :: s.stack}
      {s with
        control := .value (.closure y bodyY s.env)
        stack := .argument arg s.env :: s.stack} :=
    ChannelInternalStep.lambda
      (s := {s with stack := .argument arg s.env :: s.stack})
      (x := y) (body := bodyY)
  have hstepArg : ChannelInternalStep
      {s with
        control := .value (.closure y bodyY s.env)
        stack := .argument arg s.env :: s.stack}
      sArg :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {s with
          control := .value (.closure y bodyY s.env)
          stack := .argument arg s.env :: s.stack})
      (fn := .closure y bodyY s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack)
  have hscopedArg : ChannelConfig.WellScoped sArg :=
    ChannelInternalStep.preserve_wellScoped hstepArg
      (ChannelInternalStep.preserve_wellScoped hstepLam
        (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
  have hsArg :
      sArg.stack =
        [.function (.closure y bodyY s.env),
          .function (.recClosure self x body clo)] := by
    simp [sArg, hs]
  have harg :
      PresentedChannelConfigCompleteness D₀ j₀ realize sArg answer :=
    admin_noapp_under_function_recClosure_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize (s := sArg) (code := arg) (y := y) (self := self)
      (x := x) (bodyY := bodyY) (body := body) (cloY := s.env)
      (clo := clo) hadminArg rfl hsArg hadminY hnoapp hscopedArg
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term arg
              env := s.env
              stack :=
                .function (.closure y bodyY s.env) :: s.stack}
            _
        exact hrelArg)
  exact stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := y) (body := bodyY) (arg := arg) hc hrel harg

/-- Closed `app (recLam self x body) (app (lam y bodyY) arg)`. -/
theorem closed_recLam_app_lam_admin_noapp_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self x y : Name) (body bodyY arg : Term (QubitPrimitive C))
    (hclosed : Closed (.app (.recLam self x body) (.app (.lam y bodyY) arg)))
    (hnoapp : NoApp body)
    (hadminY : AdminNoApp bodyY) (hadminArg : AdminNoApp arg)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.app (.recLam self x body) (.app (.lam y bodyY) arg)) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.recLam self x body) (.app (.lam y bodyY) arg))
        semanticEnv) := by
  let inner : Term (QubitPrimitive C) := .app (.lam y bodyY) arg
  let code : Term (QubitPrimitive C) := .app (.recLam self x body) inner
  let s : ChannelConfig C := initialChannelConfig code quantum
  have hc : s.control = .term code := rfl
  have hrel :=
    initialChannelConfig_related D₀ j₀ realize code quantum semanticEnv
  have hscoped :=
    initialChannelConfig_wellScoped hclosed quantum
  have hsApp :
      {s with control := .term (.app (.recLam self x body) inner)} =
        s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app (.recLam self x body) inner)}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    hsApp.symm ▸ hrel
  have hrelRec :=
    channel_config_application D₀ j₀ (s := s)
      (fn := .recLam self x body) (arg := inner) hrelApp
  have hrelClo :=
    channel_config_recursive D₀ j₀
      (s := {s with stack := .argument inner s.env :: s.stack})
      hrelRec
  have hrelInner :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {s with
          control := .value (.recClosure self x body s.env)
          stack := .argument inner s.env :: s.stack})
      (fn := .recClosure self x body s.env) (arg := inner)
      (callEnv := s.env) (rest := s.stack) hrelClo
  let sInner : ChannelConfig C :=
    {s with
      control := .term inner
      stack := .function (.recClosure self x body s.env) :: s.stack}
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.recLam self x body)
        stack := .argument inner s.env :: s.stack} := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app (.recLam self x body) inner)}
          {s with
            control := .term (.recLam self x body)
            stack := .argument inner s.env :: s.stack} :=
      ChannelInternalStep.application (s := s)
        (fn := .recLam self x body) (arg := inner)
    exact hsApp.symm ▸ happ
  have hstepRec : ChannelInternalStep
      {s with
        control := .term (.recLam self x body)
        stack := .argument inner s.env :: s.stack}
      {s with
        control := .value (.recClosure self x body s.env)
        stack := .argument inner s.env :: s.stack} :=
    ChannelInternalStep.recursive
      (s := {s with stack := .argument inner s.env :: s.stack})
      (self := self) (arg := x) (body := body)
  have hstepInner : ChannelInternalStep
      {s with
        control := .value (.recClosure self x body s.env)
        stack := .argument inner s.env :: s.stack}
      sInner :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {s with
          control := .value (.recClosure self x body s.env)
          stack := .argument inner s.env :: s.stack})
      (fn := .recClosure self x body s.env) (arg := inner)
      (callEnv := s.env) (rest := s.stack)
  have hscopedInner : ChannelConfig.WellScoped sInner :=
    ChannelInternalStep.preserve_wellScoped hstepInner
      (ChannelInternalStep.preserve_wellScoped hstepRec
        (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
  have hsInner :
      sInner.stack = [.function (.recClosure self x body s.env)] := by
    simp [sInner, s, initialChannelConfig, ofConfig, initialConfig]
  have hinner :
      PresentedChannelConfigCompleteness D₀ j₀ realize sInner
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    app_lam_under_recClosure_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize (s := sInner) (y := y) (self := self) (x := x)
      (bodyY := bodyY) (body := body) (arg := arg) (clo := s.env)
      rfl hsInner hadminY hadminArg hnoapp hscopedInner
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term inner
              env := s.env
              stack :=
                .function (.recClosure self x body s.env) :: s.stack}
            _
        exact hrelInner)
  exact (stacked_recLam_app_presentedChannelConfigCompleteness
    D₀ j₀ realize (s := s) (self := self) (x := x) (body := body)
    (arg := inner) hc hrel hinner).complete

theorem closed_recLam_app_lam_admin_noapp_presented_token_adequacy
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self x y : Name) (body bodyY arg : Term (QubitPrimitive C))
    (hclosed : Closed (.app (.recLam self x body) (.app (.lam y bodyY) arg)))
    (hnoapp : NoApp body)
    (hadminY : AdminNoApp bodyY) (hadminArg : AdminNoApp arg)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize)
          (.app (.recLam self x body) (.app (.lam y bodyY) arg))
          semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig
            (.app (.recLam self x body) (.app (.lam y bodyY) arg))
            quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig
      (.app (.recLam self x body) (.app (.lam y bodyY) arg)) quantum)
    (interp (hardwarePrimitive D₀ j₀ realize)
      (.app (.recLam self x body) (.app (.lam y bodyY) arg))
      semanticEnv)
    (closed_recLam_app_lam_admin_noapp_presented_channelTreeCompleteness
      D₀ j₀ realize self x y body bodyY arg hclosed hnoapp hadminY
      hadminArg quantum semanticEnv)
    selectors ξ k hk i token

/-- Administrative NoApp at an empty stack, including lambdas whose
bodies still contain applications. -/
theorem empty_stack_admin_noapp_presentedChannelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {semanticEnv : Env (HSemanticValue D₀ j₀)}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code) (hs : s.stack = [])
    (hscoped : ChannelConfig.WellScoped s)
    (henv : EnvRel D₀ j₀ realize s.env semanticEnv) :
    PresentedChannelTreeCompleteness D₀ j₀ realize s
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) := by
  induction code generalizing s semanticEnv with
  | var x =>
      have hctl := hscoped.left
      rw [hc] at hctl
      obtain ⟨v, hlookup⟩ := hctl.right x (by simp [free])
      have hrel :
          ChannelConfigRel D₀ j₀ realize
            {s with control := .term (.var x)}
            (interp (hardwarePrimitive D₀ j₀ realize) (.var x)
              semanticEnv) :=
        ⟨interp (hardwarePrimitive D₀ j₀ realize) (.var x) semanticEnv,
          id, ControlRel.term _ s.env semanticEnv henv,
          (by rw [hs]; exact StackRel.nil), rfl⟩
      have hrelv :=
        channel_config_variable D₀ j₀ hlookup hrel
      have hscopedv : ChannelConfig.WellScoped
          {s with control := .value v} :=
        ⟨⟨hctl.left, hctl.left x v hlookup⟩, hscoped.right⟩
      have hchild :
          PresentedChannelConfigCompleteness D₀ j₀ realize
            {s with control := .value v}
            (interp (hardwarePrimitive D₀ j₀ realize) (.var x)
              semanticEnv) :=
        { related := hrelv
          complete :=
            terminal_presentedChannelTreeCompleteness D₀ j₀ realize
              (s := {s with control := .value v})
              ⟨v, rfl, hs⟩ hscopedv hrelv }
      exact PresentedChannelTreeCompleteness.congr
        (show {s with control := .term (.var x)} = s from
          ChannelConfig.ext hc.symm rfl rfl rfl)
        rfl
        (variable_presentedChannelConfigCompleteness D₀ j₀ realize
          (s := {s with control := .term (.var x)}) rfl hlookup hrel
          hchild).complete
  | app _ _ =>
      exact False.elim hadmin
  | lam x body _ih =>
      exact lam_terminal_presentedChannelTreeCompleteness D₀ j₀ realize
        hc hs hscoped henv
  | recLam self arg body _ih =>
      exact recLam_terminal_presentedChannelTreeCompleteness D₀ j₀ realize
        hc hs hscoped henv
  | intern left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hadmin
      have hctl := hscoped.left
      rw [hc] at hctl
      have hscopedL : ChannelConfig.WellScoped
          {s with control := .term left} :=
        ⟨⟨hctl.left, fun x hx => hctl.right x (by simp [free, hx])⟩,
          hscoped.right⟩
      have hscopedR : ChannelConfig.WellScoped
          {s with control := .term right} :=
        ⟨⟨hctl.left, fun x hx => hctl.right x (by simp [free, hx])⟩,
          hscoped.right⟩
      have hL :=
        ihL hnaL (s := {s with control := .term left})
          (semanticEnv := semanticEnv) rfl hs hscopedL henv
      have hR :=
        ihR hnaR (s := {s with control := .term right})
          (semanticEnv := semanticEnv) rfl hs hscopedR henv
      exact PresentedChannelTreeCompleteness.congr
        (show {s with control := .term (.intern left right)} = s from
          ChannelConfig.ext hc.symm rfl rfl rfl)
        rfl
        (intern_empty_presentedChannelTreeCompleteness D₀ j₀ realize
          s left right semanticEnv hL hR)
  | extern _ _ =>
      exact False.elim hadmin
  | prob p left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hadmin
      have hctl := hscoped.left
      rw [hc] at hctl
      have hscopedL : ChannelConfig.WellScoped
          {s with control := .term left} :=
        ⟨⟨hctl.left, fun x hx => hctl.right x (by simp [free, hx])⟩,
          hscoped.right⟩
      have hscopedR : ChannelConfig.WellScoped
          {s with control := .term right} :=
        ⟨⟨hctl.left, fun x hx => hctl.right x (by simp [free, hx])⟩,
          hscoped.right⟩
      if hI : 0 ≤ p ∧ p ≤ 1 then
        if hp0 : p = 0 then
          subst p
          have hR :=
            ihR hnaR (s := {s with control := .term right})
              (semanticEnv := semanticEnv) rfl hs hscopedR henv
          exact PresentedChannelTreeCompleteness.congr
            (show {s with control := .term (.prob 0 left right)} = s from
              ChannelConfig.ext hc.symm rfl rfl rfl)
            rfl
            (prob_zero_empty_presentedChannelTreeCompleteness D₀ j₀ realize
              s left right semanticEnv hR)
        else if hp1 : p = 1 then
          subst p
          have hL :=
            ihL hnaL (s := {s with control := .term left})
              (semanticEnv := semanticEnv) rfl hs hscopedL henv
          exact PresentedChannelTreeCompleteness.congr
            (show {s with control := .term (.prob 1 left right)} = s from
              ChannelConfig.ext hc.symm rfl rfl rfl)
            rfl
            (prob_one_empty_presentedChannelTreeCompleteness D₀ j₀ realize
              s left right semanticEnv hL)
        else
          have hp0ne : p ≠ 0 := hp0
          have hp1ne : p ≠ 1 := hp1
          have hp₀ : 0 < p := lt_of_le_of_ne hI.1 hp0ne.symm
          have hp₁ : p < 1 := lt_of_le_of_ne hI.2 hp1ne
          have hL :=
            ihL hnaL
              (s :=
                { s with
                  control := .term left
                  quantum := applyOperation
                    (sourceProbabilityOperation p hp₀.le hp₁.le)
                    s.quantum })
              (semanticEnv := semanticEnv) rfl hs hscopedL henv
          have hR :=
            ihR hnaR
              (s :=
                { s with
                  control := .term right
                  quantum := applyOperation
                    (sourceProbabilityOperation (1 - p)
                      (sub_nonneg.mpr hp₁.le) (by linarith))
                    s.quantum })
              (semanticEnv := semanticEnv) rfl hs hscopedR henv
          exact PresentedChannelTreeCompleteness.congr
            (show {s with control := .term (.prob p left right)} = s from
              ChannelConfig.ext hc.symm rfl rfl rfl)
            rfl
            (prob_empty_presented_of_presented_children D₀ j₀ realize
              s p hp₀ hp₁ left right semanticEnv hL hR)
      else
        exact PresentedChannelTreeCompleteness.congr
          (show {s with control := .term (.prob p left right)} = s from
            ChannelConfig.ext hc.symm rfl rfl rfl)
          rfl
          (prob_invalid_empty_presentedChannelTreeCompleteness D₀ j₀ realize
            s p hI left right semanticEnv)
  | prim p =>
      cases p with
      | ret value =>
          exact return_empty_presentedChannelTreeCompleteness D₀ j₀ realize
            hc hs hscoped henv
      | pauliX value =>
          exact PresentedChannelTreeCompleteness.congr
            (show {s with control := .term (.prim (.pauliX value))} = s from
              ChannelConfig.ext hc.symm rfl rfl rfl)
            rfl
            (pauliX_empty_presentedChannelTreeCompleteness D₀ j₀ realize
              s value hs semanticEnv)
      | measureZ _ _ =>
          exact False.elim hadmin

/-- Value completeness under one closure whose body is already
presented at the empty stack. -/
def ValueUnderClosureOfBody {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x : Name) (body : Term (QubitPrimitive C))
    (cloEnv : RuntimeEnv C) : Prop :=
  ∀ {s : ChannelConfig C} {arg : RuntimeValue C}
    {answer : HSemanticComp D₀ j₀},
    s.control = .value arg →
    s.stack = [.function (.closure x body cloEnv)] →
    ChannelConfig.WellScoped s →
    ChannelConfigRel D₀ j₀ realize s answer →
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer

theorem value_under_closure_of_presented_body
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {arg : RuntimeValue C} {x : Name}
    {body : Term (QubitPrimitive C)} {cloEnv : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .value arg)
    (hs : s.stack = [.function (.closure x body cloEnv)])
    (_hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer)
    (hbody : PresentedChannelConfigCompleteness D₀ j₀ realize
      {s with
        control := .term body
        env := RuntimeEnv.bind x arg cloEnv
        stack := []}
      answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer :=
  beta_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := x) (body := body) (closureEnv := cloEnv)
    (arg := arg) (rest := []) hc hs hrel hbody

theorem pauliX_under_closure_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {x : Name} {body : Term (QubitPrimitive C)} {cloEnv : RuntimeEnv C}
    (hVal : ValueUnderClosureOfBody D₀ j₀ realize x body cloEnv)
    {s : ChannelConfig C} {value : C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack = [.function (.closure x body cloEnv)])
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsPx :
      {s with control := .term (.prim (.pauliX value))} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  obtain ⟨semanticEnv, kStack, henv, hstack, rfl⟩ :=
    channelConfigRel_term_inv D₀ j₀ hc hrel
  let sVal : ChannelConfig C :=
    {s with
      control := .value (.payload value)
      quantum := applyOperation Qubit.pauliXOp s.quantum}
  have hstep : ChannelInternalStep s sVal := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.prim (.pauliX value))}
          sVal :=
      ChannelInternalStep.pauliXPrimitive (s := s) (value := value)
    exact hsPx.symm ▸ happ
  have hscopedVal : ChannelConfig.WellScoped sVal :=
    ChannelInternalStep.preserve_wellScoped hstep hscoped
  have hrelVal : ChannelConfigRel D₀ j₀ realize sVal
      (kStack
        (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) (realize value))) :=
    ⟨semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (realize value),
      kStack,
      ControlRel.value _ _ s.env
        (payload_related D₀ j₀ realize value),
      hstack, rfl⟩
  have hval :=
    hVal (s := sVal) (arg := .payload value) rfl hs hscopedVal hrelVal
  refine
    { related := hrel
      complete := ?_ }
  constructor
  intro selectors i ξ kξ hk
  have hchildEq :=
    hval.complete.selected_result_eq_channelTree_sup_presented
      selectors i ξ kξ hk
  have hden :
      interp (hardwarePrimitive D₀ j₀ realize)
          (.prim (.pauliX value)) semanticEnv =
        taggedEmbed
          (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
            (realize value)) := by
    simp [hardwarePrimitive_pauliX]
  have hne : s.stack ≠ [] := by
    rw [hs]
    exact List.cons_ne_nil _ _
  let unitVal : HSemanticComp D₀ j₀ :=
    semanticUnit (Q := TTExternalContinuationPower 2)
      (D₀ := D₀) (j₀ := j₀) (realize value)
  let opVal : HSemanticComp D₀ j₀ :=
    taggedEmbed
      (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
        (realize value))
  have hchildCoord :
      kStack unitVal (HardwareAdequacy.encodePath selectors i) kξ =
        sSup (channelTreeResults D₀ j₀ realize sVal selectors i
          kξ) := by
    have hsel :
        HardwareAdequacy.selectPath selectors (kStack unitVal) i kξ =
          kStack unitVal (HardwareAdequacy.encodePath selectors i)
            kξ :=
      congrArg (fun f => f kξ)
        (HardwareAdequacy.selectPath_apply_encode selectors
          (kStack unitVal) i)
    exact hsel.symm.trans hchildEq
  have hselParent :
      HardwareAdequacy.selectPath selectors (kStack opVal) i kξ =
        kStack opVal (HardwareAdequacy.encodePath selectors i) kξ :=
    congrArg (fun f => f kξ)
      (HardwareAdequacy.selectPath_apply_encode selectors
        (kStack opVal) i)
  have hop :
      kStack opVal (HardwareAdequacy.encodePath selectors i) kξ =
        embed (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
            (realize value))
          (ScottMap.const
            (kStack unitVal (HardwareAdequacy.encodePath selectors i)
              kξ)) :=
    stackRel_ofOperation_eval D₀ j₀ hstack hne
      Qubit.pauliXOp (realize value)
      (HardwareAdequacy.encodePath selectors i) kξ
  rw [hden, hselParent, hop, hchildCoord, embed_ofOperation_const_sSup]
  apply le_antisymm
  · apply sSup_le
    rintro T ⟨r, ⟨fuel, child, R, hdepth, rfl⟩, rfl⟩
    apply le_sSup
    refine ⟨fuel + 1, ChannelTree.internal hstep child,
      wrapInternalRealization D₀ j₀ realize hstep child R, ?_, ?_⟩
    · change child.depth + 1 ≤ fuel + 1
      omega
    · exact
        (restrictedResult_internal_pauliX D₀ j₀ realize hstep hc
          child
          (wrapInternalRealization D₀ j₀ realize hstep child R)
          selectors i ξ kξ hk).symm
  · apply sSup_le
    rintro T ⟨_, tree, R, _, rfl⟩
    cases tree with
    | terminal hterm =>
        cases hterm.control_eq.symm.trans hc
    | @internal _ t' h next =>
        have ht : t' = sVal :=
          ChannelInternalStep.eq_config_of_pauliX h hc
        subst t'
        rw [restrictedResult_internal_pauliX D₀ j₀ realize h hc
          next R selectors i ξ kξ hk]
        apply le_sSup
        refine ⟨restrictedResult D₀ j₀ realize next
            (internalChildRealization D₀ j₀ realize h next R)
            selectors i kξ,
          ⟨next.depth, next,
            internalChildRealization D₀ j₀ realize h next R,
            le_rfl, rfl⟩, rfl⟩
    | external _ hex _ =>
        exact False.elim (ChannelExternalStep.not_prim hex hc)
    | probability _ _ _ _ =>
        cases hc
    | probabilityZero _ =>
        cases hc
    | probabilityOne _ =>
        cases hc
    | measurement _ _ =>
        cases hc

theorem admin_noapp_under_closure_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {x : Name} {body : Term (QubitPrimitive C)} {cloEnv : RuntimeEnv C}
    (hVal : ValueUnderClosureOfBody D₀ j₀ realize x body cloEnv)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack = [.function (.closure x body cloEnv)])
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  induction code generalizing s answer with
  | var z =>
      have hctl := hscoped.left
      rw [hc] at hctl
      obtain ⟨v, hlookup⟩ := hctl.right z (by simp [free])
      have hsVar :
          {s with control := .term (.var z)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelVar : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.var z)} answer :=
        hsVar.symm ▸ hrel
      have hrelVal :=
        channel_config_variable D₀ j₀ hlookup hrelVar
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value v} :=
        ⟨⟨hctl.left, hctl.left z v hlookup⟩, hscoped.right⟩
      have hval :=
        hVal (s := {s with control := .value v}) (arg := v)
          rfl hs hscopedVal hrelVal
      exact variable_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hlookup hrel hval
  | app _ _ =>
      exact False.elim hadmin
  | lam z M _ih =>
      have hsLam :
          {s with control := .term (.lam z M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelLam : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.lam z M)} answer :=
        hsLam.symm ▸ hrel
      have hrelVal :=
        channel_config_lambda D₀ j₀ (s := s) hrelLam
      have hstepLam : ChannelInternalStep s
          {s with control := .value (.closure z M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.lam z M)}
              {s with control := .value (.closure z M s.env)} :=
          ChannelInternalStep.lambda (s := s) (x := z) (body := M)
        exact hsLam.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.closure z M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepLam hscoped
      have hval :=
        hVal (s := {s with control := .value (.closure z M s.env)})
          (arg := .closure z M s.env) rfl hs hscopedVal hrelVal
      exact lambda_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hrel hval
  | recLam self z M _ih =>
      have hsRec :
          {s with control := .term (.recLam self z M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelRec : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.recLam self z M)} answer :=
        hsRec.symm ▸ hrel
      have hrelVal :=
        channel_config_recursive D₀ j₀ (s := s) hrelRec
      have hstepRec : ChannelInternalStep s
          {s with control := .value (.recClosure self z M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.recLam self z M)}
              {s with
                control := .value (.recClosure self z M s.env)} :=
          ChannelInternalStep.recursive (s := s) (self := self)
            (arg := z) (body := M)
        exact hsRec.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.recClosure self z M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepRec hscoped
      have hval :=
        hVal
          (s :=
            {s with control := .value (.recClosure self z M s.env)})
          (arg := .recClosure self z M s.env) rfl hs hscopedVal hrelVal
      exact recLam_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hrel hval
  | intern left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hadmin
      have hscopedL :=
        wellScoped_term_child (child := left) hc hscoped
          (fun z hz => by simp [free, hz])
      have hscopedR :=
        wellScoped_term_child (child := right) hc hscoped
          (fun z hz => by simp [free, hz])
      refine intern_related_presentedChannelConfigCompleteness
        D₀ j₀ realize hc hrel ?_ ?_
      · intro semanticEnv k henv hstack
        exact ihL hnaL (s := {s with control := .term left}) rfl hs
          hscopedL
          ⟨interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv, k,
            ControlRel.term left s.env semanticEnv henv, hstack, rfl⟩
      · intro semanticEnv k henv hstack
        exact ihR hnaR (s := {s with control := .term right}) rfl hs
          hscopedR
          ⟨interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv, k,
            ControlRel.term right s.env semanticEnv henv, hstack, rfl⟩
  | extern _ _ _ _ =>
      exact False.elim hadmin
  | prob p left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hadmin
      have hscopedL :=
        wellScoped_term_child (child := left) hc hscoped
          (fun z hz => by simp [free, hz])
      have hscopedR :=
        wellScoped_term_child (child := right) hc hscoped
          (fun z hz => by simp [free, hz])
      refine prob_related_presentedChannelConfigCompleteness
        D₀ j₀ realize hc hrel ?_ ?_
      · intro semanticEnv k quantum henv hstack
        exact ihL hnaL
          (s := {s with control := .term left, quantum := quantum})
          rfl hs ⟨hscopedL.left, hscopedL.right⟩
          ⟨interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv, k,
            ControlRel.term left s.env semanticEnv henv, hstack, rfl⟩
      · intro semanticEnv k quantum henv hstack
        exact ihR hnaR
          (s := {s with control := .term right, quantum := quantum})
          rfl hs ⟨hscopedR.left, hscopedR.right⟩
          ⟨interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv, k,
            ControlRel.term right s.env semanticEnv henv, hstack, rfl⟩
  | prim prim =>
      cases prim with
      | ret value =>
          have hsRet :
              {s with control := .term (.prim (.ret value))} = s :=
            ChannelConfig.ext hc.symm rfl rfl rfl
          have hrelRet : ChannelConfigRel D₀ j₀ realize
              {s with control := .term (.prim (.ret value))} answer :=
            hsRet.symm ▸ hrel
          have hrelVal :=
            channel_config_return D₀ j₀ hrelRet
          have hstepRet : ChannelInternalStep s
              {s with control := .value (.payload value)} := by
            have happ :
                ChannelInternalStep
                  {s with control := .term (.prim (.ret value))}
                  {s with control := .value (.payload value)} :=
              ChannelInternalStep.returnPrimitive (s := s)
                (value := value)
            exact hsRet.symm ▸ happ
          have hscopedVal : ChannelConfig.WellScoped
              {s with control := .value (.payload value)} :=
            ChannelInternalStep.preserve_wellScoped hstepRet hscoped
          have hval :=
            hVal (s := {s with control := .value (.payload value)})
              (arg := .payload value) rfl hs hscopedVal hrelVal
          exact return_presentedChannelConfigCompleteness D₀ j₀ realize
            hc hrel hval
      | pauliX value =>
          exact pauliX_under_closure_of_value D₀ j₀ realize hVal
            hc hs hscoped hrel
      | measureZ _ _ =>
          exact False.elim hadmin


end HardwareChannelSemantics
end QLambda
