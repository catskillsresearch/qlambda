/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.HardwareChannel.UnderFrame

/-!
# FunAppFrag and Produces inductions

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

/-- Value completeness under a list of ordinary closure frames. -/
def ValueUnderFunFrames {C : Type}
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
    ChannelConfig.WellScoped s →
    ChannelConfigRel D₀ j₀ realize s answer →
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer

theorem valueUnderFunFrames_nil
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀) :
    ValueUnderFunFrames D₀ j₀ realize [] := by
  intro s arg answer hc hs hscoped hrel
  exact
    { related := hrel
      complete :=
        terminal_presentedChannelTreeCompleteness D₀ j₀ realize
          ⟨arg, hc, hs⟩ hscoped hrel }

theorem pauliX_under_fun_frames_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderFunFrames D₀ j₀ realize frames)
    {s : ChannelConfig C} {value : C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack = functionStack frames)
    (hneFrames : frames ≠ [])
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
    hVal (s := sVal) (arg := .payload value) rfl hs hscopedVal
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
    intro hstack
    exact hneFrames (functionStack_eq_nil_iff.mp hstack)
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

theorem admin_noapp_under_fun_frames_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderFunFrames D₀ j₀ realize frames)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack = functionStack frames)
    (hneFrames : frames ≠ [])
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
          (arg := .recClosure self z M s.env) rfl hs hscopedVal
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
            pauliX_under_fun_frames_of_value
              D₀ j₀ realize frames hVal hc hs hneFrames hscoped hrel
      | measureZ _ _ =>
          exact False.elim hadmin

/-- Presented completeness for FunAppFrag at any ordinary-closure
function-frame stack, including the empty stack. -/
theorem funAppFrag_under_fun_frames_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hfrag : FunAppFrag code)
    (frames : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderFunFrames D₀ j₀ realize frames)
    (hc : s.control = .term code)
    (hs : s.stack = functionStack frames)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  revert frames s answer hVal hc hs hscoped hrel
  induction hfrag with
  | admin hadmin =>
      intro
        (s : ChannelConfig C) (answer : HSemanticComp D₀ j₀)
        (frames : List
          (Name × Term (QubitPrimitive C) × RuntimeEnv C))
        (hVal : ValueUnderFunFrames D₀ j₀ realize frames)
        hc hs hscoped hrel
      if hne : frames = [] then
        subst frames
        obtain ⟨semanticEnv, k, henv, hstack, heq⟩ :=
          channelConfigRel_term_inv D₀ j₀ hc hrel
        rw [hs] at hstack
        cases hstack
        exact
          { related := hrel
            complete :=
              PresentedChannelTreeCompleteness.congr rfl heq.symm
                (empty_stack_admin_noapp_presentedChannelTreeCompleteness
                  D₀ j₀ realize hadmin hc hs hscoped henv) }
      else
        exact admin_noapp_under_fun_frames_of_value
          D₀ j₀ realize frames hVal hadmin hc hs hne hscoped hrel
  | @app_lam x body arg hbody harg ihBody ihArg =>
      intro
        (s : ChannelConfig C) (answer : HSemanticComp D₀ j₀)
        (frames : List
          (Name × Term (QubitPrimitive C) × RuntimeEnv C))
        (hVal : ValueUnderFunFrames D₀ j₀ realize frames)
        hc hs hscoped hrel
      have hsApp :
          {s with control := .term (.app (.lam x body) arg)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelApp : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.app (.lam x body) arg)} answer :=
        hsApp.symm ▸ hrel
      have hrelLam :=
        channel_config_application D₀ j₀ (s := s)
          (fn := .lam x body) (arg := arg) hrelApp
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
            functionStack ((x, body, s.env) :: frames) := by
        simp [sArg, hs, functionStack]
      have hValNew : ValueUnderFunFrames D₀ j₀ realize
          ((x, body, s.env) :: frames) := by
        intro s' arg' answer' hc' hs' hscoped' hrel'
        have hsEq :
            {s' with
              control := .value arg'
              stack :=
                .function (.closure x body s.env) ::
                  functionStack frames} = s' :=
          ChannelConfig.ext hc'.symm rfl hs'.symm rfl
        have hrelBody :=
          channel_config_beta D₀ j₀ (s := s') (x := x) (body := body)
            (closureEnv := s.env) (arg := arg')
            (rest := functionStack frames)
            (hsEq.symm ▸ hrel')
        have hstepBeta : ChannelInternalStep s'
            {s' with
              control := .term body
              env := RuntimeEnv.bind x arg' s.env
              stack := functionStack frames} := by
          have happ :
              ChannelInternalStep
                {s' with
                  control := .value arg'
                  stack :=
                    .function (.closure x body s.env) ::
                      functionStack frames}
                {s' with
                  control := .term body
                  env := RuntimeEnv.bind x arg' s.env
                  stack := functionStack frames} :=
            ChannelInternalStep.beta (s := s') (x := x) (body := body)
              (closureEnv := s.env) (arg := arg')
              (rest := functionStack frames)
          exact hsEq.symm ▸ happ
        have hscopedBody : ChannelConfig.WellScoped
            {s' with
              control := .term body
              env := RuntimeEnv.bind x arg' s.env
              stack := functionStack frames} :=
          ChannelInternalStep.preserve_wellScoped hstepBeta hscoped'
        have hchild :=
          ihBody
            (s :=
              {s' with
                control := .term body
                env := RuntimeEnv.bind x arg' s.env
                stack := functionStack frames})
            (answer := answer') frames hVal rfl rfl hscopedBody
            hrelBody
        exact beta_presentedChannelConfigCompleteness D₀ j₀ realize
          hc' (by simpa [functionStack] using hs') hrel' hchild
      have hargComplete :
          PresentedChannelConfigCompleteness D₀ j₀ realize sArg
            answer :=
        ihArg (s := sArg) (answer := answer)
          ((x, body, s.env) :: frames) hValNew rfl hsArg hscopedArg
          (by
            change ChannelConfigRel D₀ j₀ realize
                {s with
                  control := .term arg
                  env := s.env
                  stack :=
                    .function (.closure x body s.env) :: s.stack}
                _
            exact hrelArg)
      exact stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀
        realize (s := s) (x := x) (body := body) (arg := arg)
        hc hrel hargComplete

/-- Empty-stack presented completeness for the body-and-argument
nested lambda application fragment. -/
theorem funAppFrag_empty_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hfrag : FunAppFrag code)
    (hc : s.control = .term code) (hs : s.stack = [])
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer :=
  funAppFrag_under_fun_frames_presentedChannelConfigCompleteness
    D₀ j₀ realize hfrag [] (valueUnderFunFrames_nil D₀ j₀ realize)
    hc (by simpa [functionStack] using hs) hscoped hrel

/-- Value completeness under one ordinary closure over leftover
argument frames. -/
def ValueUnderFnArg {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x : Name) (body : Term (QubitPrimitive C))
    (cloEnv : RuntimeEnv C)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C)) :
    Prop :=
  ∀ {s : ChannelConfig C} {arg : RuntimeValue C}
    {answer : HSemanticComp D₀ j₀},
    s.control = .value arg →
    s.stack =
      .function (.closure x body cloEnv) :: argumentStack frames →
    ChannelConfig.WellScoped s →
    ChannelConfigRel D₀ j₀ realize s answer →
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer

theorem pauliX_under_fn_arg_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
    {s : ChannelConfig C} {value : C} {x : Name}
    {body : Term (QubitPrimitive C)} {cloX : RuntimeEnv C}
    (hVal : ValueUnderFnArg D₀ j₀ realize x body cloX frames)
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack =
      .function (.closure x body cloX) :: argumentStack frames)
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
    hVal (s := sVal) (arg := .payload value) rfl hs hscopedVal
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

/-- Administrative NoApp under one function frame over leftover
arguments, given value completeness at that stack. -/
theorem admin_noapp_under_fn_arg_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {x : Name} {body : Term (QubitPrimitive C)} {cloX : RuntimeEnv C}
    (hVal : ValueUnderFnArg D₀ j₀ realize x body cloX frames)
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack =
      .function (.closure x body cloX) :: argumentStack frames)
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
          (arg := .recClosure self z M s.env) rfl hs hscopedVal
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
            pauliX_under_fn_arg_of_value
              D₀ j₀ realize frames hVal hc hs hscoped hrel
      | measureZ _ _ =>
          exact False.elim hadmin


def ValueUnderRecArg {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self x : Name) (body : Term (QubitPrimitive C))
    (cloEnv : RuntimeEnv C)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C)) :
    Prop :=
  ∀ {s : ChannelConfig C} {arg : RuntimeValue C}
    {answer : HSemanticComp D₀ j₀},
    s.control = .value arg →
    s.stack =
      .function (.recClosure self x body cloEnv) :: argumentStack frames →
    ChannelConfig.WellScoped s →
    ChannelConfigRel D₀ j₀ realize s answer →
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer

theorem pauliX_under_rec_arg_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
    {s : ChannelConfig C} {value : C} {self x : Name}
    {body : Term (QubitPrimitive C)} {cloX : RuntimeEnv C}
    (hVal : ValueUnderRecArg D₀ j₀ realize self x body cloX frames)
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack =
      .function (.recClosure self x body cloX) :: argumentStack frames)
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
    hVal (s := sVal) (arg := .payload value) rfl hs hscopedVal
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

/-- Administrative NoApp under one recursive-closure frame over leftover
arguments, given value completeness at that stack. -/
theorem admin_noapp_under_rec_arg_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {self x : Name} {body : Term (QubitPrimitive C)} {cloX : RuntimeEnv C}
    (hVal : ValueUnderRecArg D₀ j₀ realize self x body cloX frames)
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack =
      .function (.recClosure self x body cloX) :: argumentStack frames)
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
          (arg := .recClosure self z M s.env) rfl hs hscopedVal
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
            pauliX_under_rec_arg_of_value
              D₀ j₀ realize frames hVal hc hs hscoped hrel
      | measureZ _ _ =>
          exact False.elim hadmin

/-- Value completeness under a nonempty ordinary-closure spine over
leftover FunAppFrag argument frames. -/
def ValueUnderFunsThenArgs {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C)) :
    Prop :=
  ∀ {s : ChannelConfig C} {arg : RuntimeValue C}
    {answer : HSemanticComp D₀ j₀},
    s.control = .value arg →
    s.stack = mixedStack fns args →
    ChannelConfig.WellScoped s →
    ChannelConfigRel D₀ j₀ realize s answer →
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer

theorem valueUnderFunsThenArgs_of_fnArg
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {x : Name} {body : Term (QubitPrimitive C)} {cloX : RuntimeEnv C}
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderFnArg D₀ j₀ realize x body cloX frames) :
    ValueUnderFunsThenArgs D₀ j₀ realize [(x, body, cloX)] frames := by
  intro s arg answer hc hs hscoped hrel
  have hs' : s.stack =
      .function (.closure x body cloX) :: argumentStack frames := by
    simpa [mixedStack] using hs
  exact hVal hc hs' hscoped hrel

theorem valueUnderFnArg_of_funsThenArgs
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {x : Name} {body : Term (QubitPrimitive C)} {cloX : RuntimeEnv C}
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderFunsThenArgs D₀ j₀ realize [(x, body, cloX)] frames) :
    ValueUnderFnArg D₀ j₀ realize x body cloX frames := by
  intro s arg answer hc hs hscoped hrel
  have hs' : s.stack = mixedStack [(x, body, cloX)] frames := by
    simpa [mixedStack] using hs
  exact hVal hc hs' hscoped hrel

theorem pauliX_under_funs_then_args_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hne : fns ≠ [])
    (hVal : ValueUnderFunsThenArgs D₀ j₀ realize fns args)
    {s : ChannelConfig C} {value : C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack = mixedStack fns args)
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
    hVal (s := sVal) (arg := .payload value) rfl hs hscopedVal
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
  have hneStack : s.stack ≠ [] := by
    rw [hs]
    exact mixedStack_ne_nil hne
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
    stackRel_ofOperation_eval D₀ j₀ hstack hneStack
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

/-- Administrative NoApp under a nonempty ordinary-closure spine over
leftover argument frames, given value completeness at that stack. -/
theorem admin_noapp_under_funs_then_args_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hne : fns ≠ [])
    (hVal : ValueUnderFunsThenArgs D₀ j₀ realize fns args)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack = mixedStack fns args)
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
          (arg := .recClosure self z M s.env) rfl hs hscopedVal
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
            pauliX_under_funs_then_args_of_value
              D₀ j₀ realize fns args hne hVal hc hs hscoped hrel
      | measureZ _ _ =>
          exact False.elim hadmin

/-- Presented completeness for FunAppFrag under a nonempty ordinary
closure spine over leftover argument frames. -/
theorem funAppFrag_under_funs_then_args_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hfrag : FunAppFrag code)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hne : fns ≠ [])
    (hVal : ValueUnderFunsThenArgs D₀ j₀ realize fns args)
    (hc : s.control = .term code)
    (hs : s.stack = mixedStack fns args)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  revert fns args s answer hne hVal hc hs hscoped hrel
  induction hfrag with
  | admin hadmin =>
      intro
        (s : ChannelConfig C) (answer : HSemanticComp D₀ j₀)
        (fns : List
          (Name × Term (QubitPrimitive C) × RuntimeEnv C))
        (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
        hne hVal hc hs hscoped hrel
      exact admin_noapp_under_funs_then_args_of_value
        D₀ j₀ realize fns args hne hVal hadmin hc hs hscoped hrel
  | @app_lam x body arg hbody harg ihBody ihArg =>
      intro
        (s : ChannelConfig C) (answer : HSemanticComp D₀ j₀)
        (fns : List
          (Name × Term (QubitPrimitive C) × RuntimeEnv C))
        (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
        hne hVal hc hs hscoped hrel
      have hsApp :
          {s with control := .term (.app (.lam x body) arg)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelApp : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.app (.lam x body) arg)} answer :=
        hsApp.symm ▸ hrel
      have hrelLam :=
        channel_config_application D₀ j₀ (s := s)
          (fn := .lam x body) (arg := arg) hrelApp
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
          sArg.stack = mixedStack ((x, body, s.env) :: fns) args := by
        simp [sArg, hs, mixedStack]
      have hneNew : ((x, body, s.env) :: fns) ≠ [] :=
        List.cons_ne_nil _ _
      have hValNew : ValueUnderFunsThenArgs D₀ j₀ realize
          ((x, body, s.env) :: fns) args := by
        intro s' arg' answer' hc' hs' hscoped' hrel'
        have hsEq :
            {s' with
              control := .value arg'
              stack :=
                .function (.closure x body s.env) ::
                  mixedStack fns args} = s' :=
          ChannelConfig.ext hc'.symm rfl hs'.symm rfl
        have hrelBody :=
          channel_config_beta D₀ j₀ (s := s') (x := x) (body := body)
            (closureEnv := s.env) (arg := arg')
            (rest := mixedStack fns args)
            (hsEq.symm ▸ hrel')
        have hstepBeta : ChannelInternalStep s'
            {s' with
              control := .term body
              env := RuntimeEnv.bind x arg' s.env
              stack := mixedStack fns args} := by
          have happ :
              ChannelInternalStep
                {s' with
                  control := .value arg'
                  stack :=
                    .function (.closure x body s.env) ::
                      mixedStack fns args}
                {s' with
                  control := .term body
                  env := RuntimeEnv.bind x arg' s.env
                  stack := mixedStack fns args} :=
            ChannelInternalStep.beta (s := s') (x := x) (body := body)
              (closureEnv := s.env) (arg := arg')
              (rest := mixedStack fns args)
          exact hsEq.symm ▸ happ
        have hscopedBody : ChannelConfig.WellScoped
            {s' with
              control := .term body
              env := RuntimeEnv.bind x arg' s.env
              stack := mixedStack fns args} :=
          ChannelInternalStep.preserve_wellScoped hstepBeta hscoped'
        have hchild :=
          ihBody
            (s :=
              {s' with
                control := .term body
                env := RuntimeEnv.bind x arg' s.env
                stack := mixedStack fns args})
            (answer := answer') fns args hne hVal rfl rfl hscopedBody
            hrelBody
        exact beta_presentedChannelConfigCompleteness D₀ j₀ realize
          hc' (by simpa [mixedStack] using hs') hrel' hchild
      have hargComplete :
          PresentedChannelConfigCompleteness D₀ j₀ realize sArg
            answer :=
        ihArg (s := sArg) (answer := answer)
          ((x, body, s.env) :: fns) args hneNew hValNew rfl hsArg
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
      exact stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀
        realize (s := s) (x := x) (body := body) (arg := arg)
        hc hrel hargComplete

theorem funAppFrag_under_fn_arg_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {x : Name} {body : Term (QubitPrimitive C)} {cloX : RuntimeEnv C}
    (hVal : ValueUnderFnArg D₀ j₀ realize x body cloX frames)
    {answer : HSemanticComp D₀ j₀}
    (hfrag : FunAppFrag code)
    (hc : s.control = .term code)
    (hs : s.stack =
      .function (.closure x body cloX) :: argumentStack frames)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer :=
  funAppFrag_under_funs_then_args_of_value D₀ j₀ realize hfrag
    [(x, body, cloX)] frames (List.cons_ne_nil _ _)
    (valueUnderFunsThenArgs_of_fnArg D₀ j₀ realize frames hVal)
    hc (by simpa [mixedStack] using hs) hscoped hrel

/-- Value completeness under ordinary closures over a recursive
closure over leftover argument frames. -/
def ValueUnderFunsThenRecArg {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (self x : Name) (body : Term (QubitPrimitive C))
    (cloEnv : RuntimeEnv C)
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C)) :
    Prop :=
  ∀ {s : ChannelConfig C} {arg : RuntimeValue C}
    {answer : HSemanticComp D₀ j₀},
    s.control = .value arg →
    s.stack =
      functionStack fns ++
        (.function (.recClosure self x body cloEnv) ::
          argumentStack args) →
    ChannelConfig.WellScoped s →
    ChannelConfigRel D₀ j₀ realize s answer →
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer

theorem valueUnderFunsThenRecArg_nil_of_recArg
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {self x : Name} {body : Term (QubitPrimitive C)}
    {cloX : RuntimeEnv C}
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderRecArg D₀ j₀ realize self x body cloX frames) :
    ValueUnderFunsThenRecArg D₀ j₀ realize [] self x body cloX
      frames := by
  intro s arg answer hc hs hscoped hrel
  have hs' : s.stack =
      .function (.recClosure self x body cloX) ::
        argumentStack frames := by
    simpa [functionStack] using hs
  exact hVal hc hs' hscoped hrel

theorem pauliX_under_funs_then_rec_arg_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (self x : Name) (body : Term (QubitPrimitive C))
    (cloEnv : RuntimeEnv C)
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderFunsThenRecArg D₀ j₀ realize fns self x body
      cloEnv args)
    {s : ChannelConfig C} {value : C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack =
      functionStack fns ++
        (.function (.recClosure self x body cloEnv) ::
          argumentStack args))
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
    hVal (s := sVal) (arg := .payload value) rfl hs hscopedVal
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
  have hneStack : s.stack ≠ [] := by
    rw [hs]
    cases fns with
    | nil => exact List.cons_ne_nil _ _
    | cons _ _ => exact List.cons_ne_nil _ _
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
    stackRel_ofOperation_eval D₀ j₀ hstack hneStack
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

theorem admin_noapp_under_funs_then_rec_arg_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (self x : Name) (body : Term (QubitPrimitive C))
    (cloEnv : RuntimeEnv C)
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderFunsThenRecArg D₀ j₀ realize fns self x body
      cloEnv args)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack =
      functionStack fns ++
        (.function (.recClosure self x body cloEnv) ::
          argumentStack args))
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
  | recLam self' z M _ih =>
      have hsRec :
          {s with control := .term (.recLam self' z M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelRec : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.recLam self' z M)} answer :=
        hsRec.symm ▸ hrel
      have hrelVal :=
        channel_config_recursive D₀ j₀ (s := s) hrelRec
      have hstepRec : ChannelInternalStep s
          {s with control := .value (.recClosure self' z M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.recLam self' z M)}
              {s with
                control := .value (.recClosure self' z M s.env)} :=
          ChannelInternalStep.recursive (s := s) (self := self')
            (arg := z) (body := M)
        exact hsRec.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.recClosure self' z M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepRec hscoped
      have hval :=
        hVal
          (s :=
            {s with control := .value (.recClosure self' z M s.env)})
          (arg := .recClosure self' z M s.env) rfl hs hscopedVal
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
            pauliX_under_funs_then_rec_arg_of_value
              D₀ j₀ realize fns self x body cloEnv args hVal
              hc hs hscoped hrel
      | measureZ _ _ =>
          exact False.elim hadmin

theorem funAppFrag_under_funs_then_rec_arg_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hfrag : FunAppFrag code)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (self x : Name) (body : Term (QubitPrimitive C))
    (cloEnv : RuntimeEnv C)
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderFunsThenRecArg D₀ j₀ realize fns self x body
      cloEnv args)
    (hc : s.control = .term code)
    (hs : s.stack =
      functionStack fns ++
        (.function (.recClosure self x body cloEnv) ::
          argumentStack args))
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  revert fns args s answer hVal hc hs hscoped hrel
  induction hfrag with
  | admin hadmin =>
      intro
        (s : ChannelConfig C) (answer : HSemanticComp D₀ j₀)
        (fns : List
          (Name × Term (QubitPrimitive C) × RuntimeEnv C))
        (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
        hVal hc hs hscoped hrel
      exact admin_noapp_under_funs_then_rec_arg_of_value
        D₀ j₀ realize fns self x body cloEnv args hVal hadmin
        hc hs hscoped hrel
  | @app_lam y M arg hbody harg ihBody ihArg =>
      intro
        (s : ChannelConfig C) (answer : HSemanticComp D₀ j₀)
        (fns : List
          (Name × Term (QubitPrimitive C) × RuntimeEnv C))
        (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
        hVal hc hs hscoped hrel
      have hsApp :
          {s with control := .term (.app (.lam y M) arg)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelApp : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.app (.lam y M) arg)} answer :=
        hsApp.symm ▸ hrel
      have hrelLam :=
        channel_config_application D₀ j₀ (s := s)
          (fn := .lam y M) (arg := arg) hrelApp
      have hrelClo :=
        channel_config_lambda D₀ j₀
          (s := {s with stack := .argument arg s.env :: s.stack})
          hrelLam
      have hrelArg :=
        channel_config_evaluateArgument D₀ j₀
          (s :=
            {s with
              control := .value (.closure y M s.env)
              stack := .argument arg s.env :: s.stack})
          (fn := .closure y M s.env) (arg := arg)
          (callEnv := s.env) (rest := s.stack) hrelClo
      let sArg : ChannelConfig C :=
        {s with
          control := .term arg
          stack := .function (.closure y M s.env) :: s.stack}
      have hstepApp : ChannelInternalStep s
          {s with
            control := .term (.lam y M)
            stack := .argument arg s.env :: s.stack} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.app (.lam y M) arg)}
              {s with
                control := .term (.lam y M)
                stack := .argument arg s.env :: s.stack} :=
          ChannelInternalStep.application (s := s)
            (fn := .lam y M) (arg := arg)
        exact hsApp.symm ▸ happ
      have hstepLam : ChannelInternalStep
          {s with
            control := .term (.lam y M)
            stack := .argument arg s.env :: s.stack}
          {s with
            control := .value (.closure y M s.env)
            stack := .argument arg s.env :: s.stack} :=
        ChannelInternalStep.lambda
          (s := {s with stack := .argument arg s.env :: s.stack})
          (x := y) (body := M)
      have hstepArg : ChannelInternalStep
          {s with
            control := .value (.closure y M s.env)
            stack := .argument arg s.env :: s.stack}
          sArg :=
        ChannelInternalStep.evaluateArgument
          (s :=
            {s with
              control := .value (.closure y M s.env)
              stack := .argument arg s.env :: s.stack})
          (fn := .closure y M s.env) (arg := arg)
          (callEnv := s.env) (rest := s.stack)
      have hscopedArg : ChannelConfig.WellScoped sArg :=
        ChannelInternalStep.preserve_wellScoped hstepArg
          (ChannelInternalStep.preserve_wellScoped hstepLam
            (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
      have hsArg :
          sArg.stack =
            functionStack ((y, M, s.env) :: fns) ++
              (.function (.recClosure self x body cloEnv) ::
                argumentStack args) := by
        simp [sArg, hs, functionStack]
      have hValNew : ValueUnderFunsThenRecArg D₀ j₀ realize
          ((y, M, s.env) :: fns) self x body cloEnv args := by
        intro s' arg' answer' hc' hs' hscoped' hrel'
        have hsEq :
            {s' with
              control := .value arg'
              stack :=
                .function (.closure y M s.env) ::
                  (functionStack fns ++
                    (.function (.recClosure self x body cloEnv) ::
                      argumentStack args))} = s' :=
          ChannelConfig.ext hc'.symm rfl hs'.symm rfl
        have hrelBody :=
          channel_config_beta D₀ j₀ (s := s') (x := y) (body := M)
            (closureEnv := s.env) (arg := arg')
            (rest :=
              functionStack fns ++
                (.function (.recClosure self x body cloEnv) ::
                  argumentStack args))
            (hsEq.symm ▸ hrel')
        have hstepBeta : ChannelInternalStep s'
            {s' with
              control := .term M
              env := RuntimeEnv.bind y arg' s.env
              stack :=
                functionStack fns ++
                  (.function (.recClosure self x body cloEnv) ::
                    argumentStack args)} := by
          have happ :
              ChannelInternalStep
                {s' with
                  control := .value arg'
                  stack :=
                    .function (.closure y M s.env) ::
                      (functionStack fns ++
                        (.function (.recClosure self x body cloEnv) ::
                          argumentStack args))}
                {s' with
                  control := .term M
                  env := RuntimeEnv.bind y arg' s.env
                  stack :=
                    functionStack fns ++
                      (.function (.recClosure self x body cloEnv) ::
                        argumentStack args)} :=
            ChannelInternalStep.beta (s := s') (x := y) (body := M)
              (closureEnv := s.env) (arg := arg')
              (rest :=
                functionStack fns ++
                  (.function (.recClosure self x body cloEnv) ::
                    argumentStack args))
          exact hsEq.symm ▸ happ
        have hscopedBody : ChannelConfig.WellScoped
            {s' with
              control := .term M
              env := RuntimeEnv.bind y arg' s.env
              stack :=
                functionStack fns ++
                  (.function (.recClosure self x body cloEnv) ::
                    argumentStack args)} :=
          ChannelInternalStep.preserve_wellScoped hstepBeta hscoped'
        have hchild :=
          ihBody
            (s :=
              {s' with
                control := .term M
                env := RuntimeEnv.bind y arg' s.env
                stack :=
                  functionStack fns ++
                    (.function (.recClosure self x body cloEnv) ::
                      argumentStack args)})
            (answer := answer') fns args hVal rfl rfl hscopedBody
            hrelBody
        exact beta_presentedChannelConfigCompleteness D₀ j₀ realize
          hc'
          (by
            simpa [functionStack] using hs')
          hrel' hchild
      have hargComplete :
          PresentedChannelConfigCompleteness D₀ j₀ realize sArg
            answer :=
        ihArg (s := sArg) (answer := answer)
          ((y, M, s.env) :: fns) args hValNew rfl hsArg hscopedArg
          (by
            change ChannelConfigRel D₀ j₀ realize
                {s with
                  control := .term arg
                  env := s.env
                  stack :=
                    .function (.closure y M s.env) :: s.stack}
                _
            exact hrelArg)
      exact stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀
        realize (s := s) (x := y) (body := M) (arg := arg)
        hc hrel hargComplete

theorem funAppFrag_under_rec_arg_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {self x : Name} {body : Term (QubitPrimitive C)}
    {cloX : RuntimeEnv C}
    (hVal : ValueUnderRecArg D₀ j₀ realize self x body cloX frames)
    {answer : HSemanticComp D₀ j₀}
    (hfrag : FunAppFrag code)
    (hc : s.control = .term code)
    (hs : s.stack =
      .function (.recClosure self x body cloX) :: argumentStack frames)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer :=
  funAppFrag_under_funs_then_rec_arg_of_value D₀ j₀ realize hfrag
    [] self x body cloX frames
    (valueUnderFunsThenRecArg_nil_of_recArg D₀ j₀ realize frames hVal)
    hc (by simpa [functionStack] using hs) hscoped hrel

/-- Presented completeness for a `Produces n` term sitting under
exactly `n` leftover FunAppFrag argument frames. -/
theorem produces_under_argument_frames_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {n : Nat} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hprod : Produces n code)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hlen : frames.length = n)
    (hok : FunAppFramesOk frames)
    (hc : s.control = .term code)
    (hs : s.stack = argumentStack frames)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  revert frames s answer hlen hok hc hs hscoped hrel
  induction hprod with
  | frag hfrag =>
      intro (s : ChannelConfig C) (answer : HSemanticComp D₀ j₀)
        (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
        hlen hok hc hs hscoped hrel
      have hnil : frames = [] := List.eq_nil_of_length_eq_zero hlen
      subst frames
      exact funAppFrag_empty_presentedChannelConfigCompleteness
        D₀ j₀ realize hfrag hc (by simpa [argumentStack] using hs)
        hscoped hrel
  | @lam n x body hprod ih =>
      intro (s : ChannelConfig C) (answer : HSemanticComp D₀ j₀)
        (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
        hlen hok hc hs hscoped hrel
      match frames with
      | [] =>
          exact (Nat.succ_ne_zero n hlen.symm).elim
      | (arg, callEnv) :: rest =>
          have hlenRest : rest.length = n := by
            simpa using hlen
          have hfragArg : FunAppFrag arg :=
            hok (arg, callEnv) (by simp)
          have hokRest : FunAppFramesOk rest :=
            fun q hq => hok q (by simp [hq])
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
              ChannelInternalStep.lambda (s := s) (x := x)
                (body := body)
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
                (s :=
                  {s with control := .value (.closure x body s.env)})
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
              (ChannelInternalStep.preserve_wellScoped hstepLam
                hscoped)
          have hVal : ValueUnderFnArg D₀ j₀ realize x body s.env
              rest := by
            intro s' v answer' hc' hs' hscoped' hrel'
            have hsEq :
                {s' with
                  control := .value v
                  stack :=
                    .function (.closure x body s.env) ::
                      argumentStack rest} = s' :=
              ChannelConfig.ext hc'.symm rfl hs'.symm rfl
            have hrelBody :=
              channel_config_beta D₀ j₀ (s := s') (x := x)
                (body := body) (closureEnv := s.env) (arg := v)
                (rest := argumentStack rest) (hsEq.symm ▸ hrel')
            have hstepBeta : ChannelInternalStep s'
                {s' with
                  control := .term body
                  env := RuntimeEnv.bind x v s.env
                  stack := argumentStack rest} := by
              have happ :
                  ChannelInternalStep
                    {s' with
                      control := .value v
                      stack :=
                        .function (.closure x body s.env) ::
                          argumentStack rest}
                    {s' with
                      control := .term body
                      env := RuntimeEnv.bind x v s.env
                      stack := argumentStack rest} :=
                ChannelInternalStep.beta (s := s') (x := x)
                  (body := body) (closureEnv := s.env) (arg := v)
                  (rest := argumentStack rest)
              exact hsEq.symm ▸ happ
            have hscopedBody : ChannelConfig.WellScoped
                {s' with
                  control := .term body
                  env := RuntimeEnv.bind x v s.env
                  stack := argumentStack rest} :=
              ChannelInternalStep.preserve_wellScoped hstepBeta
                hscoped'
            have hchild :=
              ih (s :=
                  {s' with
                    control := .term body
                    env := RuntimeEnv.bind x v s.env
                    stack := argumentStack rest})
                (answer := answer') rest hlenRest hokRest rfl rfl
                hscopedBody hrelBody
            exact beta_presentedChannelConfigCompleteness D₀ j₀
              realize hc' hs' hrel' hchild
          have harg :
              PresentedChannelConfigCompleteness D₀ j₀ realize
                {s with
                  control := .term arg
                  env := callEnv
                  stack :=
                    .function (.closure x body s.env) ::
                      argumentStack rest}
                answer :=
            funAppFrag_under_fn_arg_of_value D₀ j₀ realize rest
              (s :=
                {s with
                  control := .term arg
                  env := callEnv
                  stack :=
                    .function (.closure x body s.env) ::
                      argumentStack rest})
              (x := x) (body := body) (cloX := s.env) hVal
              hfragArg rfl rfl hscopedFn hrelFn
          have hClo :=
            evaluateArgument_presentedChannelConfigCompleteness
              D₀ j₀ realize
              (s := {s with control := .value (.closure x body s.env)})
              (fn := .closure x body s.env) (arg := arg)
              (callEnv := callEnv) (rest := argumentStack rest)
              rfl hs hrelClo harg
          exact lambda_presentedChannelConfigCompleteness D₀ j₀
            realize hc hrel hClo
  | @recLam n self x body hprod ih =>
      intro (s : ChannelConfig C) (answer : HSemanticComp D₀ j₀)
        (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
        hlen hok hc hs hscoped hrel
      match frames with
      | [] =>
          exact (Nat.succ_ne_zero n hlen.symm).elim
      | (arg, callEnv) :: rest =>
          have hlenRest : rest.length = n := by
            simpa using hlen
          have hfragArg : FunAppFrag arg :=
            hok (arg, callEnv) (by simp)
          have hokRest : FunAppFramesOk rest :=
            fun q hq => hok q (by simp [hq])
          have hsLam :
              {s with control := .term (.recLam self x body)} = s :=
            ChannelConfig.ext hc.symm rfl rfl rfl
          have hrelLam : ChannelConfigRel D₀ j₀ realize
              {s with control := .term (.recLam self x body)} answer :=
            hsLam.symm ▸ hrel
          have hrelClo :=
            channel_config_recursive D₀ j₀ (s := s) hrelLam
          have hsrcClo :
              {s with control := .value (.recClosure self x body s.env)} =
                {s with
                  control := .value (.recClosure self x body s.env)
                  stack :=
                    .argument arg callEnv :: argumentStack rest} :=
            ChannelConfig.ext rfl rfl hs rfl
          have hrelFn :=
            channel_config_evaluateArgument D₀ j₀
              (s := {s with control := .value (.recClosure self x body s.env)})
              (fn := .recClosure self x body s.env) (arg := arg)
              (callEnv := callEnv) (rest := argumentStack rest)
              (hsrcClo ▸ hrelClo)
          have hstepLam : ChannelInternalStep s
              {s with control := .value (.recClosure self x body s.env)} := by
            have happ :
                ChannelInternalStep
                  {s with control := .term (.recLam self x body)}
                  {s with control := .value (.recClosure self x body s.env)} :=
              ChannelInternalStep.recursive (s := s) (self := self)
                (arg := x) (body := body)
            exact hsLam.symm ▸ happ
          have hstepArg : ChannelInternalStep
              {s with control := .value (.recClosure self x body s.env)}
              {s with
                control := .term arg
                env := callEnv
                stack :=
                  .function (.recClosure self x body s.env) ::
                    argumentStack rest} := by
            have happ :
                ChannelInternalStep
                  {s with
                    control := .value (.recClosure self x body s.env)
                    stack :=
                      .argument arg callEnv :: argumentStack rest}
                  {s with
                    control := .term arg
                    env := callEnv
                    stack :=
                      .function (.recClosure self x body s.env) ::
                        argumentStack rest} :=
              ChannelInternalStep.evaluateArgument
                (s :=
                  {s with control := .value (.recClosure self x body s.env)})
                (fn := .recClosure self x body s.env) (arg := arg)
                (callEnv := callEnv) (rest := argumentStack rest)
            exact hsrcClo.symm ▸ happ
          have hscopedFn : ChannelConfig.WellScoped
              {s with
                control := .term arg
                env := callEnv
                stack :=
                  .function (.recClosure self x body s.env) ::
                    argumentStack rest} :=
            ChannelInternalStep.preserve_wellScoped hstepArg
              (ChannelInternalStep.preserve_wellScoped hstepLam
                hscoped)
          have hVal : ValueUnderRecArg D₀ j₀ realize self x body s.env
              rest := by
            intro s' v answer' hc' hs' hscoped' hrel'
            have hsEq :
                {s' with
                  control := .value v
                  stack :=
                    .function (.recClosure self x body s.env) ::
                      argumentStack rest} = s' :=
              ChannelConfig.ext hc'.symm rfl hs'.symm rfl
            have hrelBody :=
              channel_config_recBeta D₀ j₀ (s := s') (self := self) (x := x)
                (body := body) (closureEnv := s.env) (arg := v)
                (rest := argumentStack rest) (hsEq.symm ▸ hrel')
            have hstepBeta : ChannelInternalStep s'
                {s' with
                  control := .term body
                  env := RuntimeEnv.bind x v (RuntimeEnv.bind self (.recClosure self x body s.env) s.env)
                  stack := argumentStack rest} := by
              have happ :
                  ChannelInternalStep
                    {s' with
                      control := .value v
                      stack :=
                        .function (.recClosure self x body s.env) ::
                          argumentStack rest}
                    {s' with
                      control := .term body
                      env := RuntimeEnv.bind x v (RuntimeEnv.bind self (.recClosure self x body s.env) s.env)
                      stack := argumentStack rest} :=
                ChannelInternalStep.recBeta (s := s') (self := self) (x := x)
                  (body := body) (closureEnv := s.env) (arg := v)
                  (rest := argumentStack rest)
              exact hsEq.symm ▸ happ
            have hscopedBody : ChannelConfig.WellScoped
                {s' with
                  control := .term body
                  env := RuntimeEnv.bind x v (RuntimeEnv.bind self (.recClosure self x body s.env) s.env)
                  stack := argumentStack rest} :=
              ChannelInternalStep.preserve_wellScoped hstepBeta
                hscoped'
            have hchild :=
              ih (s :=
                  {s' with
                    control := .term body
                    env := RuntimeEnv.bind x v (RuntimeEnv.bind self (.recClosure self x body s.env) s.env)
                    stack := argumentStack rest})
                (answer := answer') rest hlenRest hokRest rfl rfl
                hscopedBody hrelBody
            exact recBeta_presentedChannelConfigCompleteness D₀ j₀
              realize hc' hs' hrel' hchild
          have harg :
              PresentedChannelConfigCompleteness D₀ j₀ realize
                {s with
                  control := .term arg
                  env := callEnv
                  stack :=
                    .function (.recClosure self x body s.env) ::
                      argumentStack rest}
                answer :=
            funAppFrag_under_rec_arg_of_value D₀ j₀ realize rest
              (s :=
                {s with
                  control := .term arg
                  env := callEnv
                  stack :=
                    .function (.recClosure self x body s.env) ::
                      argumentStack rest})
              (self := self) (x := x) (body := body) (cloX := s.env) hVal
              hfragArg rfl rfl hscopedFn hrelFn
          have hClo :=
            evaluateArgument_presentedChannelConfigCompleteness
              D₀ j₀ realize
              (s := {s with control := .value (.recClosure self x body s.env)})
              (fn := .recClosure self x body s.env) (arg := arg)
              (callEnv := callEnv) (rest := argumentStack rest)
              rfl hs hrelClo harg
          exact recLam_presentedChannelConfigCompleteness D₀ j₀
            realize hc hrel hClo
  | @app n fn arg hfn hfragArg ihFn =>
      intro (s : ChannelConfig C) (answer : HSemanticComp D₀ j₀)
        (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
        hlen hok hc hs hscoped hrel
      have hsApp :
          {s with control := .term (.app fn arg)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelApp : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.app fn arg)} answer :=
        hsApp.symm ▸ hrel
      have hrelFn :=
        channel_config_application D₀ j₀ (s := s) (fn := fn)
          (arg := arg) hrelApp
      have hstepApp : ChannelInternalStep s
          {s with
            control := .term fn
            stack := .argument arg s.env :: s.stack} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.app fn arg)}
              {s with
                control := .term fn
                stack := .argument arg s.env :: s.stack} :=
          ChannelInternalStep.application (s := s) (fn := fn)
            (arg := arg)
        exact hsApp.symm ▸ happ
      have hscopedFn : ChannelConfig.WellScoped
          {s with
            control := .term fn
            stack := .argument arg s.env :: s.stack} :=
        ChannelInternalStep.preserve_wellScoped hstepApp hscoped
      have hsFn :
          {s with
              control := .term fn
              stack := .argument arg s.env :: s.stack}.stack =
            argumentStack ((arg, s.env) :: frames) := by
        simp [argumentStack, hs]
      have hlenNew :
          ((arg, s.env) :: frames).length = n + 1 := by
        simp [hlen]
      have hokNew : FunAppFramesOk ((arg, s.env) :: frames) := by
        intro q hq
        rcases List.mem_cons.mp hq with h | h
        · cases h
          exact hfragArg
        · exact hok q h
      have hchild :=
        ihFn
          (s :=
            {s with
              control := .term fn
              stack := .argument arg s.env :: s.stack})
          (answer := answer) ((arg, s.env) :: frames) hlenNew hokNew
          rfl hsFn hscopedFn hrelFn
      exact application_presentedChannelConfigCompleteness D₀ j₀
        realize hc hrel hchild


end HardwareChannelSemantics
end QLambda
