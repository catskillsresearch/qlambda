/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.HardwareChannel.FunApp

/-!
# Closed Produces / FunAppFrag wrappers and token adequacy

Layer of the hardware channel-tree semantics.  All layers share the
`QLambda.HardwareChannelSemantics` namespace; import
`QLambda.HardwareChannelSemantics` for the full module.

`Produces 0` now includes applications whose residual arguments are in
`FunAppFrag` (not only administrative NoApp), so closed stacked apps
such as `app (lam x body) (app (lam y M) N)` are covered by
`closed_produces_*` whenever the pieces inhabit FunAppFrag / Produces.
`FunAppFrag.app_recLam` covers nested recursive-lambda applications,
including under mixed ordinary/recursive function-frame spines.

The path-indexed fundamental theorem and the closed-term theorems that
take a branch-complete `PathChannelEvaluation` live in
`QLambda.HardwareChannel.Fundamental` (re-exported by the barrel).
Application-free closed terms need no evaluation derivation:
`closed_term_presented_channelTreeCompleteness_of_noApp`.
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

theorem closed_produces_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (hclosed : Closed code) (hprod : Produces 0 code)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig code quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
  (produces_under_argument_frames_presentedChannelConfigCompleteness
    D₀ j₀ realize hprod [] rfl (by intro q hq; cases hq) rfl rfl
    (initialChannelConfig_wellScoped hclosed quantum)
    (initialChannelConfig_related D₀ j₀ realize code quantum
      semanticEnv)).complete

theorem closed_produces_presented_token_adequacy
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (hclosed : Closed code) (hprod : Produces 0 code)
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
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig code quantum)
    (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv)
    (closed_produces_presented_channelTreeCompleteness D₀ j₀ realize
      code hclosed hprod quantum semanticEnv)
    selectors ξ k hk i token

/-- Closed `app (lam x body) (app (lam y M) N)` when body and the
nested application are FunAppFrag. -/
theorem closed_produces_lam_funApp_arg_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x y : Name) (body M N : Term (QubitPrimitive C))
    (hclosed : Closed (.app (.lam x body) (.app (.lam y M) N)))
    (hbody : FunAppFrag body)
    (harg : FunAppFrag (.app (.lam y M) N))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.app (.lam x body) (.app (.lam y M) N))
        quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.lam x body) (.app (.lam y M) N)) semanticEnv) :=
  closed_produces_presented_channelTreeCompleteness D₀ j₀ realize
    (.app (.lam x body) (.app (.lam y M) N)) hclosed
    (Produces.app (Produces.lam (Produces.frag hbody)) harg)
    quantum semanticEnv

theorem closed_produces_lam_funApp_arg_presented_token_adequacy
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x y : Name) (body M N : Term (QubitPrimitive C))
    (hclosed : Closed (.app (.lam x body) (.app (.lam y M) N)))
    (hbody : FunAppFrag body)
    (harg : FunAppFrag (.app (.lam y M) N))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize)
          (.app (.lam x body) (.app (.lam y M) N)) semanticEnv)
        i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig
            (.app (.lam x body) (.app (.lam y M) N)) quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  closed_produces_presented_token_adequacy D₀ j₀ realize
    (.app (.lam x body) (.app (.lam y M) N)) hclosed
    (Produces.app (Produces.lam (Produces.frag hbody)) harg)
    quantum semanticEnv selectors ξ k hk i token

/-- Closed body-and-argument nested `app (lam x body) arg` fragment. -/
theorem closed_funAppFrag_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (hclosed : Closed code) (hfrag : FunAppFrag code)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig code quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
  (funAppFrag_empty_presentedChannelConfigCompleteness D₀ j₀ realize
    hfrag rfl rfl (initialChannelConfig_wellScoped hclosed quantum)
    (initialChannelConfig_related D₀ j₀ realize code quantum
      semanticEnv)).complete

/-- Closed nested `app (recLam …) arg` as a FunAppFrag fragment. -/
theorem closed_funAppFrag_app_recLam_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self x : Name) (body arg : Term (QubitPrimitive C))
    (hclosed : Closed (.app (.recLam self x body) arg))
    (hbody : FunAppFrag body) (harg : FunAppFrag arg)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.app (.recLam self x body) arg) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.recLam self x body) arg) semanticEnv) :=
  closed_funAppFrag_presented_channelTreeCompleteness D₀ j₀ realize
    (.app (.recLam self x body) arg) hclosed
    (FunAppFrag.app_recLam hbody harg) quantum semanticEnv

theorem closed_funAppFrag_presented_token_adequacy
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (hclosed : Closed code) (hfrag : FunAppFrag code)
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
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig code quantum)
    (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv)
    (closed_funAppFrag_presented_channelTreeCompleteness D₀ j₀ realize
      code hclosed hfrag quantum semanticEnv)
    selectors ξ k hk i token


end HardwareChannelSemantics
end QLambda
