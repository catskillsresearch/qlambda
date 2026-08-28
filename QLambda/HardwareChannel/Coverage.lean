/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.HardwareChannel.Productive

/-!
# Closed stuck-free coverage

Final entry-point layer for the closed fragments whose channel-tree
completeness has been established.  The predicate stores each route's
actual side conditions: only the path-productive branch needs
`MeasureDistinct`, while restricted extern applications use their
direct completeness theorem.
-/

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

/-- Named coverage boundary for closed programs known not to get stuck.

`productiveCase` accepts the complete `ProductiveClosedCase` interface.
The separate `restrictedExtern` constructor records that its direct
completeness proof does not require `MeasureDistinct`. -/
inductive ClosedStuckFreeCoverage {C : Type}
    {D₀ : QDomain.{0}}
    {j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier)}
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C)) : Prop where
  | noApp :
      Closed code →
      NoApp code →
      ClosedStuckFreeCoverage realize code
  | funAppFrag :
      Closed code →
      FunAppFrag code →
      ClosedStuckFreeCoverage realize code
  | produces :
      Closed code →
      Produces 0 code →
      ClosedStuckFreeCoverage realize code
  | productiveCase :
      Closed code →
      ProductiveClosedCase code →
      MeasureDistinct realize code →
      ClosedStuckFreeCoverage realize code
  | restrictedExtern :
      Closed code →
      RestrictedExternApplication code →
      ClosedStuckFreeCoverage realize code

/-- Every covered closed program has presented channel-tree completeness. -/
theorem closed_stuck_free_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (hcoverage : ClosedStuckFreeCoverage realize code)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig code quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) := by
  cases hcoverage with
  | noApp hclosed hnoapp =>
      exact closed_term_presented_channelTreeCompleteness_of_noApp
        D₀ j₀ realize code hclosed hnoapp quantum semanticEnv
  | funAppFrag hclosed hfrag =>
      exact closed_funAppFrag_presented_channelTreeCompleteness
        D₀ j₀ realize code hclosed hfrag quantum semanticEnv
  | produces hclosed hprod =>
      exact closed_produces_presented_channelTreeCompleteness
        D₀ j₀ realize code hclosed hprod quantum semanticEnv
  | productiveCase hclosed hcase hdist =>
      exact closed_term_presented_channelTreeCompleteness_of_productive_case
        D₀ j₀ realize code hclosed hcase hdist quantum semanticEnv
  | restrictedExtern hclosed hcase =>
      cases hcase with
      | lam x body left right hnoapp hadminBody _ _ hadminL hadminR =>
          exact
            closed_lam_extern_admin_noapp_presented_channelTreeCompleteness
              D₀ j₀ realize x body left right hclosed hnoapp hadminBody
              hadminL hadminR quantum semanticEnv
      | recLam self x body left right hnoapp hadminBody _ _ hadminL hadminR =>
          exact
            closed_recLam_extern_admin_noapp_presented_channelTreeCompleteness
              D₀ j₀ realize self x body left right hclosed hnoapp hadminBody
              hadminL hadminR quantum semanticEnv

/-- Token adequacy at the consolidated closed stuck-free boundary. -/
theorem closed_stuck_free_presented_token_adequacy
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (hcoverage : ClosedStuckFreeCoverage realize code)
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
    (closed_stuck_free_presented_channelTreeCompleteness
      D₀ j₀ realize code hcoverage quantum semanticEnv)
    selectors ξ k hk i token

end HardwareChannelSemantics
end QLambda
