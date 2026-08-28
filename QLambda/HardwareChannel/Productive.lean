/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.HardwareChannel.Fundamental

/-!
# Productive closed applications

Layer of the hardware channel-tree semantics.  All layers share the
`QLambda.HardwareChannelSemantics` namespace; import
`QLambda.HardwareChannelSemantics` for the full module.

`Atomic` is the application-free productive class (return, measure-Z,
lambda / recursive lambda as values, probability, variables, internal
choice).  `Productive n` raises arity through lambda / recursive lambda
and consumes one leftover argument when the argument is `Productive 0`.
That includes leftover-arity spines
(`app (app (lam (lam ·)) ·) ·`) and application-as-argument.

This is the class for which a `PathChannelEvaluation` is assembled
without a `FunAppFrag` / `Produces` hypothesis.  Measure-Z, probability,
and intern-in-body are included; those fragments exclude measure-Z and
probability.  Pauli-X is omitted (`pauliX` is a path constructor only at
the empty stack).  External choice is a path constructor, but as an
argument it changes the active coordinate so later `beta` cannot apply
at the child's coordinate; closed `extern` at the empty stack is
handled separately.
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

/-! ## Syntactic productivity -/

/-- Every measure-Z primitive in the term has distinct realizations. -/
def MeasureDistinct {C : Type}
    {D₀ : QDomain.{0}}
    {j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier)}
    (realize : C → HSemanticValue D₀ j₀) :
    Term (QubitPrimitive C) → Prop
  | .prim (.measureZ z o) => realize z ≠ realize o
  | .app fn arg => MeasureDistinct realize fn ∧ MeasureDistinct realize arg
  | .lam _ body => MeasureDistinct realize body
  | .recLam _ _ body => MeasureDistinct realize body
  | .prob _ left right =>
      MeasureDistinct realize left ∧ MeasureDistinct realize right
  | .intern left right =>
      MeasureDistinct realize left ∧ MeasureDistinct realize right
  | .extern left right =>
      MeasureDistinct realize left ∧ MeasureDistinct realize right
  | .var _ => True
  | .prim (.ret _) => True
  | .prim (.pauliX _) => True

/-- Application-free terms that a path evaluation can run at the empty
stack or as a leftover argument. -/
inductive Atomic {C : Type} : Term (QubitPrimitive C) → Prop
  | var (x : Name) : Atomic (.var x)
  | ret (value : C) : Atomic (.prim (.ret value))
  | measureZ (zeroValue oneValue : C) :
      Atomic (.prim (.measureZ zeroValue oneValue))
  | lam (x : Name) (body : Term (QubitPrimitive C)) :
      Atomic (.lam x body)
  | recLam (self x : Name) (body : Term (QubitPrimitive C)) :
      Atomic (.recLam self x body)
  | intern (left right : Term (QubitPrimitive C)) :
      Atomic left →
      Atomic right →
      Atomic (.intern left right)
  | prob (p : ℝ) (left right : Term (QubitPrimitive C)) :
      0 ≤ p →
      p ≤ 1 →
      Atomic left →
      Atomic right →
      Atomic (.prob p left right)

/-- Terms that absorb exactly `n` leftover `Productive 0` argument frames.
`Productive 0` is `Atomic`, or an application of a `Productive 1`
function to a `Productive 0` argument. -/
inductive Productive {C : Type} : Nat → Term (QubitPrimitive C) → Prop
  | atomic {t : Term (QubitPrimitive C)} :
      Atomic t → Productive 0 t
  | lam (n : Nat) (x : Name) (body : Term (QubitPrimitive C)) :
      Productive n body → Productive (n + 1) (.lam x body)
  | recLam (n : Nat) (self x : Name) (body : Term (QubitPrimitive C)) :
      Productive n body → Productive (n + 1) (.recLam self x body)
  | app (n : Nat) (fn arg : Term (QubitPrimitive C)) :
      Productive (n + 1) fn →
      Atomic arg →
      Productive n (.app fn arg)

theorem covers_var {C : Type} {env : RuntimeEnv C} {x : Name}
    (h : RuntimeEnv.Covers env (.var x)) :
    ∃ v, RuntimeEnv.lookup x env = some v :=
  h x (by simp [free])

theorem initialChannelConfig_control {C : Type}
    (code : Term (QubitPrimitive C)) (quantum : NormalizedDensity 2) :
    (initialChannelConfig code quantum).control = .term code :=
  rfl

theorem initialChannelConfig_stack {C : Type}
    (code : Term (QubitPrimitive C)) (quantum : NormalizedDensity 2) :
    (initialChannelConfig code quantum).stack = [] :=
  rfl

/-! ## Atomic terms at the empty stack -/

/-- An `Atomic` term at the empty stack has a branch-complete path
evaluation at every coordinate. -/
theorem atomic_nil_pathChannelEvaluation {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    (hatom : Atomic code)
    (hdist : MeasureDistinct realize code)
    (hc : s.control = .term code)
    (hs : s.stack = [])
    (hscoped : ChannelConfig.WellScoped s)
    (active : ℕ) :
    PathChannelEvaluation D₀ j₀ realize s active [] := by
  induction hatom generalizing s active with
  | var x =>
      have hx : s.control = .term (.var x) := hc
      have ⟨hctl, _⟩ := hscoped
      rw [hx] at hctl
      obtain ⟨v, hlookup⟩ := covers_var hctl.right
      refine PathChannelEvaluation.varLookup hx hlookup ?_
      exact PathChannelEvaluation.terminal ⟨v, rfl, hs⟩
  | ret value =>
      have hx : s.control = .term (.prim (.ret value)) := hc
      refine PathChannelEvaluation.returnPayload hx ?_
      exact PathChannelEvaluation.terminal ⟨.payload value, rfl, hs⟩
  | measureZ zeroValue oneValue =>
      have hx : s.control =
          .term (.prim (.measureZ zeroValue oneValue)) := hc
      refine PathChannelEvaluation.measurement hx hdist ?_ ?_
      · exact PathChannelEvaluation.terminal ⟨.payload zeroValue, rfl, hs⟩
      · exact PathChannelEvaluation.terminal ⟨.payload oneValue, rfl, hs⟩
  | lam x body =>
      have hx : s.control = .term (.lam x body) := hc
      refine PathChannelEvaluation.lambda hx ?_
      exact PathChannelEvaluation.terminal
        ⟨.closure x body s.env, rfl, hs⟩
  | recLam self x body =>
      have hx : s.control = .term (.recLam self x body) := hc
      refine PathChannelEvaluation.recursive hx ?_
      exact PathChannelEvaluation.terminal
        ⟨.recClosure self x body s.env, rfl, hs⟩
  | intern left right hleft hright ihL ihR =>
      have hx : s.control = .term (.intern left right) := hc
      have ⟨hdistL, hdistR⟩ := hdist
      refine PathChannelEvaluation.intern hx ?_ ?_
      · exact ihL (s := {s with control := .term left}) hdistL rfl hs
          (wellScoped_intern_left hx hscoped) active
      · exact ihR (s := {s with control := .term right}) hdistR rfl hs
          (wellScoped_intern_right hx hscoped) active
  | prob p left right hp₀ hp₁ hleft hright ihL ihR =>
      have hx : s.control = .term (.prob p left right) := hc
      have ⟨hdistL, hdistR⟩ := hdist
      by_cases hz : p = 0
      · subst hz
        refine PathChannelEvaluation.probZero hx ?_
        exact ihR (s :=
            {s with
              control := .term right
              quantum :=
                applyOperation
                  (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                  s.quantum})
          hdistR rfl hs (wellScoped_prob_right hx hscoped _) active
      · by_cases ho : p = 1
        · subst ho
          refine PathChannelEvaluation.probOne hx ?_
          exact ihL (s :=
              {s with
                control := .term left
                quantum :=
                  applyOperation
                    (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                    s.quantum})
            hdistL rfl hs (wellScoped_prob_left hx hscoped _) active
        · have hp0' : 0 < p := lt_of_le_of_ne hp₀ (Ne.symm hz)
          have hp1' : p < 1 := lt_of_le_of_ne hp₁ ho
          refine PathChannelEvaluation.probability hp0' hp1' hx ?_ ?_
          · exact ihL (s :=
                {s with
                  control := .term left
                  quantum :=
                    applyOperation
                      (sourceProbabilityOperation p hp0'.le hp1'.le)
                      s.quantum})
              hdistL rfl hs (wellScoped_prob_left hx hscoped _) active
          · exact ihR (s :=
                {s with
                  control := .term right
                  quantum :=
                    applyOperation
                      (sourceProbabilityOperation (1 - p)
                        (sub_nonneg.mpr hp1'.le) (by linarith))
                      s.quantum})
              hdistR rfl hs (wellScoped_prob_right hx hscoped _) active

/-! ## Atomic argument under one closure, then the body at the empty stack -/

/-- An `Atomic` argument under a single ordinary closure frame evaluates
and betas into an empty-stack `Atomic` (or `Productive 0` via `atomic`)
body. -/
theorem atomic_under_closure_pathChannelEvaluation {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {arg : Term (QubitPrimitive C)}
    {x : Name} {body : Term (QubitPrimitive C)} {cloEnv : RuntimeEnv C}
    (hatom : Atomic arg)
    (hdistArg : MeasureDistinct realize arg)
    (hbody : Atomic body)
    (hdistBody : MeasureDistinct realize body)
    (hc : s.control = .term arg)
    (hs : s.stack = [.function (.closure x body cloEnv)])
    (hscoped : ChannelConfig.WellScoped s)
    (active : ℕ) :
    PathChannelEvaluation D₀ j₀ realize s active
      [(.function (.closure x body cloEnv), active)] := by
  induction hatom generalizing s active with
  | var y =>
      have hx : s.control = .term (.var y) := hc
      have ⟨hctl, _⟩ := hscoped
      rw [hx] at hctl
      obtain ⟨v, hlookup⟩ := covers_var hctl.right
      refine PathChannelEvaluation.varLookup hx hlookup ?_
      refine PathChannelEvaluation.beta rfl hs ?_
      exact atomic_nil_pathChannelEvaluation D₀ j₀ realize hbody hdistBody
        rfl rfl
        ((channelInternalStep_of_beta (s := {s with control := .value v})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_variable hx hlookup).preserve_wellScoped
            hscoped))
        active
  | ret value =>
      have hx : s.control = .term (.prim (.ret value)) := hc
      refine PathChannelEvaluation.returnPayload hx ?_
      refine PathChannelEvaluation.beta rfl hs ?_
      exact atomic_nil_pathChannelEvaluation D₀ j₀ realize hbody hdistBody
        rfl rfl
        ((channelInternalStep_of_beta
          (s := {s with control := .value (.payload value)})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_return hx).preserve_wellScoped hscoped))
        active
  | measureZ zeroValue oneValue =>
      have hx : s.control =
          .term (.prim (.measureZ zeroValue oneValue)) := hc
      refine PathChannelEvaluation.measurement hx hdistArg ?_ ?_
      · refine PathChannelEvaluation.beta rfl hs ?_
        exact atomic_nil_pathChannelEvaluation D₀ j₀ realize hbody
          hdistBody rfl rfl
          ((channelInternalStep_of_beta
            (s :=
              {s with
                control := .value (.payload zeroValue)
                quantum :=
                  applyOperation (measurementOperation false) s.quantum})
            rfl hs).preserve_wellScoped
            (wellScoped_payload_child hx hscoped zeroValue _))
          active
      · refine PathChannelEvaluation.beta rfl hs ?_
        exact atomic_nil_pathChannelEvaluation D₀ j₀ realize hbody
          hdistBody rfl rfl
          ((channelInternalStep_of_beta
            (s :=
              {s with
                control := .value (.payload oneValue)
                quantum :=
                  applyOperation (measurementOperation true) s.quantum})
            rfl hs).preserve_wellScoped
            (wellScoped_payload_child hx hscoped oneValue _))
          active
  | lam z b =>
      have hx : s.control = .term (.lam z b) := hc
      refine PathChannelEvaluation.lambda hx ?_
      refine PathChannelEvaluation.beta rfl hs ?_
      exact atomic_nil_pathChannelEvaluation D₀ j₀ realize hbody hdistBody
        rfl rfl
        ((channelInternalStep_of_beta
          (s := {s with control := .value (.closure z b s.env)})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_lambda hx).preserve_wellScoped hscoped))
        active
  | recLam self z b =>
      have hx : s.control = .term (.recLam self z b) := hc
      refine PathChannelEvaluation.recursive hx ?_
      refine PathChannelEvaluation.beta rfl hs ?_
      exact atomic_nil_pathChannelEvaluation D₀ j₀ realize hbody hdistBody
        rfl rfl
        ((channelInternalStep_of_beta
          (s :=
            {s with control := .value (.recClosure self z b s.env)})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_recursive hx).preserve_wellScoped
            hscoped))
        active
  | intern left right hleft hright ihL ihR =>
      have hx : s.control = .term (.intern left right) := hc
      have ⟨hdistL, hdistR⟩ := hdistArg
      refine PathChannelEvaluation.intern hx ?_ ?_
      · exact ihL (s := {s with control := .term left}) hdistL rfl hs
          (wellScoped_intern_left hx hscoped) active
      · exact ihR (s := {s with control := .term right}) hdistR rfl hs
          (wellScoped_intern_right hx hscoped) active
  | prob p left right hp₀ hp₁ hleft hright ihL ihR =>
      have hx : s.control = .term (.prob p left right) := hc
      have ⟨hdistL, hdistR⟩ := hdistArg
      by_cases hz : p = 0
      · subst hz
        refine PathChannelEvaluation.probZero hx ?_
        exact ihR (s :=
            {s with
              control := .term right
              quantum :=
                applyOperation
                  (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                  s.quantum})
          hdistR rfl hs (wellScoped_prob_right hx hscoped _) active
      · by_cases ho : p = 1
        · subst ho
          refine PathChannelEvaluation.probOne hx ?_
          exact ihL (s :=
              {s with
                control := .term left
                quantum :=
                  applyOperation
                    (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                    s.quantum})
            hdistL rfl hs (wellScoped_prob_left hx hscoped _) active
        · have hp0' : 0 < p := lt_of_le_of_ne hp₀ (Ne.symm hz)
          have hp1' : p < 1 := lt_of_le_of_ne hp₁ ho
          refine PathChannelEvaluation.probability hp0' hp1' hx ?_ ?_
          · exact ihL (s :=
                {s with
                  control := .term left
                  quantum :=
                    applyOperation
                      (sourceProbabilityOperation p hp0'.le hp1'.le)
                      s.quantum})
              hdistL rfl hs (wellScoped_prob_left hx hscoped _) active
          · exact ihR (s :=
                {s with
                  control := .term right
                  quantum :=
                    applyOperation
                      (sourceProbabilityOperation (1 - p)
                        (sub_nonneg.mpr hp1'.le) (by linarith))
                      s.quantum})
              hdistR rfl hs (wellScoped_prob_right hx hscoped _) active

/-- The same as `atomic_under_closure_pathChannelEvaluation` for a
recursive closure frame. -/
theorem atomic_under_recClosure_pathChannelEvaluation {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {arg : Term (QubitPrimitive C)}
    {self x : Name} {body : Term (QubitPrimitive C)}
    {cloEnv : RuntimeEnv C}
    (hatom : Atomic arg)
    (hdistArg : MeasureDistinct realize arg)
    (hbody : Atomic body)
    (hdistBody : MeasureDistinct realize body)
    (hc : s.control = .term arg)
    (hs : s.stack = [.function (.recClosure self x body cloEnv)])
    (hscoped : ChannelConfig.WellScoped s)
    (active : ℕ) :
    PathChannelEvaluation D₀ j₀ realize s active
      [(.function (.recClosure self x body cloEnv), active)] := by
  induction hatom generalizing s active with
  | var y =>
      have hx : s.control = .term (.var y) := hc
      have ⟨hctl, _⟩ := hscoped
      rw [hx] at hctl
      obtain ⟨v, hlookup⟩ := covers_var hctl.right
      refine PathChannelEvaluation.varLookup hx hlookup ?_
      refine PathChannelEvaluation.recBeta rfl hs ?_
      exact atomic_nil_pathChannelEvaluation D₀ j₀ realize hbody hdistBody
        rfl rfl
        ((channelInternalStep_of_recBeta
          (s := {s with control := .value v})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_variable hx hlookup).preserve_wellScoped
            hscoped))
        active
  | ret value =>
      have hx : s.control = .term (.prim (.ret value)) := hc
      refine PathChannelEvaluation.returnPayload hx ?_
      refine PathChannelEvaluation.recBeta rfl hs ?_
      exact atomic_nil_pathChannelEvaluation D₀ j₀ realize hbody hdistBody
        rfl rfl
        ((channelInternalStep_of_recBeta
          (s := {s with control := .value (.payload value)})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_return hx).preserve_wellScoped hscoped))
        active
  | measureZ zeroValue oneValue =>
      have hx : s.control =
          .term (.prim (.measureZ zeroValue oneValue)) := hc
      refine PathChannelEvaluation.measurement hx hdistArg ?_ ?_
      · refine PathChannelEvaluation.recBeta rfl hs ?_
        exact atomic_nil_pathChannelEvaluation D₀ j₀ realize hbody
          hdistBody rfl rfl
          ((channelInternalStep_of_recBeta
            (s :=
              {s with
                control := .value (.payload zeroValue)
                quantum :=
                  applyOperation (measurementOperation false) s.quantum})
            rfl hs).preserve_wellScoped
            (wellScoped_payload_child hx hscoped zeroValue _))
          active
      · refine PathChannelEvaluation.recBeta rfl hs ?_
        exact atomic_nil_pathChannelEvaluation D₀ j₀ realize hbody
          hdistBody rfl rfl
          ((channelInternalStep_of_recBeta
            (s :=
              {s with
                control := .value (.payload oneValue)
                quantum :=
                  applyOperation (measurementOperation true) s.quantum})
            rfl hs).preserve_wellScoped
            (wellScoped_payload_child hx hscoped oneValue _))
          active
  | lam z b =>
      have hx : s.control = .term (.lam z b) := hc
      refine PathChannelEvaluation.lambda hx ?_
      refine PathChannelEvaluation.recBeta rfl hs ?_
      exact atomic_nil_pathChannelEvaluation D₀ j₀ realize hbody hdistBody
        rfl rfl
        ((channelInternalStep_of_recBeta
          (s := {s with control := .value (.closure z b s.env)})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_lambda hx).preserve_wellScoped hscoped))
        active
  | recLam self' z b =>
      have hx : s.control = .term (.recLam self' z b) := hc
      refine PathChannelEvaluation.recursive hx ?_
      refine PathChannelEvaluation.recBeta rfl hs ?_
      exact atomic_nil_pathChannelEvaluation D₀ j₀ realize hbody hdistBody
        rfl rfl
        ((channelInternalStep_of_recBeta
          (s :=
            {s with control := .value (.recClosure self' z b s.env)})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_recursive hx).preserve_wellScoped
            hscoped))
        active
  | intern left right hleft hright ihL ihR =>
      have hx : s.control = .term (.intern left right) := hc
      have ⟨hdistL, hdistR⟩ := hdistArg
      refine PathChannelEvaluation.intern hx ?_ ?_
      · exact ihL (s := {s with control := .term left}) hdistL rfl hs
          (wellScoped_intern_left hx hscoped) active
      · exact ihR (s := {s with control := .term right}) hdistR rfl hs
          (wellScoped_intern_right hx hscoped) active
  | prob p left right hp₀ hp₁ hleft hright ihL ihR =>
      have hx : s.control = .term (.prob p left right) := hc
      have ⟨hdistL, hdistR⟩ := hdistArg
      by_cases hz : p = 0
      · subst hz
        refine PathChannelEvaluation.probZero hx ?_
        exact ihR (s :=
            {s with
              control := .term right
              quantum :=
                applyOperation
                  (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                  s.quantum})
          hdistR rfl hs (wellScoped_prob_right hx hscoped _) active
      · by_cases ho : p = 1
        · subst ho
          refine PathChannelEvaluation.probOne hx ?_
          exact ihL (s :=
              {s with
                control := .term left
                quantum :=
                  applyOperation
                    (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                    s.quantum})
            hdistL rfl hs (wellScoped_prob_left hx hscoped _) active
        · have hp0' : 0 < p := lt_of_le_of_ne hp₀ (Ne.symm hz)
          have hp1' : p < 1 := lt_of_le_of_ne hp₁ ho
          refine PathChannelEvaluation.probability hp0' hp1' hx ?_ ?_
          · exact ihL (s :=
                {s with
                  control := .term left
                  quantum :=
                    applyOperation
                      (sourceProbabilityOperation p hp0'.le hp1'.le)
                      s.quantum})
              hdistL rfl hs (wellScoped_prob_left hx hscoped _) active
          · exact ihR (s :=
                {s with
                  control := .term right
                  quantum :=
                    applyOperation
                      (sourceProbabilityOperation (1 - p)
                        (sub_nonneg.mpr hp1'.le) (by linarith))
                      s.quantum})
              hdistR rfl hs (wellScoped_prob_right hx hscoped _) active

/-! ## Closed `app (lam / recLam) arg` with an atomic argument -/

/-- Path evaluation of `app (lam x body) arg` at the empty stack when
the body and argument are atomic. -/
theorem app_lam_atomic_nil_pathChannelEvaluation {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x : Name}
    {body arg : Term (QubitPrimitive C)}
    (hbody : Atomic body)
    (harg : Atomic arg)
    (hdist : MeasureDistinct realize (.app (.lam x body) arg))
    (hc : s.control = .term (.app (.lam x body) arg))
    (hs : s.stack = [])
    (hscoped : ChannelConfig.WellScoped s)
    (active : ℕ) :
    PathChannelEvaluation D₀ j₀ realize s active [] := by
  have ⟨hdistFn, hdistArg⟩ := hdist
  have hdistBody : MeasureDistinct realize body := hdistFn
  let sFn : ChannelConfig C :=
    {s with
      control := .term (.lam x body)
      stack := .argument arg s.env :: s.stack}
  let sClo : ChannelConfig C :=
    {s with
      control := .value (.closure x body s.env)
      stack := .argument arg s.env :: s.stack}
  let sArg : ChannelConfig C :=
    {s with
      control := .term arg
      env := s.env
      stack := .function (.closure x body s.env) :: s.stack}
  refine PathChannelEvaluation.application hc ?_
  refine PathChannelEvaluation.lambda (s := sFn) rfl ?_
  refine PathChannelEvaluation.evaluateArgument (s := sClo) rfl rfl ?_
  exact atomic_under_closure_pathChannelEvaluation D₀ j₀ realize
    (s := sArg) harg hdistArg hbody hdistBody rfl (by simp [sArg, hs])
    ((channelInternalStep_of_evaluateArgument (s := sClo) rfl
      rfl).preserve_wellScoped
      ((channelInternalStep_of_lambda (s := sFn) rfl).preserve_wellScoped
        ((channelInternalStep_of_application hc).preserve_wellScoped
          hscoped)))
    active

/-- Path evaluation of `app (recLam self x body) arg` at the empty stack
when the body and argument are atomic. -/
theorem app_recLam_atomic_nil_pathChannelEvaluation {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {self x : Name}
    {body arg : Term (QubitPrimitive C)}
    (hbody : Atomic body)
    (harg : Atomic arg)
    (hdist : MeasureDistinct realize (.app (.recLam self x body) arg))
    (hc : s.control = .term (.app (.recLam self x body) arg))
    (hs : s.stack = [])
    (hscoped : ChannelConfig.WellScoped s)
    (active : ℕ) :
    PathChannelEvaluation D₀ j₀ realize s active [] := by
  have ⟨hdistFn, hdistArg⟩ := hdist
  have hdistBody : MeasureDistinct realize body := hdistFn
  let sFn : ChannelConfig C :=
    {s with
      control := .term (.recLam self x body)
      stack := .argument arg s.env :: s.stack}
  let sClo : ChannelConfig C :=
    {s with
      control := .value (.recClosure self x body s.env)
      stack := .argument arg s.env :: s.stack}
  let sArg : ChannelConfig C :=
    {s with
      control := .term arg
      env := s.env
      stack := .function (.recClosure self x body s.env) :: s.stack}
  refine PathChannelEvaluation.application hc ?_
  refine PathChannelEvaluation.recursive (s := sFn) rfl ?_
  refine PathChannelEvaluation.evaluateArgument (s := sClo) rfl rfl ?_
  exact atomic_under_recClosure_pathChannelEvaluation D₀ j₀ realize
    (s := sArg) harg hdistArg hbody hdistBody rfl (by simp [sArg, hs])
    ((channelInternalStep_of_evaluateArgument (s := sClo) rfl
      rfl).preserve_wellScoped
      ((channelInternalStep_of_recursive (s := sFn) rfl).preserve_wellScoped
        ((channelInternalStep_of_application hc).preserve_wellScoped
          hscoped)))
    active

/-! ## Leftover-arity spines and `Productive 0` arguments -/

/-- Observed leftover argument frames, all tagged with the same active
coordinate. -/
def argumentObserved {C : Type} (active : ℕ)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C)) :
    ObservedStack C :=
  frames.map fun p => (.argument p.1 p.2, active)

@[simp]
theorem argumentObserved_nil {C : Type} (active : ℕ) :
    argumentObserved active
      ([] : List (Term (QubitPrimitive C) × RuntimeEnv C)) = [] :=
  rfl

@[simp]
theorem argumentObserved_cons {C : Type} (active : ℕ)
    (arg : Term (QubitPrimitive C)) (callEnv : RuntimeEnv C)
    (rest : List (Term (QubitPrimitive C) × RuntimeEnv C)) :
    argumentObserved active ((arg, callEnv) :: rest) =
      (.argument arg callEnv, active) ::
        argumentObserved active rest :=
  rfl

theorem argumentObserved_erase {C : Type} (active : ℕ)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C)) :
    ObservedStack.erase (argumentObserved active frames) =
      argumentStack frames := by
  induction frames with
  | nil => simp [argumentObserved, argumentStack, ObservedStack.erase]
  | cons p rest ih =>
      cases p
      simp [argumentObserved, argumentStack, ObservedStack.erase, ih]

/-- Leftover frames that a path evaluation can run as arguments. -/
def AtomicFramesOk {C : Type}
    {D₀ : QDomain.{0}}
    {j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier)}
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C)) : Prop :=
  ∀ p ∈ frames, Atomic p.1 ∧ MeasureDistinct realize p.1

/-- An `Atomic` argument under an ordinary closure, then a `Productive n`
body under `n` leftover Atomic argument frames. -/
theorem atomic_under_closure_then_args_pathChannelEvaluation {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {arg : Term (QubitPrimitive C)}
    {x : Name} {body : Term (QubitPrimitive C)} {cloEnv : RuntimeEnv C}
    {n : Nat} {frames : List (Term (QubitPrimitive C) × RuntimeEnv C)}
    (hatom : Atomic arg)
    (hdistArg : MeasureDistinct realize arg)
    (_hbody : Productive n body)
    (hdistBody : MeasureDistinct realize body)
    (_hframes : frames.length = n)
    (_hok : AtomicFramesOk realize frames)
    (hc : s.control = .term arg)
    (hs : s.stack =
      .function (.closure x body cloEnv) :: argumentStack frames)
    (hscoped : ChannelConfig.WellScoped s)
    (active : ℕ)
    (hbodyEval :
      ∀ (s' : ChannelConfig C),
        s'.control = .term body →
        s'.stack = argumentStack frames →
        ChannelConfig.WellScoped s' →
        PathChannelEvaluation D₀ j₀ realize s' active
          (argumentObserved active frames)) :
    PathChannelEvaluation D₀ j₀ realize s active
      ((.function (.closure x body cloEnv), active) ::
        argumentObserved active frames) := by
  induction hatom generalizing s with
  | var y =>
      have hx : s.control = .term (.var y) := hc
      have ⟨hctl, _⟩ := hscoped
      rw [hx] at hctl
      obtain ⟨v, hlookup⟩ := covers_var hctl.right
      refine PathChannelEvaluation.varLookup hx hlookup ?_
      refine PathChannelEvaluation.beta rfl hs ?_
      exact hbodyEval _ rfl rfl
        ((channelInternalStep_of_beta (s := {s with control := .value v})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_variable hx hlookup).preserve_wellScoped
            hscoped))
  | ret value =>
      have hx : s.control = .term (.prim (.ret value)) := hc
      refine PathChannelEvaluation.returnPayload hx ?_
      refine PathChannelEvaluation.beta rfl hs ?_
      exact hbodyEval _ rfl rfl
        ((channelInternalStep_of_beta
          (s := {s with control := .value (.payload value)})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_return hx).preserve_wellScoped hscoped))
  | measureZ zeroValue oneValue =>
      have hx : s.control =
          .term (.prim (.measureZ zeroValue oneValue)) := hc
      refine PathChannelEvaluation.measurement hx hdistArg ?_ ?_
      · refine PathChannelEvaluation.beta rfl hs ?_
        exact hbodyEval _ rfl rfl
          ((channelInternalStep_of_beta
            (s :=
              {s with
                control := .value (.payload zeroValue)
                quantum :=
                  applyOperation (measurementOperation false) s.quantum})
            rfl hs).preserve_wellScoped
            (wellScoped_payload_child hx hscoped zeroValue _))
      · refine PathChannelEvaluation.beta rfl hs ?_
        exact hbodyEval _ rfl rfl
          ((channelInternalStep_of_beta
            (s :=
              {s with
                control := .value (.payload oneValue)
                quantum :=
                  applyOperation (measurementOperation true) s.quantum})
            rfl hs).preserve_wellScoped
            (wellScoped_payload_child hx hscoped oneValue _))
  | lam z b =>
      have hx : s.control = .term (.lam z b) := hc
      refine PathChannelEvaluation.lambda hx ?_
      refine PathChannelEvaluation.beta rfl hs ?_
      exact hbodyEval _ rfl rfl
        ((channelInternalStep_of_beta
          (s := {s with control := .value (.closure z b s.env)})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_lambda hx).preserve_wellScoped hscoped))
  | recLam self z b =>
      have hx : s.control = .term (.recLam self z b) := hc
      refine PathChannelEvaluation.recursive hx ?_
      refine PathChannelEvaluation.beta rfl hs ?_
      exact hbodyEval _ rfl rfl
        ((channelInternalStep_of_beta
          (s :=
            {s with control := .value (.recClosure self z b s.env)})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_recursive hx).preserve_wellScoped
            hscoped))
  | intern left right hleft hright ihL ihR =>
      have hx : s.control = .term (.intern left right) := hc
      have ⟨hdistL, hdistR⟩ := hdistArg
      refine PathChannelEvaluation.intern hx ?_ ?_
      · exact ihL (s := {s with control := .term left}) hdistL rfl hs
          (wellScoped_intern_left hx hscoped)
      · exact ihR (s := {s with control := .term right}) hdistR rfl hs
          (wellScoped_intern_right hx hscoped)
  | prob p left right hp₀ hp₁ hleft hright ihL ihR =>
      have hx : s.control = .term (.prob p left right) := hc
      have ⟨hdistL, hdistR⟩ := hdistArg
      by_cases hz : p = 0
      · subst hz
        refine PathChannelEvaluation.probZero hx ?_
        exact ihR (s :=
            {s with
              control := .term right
              quantum :=
                applyOperation
                  (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                  s.quantum})
          hdistR rfl hs (wellScoped_prob_right hx hscoped _)
      · by_cases ho : p = 1
        · subst ho
          refine PathChannelEvaluation.probOne hx ?_
          exact ihL (s :=
              {s with
                control := .term left
                quantum :=
                  applyOperation
                    (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                    s.quantum})
            hdistL rfl hs (wellScoped_prob_left hx hscoped _)
        · have hp0' : 0 < p := lt_of_le_of_ne hp₀ (Ne.symm hz)
          have hp1' : p < 1 := lt_of_le_of_ne hp₁ ho
          refine PathChannelEvaluation.probability hp0' hp1' hx ?_ ?_
          · exact ihL (s :=
                {s with
                  control := .term left
                  quantum :=
                    applyOperation
                      (sourceProbabilityOperation p hp0'.le hp1'.le)
                      s.quantum})
              hdistL rfl hs (wellScoped_prob_left hx hscoped _)
          · exact ihR (s :=
                {s with
                  control := .term right
                  quantum :=
                    applyOperation
                      (sourceProbabilityOperation (1 - p)
                        (sub_nonneg.mpr hp1'.le) (by linarith))
                      s.quantum})
              hdistR rfl hs (wellScoped_prob_right hx hscoped _)

/-- The same as `atomic_under_closure_then_args_pathChannelEvaluation`
for a recursive closure frame. -/
theorem atomic_under_recClosure_then_args_pathChannelEvaluation {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {arg : Term (QubitPrimitive C)}
    {self x : Name} {body : Term (QubitPrimitive C)} {cloEnv : RuntimeEnv C}
    {n : Nat} {frames : List (Term (QubitPrimitive C) × RuntimeEnv C)}
    (hatom : Atomic arg)
    (hdistArg : MeasureDistinct realize arg)
    (_hbody : Productive n body)
    (hdistBody : MeasureDistinct realize body)
    (_hframes : frames.length = n)
    (_hok : AtomicFramesOk realize frames)
    (hc : s.control = .term arg)
    (hs : s.stack =
      .function (.recClosure self x body cloEnv) :: argumentStack frames)
    (hscoped : ChannelConfig.WellScoped s)
    (active : ℕ)
    (hbodyEval :
      ∀ (s' : ChannelConfig C),
        s'.control = .term body →
        s'.stack = argumentStack frames →
        ChannelConfig.WellScoped s' →
        PathChannelEvaluation D₀ j₀ realize s' active
          (argumentObserved active frames)) :
    PathChannelEvaluation D₀ j₀ realize s active
      ((.function (.recClosure self x body cloEnv), active) ::
        argumentObserved active frames) := by
  induction hatom generalizing s with
  | var y =>
      have hx : s.control = .term (.var y) := hc
      have ⟨hctl, _⟩ := hscoped
      rw [hx] at hctl
      obtain ⟨v, hlookup⟩ := covers_var hctl.right
      refine PathChannelEvaluation.varLookup hx hlookup ?_
      refine PathChannelEvaluation.recBeta rfl hs ?_
      exact hbodyEval _ rfl rfl
        ((channelInternalStep_of_recBeta (s := {s with control := .value v})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_variable hx hlookup).preserve_wellScoped
            hscoped))
  | ret value =>
      have hx : s.control = .term (.prim (.ret value)) := hc
      refine PathChannelEvaluation.returnPayload hx ?_
      refine PathChannelEvaluation.recBeta rfl hs ?_
      exact hbodyEval _ rfl rfl
        ((channelInternalStep_of_recBeta
          (s := {s with control := .value (.payload value)})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_return hx).preserve_wellScoped hscoped))
  | measureZ zeroValue oneValue =>
      have hx : s.control =
          .term (.prim (.measureZ zeroValue oneValue)) := hc
      refine PathChannelEvaluation.measurement hx hdistArg ?_ ?_
      · refine PathChannelEvaluation.recBeta rfl hs ?_
        exact hbodyEval _ rfl rfl
          ((channelInternalStep_of_recBeta
            (s :=
              {s with
                control := .value (.payload zeroValue)
                quantum :=
                  applyOperation (measurementOperation false) s.quantum})
            rfl hs).preserve_wellScoped
            (wellScoped_payload_child hx hscoped zeroValue _))
      · refine PathChannelEvaluation.recBeta rfl hs ?_
        exact hbodyEval _ rfl rfl
          ((channelInternalStep_of_recBeta
            (s :=
              {s with
                control := .value (.payload oneValue)
                quantum :=
                  applyOperation (measurementOperation true) s.quantum})
            rfl hs).preserve_wellScoped
            (wellScoped_payload_child hx hscoped oneValue _))
  | lam z b =>
      have hx : s.control = .term (.lam z b) := hc
      refine PathChannelEvaluation.lambda hx ?_
      refine PathChannelEvaluation.recBeta rfl hs ?_
      exact hbodyEval _ rfl rfl
        ((channelInternalStep_of_recBeta
          (s := {s with control := .value (.closure z b s.env)})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_lambda hx).preserve_wellScoped hscoped))
  | recLam self' z b =>
      have hx : s.control = .term (.recLam self' z b) := hc
      refine PathChannelEvaluation.recursive hx ?_
      refine PathChannelEvaluation.recBeta rfl hs ?_
      exact hbodyEval _ rfl rfl
        ((channelInternalStep_of_recBeta
          (s :=
            {s with control := .value (.recClosure self' z b s.env)})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_recursive hx).preserve_wellScoped
            hscoped))
  | intern left right hleft hright ihL ihR =>
      have hx : s.control = .term (.intern left right) := hc
      have ⟨hdistL, hdistR⟩ := hdistArg
      refine PathChannelEvaluation.intern hx ?_ ?_
      · exact ihL (s := {s with control := .term left}) hdistL rfl hs
          (wellScoped_intern_left hx hscoped)
      · exact ihR (s := {s with control := .term right}) hdistR rfl hs
          (wellScoped_intern_right hx hscoped)
  | prob p left right hp₀ hp₁ hleft hright ihL ihR =>
      have hx : s.control = .term (.prob p left right) := hc
      have ⟨hdistL, hdistR⟩ := hdistArg
      by_cases hz : p = 0
      · subst hz
        refine PathChannelEvaluation.probZero hx ?_
        exact ihR (s :=
            {s with
              control := .term right
              quantum :=
                applyOperation
                  (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                  s.quantum})
          hdistR rfl hs (wellScoped_prob_right hx hscoped _)
      · by_cases ho : p = 1
        · subst ho
          refine PathChannelEvaluation.probOne hx ?_
          exact ihL (s :=
              {s with
                control := .term left
                quantum :=
                  applyOperation
                    (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                    s.quantum})
            hdistL rfl hs (wellScoped_prob_left hx hscoped _)
        · have hp0' : 0 < p := lt_of_le_of_ne hp₀ (Ne.symm hz)
          have hp1' : p < 1 := lt_of_le_of_ne hp₁ ho
          refine PathChannelEvaluation.probability hp0' hp1' hx ?_ ?_
          · exact ihL (s :=
                {s with
                  control := .term left
                  quantum :=
                    applyOperation
                      (sourceProbabilityOperation p hp0'.le hp1'.le)
                      s.quantum})
              hdistL rfl hs (wellScoped_prob_left hx hscoped _)
          · exact ihR (s :=
                {s with
                  control := .term right
                  quantum :=
                    applyOperation
                      (sourceProbabilityOperation (1 - p)
                        (sub_nonneg.mpr hp1'.le) (by linarith))
                      s.quantum})
              hdistR rfl hs (wellScoped_prob_right hx hscoped _)

/-- A `Productive n` term under exactly `n` leftover Atomic argument
frames has a branch-complete path evaluation.  This is leftover-arity
(`app (app (lam (lam ·)) ·) ·`) and, when the leftover argument is
itself `Productive 0` via `atomic`, the inner application spine. -/
theorem productive_under_argument_frames_pathChannelEvaluation {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {n : Nat} {code : Term (QubitPrimitive C)}
    {frames : List (Term (QubitPrimitive C) × RuntimeEnv C)}
    (hprod : Productive n code)
    (hdist : MeasureDistinct realize code)
    (hlen : frames.length = n)
    (hok : AtomicFramesOk realize frames)
    (hc : s.control = .term code)
    (hs : s.stack = argumentStack frames)
    (hscoped : ChannelConfig.WellScoped s)
    (active : ℕ) :
    PathChannelEvaluation D₀ j₀ realize s active
      (argumentObserved active frames) := by
  induction hprod generalizing s frames with
  | atomic hatom =>
      have hnil : frames = [] := List.eq_nil_of_length_eq_zero hlen
      subst frames
      exact atomic_nil_pathChannelEvaluation D₀ j₀ realize hatom hdist hc
        (by simpa [argumentStack] using hs) hscoped active
  | lam n x body hprod ih =>
      match frames with
      | [] =>
          exact (Nat.succ_ne_zero n hlen.symm).elim
      | (arg, callEnv) :: rest =>
          have hlenRest : rest.length = n := by simpa using hlen
          have ⟨hatomArg, hdistArg⟩ := hok (arg, callEnv) (by simp)
          have hokRest : AtomicFramesOk realize rest :=
            fun q hq => hok q (by simp [hq])
          have hdistBody : MeasureDistinct realize body := hdist
          have hscopedArg :
              ChannelConfig.WellScoped
                {s with
                  control := .term arg
                  env := callEnv
                  stack :=
                    .function (.closure x body s.env) ::
                      argumentStack rest} :=
            (channelInternalStep_of_evaluateArgument
              (s := {s with control := .value (.closure x body s.env)})
              rfl (by simpa using hs)).preserve_wellScoped
              ((channelInternalStep_of_lambda (s := s) hc).preserve_wellScoped
                hscoped)
          refine PathChannelEvaluation.lambda (s := s) hc ?_
          refine PathChannelEvaluation.evaluateArgument
            (s := {s with control := .value (.closure x body s.env)})
            rfl (by simpa using hs) ?_
          exact atomic_under_closure_then_args_pathChannelEvaluation
            D₀ j₀ realize hatomArg hdistArg hprod hdistBody hlenRest hokRest
            rfl rfl hscopedArg active
            (fun s' hc' hs' hscoped' =>
              ih (s := s') (frames := rest) hdistBody hlenRest hokRest
                hc' hs' hscoped')
  | recLam n self x body hprod ih =>
      match frames with
      | [] =>
          exact (Nat.succ_ne_zero n hlen.symm).elim
      | (arg, callEnv) :: rest =>
          have hlenRest : rest.length = n := by simpa using hlen
          have ⟨hatomArg, hdistArg⟩ := hok (arg, callEnv) (by simp)
          have hokRest : AtomicFramesOk realize rest :=
            fun q hq => hok q (by simp [hq])
          have hdistBody : MeasureDistinct realize body := hdist
          have hscopedArg :
              ChannelConfig.WellScoped
                {s with
                  control := .term arg
                  env := callEnv
                  stack :=
                    .function (.recClosure self x body s.env) ::
                      argumentStack rest} :=
            (channelInternalStep_of_evaluateArgument
              (s := {s with control := .value (.recClosure self x body s.env)})
              rfl (by simpa using hs)).preserve_wellScoped
              ((channelInternalStep_of_recursive (s := s) hc).preserve_wellScoped
                hscoped)
          refine PathChannelEvaluation.recursive (s := s) hc ?_
          refine PathChannelEvaluation.evaluateArgument
            (s := {s with control := .value (.recClosure self x body s.env)})
            rfl (by simpa using hs) ?_
          exact atomic_under_recClosure_then_args_pathChannelEvaluation
            D₀ j₀ realize hatomArg hdistArg hprod hdistBody hlenRest hokRest
            rfl rfl hscopedArg active
            (fun s' hc' hs' hscoped' =>
              ih (s := s') (frames := rest) hdistBody hlenRest hokRest
                hc' hs' hscoped')
  | app n fn arg hfn harg ih =>
      have ⟨hdistFn, hdistArg⟩ := hdist
      refine PathChannelEvaluation.application hc ?_
      exact ih (frames := (arg, s.env) :: frames) hdistFn
        (by simpa using hlen)
        (fun q hq => by
          simp at hq
          rcases hq with hhere | hrest
          · cases hhere
            exact ⟨harg, hdistArg⟩
          · exact hok q hrest)
        rfl (by simp [hs])
        ((channelInternalStep_of_application hc).preserve_wellScoped
          hscoped)

/-- Closed `extern` at the empty stack, with Atomic children. -/
theorem extern_nil_pathChannelEvaluation {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
    (hleft : Atomic left)
    (hright : Atomic right)
    (hdist : MeasureDistinct realize (.extern left right))
    (hc : s.control = .term (.extern left right))
    (hs : s.stack = [])
    (hscoped : ChannelConfig.WellScoped s)
    (active : ℕ) :
    PathChannelEvaluation D₀ j₀ realize s active [] := by
  have ⟨hdistL, hdistR⟩ := hdist
  match active with
  | 0 => exact PathChannelEvaluation.externRoot hc
  | n + 1 =>
      let selected : Bool := n % 2 ≠ 0
      let childActive : ℕ := n / 2
      have hstep :=
        channelExternalStep_of_extern (selected := selected) hc
      refine (branchCoordinate_succ n) ▸
        PathChannelEvaluation.externBranch hc hstep ?_
      exact atomic_nil_pathChannelEvaluation D₀ j₀ realize
        (s := {s with control := .term (if selected then right else left)})
        (by cases selected <;> first | exact hright | exact hleft)
        (by cases selected <;> first | exact hdistR | exact hdistL)
        rfl hs (hstep.preserve_wellScoped hscoped) childActive

/-- An `Atomic` argument under two ordinary closures: beta into the
inner `Atomic` body under the outer closure, then the outer body at
the empty stack.  This is `app` as an argument. -/
theorem atomic_under_two_closures_pathChannelEvaluation {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {arg : Term (QubitPrimitive C)}
    {y : Name} {inner : Term (QubitPrimitive C)} {cloY : RuntimeEnv C}
    {x : Name} {body : Term (QubitPrimitive C)} {cloX : RuntimeEnv C}
    (hatom : Atomic arg)
    (hdistArg : MeasureDistinct realize arg)
    (hinner : Atomic inner)
    (hdistInner : MeasureDistinct realize inner)
    (hbody : Atomic body)
    (hdistBody : MeasureDistinct realize body)
    (hc : s.control = .term arg)
    (hs : s.stack =
      [.function (.closure y inner cloY),
        .function (.closure x body cloX)])
    (hscoped : ChannelConfig.WellScoped s)
    (active : ℕ) :
    PathChannelEvaluation D₀ j₀ realize s active
      [(.function (.closure y inner cloY), active),
        (.function (.closure x body cloX), active)] := by
  induction hatom generalizing s with
  | var z =>
      have hx : s.control = .term (.var z) := hc
      have ⟨hctl, _⟩ := hscoped
      rw [hx] at hctl
      obtain ⟨v, hlookup⟩ := covers_var hctl.right
      refine PathChannelEvaluation.varLookup hx hlookup ?_
      refine PathChannelEvaluation.beta rfl hs ?_
      exact atomic_under_closure_pathChannelEvaluation D₀ j₀ realize
        hinner hdistInner hbody hdistBody rfl rfl
        ((channelInternalStep_of_beta (s := {s with control := .value v})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_variable hx hlookup).preserve_wellScoped
            hscoped))
        active
  | ret value =>
      have hx : s.control = .term (.prim (.ret value)) := hc
      refine PathChannelEvaluation.returnPayload hx ?_
      refine PathChannelEvaluation.beta rfl hs ?_
      exact atomic_under_closure_pathChannelEvaluation D₀ j₀ realize
        hinner hdistInner hbody hdistBody rfl rfl
        ((channelInternalStep_of_beta
          (s := {s with control := .value (.payload value)})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_return hx).preserve_wellScoped hscoped))
        active
  | measureZ zeroValue oneValue =>
      have hx : s.control =
          .term (.prim (.measureZ zeroValue oneValue)) := hc
      refine PathChannelEvaluation.measurement hx hdistArg ?_ ?_
      · refine PathChannelEvaluation.beta rfl hs ?_
        exact atomic_under_closure_pathChannelEvaluation D₀ j₀ realize
          hinner hdistInner hbody hdistBody rfl rfl
          ((channelInternalStep_of_beta
            (s :=
              {s with
                control := .value (.payload zeroValue)
                quantum :=
                  applyOperation (measurementOperation false) s.quantum})
            rfl hs).preserve_wellScoped
            (wellScoped_payload_child hx hscoped zeroValue _))
          active
      · refine PathChannelEvaluation.beta rfl hs ?_
        exact atomic_under_closure_pathChannelEvaluation D₀ j₀ realize
          hinner hdistInner hbody hdistBody rfl rfl
          ((channelInternalStep_of_beta
            (s :=
              {s with
                control := .value (.payload oneValue)
                quantum :=
                  applyOperation (measurementOperation true) s.quantum})
            rfl hs).preserve_wellScoped
            (wellScoped_payload_child hx hscoped oneValue _))
          active
  | lam z b =>
      have hx : s.control = .term (.lam z b) := hc
      refine PathChannelEvaluation.lambda hx ?_
      refine PathChannelEvaluation.beta rfl hs ?_
      exact atomic_under_closure_pathChannelEvaluation D₀ j₀ realize
        hinner hdistInner hbody hdistBody rfl rfl
        ((channelInternalStep_of_beta
          (s := {s with control := .value (.closure z b s.env)})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_lambda hx).preserve_wellScoped hscoped))
        active
  | recLam self z b =>
      have hx : s.control = .term (.recLam self z b) := hc
      refine PathChannelEvaluation.recursive hx ?_
      refine PathChannelEvaluation.beta rfl hs ?_
      exact atomic_under_closure_pathChannelEvaluation D₀ j₀ realize
        hinner hdistInner hbody hdistBody rfl rfl
        ((channelInternalStep_of_beta
          (s :=
            {s with control := .value (.recClosure self z b s.env)})
          rfl hs).preserve_wellScoped
          ((channelInternalStep_of_recursive hx).preserve_wellScoped
            hscoped))
        active
  | intern left right hleft hright ihL ihR =>
      have hx : s.control = .term (.intern left right) := hc
      have ⟨hdistL, hdistR⟩ := hdistArg
      refine PathChannelEvaluation.intern hx ?_ ?_
      · exact ihL (s := {s with control := .term left}) hdistL rfl hs
          (wellScoped_intern_left hx hscoped)
      · exact ihR (s := {s with control := .term right}) hdistR rfl hs
          (wellScoped_intern_right hx hscoped)
  | prob p left right hp₀ hp₁ hleft hright ihL ihR =>
      have hx : s.control = .term (.prob p left right) := hc
      have ⟨hdistL, hdistR⟩ := hdistArg
      by_cases hz : p = 0
      · subst hz
        refine PathChannelEvaluation.probZero hx ?_
        exact ihR (s :=
            {s with
              control := .term right
              quantum :=
                applyOperation
                  (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                  s.quantum})
          hdistR rfl hs (wellScoped_prob_right hx hscoped _)
      · by_cases ho : p = 1
        · subst ho
          refine PathChannelEvaluation.probOne hx ?_
          exact ihL (s :=
              {s with
                control := .term left
                quantum :=
                  applyOperation
                    (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                    s.quantum})
            hdistL rfl hs (wellScoped_prob_left hx hscoped _)
        · have hp0' : 0 < p := lt_of_le_of_ne hp₀ (Ne.symm hz)
          have hp1' : p < 1 := lt_of_le_of_ne hp₁ ho
          refine PathChannelEvaluation.probability hp0' hp1' hx ?_ ?_
          · exact ihL (s :=
                {s with
                  control := .term left
                  quantum :=
                    applyOperation
                      (sourceProbabilityOperation p hp0'.le hp1'.le)
                      s.quantum})
              hdistL rfl hs (wellScoped_prob_left hx hscoped _)
          · exact ihR (s :=
                {s with
                  control := .term right
                  quantum :=
                    applyOperation
                      (sourceProbabilityOperation (1 - p)
                        (sub_nonneg.mpr hp1'.le) (by linarith))
                      s.quantum})
              hdistR rfl hs (wellScoped_prob_right hx hscoped _)

/-- Path evaluation of `app (lam x body) (app (lam y inner) arg)` at the
empty stack when every piece is atomic. -/
theorem app_lam_app_nil_pathChannelEvaluation {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x y : Name}
    {body inner arg : Term (QubitPrimitive C)}
    (hbody : Atomic body)
    (hinner : Atomic inner)
    (harg : Atomic arg)
    (hdist :
      MeasureDistinct realize
        (.app (.lam x body) (.app (.lam y inner) arg)))
    (hc : s.control =
      .term (.app (.lam x body) (.app (.lam y inner) arg)))
    (hs : s.stack = [])
    (hscoped : ChannelConfig.WellScoped s)
    (active : ℕ) :
    PathChannelEvaluation D₀ j₀ realize s active [] := by
  have ⟨hdistFn, hdistInnerApp⟩ := hdist
  have hdistBody : MeasureDistinct realize body := hdistFn
  have ⟨hdistInnerFn, hdistArg⟩ := hdistInnerApp
  have hdistInner : MeasureDistinct realize inner := hdistInnerFn
  refine PathChannelEvaluation.application hc ?_
  refine PathChannelEvaluation.lambda
    (s :=
      {s with
        control := .term (.lam x body)
        stack := .argument (.app (.lam y inner) arg) s.env :: s.stack})
    rfl ?_
  refine PathChannelEvaluation.evaluateArgument
    (s :=
      {s with
        control := .value (.closure x body s.env)
        stack := .argument (.app (.lam y inner) arg) s.env :: s.stack})
    rfl rfl ?_
  refine PathChannelEvaluation.application
    (s :=
      {s with
        control := .term (.app (.lam y inner) arg)
        stack := .function (.closure x body s.env) :: s.stack})
    rfl ?_
  refine PathChannelEvaluation.lambda
    (s :=
      {s with
        control := .term (.lam y inner)
        stack :=
          .argument arg s.env ::
            .function (.closure x body s.env) :: s.stack})
    rfl ?_
  refine PathChannelEvaluation.evaluateArgument
    (s :=
      {s with
        control := .value (.closure y inner s.env)
        stack :=
          .argument arg s.env ::
            .function (.closure x body s.env) :: s.stack})
    rfl rfl ?_
  exact atomic_under_two_closures_pathChannelEvaluation D₀ j₀ realize
    harg hdistArg hinner hdistInner hbody hdistBody rfl
    (by simp [hs])
    ((channelInternalStep_of_evaluateArgument
      (s :=
        {s with
          control := .value (.closure y inner s.env)
          stack :=
            .argument arg s.env ::
              .function (.closure x body s.env) :: s.stack})
      rfl rfl).preserve_wellScoped
      ((channelInternalStep_of_lambda
        (s :=
          {s with
            control := .term (.lam y inner)
            stack :=
              .argument arg s.env ::
                .function (.closure x body s.env) :: s.stack})
        rfl).preserve_wellScoped
        ((channelInternalStep_of_application
          (s :=
            {s with
              control := .term (.app (.lam y inner) arg)
              stack := .function (.closure x body s.env) :: s.stack})
          rfl).preserve_wellScoped
          ((channelInternalStep_of_evaluateArgument
            (s :=
              {s with
                control := .value (.closure x body s.env)
                stack :=
                  .argument (.app (.lam y inner) arg) s.env :: s.stack})
            rfl rfl).preserve_wellScoped
            ((channelInternalStep_of_lambda
              (s :=
                {s with
                  control := .term (.lam x body)
                  stack :=
                    .argument (.app (.lam y inner) arg) s.env ::
                      s.stack})
              rfl).preserve_wellScoped
              ((channelInternalStep_of_application hc).preserve_wellScoped
                hscoped))))))
    active

/-- A closed `Productive 0` program, or a closed `extern` with Atomic
children, has a branch-complete path evaluation at every heap
coordinate.  `Productive 0` includes leftover-arity spines and
intern-in-body. -/
theorem closed_productive_pathChannelEvaluation {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (hclosed : Closed code)
    (hprod : Productive 0 code ∨
      (∃ left right,
        code = .extern left right ∧ Atomic left ∧ Atomic right) ∨
      (∃ x y body inner arg,
        code = .app (.lam x body) (.app (.lam y inner) arg) ∧
          Atomic body ∧ Atomic inner ∧ Atomic arg))
    (hdist : MeasureDistinct realize code)
    (quantum : NormalizedDensity 2)
    (i : ℕ) :
    PathChannelEvaluation D₀ j₀ realize
      (initialChannelConfig code quantum) i [] := by
  have hscoped := initialChannelConfig_wellScoped hclosed quantum
  have hc := initialChannelConfig_control code quantum
  have hs := initialChannelConfig_stack code quantum
  rcases hprod with hP | hex | happ
  · exact productive_under_argument_frames_pathChannelEvaluation D₀ j₀
      realize hP hdist (frames := []) rfl (fun _ h => by cases h) hc
      (by simp [argumentStack, hs]) hscoped i
  · obtain ⟨left, right, rfl, hL, hR⟩ := hex
    exact extern_nil_pathChannelEvaluation D₀ j₀ realize hL hR hdist hc hs
      hscoped i
  · obtain ⟨x, y, body, inner, arg, rfl, hbody, hinner, harg⟩ := happ
    exact app_lam_app_nil_pathChannelEvaluation D₀ j₀ realize hbody
      hinner harg hdist hc hs hscoped i

/-- Channel-tree completeness for a closed productive program. -/
theorem closed_term_presented_channelTreeCompleteness_of_productive
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (hclosed : Closed code)
    (hprod : Productive 0 code ∨
      (∃ left right,
        code = .extern left right ∧ Atomic left ∧ Atomic right) ∨
      (∃ x y body inner arg,
        code = .app (.lam x body) (.app (.lam y inner) arg) ∧
          Atomic body ∧ Atomic inner ∧ Atomic arg))
    (hdist : MeasureDistinct realize code)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig code quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
  closed_term_presented_channelTreeCompleteness D₀ j₀ realize code hclosed
    quantum semanticEnv
    (fun i =>
      closed_productive_pathChannelEvaluation D₀ j₀ realize code hclosed
        hprod hdist quantum i)

/-- Token adequacy for a closed productive program. -/
theorem closed_term_presented_token_adequacy_of_productive {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (hclosed : Closed code)
    (hprod : Productive 0 code ∨
      (∃ left right,
        code = .extern left right ∧ Atomic left ∧ Atomic right) ∨
      (∃ x y body inner arg,
        code = .app (.lam x body) (.app (.lam y inner) arg) ∧
          Atomic body ∧ Atomic inner ∧ Atomic arg))
    (hdist : MeasureDistinct realize code)
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
  closed_term_presented_token_adequacy D₀ j₀ realize code hclosed quantum
    semanticEnv
    (fun i =>
      closed_productive_pathChannelEvaluation D₀ j₀ realize code hclosed
        hprod hdist quantum i)
    selectors ξ k hk i token

end HardwareChannelSemantics
end QLambda
