/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.HardwareObservation
import QLambda.Adequacy

/-!
# A logical relation for the hardware CEK machine

This file relates the classical part of the hardware machine to the recursive
value domain of the two-dimensional external-continuation model.  The
relation is parameterized by a realization of hardware payloads.  Concrete
density matrices are deliberately not erased into the denotational value
domain: their effects are represented by the physical primitive
interpretation.

No general token-adequacy claim is made here.
-/

namespace QLambda
namespace HardwareLogicalRelation

open Scott1972.ContinuousLattice
open HardwareOperational
open TTPhysicalPrimitives
open TTContinuation

abbrev QubitQ := TTExternalContinuationPower 2

variable (D₀ : QDomain.{0})
variable (j₀ : IsContinuousLatticeProjection D₀.carrier
  (QuantumFunctor (QModel QubitQ) D₀.carrier))

abbrev HSemanticValue :=
  SemanticValue QubitQ D₀ j₀

abbrev HSemanticComp :=
  SemanticComp QubitQ D₀ j₀

/-- Map every classical payload in a hardware primitive through its chosen
realization. -/
def realizePrimitive {C : Type} (realize : C → HSemanticValue D₀ j₀) :
    QubitPrimitive C → SemanticQubitPrimitive D₀ j₀
  | .ret c => .ret (realize c)
  | .pauliX c => .pauliX (realize c)
  | .measureZ c₀ c₁ => .measureZ (realize c₀) (realize c₁)

/-- The primitive interpretation used for hardware syntax. -/
noncomputable def hardwarePrimitive {C : Type}
    (realize : C → HSemanticValue D₀ j₀) :
    QubitPrimitive C → HSemanticComp D₀ j₀ :=
  fun p => semanticPrimitive D₀ j₀ (realizePrimitive D₀ j₀ realize p)

@[simp] theorem hardwarePrimitive_ret {C : Type}
    (realize : C → HSemanticValue D₀ j₀) (c : C) :
    hardwarePrimitive D₀ j₀ realize (.ret c) =
      taggedUnit (n := 2) (realize c) := by
  simp [hardwarePrimitive, realizePrimitive, semanticPrimitive]

@[simp] theorem hardwarePrimitive_pauliX {C : Type}
    (realize : C → HSemanticValue D₀ j₀) (c : C) :
    hardwarePrimitive D₀ j₀ realize (.pauliX c) =
      TTPhysicalEmbedding.taggedEmbed
        (FiniteInstrumentComp.ofOperation Qubit.pauliXOp (realize c)) := by
  rfl

@[simp] theorem hardwarePrimitive_measureZ {C : Type}
    (realize : C → HSemanticValue D₀ j₀) (c₀ c₁ : C) :
    hardwarePrimitive D₀ j₀ realize (.measureZ c₀ c₁) =
      TTPhysicalEmbedding.taggedEmbed
        (Qubit.measureZComp.map
          (fun b => if b then realize c₁ else realize c₀)) := by
  rfl

/-- A runtime value is related to the exact semantic value represented by
its payload or lexical closure.  Closure environments need only agree at
names which the finite runtime environment actually binds. -/
inductive ValueRel {C : Type} (realize : C → HSemanticValue D₀ j₀) :
    RuntimeValue C → HSemanticValue D₀ j₀ → Prop where
  | payload (c : C) :
      ValueRel realize (.payload c) (realize c)
  | closure (x : Name) (body : Term (QubitPrimitive C))
      (runtimeEnv : RuntimeEnv C)
      (semanticEnv : Env (HSemanticValue D₀ j₀))
      (henv : ∀ y v, RuntimeEnv.lookup y runtimeEnv = some v →
        ValueRel realize v (semanticEnv y)) :
      ValueRel realize (.closure x body runtimeEnv)
        (lambdaValue (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) x
          (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv)
  | recClosure (self arg : Name) (body : Term (QubitPrimitive C))
      (runtimeEnv : RuntimeEnv C)
      (semanticEnv : Env (HSemanticValue D₀ j₀))
      (henv : ∀ y v, RuntimeEnv.lookup y runtimeEnv = some v →
        ValueRel realize v (semanticEnv y)) :
      ValueRel realize (.recClosure self arg body runtimeEnv)
        (recLambdaValue (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) self arg
          (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv)

/-- Agreement of a finite runtime environment with a total semantic one. -/
def EnvRel {C : Type} (realize : C → HSemanticValue D₀ j₀)
    (runtimeEnv : RuntimeEnv C)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) : Prop :=
  ∀ x v, RuntimeEnv.lookup x runtimeEnv = some v →
    ValueRel D₀ j₀ realize v (semanticEnv x)

theorem env_lookup {C : Type} {realize : C → HSemanticValue D₀ j₀}
    {runtimeEnv : RuntimeEnv C} {semanticEnv : Env (HSemanticValue D₀ j₀)}
    (henv : EnvRel D₀ j₀ realize runtimeEnv semanticEnv)
    {x : Name} {v : RuntimeValue C}
    (hlookup : RuntimeEnv.lookup x runtimeEnv = some v) :
    ValueRel D₀ j₀ realize v (semanticEnv x) :=
  henv x v hlookup

theorem env_nil {C : Type} (realize : C → HSemanticValue D₀ j₀)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    EnvRel D₀ j₀ realize [] semanticEnv := by
  intro x v h
  simp [RuntimeEnv.lookup] at h

theorem env_bind {C : Type} {realize : C → HSemanticValue D₀ j₀}
    {runtimeEnv : RuntimeEnv C} {semanticEnv : Env (HSemanticValue D₀ j₀)}
    {x : Name} {v : RuntimeValue C} {d : HSemanticValue D₀ j₀}
    (henv : EnvRel D₀ j₀ realize runtimeEnv semanticEnv)
    (hv : ValueRel D₀ j₀ realize v d) :
    EnvRel D₀ j₀ realize (RuntimeEnv.bind x v runtimeEnv)
      (envUpdate (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
        x (semanticEnv, d)) := by
  intro y w hw
  by_cases hyx : y = x
  · subst y
    simp [RuntimeEnv.bind, RuntimeEnv.lookup] at hw
    cases hw
    simpa using hv
  · simp [RuntimeEnv.bind, RuntimeEnv.lookup, hyx] at hw
    rw [envUpdate_other hyx]
    exact henv y w hw

theorem payload_related {C : Type}
    (realize : C → HSemanticValue D₀ j₀) (c : C) :
    ValueRel D₀ j₀ realize (.payload c) (realize c) :=
  .payload c

theorem closure_created {C : Type}
    (realize : C → HSemanticValue D₀ j₀)
    (x : Name) (body : Term (QubitPrimitive C))
    (runtimeEnv : RuntimeEnv C)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (henv : EnvRel D₀ j₀ realize runtimeEnv semanticEnv) :
    ValueRel D₀ j₀ realize (.closure x body runtimeEnv)
      (lambdaValue (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) x
        (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv) :=
  .closure x body runtimeEnv semanticEnv henv

theorem recClosure_created {C : Type}
    (realize : C → HSemanticValue D₀ j₀)
    (self arg : Name) (body : Term (QubitPrimitive C))
    (runtimeEnv : RuntimeEnv C)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (henv : EnvRel D₀ j₀ realize runtimeEnv semanticEnv) :
    ValueRel D₀ j₀ realize (.recClosure self arg body runtimeEnv)
      (recLambdaValue (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) self arg
        (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv) :=
  .recClosure self arg body runtimeEnv semanticEnv henv

theorem closure_beta_env {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {x : Name}
    {runtimeEnv : RuntimeEnv C}
    {semanticEnv : Env (HSemanticValue D₀ j₀)}
    {arg : RuntimeValue C} {d : HSemanticValue D₀ j₀}
    (henv : EnvRel D₀ j₀ realize runtimeEnv semanticEnv)
    (harg : ValueRel D₀ j₀ realize arg d) :
    EnvRel D₀ j₀ realize (RuntimeEnv.bind x arg runtimeEnv)
      (envUpdate (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
        x (semanticEnv, d)) := by
  exact env_bind D₀ j₀ henv harg

theorem recClosure_unfold_env {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {self arg : Name} {body : Term (QubitPrimitive C)}
    {runtimeEnv : RuntimeEnv C}
    {semanticEnv : Env (HSemanticValue D₀ j₀)}
    {value : RuntimeValue C} {d : HSemanticValue D₀ j₀}
    (henv : EnvRel D₀ j₀ realize runtimeEnv semanticEnv)
    (hvalue : ValueRel D₀ j₀ realize value d) :
    EnvRel D₀ j₀ realize
      (RuntimeEnv.bind arg value
        (RuntimeEnv.bind self (.recClosure self arg body runtimeEnv)
          runtimeEnv))
      (envUpdate (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) arg
        (envUpdate (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) self
          (semanticEnv,
            recLambdaValue (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
              self arg (interp (hardwarePrimitive D₀ j₀ realize) body)
              semanticEnv),
          d)) := by
  exact env_bind D₀ j₀
    (env_bind D₀ j₀ henv
      (ValueRel.recClosure self arg body runtimeEnv semanticEnv henv))
    hvalue

/-- A stack relation presents a hardware stack as an exact semantic
continuation on computations. -/
inductive StackRel {C : Type} (realize : C → HSemanticValue D₀ j₀) :
    EvalStack C → (HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀) → Prop where
  | nil :
      StackRel realize [] id
  | argument (arg : Term (QubitPrimitive C))
      (runtimeEnv : RuntimeEnv C)
      (semanticEnv : Env (HSemanticValue D₀ j₀))
      (rest : EvalStack C)
      (k : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀)
      (henv : EnvRel D₀ j₀ realize runtimeEnv semanticEnv)
      (hrest : StackRel realize rest k) :
      StackRel realize (.argument arg runtimeEnv :: rest)
        (fun mf => k
          (semanticBind (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
            (applyContinuation (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
              (interp (hardwarePrimitive D₀ j₀ realize) arg) semanticEnv)
            mf))
  | function (fn : RuntimeValue C) (f : HSemanticValue D₀ j₀)
      (rest : EvalStack C)
      (k : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀)
      (hfn : ValueRel D₀ j₀ realize fn f)
      (hrest : StackRel realize rest k) :
      StackRel realize (.function fn :: rest)
        (fun ma => k
          (semanticBind (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
            (semanticUnfold (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) f) ma))

theorem stack_nil {C : Type}
    (realize : C → HSemanticValue D₀ j₀) :
    StackRel D₀ j₀ realize [] id :=
  .nil

theorem stack_push_argument {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {arg : Term (QubitPrimitive C)} {runtimeEnv : RuntimeEnv C}
    {semanticEnv : Env (HSemanticValue D₀ j₀)}
    {rest : EvalStack C}
    {k : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀}
    (henv : EnvRel D₀ j₀ realize runtimeEnv semanticEnv)
    (hrest : StackRel D₀ j₀ realize rest k) :
    StackRel D₀ j₀ realize (.argument arg runtimeEnv :: rest)
      (fun mf => k
        (semanticBind (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
          (applyContinuation (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
            (interp (hardwarePrimitive D₀ j₀ realize) arg) semanticEnv)
          mf)) :=
  .argument arg runtimeEnv semanticEnv rest k henv hrest

theorem stack_argument_to_function {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {fn : RuntimeValue C} {f : HSemanticValue D₀ j₀}
    {rest : EvalStack C}
    {k : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀}
    (hfn : ValueRel D₀ j₀ realize fn f)
    (hrest : StackRel D₀ j₀ realize rest k) :
    StackRel D₀ j₀ realize (.function fn :: rest)
      (fun ma => k
        (semanticBind (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
          (semanticUnfold (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) f) ma)) :=
  .function fn f rest k hfn hrest

/-- Relation for CEK control.  A term is interpreted in a related
environment; a returned runtime value is lifted by semantic unit. -/
inductive ControlRel {C : Type} (realize : C → HSemanticValue D₀ j₀) :
    Control C → RuntimeEnv C → HSemanticComp D₀ j₀ → Prop where
  | term (code : Term (QubitPrimitive C))
      (runtimeEnv : RuntimeEnv C)
      (semanticEnv : Env (HSemanticValue D₀ j₀))
      (henv : EnvRel D₀ j₀ realize runtimeEnv semanticEnv) :
      ControlRel realize (.term code) runtimeEnv
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv)
  | value (result : RuntimeValue C) (d : HSemanticValue D₀ j₀)
      (runtimeEnv : RuntimeEnv C)
      (hvalue : ValueRel D₀ j₀ realize result d) :
      ControlRel realize (.value result) runtimeEnv
        (semanticUnit (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) d)

/-- The classical CEK components denote a computation after applying their
related stack continuation.  The concrete quantum field is intentionally
left to the physical primitive semantics. -/
def ConfigRel {C : Type} (realize : C → HSemanticValue D₀ j₀)
    (s : Config C) (answer : HSemanticComp D₀ j₀) : Prop :=
  ∃ current k,
    ControlRel D₀ j₀ realize s.control s.env current ∧
    StackRel D₀ j₀ realize s.stack k ∧
    answer = k current

/-- A closed program in an empty CEK environment represents its compositional
interpreter denotation, independently of the concrete initial density. -/
theorem initialConfig_related {C : Type}
    (realize : C → HSemanticValue D₀ j₀)
    (code : Term (QubitPrimitive C))
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    ConfigRel D₀ j₀ realize (initialConfig code quantum)
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) := by
  refine ⟨interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv,
    id, ?_, StackRel.nil, rfl⟩
  exact ControlRel.term code [] semanticEnv (env_nil D₀ j₀ realize semanticEnv)

/-- At a terminal configuration the logical relation has no residual stack:
the represented computation is exactly the tagged return of a value related
to the runtime result.  This is the leaf invariant used by tree soundness. -/
theorem terminal_config_related {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {s : Config C} (hterminal : HardwareObservation.Terminal s)
    {answer : HSemanticComp D₀ j₀}
    (hrel : ConfigRel D₀ j₀ realize s answer) :
    ∃ d : HSemanticValue D₀ j₀,
      ValueRel D₀ j₀ realize hterminal.value d ∧
      answer =
        semanticUnit (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) d := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  have hcontrolEq : s.control = .value hterminal.value :=
    hterminal.control_eq
  have hstackEq : s.stack = [] := hterminal.stack_eq
  rw [hcontrolEq] at hcontrol
  rw [hstackEq] at hstack
  cases hcontrol with
  | value _ d _ hvalue =>
      cases hstack
      exact ⟨d, hvalue, rfl⟩

theorem control_returnPrimitive {C : Type}
    (realize : C → HSemanticValue D₀ j₀) (c : C)
    (runtimeEnv : RuntimeEnv C)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (henv : EnvRel D₀ j₀ realize runtimeEnv semanticEnv) :
    ControlRel D₀ j₀ realize (.term (.prim (.ret c))) runtimeEnv
      (taggedUnit (n := 2) (realize c)) := by
  rw [← hardwarePrimitive_ret D₀ j₀ realize c]
  exact .term _ runtimeEnv semanticEnv henv

theorem control_pauliXPrimitive {C : Type}
    (realize : C → HSemanticValue D₀ j₀) (c : C)
    (runtimeEnv : RuntimeEnv C)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (henv : EnvRel D₀ j₀ realize runtimeEnv semanticEnv) :
    ControlRel D₀ j₀ realize (.term (.prim (.pauliX c))) runtimeEnv
      (TTPhysicalEmbedding.taggedEmbed
        (FiniteInstrumentComp.ofOperation Qubit.pauliXOp (realize c))) := by
  rw [← hardwarePrimitive_pauliX D₀ j₀ realize c]
  exact .term _ runtimeEnv semanticEnv henv

theorem control_measureZPrimitive {C : Type}
    (realize : C → HSemanticValue D₀ j₀) (c₀ c₁ : C)
    (runtimeEnv : RuntimeEnv C)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (henv : EnvRel D₀ j₀ realize runtimeEnv semanticEnv) :
    ControlRel D₀ j₀ realize (.term (.prim (.measureZ c₀ c₁))) runtimeEnv
      (TTPhysicalEmbedding.taggedEmbed
        (Qubit.measureZComp.map
          (fun b => if b then realize c₁ else realize c₀))) := by
  rw [← hardwarePrimitive_measureZ D₀ j₀ realize c₀ c₁]
  exact .term _ runtimeEnv semanticEnv henv

theorem control_application {C : Type}
    (realize : C → HSemanticValue D₀ j₀)
    (fn arg : Term (QubitPrimitive C))
    (runtimeEnv : RuntimeEnv C)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (henv : EnvRel D₀ j₀ realize runtimeEnv semanticEnv) :
    ControlRel D₀ j₀ realize (.term (.app fn arg)) runtimeEnv
      (applyComp (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
        (interp (hardwarePrimitive D₀ j₀ realize) fn)
        (interp (hardwarePrimitive D₀ j₀ realize) arg) semanticEnv) :=
  .term _ runtimeEnv semanticEnv henv

/-- Denotational compatibility of closure application with the environment
installed by the hardware `beta` transition. -/
theorem closure_application {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    (x : Name) (body : Term (QubitPrimitive C))
    (runtimeEnv : RuntimeEnv C)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (arg : RuntimeValue C) (d : HSemanticValue D₀ j₀)
    (_henv : EnvRel D₀ j₀ realize runtimeEnv semanticEnv)
    (_harg : ValueRel D₀ j₀ realize arg d) :
    applyComp (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
        ((semanticUnit (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)).comp
          (lambdaValue (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) x
            (interp (hardwarePrimitive D₀ j₀ realize) body)))
        ((semanticUnit (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)).comp
          (ScottMap.const d))
        semanticEnv =
      interp (hardwarePrimitive D₀ j₀ realize) body
        (envUpdate (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
          x (semanticEnv, d)) := by
  exact applyComp_pure_lambda
    (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
    x (interp (hardwarePrimitive D₀ j₀ realize) body)
    (ScottMap.const d) semanticEnv

/-- Denotational compatibility of recursive closure application with the
self-then-argument environment installed by `recBeta`. -/
theorem recClosure_application {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    (self arg : Name) (body : Term (QubitPrimitive C))
    (runtimeEnv : RuntimeEnv C)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (value : RuntimeValue C) (d : HSemanticValue D₀ j₀)
    (_henv : EnvRel D₀ j₀ realize runtimeEnv semanticEnv)
    (_hvalue : ValueRel D₀ j₀ realize value d) :
    applyComp (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
        ((semanticUnit (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)).comp
          (recLambdaValue (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
            self arg (interp (hardwarePrimitive D₀ j₀ realize) body)))
        ((semanticUnit (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)).comp
          (ScottMap.const d))
        semanticEnv =
      interp (hardwarePrimitive D₀ j₀ realize) body
        (envUpdate (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) arg
          (envUpdate (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) self
            (semanticEnv,
              recLambdaValue (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
                self arg (interp (hardwarePrimitive D₀ j₀ realize) body)
                semanticEnv),
            d)) := by
  exact applyComp_pure_recLambda
    (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
    self arg (interp (hardwarePrimitive D₀ j₀ realize) body)
    (ScottMap.const d) semanticEnv

/-- Pushing an argument frame is exactly the decomposition of compositional
application under any already-related remainder continuation. -/
theorem application_under_stack {C : Type}
    (realize : C → HSemanticValue D₀ j₀)
    (fn arg : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (k : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀) :
    k (interp (hardwarePrimitive D₀ j₀ realize) (.app fn arg) semanticEnv) =
      k (semanticBind (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
        (applyContinuation (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
          (interp (hardwarePrimitive D₀ j₀ realize) arg) semanticEnv)
        (interp (hardwarePrimitive D₀ j₀ realize) fn semanticEnv)) :=
  rfl

/-- Once the function control has returned a related value, the hardware
`evaluateArgument` frame change is justified by the monad left-unit law. -/
theorem evaluateArgument_under_stack {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    (arg : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (f : HSemanticValue D₀ j₀)
    (k : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀) :
    k (semanticBind (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
        (applyContinuation (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
          (interp (hardwarePrimitive D₀ j₀ realize) arg) semanticEnv)
        (semanticUnit (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) f)) =
      k (semanticBind (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
        (semanticUnfold (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) f)
        (interp (hardwarePrimitive D₀ j₀ realize) arg semanticEnv)) := by
  apply congrArg k
  have h := congrArg
    (fun g : ScottMap (HSemanticValue D₀ j₀) (HSemanticComp D₀ j₀) => g f)
    (IsQuantumMonad.unit_bind (Q := QubitQ)
      (applyContinuation (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
        (interp (hardwarePrimitive D₀ j₀ realize) arg) semanticEnv))
  rw [ScottMap.comp_apply] at h
  simpa using h

/-! ## Choice-transition compatibility -/

/-- Either hardware scheduler step from an internal choice refines the
denotation of the unresolved choice. -/
theorem internal_left_le {C : Type}
    (realize : C → HSemanticValue D₀ j₀)
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv ≤
      interp (hardwarePrimitive D₀ j₀ realize)
        (.intern left right) semanticEnv :=
  interp_le_intern_left
    (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
    (hardwarePrimitive D₀ j₀ realize) left right semanticEnv

theorem internal_right_le {C : Type}
    (realize : C → HSemanticValue D₀ j₀)
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv ≤
      interp (hardwarePrimitive D₀ j₀ realize)
        (.intern left right) semanticEnv :=
  interp_le_intern_right
    (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
    (hardwarePrimitive D₀ j₀ realize) left right semanticEnv

/-- A source-probability hardware branch retains its declared physical
weight in the concrete TT weighted-branch relation. -/
theorem probability_left_weighted {C : Type}
    (realize : C → HSemanticValue D₀ j₀)
    (p : Prob) (left right : Term (QubitPrimitive C))
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    HasWeightedBranchSemantics.weightedBranch
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.prob p left right) semanticEnv)
      p
      (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv) :=
  interp_prob_left_weighted
    (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
    (hardwarePrimitive D₀ j₀ realize) p left right hp₀ hp₁ semanticEnv

theorem probability_right_weighted {C : Type}
    (realize : C → HSemanticValue D₀ j₀)
    (p : Prob) (left right : Term (QubitPrimitive C))
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    HasWeightedBranchSemantics.weightedBranch
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.prob p left right) semanticEnv)
      (1 - p)
      (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv) :=
  interp_prob_right_weighted
    (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
    (hardwarePrimitive D₀ j₀ realize) p left right hp₀ hp₁ semanticEnv

/-- Resolving an external hardware branch is exactly Boolean selection in the
tagged TT model. -/
theorem external_select {C : Type}
    (realize : C → HSemanticValue D₀ j₀)
    (selected : Bool) (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    HasExternalSelection.select selected
        (interp (hardwarePrimitive D₀ j₀ realize)
          (.extern left right) semanticEnv) =
      interp (hardwarePrimitive D₀ j₀ realize)
        (if selected then right else left) semanticEnv := by
  cases selected
  · exact interp_external_step_select
      (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
      (hardwarePrimitive D₀ j₀ realize)
      (ExternalStep.left left right) semanticEnv
  · exact interp_external_step_select
      (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
      (hardwarePrimitive D₀ j₀ realize)
      (ExternalStep.right left right) semanticEnv

/-! ## Configuration-level one-step compatibility -/

/-- Runtime variable lookup preserves the exact computation represented by a
related configuration. -/
theorem config_variable {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {s : Config C} {x : Name} {v : RuntimeValue C}
    (hlookup : RuntimeEnv.lookup x s.env = some v)
    {answer : HSemanticComp D₀ j₀}
    (hrel : ConfigRel D₀ j₀ realize
      {s with control := .term (.var x)} answer) :
    ConfigRel D₀ j₀ realize
      {s with control := .value v} answer := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨semanticUnit (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
        (semanticEnv x), k, ?_, hstack, ?_⟩
      · exact ControlRel.value v (semanticEnv x) s.env
          (env_lookup D₀ j₀ henv hlookup)
      · simp

/-- Lambda creation preserves the exact represented computation. -/
theorem config_lambda {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {s : Config C} {x : Name} {body : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hrel : ConfigRel D₀ j₀ realize
      {s with control := .term (.lam x body)} answer) :
    ConfigRel D₀ j₀ realize
      {s with control := .value (.closure x body s.env)} answer := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨semanticUnit (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
        (lambdaValue (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) x
          (interp (hardwarePrimitive D₀ j₀ realize) body) semanticEnv),
        k, ?_, hstack, ?_⟩
      · exact ControlRel.value _ _ s.env
          (closure_created D₀ j₀ realize x body s.env semanticEnv henv)
      · simp

/-- Recursive-closure creation preserves the exact represented computation. -/
theorem config_recursive {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {s : Config C} {self arg : Name}
    {body : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hrel : ConfigRel D₀ j₀ realize
      {s with control := .term (.recLam self arg body)} answer) :
    ConfigRel D₀ j₀ realize
      {s with control :=
        .value (.recClosure self arg body s.env)} answer := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨semanticUnit (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
        (recLambdaValue (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
          self arg (interp (hardwarePrimitive D₀ j₀ realize) body)
          semanticEnv), k, ?_, hstack, ?_⟩
      · exact ControlRel.value _ _ s.env
          (recClosure_created D₀ j₀ realize self arg body
            s.env semanticEnv henv)
      · simp

/-- Pushing an application argument frame preserves the exact represented
computation. -/
theorem config_application {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {s : Config C} {fn arg : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hrel : ConfigRel D₀ j₀ realize
      {s with control := .term (.app fn arg)} answer) :
    ConfigRel D₀ j₀ realize
      {s with control := .term fn,
              stack := .argument arg s.env :: s.stack} answer := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨interp (hardwarePrimitive D₀ j₀ realize) fn semanticEnv,
        (fun mf => k
          (semanticBind (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
            (applyContinuation (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
              (interp (hardwarePrimitive D₀ j₀ realize) arg) semanticEnv)
            mf)), ?_, ?_, ?_⟩
      · exact ControlRel.term fn s.env semanticEnv henv
      · exact stack_push_argument D₀ j₀ henv hstack
      · exact (application_under_stack D₀ j₀ realize
          fn arg semanticEnv k).symm

/-- Replacing an argument frame by a function frame preserves the exact
represented computation. -/
theorem config_evaluateArgument {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {s : Config C} {fn : RuntimeValue C}
    {arg : Term (QubitPrimitive C)} {callEnv : RuntimeEnv C}
    {rest : EvalStack C} {answer : HSemanticComp D₀ j₀}
    (hrel : ConfigRel D₀ j₀ realize
      {s with control := .value fn,
              stack := .argument arg callEnv :: rest} answer) :
    ConfigRel D₀ j₀ realize
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
              (semanticBind (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
                (semanticUnfold (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) f)
                ma)), ?_, ?_, ?_⟩
          · exact ControlRel.term arg callEnv semanticEnv henv
          · exact stack_argument_to_function D₀ j₀ hfn hrest
          · exact (evaluateArgument_under_stack D₀ j₀
              arg semanticEnv f k).symm

/-- Closure β-reduction preserves the exact represented computation. -/
theorem config_beta {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {s : Config C} {x : Name} {body : Term (QubitPrimitive C)}
    {closureEnv : RuntimeEnv C} {arg : RuntimeValue C}
    {rest : EvalStack C} {answer : HSemanticComp D₀ j₀}
    (hrel : ConfigRel D₀ j₀ realize
      {s with control := .value arg,
              stack := .function (.closure x body closureEnv) :: rest}
      answer) :
    ConfigRel D₀ j₀ realize
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
                (envUpdate (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
                  x (semanticEnv, d)), k, ?_, hrest, ?_⟩
              · exact ControlRel.term body _ _
                  (closure_beta_env D₀ j₀ henv harg)
              · exact congrArg k (closure_application D₀ j₀
                  x body closureEnv semanticEnv arg d henv harg)

/-- Recursive-closure β-reduction preserves the exact represented
computation. -/
theorem config_recBeta {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {s : Config C} {self x : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    {arg : RuntimeValue C} {rest : EvalStack C}
    {answer : HSemanticComp D₀ j₀}
    (hrel : ConfigRel D₀ j₀ realize
      {s with control := .value arg,
              stack :=
                .function (.recClosure self x body closureEnv) :: rest}
      answer) :
    ConfigRel D₀ j₀ realize
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
                (envUpdate (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) x
                  (envUpdate (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) self
                    (semanticEnv,
                      recLambdaValue (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
                        self x
                        (interp (hardwarePrimitive D₀ j₀ realize) body)
                        semanticEnv),
                    d)), k, ?_, hrest, ?_⟩
              · exact ControlRel.term body _ _
                  (recClosure_unfold_env D₀ j₀ henv harg)
              · exact congrArg k (recClosure_application D₀ j₀
                  self x body closureEnv semanticEnv arg d henv harg)

/-- A classical return primitive preserves the exact represented computation;
unlike Pauli-X and measurement, it performs no physical operation. -/
theorem config_returnPrimitive {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {s : Config C} {value : C}
    {answer : HSemanticComp D₀ j₀}
    (hrel : ConfigRel D₀ j₀ realize
      {s with control := .term (.prim (.ret value))} answer) :
    ConfigRel D₀ j₀ realize
      {s with control := .value (.payload value)} answer := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨semanticUnit (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
        (realize value), k, ?_, hstack, ?_⟩
      · exact ControlRel.value _ _ s.env (.payload value)
      · congr 1
        rw [interp_prim_apply, hardwarePrimitive_ret]
        change
          TTContinuation.taggedUnit (n := 2) (realize value) =
            TTContinuation.taggedUnit (n := 2) (realize value)
        rfl

/-- Every continuation represented by a hardware stack is monotone. -/
theorem stack_monotone {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {stack : EvalStack C}
    {k : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀}
    (hstack : StackRel D₀ j₀ realize stack k) :
    Monotone k := by
  induction hstack with
  | nil => exact monotone_id
  | argument arg runtimeEnv semanticEnv rest k henv hrest ih =>
      intro a b hab
      apply ih
      exact
        (semanticBind (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
          (applyContinuation (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
            (interp (hardwarePrimitive D₀ j₀ realize) arg) semanticEnv)).monotone
          hab
  | function fn f rest k hfn hrest ih =>
      intro a b hab
      apply ih
      exact
        (semanticBind (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
          (semanticUnfold (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) f)).monotone
          hab

/-- Internal-left scheduling produces a related target whose denotation
refines that of the unresolved source, through every related stack. -/
theorem config_internalLeft {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {s : Config C} {left right : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hrel : ConfigRel D₀ j₀ realize
      {s with control := .term (.intern left right)} answer) :
    ∃ targetAnswer,
      ConfigRel D₀ j₀ realize
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

/-- Internal-right scheduling produces a related target whose denotation
refines that of the unresolved source, through every related stack. -/
theorem config_internalRight {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {s : Config C} {left right : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hrel : ConfigRel D₀ j₀ realize
      {s with control := .term (.intern left right)} answer) :
    ∃ targetAnswer,
      ConfigRel D₀ j₀ realize
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

/-- The concrete tagged weighted-branch relation is closed under every
continuation generated by a related CEK stack. -/
theorem stack_weightedBranch {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {stack : EvalStack C}
    {k : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀}
    (hstack : StackRel D₀ j₀ realize stack k)
    {source target : HSemanticComp D₀ j₀} {p : Prob}
    (hbranch : HasWeightedBranchSemantics.weightedBranch source p target) :
    HasWeightedBranchSemantics.weightedBranch (k source) p (k target) := by
  induction hstack generalizing source target p with
  | nil => simpa using hbranch
  | argument arg runtimeEnv semanticEnv rest k henv hrest ih =>
      exact ih
        (TTContinuation.TaggedWeightedBranch.bindLeft hbranch
          (applyContinuation (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
            (interp (hardwarePrimitive D₀ j₀ realize) arg) semanticEnv))
  | function fn f rest k hfn hrest ih =>
      exact ih
        (TTContinuation.TaggedWeightedBranch.bindLeft hbranch
          (semanticUnfold (Q := QubitQ) (D₀ := D₀) (j₀ := j₀) f))

/-- A left source-probability transition retains its declared weight through
every related CEK stack. -/
theorem config_probabilityLeft {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {s : Config C} {p : Prob}
    {left right : Term (QubitPrimitive C)}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {answer : HSemanticComp D₀ j₀}
    (hrel : ConfigRel D₀ j₀ realize
      {s with control := .term (.prob p left right)} answer) :
    ∃ targetAnswer,
      ConfigRel D₀ j₀ realize
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

/-- A right source-probability transition retains weight `1-p` through every
related CEK stack. -/
theorem config_probabilityRight {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {s : Config C} {p : Prob}
    {left right : Term (QubitPrimitive C)}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {answer : HSemanticComp D₀ j₀}
    (hrel : ConfigRel D₀ j₀ realize
      {s with control := .term (.prob p left right)} answer) :
    ∃ targetAnswer,
      ConfigRel D₀ j₀ realize
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

/-- A selector may be transported through a related stack exactly when the
model's selector commutes with that stack continuation.  This hypothesis is
explicit because top-level external-selection laws do not imply sequencing
closure. -/
theorem config_externalSelect {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {s : Config C} {selected : Bool}
    {left right : Term (QubitPrimitive C)}
    (hcommute :
      ∀ current k,
        StackRel D₀ j₀ realize s.stack k →
        HasExternalSelection.select selected (k current) =
          k (HasExternalSelection.select selected current))
    {answer : HSemanticComp D₀ j₀}
    (hrel : ConfigRel D₀ j₀ realize
      {s with control := .term (.extern left right)} answer) :
    ConfigRel D₀ j₀ realize
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

/-- External selection is unconditionally exact at an empty stack. -/
theorem config_externalSelect_nil {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {s : Config C} (hstack : s.stack = [])
    {selected : Bool} {left right : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hrel : ConfigRel D₀ j₀ realize
      {s with control := .term (.extern left right)} answer) :
    ConfigRel D₀ j₀ realize
      {s with control := .term (if selected then right else left)}
      (HasExternalSelection.select selected answer) := by
  apply config_externalSelect D₀ j₀ (s := s)
  intro current k hk
  rw [hstack] at hk
  cases hk
  rfl
  exact hrel

/-! ## Operation-aware primitive transitions -/

/-- Pauli-X relates the source to the embedded physical operation and the
target to the pure payload return; these computations are deliberately not
equated.  The final conjunct records the exact concrete state update. -/
theorem config_pauliXPrimitive_operation {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {s : Config C} {value : C}
    {answer : HSemanticComp D₀ j₀}
    (hrel : ConfigRel D₀ j₀ realize
      {s with control := .term (.prim (.pauliX value))} answer) :
    ∃ (targetAnswer : HSemanticComp D₀ j₀)
      (k : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀),
      ConfigRel D₀ j₀ realize
        {s with control := .value (.payload value),
                quantum := NormalizedDensity.pauliX s.quantum}
        targetAnswer ∧
      answer =
        k (TTPhysicalEmbedding.taggedEmbed
          (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
            (realize value))) ∧
      targetAnswer =
        k (semanticUnit (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
          (realize value)) ∧
      KrausFamily.applyMat Qubit.pauliXOp.kraus s.quantum.mat =
        (NormalizedDensity.pauliX s.quantum).mat := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨k (semanticUnit (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
          (realize value)), k, ?_, ?_, rfl, rfl⟩
      · exact ⟨_, k,
          ControlRel.value _ _ s.env (.payload value), hstack, rfl⟩
      · simp only [interp_prim_apply, hardwarePrimitive_pauliX]

/-- A nonzero measurement branch keeps the source as the complete embedded
measurement instrument, relates the selected target payload separately, and
records the exact unnormalized Born branch of the concrete density matrix. -/
theorem config_measureZPrimitive_operation {C : Type}
    {realize : C → HSemanticValue D₀ j₀}
    {s : Config C} {zeroValue oneValue : C} {b : Bool}
    (hpositive : 0 < measureProbability s b)
    {answer : HSemanticComp D₀ j₀}
    (hrel : ConfigRel D₀ j₀ realize
      ({ control := .term (.prim (.measureZ zeroValue oneValue)),
         env := s.env, stack := s.stack, quantum := s.quantum } : Config C)
      answer) :
    ∃ (targetAnswer : HSemanticComp D₀ j₀)
      (k : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀),
      ConfigRel D₀ j₀ realize
        ({ control :=
             .value (.payload (if b then oneValue else zeroValue)),
           env := s.env, stack := s.stack,
           quantum := measuredState s b hpositive } : Config C)
        targetAnswer ∧
      answer =
        k (TTPhysicalEmbedding.taggedEmbed
          (Qubit.measureZComp.map
            (fun outcome =>
              if outcome then realize oneValue else realize zeroValue))) ∧
      targetAnswer =
        k (semanticUnit (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
          (realize (if b then oneValue else zeroValue))) ∧
      KrausFamily.applyMat (measureBranch b) s.quantum.mat =
        (measureProbability s b : ℂ) •
          (measuredState s b hpositive).mat := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      refine ⟨k (semanticUnit (Q := QubitQ) (D₀ := D₀) (j₀ := j₀)
          (realize (if b then oneValue else zeroValue))), k, ?_, ?_,
        rfl, ?_⟩
      · exact ⟨_, k,
          ControlRel.value _ _ s.env
            (.payload (if b then oneValue else zeroValue)),
          hstack, rfl⟩
      · simp only [interp_prim_apply, hardwarePrimitive_measureZ]
      · simpa [HardwareObservation.QuantumAction.kraus] using
          (HardwareObservation.QuantumAction.apply_measurement
            s b hpositive)

end HardwareLogicalRelation
end QLambda
