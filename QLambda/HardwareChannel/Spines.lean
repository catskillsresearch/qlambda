/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.HardwareChannel.Identity

/-!
# Fragment predicates and residual stack spines

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

/-- Application-free terms: the closed lambda-and-choice fragment. -/
def NoApp {Prim : Type} : Term Prim → Prop
  | .app _ _ => False
  | .lam _ M => NoApp M
  | .recLam _ _ M => NoApp M
  | .prob _ M N => NoApp M ∧ NoApp N
  | .intern M N => NoApp M ∧ NoApp N
  | .extern M N => NoApp M ∧ NoApp N
  | .var _ => True
  | .prim _ => True

/-- Application-free terms that evaluate by identity CEK steps, intern,
probability, and Pauli-X.  Measurement and extern change the physical
tree shape under a residual stack and are excluded here. -/
def AdminNoApp {C : Type} : Term (QubitPrimitive C) → Prop
  | .app _ _ => False
  | .extern _ _ => False
  | .prob _ M N => AdminNoApp M ∧ AdminNoApp N
  | .intern M N => AdminNoApp M ∧ AdminNoApp N
  | .var _ => True
  | .lam _ _ => True
  | .recLam _ _ _ => True
  | .prim (.ret _) => True
  | .prim (.pauliX _) => True
  | .prim (.measureZ _ _) => False

/-- Body-nested and argument-nested lambda / recursive-lambda
applications. Stuck `app (ret c) M` is excluded: the function must be
a syntactic lambda or recursive lambda. Left-nested `app (app …) …`
is covered by `Produces`. -/
inductive FunAppFrag {C : Type} : Term (QubitPrimitive C) → Prop
  | admin {t : Term (QubitPrimitive C)} :
      AdminNoApp t → FunAppFrag t
  | app_lam {x : Name} {body arg : Term (QubitPrimitive C)} :
      FunAppFrag body →
      FunAppFrag arg →
      FunAppFrag (.app (.lam x body) arg)
  | app_recLam {self x : Name} {body arg : Term (QubitPrimitive C)} :
      FunAppFrag body →
      FunAppFrag arg →
      FunAppFrag (.app (.recLam self x body) arg)

/-- Terms that absorb exactly `n` leftover argument frames without
getting stuck. `Produces 0` is FunAppFrag. A lambda or recursive
lambda raises the arity; an application consumes one arity if the
argument is in the FunAppFrag fragment (including admin NoApp). -/
inductive Produces {C : Type} : Nat → Term (QubitPrimitive C) → Prop
  | frag {t : Term (QubitPrimitive C)} :
      FunAppFrag t → Produces 0 t
  | lam {n : Nat} {x : Name} {body : Term (QubitPrimitive C)} :
      Produces n body → Produces (n + 1) (.lam x body)
  | recLam {n : Nat} {self x : Name} {body : Term (QubitPrimitive C)} :
      Produces n body → Produces (n + 1) (.recLam self x body)
  | app {n : Nat} {fn arg : Term (QubitPrimitive C)} :
      Produces (n + 1) fn →
      FunAppFrag arg →
      Produces n (.app fn arg)

/-- After beta, a body may sit under `n` leftover argument frames.
Zero leftovers require an application-free body; each extra leftover
requires another lambda. -/
def BodyUnderArgs {C : Type} : Nat → Term (QubitPrimitive C) → Prop
  | 0, t => NoApp t
  | n + 1, t =>
      match t with
      | .lam _ b => BodyUnderArgs n b
      | _ => False

/-- A lambda `lam x body` can absorb `n` leftover argument frames:
none means the closure is a value; otherwise the body sits under
`n - 1` leftovers. -/
def LamAbsorbs {C : Type} : Nat → Term (QubitPrimitive C) → Prop
  | 0, _ => True
  | n + 1, body => BodyUnderArgs n body

@[simp]
theorem BodyUnderArgs_zero {C : Type} {t : Term (QubitPrimitive C)} :
    BodyUnderArgs 0 t ↔ NoApp t :=
  Iff.rfl

@[simp]
theorem BodyUnderArgs_succ_lam {C : Type} {n : Nat} {x : Name}
    {b : Term (QubitPrimitive C)} :
    BodyUnderArgs (n + 1) (.lam x b) ↔ BodyUnderArgs n b :=
  Iff.rfl

theorem BodyUnderArgs_succ_inv {C : Type} {n : Nat}
    {t : Term (QubitPrimitive C)}
    (h : BodyUnderArgs (n + 1) t) :
    ∃ x b, t = .lam x b ∧ BodyUnderArgs n b := by
  cases t with
  | lam x b => exact ⟨x, b, rfl, h⟩
  | app _ _ => cases h
  | var _ => cases h
  | recLam _ _ _ => cases h
  | intern _ _ => cases h
  | extern _ _ => cases h
  | prob _ _ _ => cases h
  | prim _ => cases h

@[simp]
theorem LamAbsorbs_zero {C : Type} {body : Term (QubitPrimitive C)} :
    LamAbsorbs 0 body ↔ True :=
  Iff.rfl

@[simp]
theorem LamAbsorbs_succ {C : Type} {n : Nat}
    {body : Term (QubitPrimitive C)} :
    LamAbsorbs (n + 1) body ↔ BodyUnderArgs n body :=
  Iff.rfl

/-- Residual argument frames waiting after a curried application. -/
def argumentStack {C : Type}
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C)) :
    EvalStack C :=
  frames.map fun p => .argument p.1 p.2

@[simp]
theorem argumentStack_nil {C : Type} :
    argumentStack ([] : List (Term (QubitPrimitive C) × RuntimeEnv C)) =
      [] :=
  rfl

@[simp]
theorem argumentStack_cons {C : Type}
    (arg : Term (QubitPrimitive C)) (callEnv : RuntimeEnv C)
    (rest : List (Term (QubitPrimitive C) × RuntimeEnv C)) :
    argumentStack ((arg, callEnv) :: rest) =
      .argument arg callEnv :: argumentStack rest :=
  rfl

/-- Residual ordinary closure frames of a right-nested application. -/
def functionStack {C : Type}
    (frames : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)) :
    EvalStack C :=
  frames.map fun p => .function (.closure p.1 p.2.1 p.2.2)

@[simp]
theorem functionStack_nil {C : Type} :
    functionStack
      ([] : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)) =
      [] :=
  rfl

@[simp]
theorem functionStack_cons {C : Type} (x : Name)
    (body : Term (QubitPrimitive C)) (clo : RuntimeEnv C)
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)) :
    functionStack ((x, body, clo) :: rest) =
      .function (.closure x body clo) :: functionStack rest :=
  rfl

@[simp]
theorem functionStack_singleton {C : Type} (x : Name)
    (body : Term (QubitPrimitive C)) (clo : RuntimeEnv C) :
    functionStack [(x, body, clo)] =
      [.function (.closure x body clo)] :=
  rfl

/-- A nonempty right-nested closure spine: the last body is
application-free and every earlier body is administrative NoApp. -/
def FunctionSpineOk {C : Type} :
    List (Name × Term (QubitPrimitive C) × RuntimeEnv C) → Prop
  | [] => False
  | [(_, body, _)] => NoApp body
  | (_, body, _) :: y :: rest =>
      AdminNoApp body ∧ FunctionSpineOk (y :: rest)

@[simp]
theorem FunctionSpineOk_nil {C : Type} :
    FunctionSpineOk
      ([] : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)) =
      False :=
  rfl

@[simp]
theorem FunctionSpineOk_singleton {C : Type} {x : Name}
    {body : Term (QubitPrimitive C)} {clo : RuntimeEnv C} :
    FunctionSpineOk [(x, body, clo)] ↔ NoApp body :=
  Iff.rfl

@[simp]
theorem FunctionSpineOk_cons_cons {C : Type} {x : Name}
    {body : Term (QubitPrimitive C)} {clo : RuntimeEnv C}
    {y : Name × Term (QubitPrimitive C) × RuntimeEnv C}
    {rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)} :
    FunctionSpineOk ((x, body, clo) :: y :: rest) ↔
      AdminNoApp body ∧ FunctionSpineOk (y :: rest) :=
  Iff.rfl

theorem FunctionSpineOk.ne_nil {C : Type}
    {frames : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)}
    (h : FunctionSpineOk frames) : frames ≠ [] := by
  cases frames <;> simp_all

theorem functionStack_eq_nil_iff {C : Type}
    {frames : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)} :
    functionStack frames = [] ↔ frames = [] := by
  cases frames <;> simp [functionStack]

theorem FunctionSpineOk.stack_ne_nil {C : Type}
    {frames : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)}
    (h : FunctionSpineOk frames) : functionStack frames ≠ [] := by
  intro hs
  exact h.ne_nil (functionStack_eq_nil_iff.mp hs)

theorem FunctionSpineOk.cons {C : Type} {x : Name}
    {body : Term (QubitPrimitive C)} {clo : RuntimeEnv C}
    {rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)}
    (hne : rest ≠ []) (hadmin : AdminNoApp body)
    (hok : FunctionSpineOk rest) :
    FunctionSpineOk ((x, body, clo) :: rest) := by
  match rest, hne, hok with
  | [], hne, _ => exact False.elim (hne rfl)
  | y :: rest, _, hok => exact ⟨hadmin, hok⟩

/-- Residual argument frames that evaluate by administrative NoApp. -/
def ArgumentFramesOk {C : Type}
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C)) : Prop :=
  ∀ p ∈ args, AdminNoApp p.1

/-- Residual argument frames in the FunAppFrag fragment (stacked apps). -/
def FunAppFramesOk {C : Type}
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C)) : Prop :=
  ∀ p ∈ args, FunAppFrag p.1

theorem FunAppFrag.of_admin {C : Type} {t : Term (QubitPrimitive C)}
    (h : AdminNoApp t) : FunAppFrag t :=
  FunAppFrag.admin h

theorem FunAppFramesOk.of_argumentFramesOk {C : Type}
    {args : List (Term (QubitPrimitive C) × RuntimeEnv C)}
    (h : ArgumentFramesOk args) : FunAppFramesOk args :=
  fun p hp => FunAppFrag.of_admin (h p hp)

/-- Ordinary or recursive closure frames pushed by FunAppFrag apps. -/
inductive FunFrame (C : Type) where
  | clo (x : Name) (body : Term (QubitPrimitive C)) (env : RuntimeEnv C)
  | recClo (self x : Name) (body : Term (QubitPrimitive C)) (env : RuntimeEnv C)

/-- Stack projection of a mixed ordinary/recursive function-frame spine. -/
def funFrameStack {C : Type} : List (FunFrame C) → EvalStack C
  | [] => []
  | .clo x body env :: rest =>
      .function (.closure x body env) :: funFrameStack rest
  | .recClo self x body env :: rest =>
      .function (.recClosure self x body env) :: funFrameStack rest

@[simp]
theorem funFrameStack_nil {C : Type} :
    funFrameStack ([] : List (FunFrame C)) = [] :=
  rfl

@[simp]
theorem funFrameStack_clo_cons {C : Type} (x : Name)
    (body : Term (QubitPrimitive C)) (env : RuntimeEnv C)
    (rest : List (FunFrame C)) :
    funFrameStack (.clo x body env :: rest) =
      .function (.closure x body env) :: funFrameStack rest :=
  rfl

@[simp]
theorem funFrameStack_recClo_cons {C : Type} (self x : Name)
    (body : Term (QubitPrimitive C)) (env : RuntimeEnv C)
    (rest : List (FunFrame C)) :
    funFrameStack (.recClo self x body env :: rest) =
      .function (.recClosure self x body env) :: funFrameStack rest :=
  rfl

/-- Ordinary closure triples as FunFrame.clo frames. -/
def cloFrames {C : Type} :
    List (Name × Term (QubitPrimitive C) × RuntimeEnv C) →
      List (FunFrame C)
  | [] => []
  | (x, body, env) :: rest => .clo x body env :: cloFrames rest

@[simp]
theorem cloFrames_nil {C : Type} :
    cloFrames
      ([] : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)) =
      [] :=
  rfl

@[simp]
theorem cloFrames_cons {C : Type} (x : Name)
    (body : Term (QubitPrimitive C)) (env : RuntimeEnv C)
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)) :
    cloFrames ((x, body, env) :: rest) =
      .clo x body env :: cloFrames rest :=
  rfl

theorem funFrameStack_cloFrames {C : Type}
    (frames : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)) :
    funFrameStack (cloFrames frames) = functionStack frames := by
  induction frames with
  | nil => rfl
  | cons p rest ih =>
      rcases p with ⟨x, body, env⟩
      simp [cloFrames, functionStack, ih]

theorem funFrameStack_ne_nil_of_cons {C : Type}
    (f : FunFrame C) (rest : List (FunFrame C)) :
    funFrameStack (f :: rest) ≠ [] := by
  cases f <;> simp [funFrameStack]

/-- A function-frame spine over leftover argument frames. -/
def mixedStack {C : Type}
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C)) :
    EvalStack C :=
  functionStack fns ++ argumentStack args

theorem funFrameStack_cloFrames_append_args {C : Type}
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C)) :
    funFrameStack (cloFrames fns) ++ argumentStack args =
      mixedStack fns args := by
  simp [mixedStack, funFrameStack_cloFrames]

theorem funFrameStack_cloFrames_recClo_append_args {C : Type}
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (self x : Name) (body : Term (QubitPrimitive C))
    (env : RuntimeEnv C)
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C)) :
    funFrameStack
        (cloFrames fns ++ [.recClo self x body env]) ++
          argumentStack args =
      functionStack fns ++
        (.function (.recClosure self x body env) ::
          argumentStack args) := by
  induction fns with
  | nil => simp [cloFrames, functionStack, funFrameStack]
  | cons p rest ih =>
      rcases p with ⟨y, M, clo⟩
      simp [cloFrames, functionStack, funFrameStack, ih]

@[simp]
theorem mixedStack_nil_fns {C : Type}
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C)) :
    mixedStack [] args = argumentStack args :=
  rfl

@[simp]
theorem mixedStack_cons {C : Type} (x : Name)
    (body : Term (QubitPrimitive C)) (clo : RuntimeEnv C)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C)) :
    mixedStack ((x, body, clo) :: fns) args =
      .function (.closure x body clo) :: mixedStack fns args :=
  rfl

@[simp]
theorem mixedStack_singleton {C : Type} (x : Name)
    (body : Term (QubitPrimitive C)) (clo : RuntimeEnv C)
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C)) :
    mixedStack [(x, body, clo)] args =
      .function (.closure x body clo) :: argumentStack args :=
  rfl

/-- Nonempty function spine over leftover argument frames: earlier
function bodies are administrative NoApp; the last body absorbs the
leftover arguments. -/
def MixedSpineOk {C : Type} :
    List (Name × Term (QubitPrimitive C) × RuntimeEnv C) →
    List (Term (QubitPrimitive C) × RuntimeEnv C) → Prop
  | [], _ => False
  | [(_, body, _)], args => BodyUnderArgs args.length body
  | (_, body, _) :: y :: rest, args =>
      AdminNoApp body ∧ MixedSpineOk (y :: rest) args

@[simp]
theorem MixedSpineOk_nil {C : Type}
    {args : List (Term (QubitPrimitive C) × RuntimeEnv C)} :
    MixedSpineOk
      ([] : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
      args = False :=
  rfl

@[simp]
theorem MixedSpineOk_singleton {C : Type} {x : Name}
    {body : Term (QubitPrimitive C)} {clo : RuntimeEnv C}
    {args : List (Term (QubitPrimitive C) × RuntimeEnv C)} :
    MixedSpineOk [(x, body, clo)] args ↔
      BodyUnderArgs args.length body :=
  Iff.rfl

@[simp]
theorem MixedSpineOk_cons_cons {C : Type} {x : Name}
    {body : Term (QubitPrimitive C)} {clo : RuntimeEnv C}
    {y : Name × Term (QubitPrimitive C) × RuntimeEnv C}
    {rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)}
    {args : List (Term (QubitPrimitive C) × RuntimeEnv C)} :
    MixedSpineOk ((x, body, clo) :: y :: rest) args ↔
      AdminNoApp body ∧ MixedSpineOk (y :: rest) args :=
  Iff.rfl

theorem MixedSpineOk.ne_nil {C : Type}
    {fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)}
    {args : List (Term (QubitPrimitive C) × RuntimeEnv C)}
    (h : MixedSpineOk fns args) : fns ≠ [] := by
  cases fns <;> simp_all

theorem mixedStack_ne_nil {C : Type}
    {fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)}
    {args : List (Term (QubitPrimitive C) × RuntimeEnv C)}
    (hne : fns ≠ []) : mixedStack fns args ≠ [] := by
  match fns with
  | [] => exact False.elim (hne rfl)
  | (x, body, clo) :: rest =>
      rw [mixedStack_cons]
      exact List.cons_ne_nil _ _

theorem MixedSpineOk.stack_ne_nil {C : Type}
    {fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)}
    {args : List (Term (QubitPrimitive C) × RuntimeEnv C)}
    (h : MixedSpineOk fns args) : mixedStack fns args ≠ [] :=
  mixedStack_ne_nil h.ne_nil

theorem MixedSpineOk.cons {C : Type} {x : Name}
    {body : Term (QubitPrimitive C)} {clo : RuntimeEnv C}
    {fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)}
    {args : List (Term (QubitPrimitive C) × RuntimeEnv C)}
    (hne : fns ≠ []) (hadmin : AdminNoApp body)
    (hok : MixedSpineOk fns args) :
    MixedSpineOk ((x, body, clo) :: fns) args := by
  match fns, hne, hok with
  | [], hne, _ => exact False.elim (hne rfl)
  | y :: rest, _, hok => exact ⟨hadmin, hok⟩

/-- After leftover argument frames are absorbed, the residual body is
an earlier function-spine body (`AdminNoApp`), not the last `NoApp`
body. -/
def BodyUnderArgsThenAdmin {C : Type} :
    Nat → Term (QubitPrimitive C) → Prop
  | 0, t => AdminNoApp t
  | n + 1, t =>
      match t with
      | .lam _ b => BodyUnderArgsThenAdmin n b
      | _ => False

/-- A lambda `lam x body` can absorb `n` leftover argument frames
before a residual function-frame spine. -/
def LamAbsorbsThenAdmin {C : Type} :
    Nat → Term (QubitPrimitive C) → Prop
  | 0, _ => True
  | n + 1, body => BodyUnderArgsThenAdmin n body

@[simp]
theorem BodyUnderArgsThenAdmin_zero {C : Type}
    {t : Term (QubitPrimitive C)} :
    BodyUnderArgsThenAdmin 0 t ↔ AdminNoApp t :=
  Iff.rfl

@[simp]
theorem BodyUnderArgsThenAdmin_succ_lam {C : Type} {n : Nat}
    {x : Name} {b : Term (QubitPrimitive C)} :
    BodyUnderArgsThenAdmin (n + 1) (.lam x b) ↔
      BodyUnderArgsThenAdmin n b :=
  Iff.rfl

theorem BodyUnderArgsThenAdmin_succ_inv {C : Type} {n : Nat}
    {t : Term (QubitPrimitive C)}
    (h : BodyUnderArgsThenAdmin (n + 1) t) :
    ∃ x b, t = .lam x b ∧ BodyUnderArgsThenAdmin n b := by
  cases t with
  | lam x b => exact ⟨x, b, rfl, h⟩
  | app _ _ => cases h
  | var _ => cases h
  | recLam _ _ _ => cases h
  | intern _ _ => cases h
  | extern _ _ => cases h
  | prob _ _ _ => cases h
  | prim _ => cases h

@[simp]
theorem LamAbsorbsThenAdmin_zero {C : Type}
    {body : Term (QubitPrimitive C)} :
    LamAbsorbsThenAdmin 0 body ↔ True :=
  Iff.rfl

@[simp]
theorem LamAbsorbsThenAdmin_succ {C : Type} {n : Nat}
    {body : Term (QubitPrimitive C)} :
    LamAbsorbsThenAdmin (n + 1) body ↔
      BodyUnderArgsThenAdmin n body :=
  Iff.rfl

/-- Leftover argument frames over a residual function-frame spine. -/
def argumentThenFunctionStack {C : Type}
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)) :
    EvalStack C :=
  argumentStack args ++ functionStack rest

@[simp]
theorem argumentThenFunctionStack_nil {C : Type}
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)) :
    argumentThenFunctionStack [] rest = functionStack rest :=
  rfl

@[simp]
theorem argumentThenFunctionStack_cons {C : Type}
    (arg : Term (QubitPrimitive C)) (callEnv : RuntimeEnv C)
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)) :
    argumentThenFunctionStack ((arg, callEnv) :: args) rest =
      .argument arg callEnv :: argumentThenFunctionStack args rest :=
  rfl

/-- A function-frame spine over leftover arguments over a residual
function-frame spine. -/
def mixedThenFunctionStack {C : Type}
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)) :
    EvalStack C :=
  functionStack fns ++ argumentThenFunctionStack args rest

@[simp]
theorem mixedThenFunctionStack_nil_fns {C : Type}
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)) :
    mixedThenFunctionStack [] args rest =
      argumentThenFunctionStack args rest :=
  rfl

@[simp]
theorem mixedThenFunctionStack_cons {C : Type} (x : Name)
    (body : Term (QubitPrimitive C)) (clo : RuntimeEnv C)
    (fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)) :
    mixedThenFunctionStack ((x, body, clo) :: fns) args rest =
      .function (.closure x body clo) ::
        mixedThenFunctionStack fns args rest :=
  rfl

@[simp]
theorem mixedThenFunctionStack_singleton {C : Type} (x : Name)
    (body : Term (QubitPrimitive C)) (clo : RuntimeEnv C)
    (args : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)) :
    mixedThenFunctionStack [(x, body, clo)] args rest =
      .function (.closure x body clo) ::
        argumentThenFunctionStack args rest :=
  rfl

/-- Nonempty leading function spine over leftover arguments over a
residual function-frame spine. The last leading body absorbs leftover
arguments into `AdminNoApp`; earlier leading bodies are
`AdminNoApp`. -/
def MixedThenFnOk {C : Type} :
    List (Name × Term (QubitPrimitive C) × RuntimeEnv C) →
    List (Term (QubitPrimitive C) × RuntimeEnv C) →
    List (Name × Term (QubitPrimitive C) × RuntimeEnv C) → Prop
  | [], _, _ => False
  | [(_, body, _)], args, rest =>
      BodyUnderArgsThenAdmin args.length body ∧ FunctionSpineOk rest
  | (_, body, _) :: y :: restFns, args, rest =>
      AdminNoApp body ∧ MixedThenFnOk (y :: restFns) args rest

@[simp]
theorem MixedThenFnOk_nil {C : Type}
    {args : List (Term (QubitPrimitive C) × RuntimeEnv C)}
    {rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)} :
    MixedThenFnOk
      ([] : List (Name × Term (QubitPrimitive C) × RuntimeEnv C))
      args rest = False :=
  rfl

@[simp]
theorem MixedThenFnOk_singleton {C : Type} {x : Name}
    {body : Term (QubitPrimitive C)} {clo : RuntimeEnv C}
    {args : List (Term (QubitPrimitive C) × RuntimeEnv C)}
    {rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)} :
    MixedThenFnOk [(x, body, clo)] args rest ↔
      BodyUnderArgsThenAdmin args.length body ∧
        FunctionSpineOk rest :=
  Iff.rfl

@[simp]
theorem MixedThenFnOk_cons_cons {C : Type} {x : Name}
    {body : Term (QubitPrimitive C)} {clo : RuntimeEnv C}
    {y : Name × Term (QubitPrimitive C) × RuntimeEnv C}
    {restFns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)}
    {args : List (Term (QubitPrimitive C) × RuntimeEnv C)}
    {rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)} :
    MixedThenFnOk ((x, body, clo) :: y :: restFns) args rest ↔
      AdminNoApp body ∧ MixedThenFnOk (y :: restFns) args rest :=
  Iff.rfl

theorem MixedThenFnOk.ne_nil {C : Type}
    {fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)}
    {args : List (Term (QubitPrimitive C) × RuntimeEnv C)}
    {rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)}
    (h : MixedThenFnOk fns args rest) : fns ≠ [] := by
  cases fns <;> simp_all

theorem mixedThenFunctionStack_ne_nil {C : Type}
    {fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)}
    {args : List (Term (QubitPrimitive C) × RuntimeEnv C)}
    {rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)}
    (hne : fns ≠ []) : mixedThenFunctionStack fns args rest ≠ [] := by
  match fns with
  | [] => exact False.elim (hne rfl)
  | (x, body, clo) :: restFns =>
      rw [mixedThenFunctionStack_cons]
      exact List.cons_ne_nil _ _

theorem MixedThenFnOk.stack_ne_nil {C : Type}
    {fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)}
    {args : List (Term (QubitPrimitive C) × RuntimeEnv C)}
    {rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)}
    (h : MixedThenFnOk fns args rest) :
    mixedThenFunctionStack fns args rest ≠ [] :=
  mixedThenFunctionStack_ne_nil h.ne_nil

theorem MixedThenFnOk.cons {C : Type} {x : Name}
    {body : Term (QubitPrimitive C)} {clo : RuntimeEnv C}
    {fns : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)}
    {args : List (Term (QubitPrimitive C) × RuntimeEnv C)}
    {rest : List (Name × Term (QubitPrimitive C) × RuntimeEnv C)}
    (hne : fns ≠ []) (hadmin : AdminNoApp body)
    (hok : MixedThenFnOk fns args rest) :
    MixedThenFnOk ((x, body, clo) :: fns) args rest := by
  match fns, hne, hok with
  | [], hne, _ => exact False.elim (hne rfl)
  | y :: restFns, _, hok => exact ⟨hadmin, hok⟩

theorem empty_env_closed_wellScoped {C : Type}
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    (hclosed : Closed code)
    (hc : s.control = .term code) (he : s.env = [])
    (hs : s.stack = []) :
    ChannelConfig.WellScoped s := by
  refine ⟨?_, ?_⟩
  · rw [hc, he]
    exact ⟨RuntimeEnv.wellScoped_nil, fun x hx =>
      False.elim ((closed_iff_forall_not_mem.mp hclosed x) hx)⟩
  · intro frame hf
    rw [hs] at hf
    cases hf

/-- A return at any empty stack is the identity wrap of its payload. -/
theorem return_empty_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {value : C}
    (hc : s.control = .term (.prim (.ret value)))
    (hs : s.stack = [])
    (hscoped : ChannelConfig.WellScoped s)
    {semanticEnv : Env (HSemanticValue D₀ j₀)}
    (_henv : EnvRel D₀ j₀ realize s.env semanticEnv) :
    PresentedChannelTreeCompleteness D₀ j₀ realize s
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.prim (.ret value)) semanticEnv) := by
  let t : ChannelConfig C :=
    {s with control := .value (.payload value)}
  have hstep : ChannelInternalStep s t := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.prim (.ret value))} t :=
      ChannelInternalStep.returnPrimitive (s := s) (value := value)
    have hsrc : s = {s with control := .term (.prim (.ret value))} :=
      ChannelConfig.ext hc rfl rfl rfl
    exact hsrc.symm ▸ happ
  have hchildScoped : ChannelConfig.WellScoped t :=
    ChannelInternalStep.preserve_wellScoped hstep hscoped
  have hchildRel : ChannelConfigRel D₀ j₀ realize t
      (semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (realize value)) := by
    refine ⟨semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (realize value), id, ?_, ?_, rfl⟩
    · exact ControlRel.value _ _ t.env
        (payload_related D₀ j₀ realize value)
    · change StackRel D₀ j₀ realize s.stack id
      rw [hs]
      exact StackRel.nil
  have hchild : PresentedChannelTreeCompleteness D₀ j₀ realize t
      (semanticUnit (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (realize value)) :=
    terminal_presentedChannelTreeCompleteness D₀ j₀ realize
      (s := t) ⟨.payload value, rfl, hs⟩ hchildScoped hchildRel
  simp [hardwarePrimitive_ret]
  exact identity_step_presentedChannelTreeCompleteness D₀ j₀ realize
    hstep (by simp [channelInternalOperation, hc])
    (fun h' => ChannelConfig.ext
      (ChannelInternalStep.eq_of_return h' hc).1
      (ChannelInternalStep.eq_of_return h' hc).2.1
      (ChannelInternalStep.eq_of_return h' hc).2.2.1
      (ChannelInternalStep.eq_of_return h' hc).2.2.2)
    hchild

/-- Wrap a left intern child at an arbitrary source with definitional
intern control. -/
def wrapInternLeftAt {C : Type} (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (child : ChannelTree C {s with control := .term left}) :
    ChannelTree C {s with control := .term (.intern left right)} :=
  ChannelTree.internal
    (ChannelInternalStep.internalLeft
      (s := {s with control := .term (.intern left right)}))
    child

def wrapInternRightAt {C : Type} (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (child : ChannelTree C {s with control := .term right}) :
    ChannelTree C {s with control := .term (.intern left right)} :=
  ChannelTree.internal
    (ChannelInternalStep.internalRight
      (s := {s with control := .term (.intern left right)}))
    child

theorem wrapInternLeftAt_depth {C : Type} (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (child : ChannelTree C {s with control := .term left}) :
    (wrapInternLeftAt s left right child).depth = child.depth + 1 :=
  rfl

theorem wrapInternRightAt_depth {C : Type} (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (child : ChannelTree C {s with control := .term right}) :
    (wrapInternRightAt s left right child).depth = child.depth + 1 :=
  rfl

/-- Internal choice at an empty stack is the join of presented children
that keep the same environment, stack, and quantum state. -/
theorem intern_empty_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hleft : PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term left}
      (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv))
    (hright : PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term right}
      (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term (.intern left right)}
      (interp (hardwarePrimitive D₀ j₀ realize) (.intern left right)
        semanticEnv) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ k hk
    rw [selectPath_intern,
      hleft.selected_result_eq_channelTree_sup_presented selectors i ξ k hk,
      hright.selected_result_eq_channelTree_sup_presented selectors i ξ k hk]
    have hop :
        channelInternalOperation
          {s with control := .term (.intern left right)} =
          QuantumOperation.identity 2 :=
      rfl
    refine le_antisymm ?_ ?_
    · apply sup_le
      · apply sSup_le
        rintro T ⟨fuel, child, R, hdepth, rfl⟩
        apply le_sSup
        refine ⟨fuel + 1, wrapInternLeftAt s left right child,
          wrapInternalRealization D₀ j₀ realize
            (ChannelInternalStep.internalLeft
              (s := {s with control := .term (.intern left right)}))
            child R, ?_, ?_⟩
        · simpa [wrapInternLeftAt_depth] using Nat.succ_le_succ hdepth
        · exact
            (restrictedResult_internal_of_identity D₀ j₀ realize
              (ChannelInternalStep.internalLeft
                (s := {s with control := .term (.intern left right)}))
              hop child
              (wrapInternalRealization D₀ j₀ realize
                (ChannelInternalStep.internalLeft
                  (s := {s with control := .term (.intern left right)}))
                child R)
              selectors i k).symm
      · apply sSup_le
        rintro T ⟨fuel, child, R, hdepth, rfl⟩
        apply le_sSup
        refine ⟨fuel + 1, wrapInternRightAt s left right child,
          wrapInternalRealization D₀ j₀ realize
            (ChannelInternalStep.internalRight
              (s := {s with control := .term (.intern left right)}))
            child R, ?_, ?_⟩
        · simpa [wrapInternRightAt_depth] using Nat.succ_le_succ hdepth
        · exact
            (restrictedResult_internal_of_identity D₀ j₀ realize
              (ChannelInternalStep.internalRight
                (s := {s with control := .term (.intern left right)}))
              hop child
              (wrapInternalRealization D₀ j₀ realize
                (ChannelInternalStep.internalRight
                  (s := {s with control := .term (.intern left right)}))
                child R)
              selectors i k).symm
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      have hctrl :
          ({s with control := .term (.intern left right)}).control =
            .term (.intern left right) :=
        rfl
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
            exact ⟨next.depth, next,
              internalChildRealization D₀ j₀ realize h next R,
              le_rfl, rfl⟩
          · cases ht
            have := restrictedResult_internal_of_identity D₀ j₀ realize
              h hop next R selectors i k
            rw [this]
            apply le_sup_of_le_right
            apply le_sSup
            exact ⟨next.depth, next,
              internalChildRealization D₀ j₀ realize h next R,
              le_rfl, rfl⟩
      | external _ hex _ =>
          exact False.elim (ChannelExternalStep.not_intern hex hctrl)

/-- Internal choice under an arbitrary stack continuation.  The continuation
must preserve intern, which every `StackRel` continuation does. -/
theorem intern_stacked_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (k : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀)
    (hk : ∀ q r, k (HasComputationChoice.intern (q, r)) =
      HasComputationChoice.intern (k q, k r))
    (hleft : PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term left}
      (k (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv)))
    (hright : PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term right}
      (k (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv))) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term (.intern left right)}
      (k (interp (hardwarePrimitive D₀ j₀ realize) (.intern left right)
        semanticEnv)) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ kξ hkξ
    rw [interp_intern_apply, hk,
      selectPath_computation_intern D₀ j₀,
      hleft.selected_result_eq_channelTree_sup_presented
        selectors i ξ kξ hkξ,
      hright.selected_result_eq_channelTree_sup_presented
        selectors i ξ kξ hkξ]
    have hop :
        channelInternalOperation
          {s with control := .term (.intern left right)} =
          QuantumOperation.identity 2 :=
      rfl
    refine le_antisymm ?_ ?_
    · apply sup_le
      · apply sSup_le
        rintro T ⟨fuel, child, R, hdepth, rfl⟩
        apply le_sSup
        refine ⟨fuel + 1, wrapInternLeftAt s left right child,
          wrapInternalRealization D₀ j₀ realize
            (ChannelInternalStep.internalLeft
              (s := {s with control := .term (.intern left right)}))
            child R, ?_, ?_⟩
        · simpa [wrapInternLeftAt_depth] using Nat.succ_le_succ hdepth
        · exact
            (restrictedResult_internal_of_identity D₀ j₀ realize
              (ChannelInternalStep.internalLeft
                (s := {s with control := .term (.intern left right)}))
              hop child
              (wrapInternalRealization D₀ j₀ realize
                (ChannelInternalStep.internalLeft
                  (s := {s with control := .term (.intern left right)}))
                child R)
              selectors i kξ).symm
      · apply sSup_le
        rintro T ⟨fuel, child, R, hdepth, rfl⟩
        apply le_sSup
        refine ⟨fuel + 1, wrapInternRightAt s left right child,
          wrapInternalRealization D₀ j₀ realize
            (ChannelInternalStep.internalRight
              (s := {s with control := .term (.intern left right)}))
            child R, ?_, ?_⟩
        · simpa [wrapInternRightAt_depth] using Nat.succ_le_succ hdepth
        · exact
            (restrictedResult_internal_of_identity D₀ j₀ realize
              (ChannelInternalStep.internalRight
                (s := {s with control := .term (.intern left right)}))
              hop child
              (wrapInternalRealization D₀ j₀ realize
                (ChannelInternalStep.internalRight
                  (s := {s with control := .term (.intern left right)}))
                child R)
              selectors i kξ).symm
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      have hctrl :
          ({s with control := .term (.intern left right)}).control =
            .term (.intern left right) :=
        rfl
      cases tree with
      | terminal hterm =>
          have := hterm.control_eq.symm.trans hctrl
          cases this
      | @internal _ t h next =>
          rcases ChannelInternalStep.eq_of_intern h hctrl with ht | ht
          · cases ht
            have := restrictedResult_internal_of_identity D₀ j₀ realize
              h hop next R selectors i kξ
            rw [this]
            apply le_sup_of_le_left
            apply le_sSup
            exact ⟨next.depth, next,
              internalChildRealization D₀ j₀ realize h next R,
              le_rfl, rfl⟩
          · cases ht
            have := restrictedResult_internal_of_identity D₀ j₀ realize
              h hop next R selectors i kξ
            rw [this]
            apply le_sup_of_le_right
            apply le_sSup
            exact ⟨next.depth, next,
              internalChildRealization D₀ j₀ realize h next R,
              le_rfl, rfl⟩
      | external _ hex _ =>
          exact False.elim (ChannelExternalStep.not_intern hex hctrl)

/-- Wrap a completed child under one external-selection node at an
arbitrary source with definitional extern control. -/
def wrapExternAt {C : Type} (s : ChannelConfig C) (b : Bool)
    (left right : Term (QubitPrimitive C))
    (child : ChannelTree C
      {s with control := .term (if b then right else left)}) :
    ChannelTree C {s with control := .term (.extern left right)} :=
  ChannelTree.external b
    (by
      cases b
      · exact ChannelExternalStep.selectFalse
          (s := {s with control := .term (.extern left right)})
      · exact ChannelExternalStep.selectTrue
          (s := {s with control := .term (.extern left right)}))
    child

theorem wrapExternAt_depth {C : Type} (s : ChannelConfig C) (b : Bool)
    (left right : Term (QubitPrimitive C))
    (child : ChannelTree C
      {s with control := .term (if b then right else left)}) :
    (wrapExternAt s b left right child).depth = child.depth + 1 :=
  rfl

theorem external_cons_channelTreeSup_at {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (b : Bool) (selectors : List Bool) (i : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    sSup (channelTreeResults D₀ j₀ realize
        {s with control := .term (.extern left right)}
        (b :: selectors) i k) =
      sSup (channelTreeResults D₀ j₀ realize
        {s with control := .term (if b then right else left)}
        selectors i k) := by
  let source := {s with control := .term (.extern left right)}
  let target := {s with control := .term (if b then right else left)}
  have hb : ChannelExternalStep source b target := by
    cases b
    · exact ChannelExternalStep.selectFalse
        (s := {s with control := .term (.extern left right)})
    · exact ChannelExternalStep.selectTrue
        (s := {s with control := .term (.extern left right)})
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

theorem external_coordinate_channelTreeSup_at {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (b : Bool) (j : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    sSup (channelTreeResults D₀ j₀ realize
        {s with control := .term (.extern left right)} []
        (HardwareAdequacy.branchCoordinate b j) k) =
      sSup (channelTreeResults D₀ j₀ realize
        {s with control := .term (if b then right else left)} [] j k) := by
  let source := {s with control := .term (.extern left right)}
  let target := {s with control := .term (if b then right else left)}
  have hb : ChannelExternalStep source b target := by
    cases b
    · exact ChannelExternalStep.selectFalse
        (s := {s with control := .term (.extern left right)})
    · exact ChannelExternalStep.selectTrue
        (s := {s with control := .term (.extern left right)})
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

theorem external_root_channelTreeSup_at {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    sSup (channelTreeResults D₀ j₀ realize
      {s with control := .term (.extern left right)} [] 0 k) = ⊥ := by
  apply le_antisymm
  · apply sSup_le
    rintro T ⟨_, tree, R, _, rfl⟩
    have hctrl :
        ({s with control := .term (.extern left right)}).control =
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

/-- External choice at an empty stack is the selected child-tree supremum. -/
theorem extern_empty_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hleft : PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term left}
      (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv))
    (hright : PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term right}
      (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term (.extern left right)}
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
            external_cons_channelTreeSup_at]
          simp
        · simp only [if_true]
          rw [hright.selected_result_eq_channelTree_sup_presented
            selectors i ξ k hk,
            external_cons_channelTreeSup_at]
          simp
    | nil =>
        cases i with
        | zero =>
            rw [HardwareAdequacy.selectPath_nil, interp_extern_apply,
              external_root_channelTreeSup_at]
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
                      {s with control := .term left} [] (n / 2) k) := by
                simpa using hc
              exact hc'.trans
                (external_coordinate_channelTreeSup_at D₀ j₀ realize s
                  left right false (n / 2) k).symm
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
                      {s with control := .term right} [] (n / 2) k) := by
                simpa using hc
              exact hc'.trans
                (external_coordinate_channelTreeSup_at D₀ j₀ realize s
                  left right true (n / 2) k).symm

/-- External choice under a stack continuation that commutes with
selection and is strict at the unresolved root.  Ordinary Kleisli
stack frames are root-strict; they commute with selection precisely
when their unfoldings are coordinate-constant. -/
theorem extern_stacked_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (k : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀)
    (hcommute :
      ∀ selected,
        TTContinuation.selectBranch selected
            (k (interp (hardwarePrimitive D₀ j₀ realize)
              (.extern left right) semanticEnv)) =
          k (TTContinuation.selectBranch selected
            (interp (hardwarePrimitive D₀ j₀ realize)
              (.extern left right) semanticEnv)))
    (hroot :
      k (interp (hardwarePrimitive D₀ j₀ realize) (.extern left right)
          semanticEnv) 0 =
        ⊥)
    (hleft : PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term left}
      (k (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv)))
    (hright : PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term right}
      (k (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv))) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term (.extern left right)}
      (k (interp (hardwarePrimitive D₀ j₀ realize) (.extern left right)
        semanticEnv)) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ kξ hk
    cases selectors with
    | cons b selectors =>
        rw [HardwareAdequacy.selectPath_cons, hcommute,
          interp_extern_apply]
        cases b
        · rw [TTContinuation.computation_extern_select_false]
          rw [hleft.selected_result_eq_channelTree_sup_presented
            selectors i ξ kξ hk,
            external_cons_channelTreeSup_at]
          simp
        · rw [TTContinuation.computation_extern_select_true]
          rw [hright.selected_result_eq_channelTree_sup_presented
            selectors i ξ kξ hk,
            external_cons_channelTreeSup_at]
          simp
    | nil =>
        cases i with
        | zero =>
            rw [HardwareAdequacy.selectPath_nil, hroot,
              external_root_channelTreeSup_at]
            exact ScottMap.bot_apply
              (D := ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
              (D' := TTResult 2) kξ
        | succ n =>
            by_cases heven : n % 2 = 0
            · have hi : n + 1 =
                  HardwareAdequacy.branchCoordinate false (n / 2) := by
                simp [HardwareAdequacy.branchCoordinate]
                omega
              have hsel :
                  TTContinuation.selectBranch false
                      (k (interp (hardwarePrimitive D₀ j₀ realize)
                        (.extern left right) semanticEnv))
                      (n / 2) =
                    k (interp (hardwarePrimitive D₀ j₀ realize)
                      (.extern left right) semanticEnv)
                      (n + 1) := by
                rw [hi]
                rfl
              have hchild :
                  k (interp (hardwarePrimitive D₀ j₀ realize)
                      (.extern left right) semanticEnv)
                      (n + 1) kξ =
                    k (interp (hardwarePrimitive D₀ j₀ realize) left
                      semanticEnv) (n / 2) kξ := by
                rw [← hsel, hcommute, interp_extern_apply,
                  TTContinuation.computation_extern_select_false]
              have hc :=
                hleft.selected_result_eq_channelTree_sup_presented
                  [] (n / 2) ξ kξ hk
              have hc' :
                  k (interp (hardwarePrimitive D₀ j₀ realize) left
                      semanticEnv) (n / 2) kξ =
                    sSup (channelTreeResults D₀ j₀ realize
                      {s with control := .term left} [] (n / 2) kξ) := by
                simpa using hc
              rw [HardwareAdequacy.selectPath_nil, hchild, hc', hi]
              exact
                (external_coordinate_channelTreeSup_at D₀ j₀ realize s
                  left right false (n / 2) kξ).symm
            · have hodd : n % 2 = 1 := by omega
              have hi : n + 1 =
                  HardwareAdequacy.branchCoordinate true (n / 2) := by
                simp [HardwareAdequacy.branchCoordinate]
                omega
              have hsel :
                  TTContinuation.selectBranch true
                      (k (interp (hardwarePrimitive D₀ j₀ realize)
                        (.extern left right) semanticEnv))
                      (n / 2) =
                    k (interp (hardwarePrimitive D₀ j₀ realize)
                      (.extern left right) semanticEnv)
                      (n + 1) := by
                rw [hi]
                rfl
              have hchild :
                  k (interp (hardwarePrimitive D₀ j₀ realize)
                      (.extern left right) semanticEnv)
                      (n + 1) kξ =
                    k (interp (hardwarePrimitive D₀ j₀ realize) right
                      semanticEnv) (n / 2) kξ := by
                rw [← hsel, hcommute, interp_extern_apply,
                  TTContinuation.computation_extern_select_true]
              have hc :=
                hright.selected_result_eq_channelTree_sup_presented
                  [] (n / 2) ξ kξ hk
              have hc' :
                  k (interp (hardwarePrimitive D₀ j₀ realize) right
                      semanticEnv) (n / 2) kξ =
                    sSup (channelTreeResults D₀ j₀ realize
                      {s with control := .term right} [] (n / 2) kξ) := by
                simpa using hc
              rw [HardwareAdequacy.selectPath_nil, hchild, hc', hi]
              exact
                (external_coordinate_channelTreeSup_at D₀ j₀ realize s
                  left right true (n / 2) kξ).symm

noncomputable def wrapProbAt {C : Type} {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (leftChild : ChannelTree C
      { s with
        control := .term left
        quantum := applyOperation
          (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum })
    (rightChild : ChannelTree C
      { s with
        control := .term right
        quantum := applyOperation
          (sourceProbabilityOperation (1 - p)
            (sub_nonneg.mpr hp₁.le) (by linarith)) s.quantum }) :
    ChannelTree C {s with control := .term (.prob p left right)} :=
  ChannelTree.probability (s := s) hp₀ hp₁ leftChild rightChild

noncomputable def wrapProbZeroAt {C : Type} (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (rightChild : ChannelTree C
      { s with
        control := .term right
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
          s.quantum }) :
    ChannelTree C {s with control := .term (.prob 0 left right)} :=
  ChannelTree.probabilityZero (s := s) (left := left) rightChild

noncomputable def wrapProbOneAt {C : Type} (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (leftChild : ChannelTree C
      { s with
        control := .term left
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
          s.quantum }) :
    ChannelTree C {s with control := .term (.prob 1 left right)} :=
  ChannelTree.probabilityOne (s := s) (right := right) leftChild

theorem wrapProbAt_depth {C : Type} {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (leftChild : ChannelTree C
      { s with
        control := .term left
        quantum := applyOperation
          (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum })
    (rightChild : ChannelTree C
      { s with
        control := .term right
        quantum := applyOperation
          (sourceProbabilityOperation (1 - p)
            (sub_nonneg.mpr hp₁.le) (by linarith)) s.quantum }) :
    (wrapProbAt hp₀ hp₁ s left right leftChild rightChild).depth =
      max leftChild.depth rightChild.depth + 1 :=
  rfl

theorem wrapProbZeroAt_depth {C : Type} (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (rightChild : ChannelTree C
      { s with
        control := .term right
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
          s.quantum }) :
    (wrapProbZeroAt s left right rightChild).depth =
      rightChild.depth + 1 :=
  rfl

theorem wrapProbOneAt_depth {C : Type} (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (leftChild : ChannelTree C
      { s with
        control := .term left
        quantum := applyOperation
          (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
          s.quantum }) :
    (wrapProbOneAt s left right leftChild).depth =
      leftChild.depth + 1 :=
  rfl

theorem prob_zero_empty_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hright : PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term right}
      (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term (.prob 0 left right)}
      (interp (hardwarePrimitive D₀ j₀ realize) (.prob 0 left right)
        semanticEnv) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ k hk
    have hright' :=
      PresentedChannelTreeCompleteness.congr
        (show
            { s with
              control := .term right
              quantum := applyOperation
                (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                s.quantum } =
              {s with control := .term right} from
          ChannelConfig.ext rfl rfl rfl
            (applyOperation_sourceProbability_one s.quantum)).symm
        rfl hright
    rw [selectPath_prob_zero,
      hright'.selected_result_eq_channelTree_sup_presented
        selectors i ξ k hk]
    apply le_antisymm
    · apply sSup_le
      rintro T ⟨fuel, child, R, hdepth, rfl⟩
      apply le_sSup
      refine ⟨fuel + 1, wrapProbZeroAt s left right child,
        wrapProbabilityZeroRealization D₀ j₀ realize
          (s := s) (leftTerm := left) (rightTerm := right) child R, ?_, ?_⟩
      · simpa [wrapProbZeroAt_depth] using Nat.succ_le_succ hdepth
      · exact
          (restrictedResult_probabilityZero D₀ j₀ realize child
            (wrapProbabilityZeroRealization D₀ j₀ realize
              (s := s) (leftTerm := left) (rightTerm := right) child R)
            selectors i k).symm
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      exact restrictedResult_of_control_prob_zero D₀ j₀ realize tree R rfl
        selectors i k

theorem prob_one_empty_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hleft : PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term left}
      (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term (.prob 1 left right)}
      (interp (hardwarePrimitive D₀ j₀ realize) (.prob 1 left right)
        semanticEnv) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ k hk
    have hleft' :=
      PresentedChannelTreeCompleteness.congr
        (show
            { s with
              control := .term left
              quantum := applyOperation
                (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                s.quantum } =
              {s with control := .term left} from
          ChannelConfig.ext rfl rfl rfl
            (applyOperation_sourceProbability_one s.quantum)).symm
        rfl hleft
    rw [selectPath_prob_one,
      hleft'.selected_result_eq_channelTree_sup_presented
        selectors i ξ k hk]
    apply le_antisymm
    · apply sSup_le
      rintro T ⟨fuel, child, R, hdepth, rfl⟩
      apply le_sSup
      refine ⟨fuel + 1, wrapProbOneAt s left right child,
        wrapProbabilityOneRealization D₀ j₀ realize
          (s := s) (leftTerm := left) (rightTerm := right) child R, ?_, ?_⟩
      · simpa [wrapProbOneAt_depth] using Nat.succ_le_succ hdepth
      · exact
          (restrictedResult_probabilityOne D₀ j₀ realize child
            (wrapProbabilityOneRealization D₀ j₀ realize
              (s := s) (leftTerm := left) (rightTerm := right) child R)
            selectors i k).symm
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      exact restrictedResult_of_control_prob_one D₀ j₀ realize tree R rfl
        selectors i k

theorem prob_invalid_empty_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C)
    (p : ℝ) (hp : ¬ (0 ≤ p ∧ p ≤ 1))
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term (.prob p left right)}
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

theorem prob_empty_presented_of_presented_children {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C)
    (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1)
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (hleft : PresentedChannelTreeCompleteness D₀ j₀ realize
      { s with
        control := .term left
        quantum := applyOperation
          (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum }
      (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv))
    (hright : PresentedChannelTreeCompleteness D₀ j₀ realize
      { s with
        control := .term right
        quantum := applyOperation
          (sourceProbabilityOperation (1 - p)
            (sub_nonneg.mpr hp₁.le) (by linarith)) s.quantum }
      (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term (.prob p left right)}
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
        { s with
          control := .term left
          quantum := applyOperation
            (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum }
        selectors i k
    let SR :=
      channelTreeResults D₀ j₀ realize
        { s with
          control := .term right
          quantum := applyOperation
            (sourceProbabilityOperation (1 - p)
              (sub_nonneg.mpr hp₁.le) (by linarith)) s.quantum }
        selectors i k
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
            wrapProbAt hp₀ hp₁ s left right leftT rightT,
            wrapProbabilityRealization D₀ j₀ realize hp₀ hp₁ leftT rightT
              leftR rightR, ?_, ?_⟩
          · simp [wrapProbAt_depth]
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
      exact restrictedResult_of_control_prob_presented D₀ j₀ realize tree R
        hp₀ hp₁ rfl selectors i ξ k hk

theorem prob_zero_stacked_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (k : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀)
    (hk : ∀ q r,
      k (HasComputationChoice.prob 0 (q, r)) =
        HasComputationChoice.prob 0 (k q, k r))
    (hright : PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term right}
      (k (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv))) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term (.prob 0 left right)}
      (k (interp (hardwarePrimitive D₀ j₀ realize) (.prob 0 left right)
        semanticEnv)) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ kξ hkξ
    have hright' :=
      PresentedChannelTreeCompleteness.congr
        (show
            { s with
              control := .term right
              quantum := applyOperation
                (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                s.quantum } =
              {s with control := .term right} from
          ChannelConfig.ext rfl rfl rfl
            (applyOperation_sourceProbability_one s.quantum)).symm
        rfl hright
    rw [interp_prob_apply, hk, selectPath_computation_prob D₀ j₀,
      TTContinuation.probChoice_zero,
      hright'.selected_result_eq_channelTree_sup_presented
        selectors i ξ kξ hkξ]
    apply le_antisymm
    · apply sSup_le
      rintro T ⟨fuel, child, R, hdepth, rfl⟩
      apply le_sSup
      refine ⟨fuel + 1, wrapProbZeroAt s left right child,
        wrapProbabilityZeroRealization D₀ j₀ realize
          (s := s) (leftTerm := left) (rightTerm := right) child R, ?_, ?_⟩
      · simpa [wrapProbZeroAt_depth] using Nat.succ_le_succ hdepth
      · exact
          (restrictedResult_probabilityZero D₀ j₀ realize child
            (wrapProbabilityZeroRealization D₀ j₀ realize
              (s := s) (leftTerm := left) (rightTerm := right) child R)
            selectors i kξ).symm
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      exact restrictedResult_of_control_prob_zero D₀ j₀ realize tree R rfl
        selectors i kξ

theorem prob_one_stacked_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C)
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (k : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀)
    (hk : ∀ q r,
      k (HasComputationChoice.prob 1 (q, r)) =
        HasComputationChoice.prob 1 (k q, k r))
    (hleft : PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term left}
      (k (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv))) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term (.prob 1 left right)}
      (k (interp (hardwarePrimitive D₀ j₀ realize) (.prob 1 left right)
        semanticEnv)) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ kξ hkξ
    have hleft' :=
      PresentedChannelTreeCompleteness.congr
        (show
            { s with
              control := .term left
              quantum := applyOperation
                (sourceProbabilityOperation 1 zero_le_one (le_refl 1))
                s.quantum } =
              {s with control := .term left} from
          ChannelConfig.ext rfl rfl rfl
            (applyOperation_sourceProbability_one s.quantum)).symm
        rfl hleft
    rw [interp_prob_apply, hk, selectPath_computation_prob D₀ j₀,
      TTContinuation.probChoice_one,
      hleft'.selected_result_eq_channelTree_sup_presented
        selectors i ξ kξ hkξ]
    apply le_antisymm
    · apply sSup_le
      rintro T ⟨fuel, child, R, hdepth, rfl⟩
      apply le_sSup
      refine ⟨fuel + 1, wrapProbOneAt s left right child,
        wrapProbabilityOneRealization D₀ j₀ realize
          (s := s) (leftTerm := left) (rightTerm := right) child R, ?_, ?_⟩
      · simpa [wrapProbOneAt_depth] using Nat.succ_le_succ hdepth
      · exact
          (restrictedResult_probabilityOne D₀ j₀ realize child
            (wrapProbabilityOneRealization D₀ j₀ realize
              (s := s) (leftTerm := left) (rightTerm := right) child R)
            selectors i kξ).symm
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      exact restrictedResult_of_control_prob_one D₀ j₀ realize tree R rfl
        selectors i kξ

theorem prob_invalid_stacked_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C)
    (p : ℝ) (hp : ¬ (0 ≤ p ∧ p ≤ 1))
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (k : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀)
    (hk : ∀ q r,
      k (HasComputationChoice.prob p (q, r)) =
        HasComputationChoice.prob p (k q, k r)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term (.prob p left right)}
      (k (interp (hardwarePrimitive D₀ j₀ realize) (.prob p left right)
        semanticEnv)) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ kξ hkξ
    have hbot :
        HardwareAdequacy.selectPath selectors
          (k (interp (hardwarePrimitive D₀ j₀ realize)
            (.prob p left right) semanticEnv)) i kξ = ⊥ := by
      rw [interp_prob_apply, hk, selectPath_computation_prob D₀ j₀,
        TTContinuation.probChoice_apply, dif_neg hp]
    rw [hbot]
    apply le_antisymm
    · exact bot_le
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      exact False.elim
        (no_channelTree_of_invalid_prob tree rfl hp)

theorem prob_stacked_presented_of_presented_children {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C)
    (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1)
    (left right : Term (QubitPrimitive C))
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (k : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀)
    (hk : ∀ q r,
      k (HasComputationChoice.prob p (q, r)) =
        HasComputationChoice.prob p (k q, k r))
    (hleft : PresentedChannelTreeCompleteness D₀ j₀ realize
      { s with
        control := .term left
        quantum := applyOperation
          (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum }
      (k (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv)))
    (hright : PresentedChannelTreeCompleteness D₀ j₀ realize
      { s with
        control := .term right
        quantum := applyOperation
          (sourceProbabilityOperation (1 - p)
            (sub_nonneg.mpr hp₁.le) (by linarith)) s.quantum }
      (k (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv))) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term (.prob p left right)}
      (k (interp (hardwarePrimitive D₀ j₀ realize) (.prob p left right)
        semanticEnv)) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ kξ hkξ
    have hpI : 0 ≤ p ∧ p ≤ 1 := ⟨hp₀.le, hp₁.le⟩
    rw [interp_prob_apply, hk, selectPath_computation_prob D₀ j₀,
      TTContinuation.probChoice_apply, dif_pos hpI,
      hleft.selected_result_eq_channelTree_sup_presented
        selectors i ξ kξ hkξ,
      hright.selected_result_eq_channelTree_sup_presented
        selectors i ξ kξ hkξ]
    let SL :=
      channelTreeResults D₀ j₀ realize
        { s with
          control := .term left
          quantum := applyOperation
            (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum }
        selectors i kξ
    let SR :=
      channelTreeResults D₀ j₀ realize
        { s with
          control := .term right
          quantum := applyOperation
            (sourceProbabilityOperation (1 - p)
              (sub_nonneg.mpr hp₁.le) (by linarith)) s.quantum }
        selectors i kξ
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
            wrapProbAt hp₀ hp₁ s left right leftT rightT,
            wrapProbabilityRealization D₀ j₀ realize hp₀ hp₁ leftT rightT
              leftR rightR, ?_, ?_⟩
          · simp [wrapProbAt_depth]
            omega
          · exact
              (restrictedResult_probability_presented D₀ j₀ realize hp₀ hp₁
                leftT rightT
                (wrapProbabilityRealization D₀ j₀ realize hp₀ hp₁
                  leftT rightT leftR rightR)
                selectors i ξ kξ hkξ).symm
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
      exact restrictedResult_of_control_prob_presented D₀ j₀ realize tree R
        hp₀ hp₁ rfl selectors i ξ kξ hkξ

/-- Pauli-X at an empty stack, with definitional primitive control. -/
noncomputable def pauliXTreeAt {C : Type} (s : ChannelConfig C) (value : C)
    (hs : s.stack = []) :
    ChannelTree C {s with control := .term (.prim (.pauliX value))} :=
  ChannelTree.internal
    (ChannelInternalStep.pauliXPrimitive
      (s := {s with control := .term (.prim (.pauliX value))}))
    (ChannelTree.terminal
      { value := .payload value, control_eq := rfl, stack_eq := hs })

theorem pauliXTreeAt_depth {C : Type} (s : ChannelConfig C) (value : C)
    (hs : s.stack = []) :
    (pauliXTreeAt s value hs).depth = 1 :=
  rfl

noncomputable def pauliXTreeAtRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C) (value : C) (hs : s.stack = []) :
    ChannelTreeRealization D₀ j₀ realize (pauliXTreeAt s value hs) where
  value := payloadLeafValue D₀ j₀ realize
  related := by
    intro o
    rcases o with ⟨⟨⟩, ⟨⟩⟩
    exact ValueRel.payload value

theorem pauliXTreeAt_leaf_payload {C : Type} (s : ChannelConfig C)
    (value : C) (hs : s.stack = [])
    (o : (pauliXTreeAt s value hs).instrument.Outcome) :
    ((pauliXTreeAt s value hs).instrument.value o).isTerminal.value =
      .payload value := by
  rcases o with ⟨⟨⟩, ⟨⟩⟩
  rfl

theorem pauliXTreeAt_compatible {C : Type} (s : ChannelConfig C)
    (value : C) (hs : s.stack = []) (selectors : List Bool) (i : ℕ)
    (o : (pauliXTreeAt s value hs).instrument.Outcome) :
    OutcomeCompatible (pauliXTreeAt s value hs) selectors i o := by
  rcases o with ⟨⟨⟩, ⟨⟩⟩
  simp [OutcomeCompatible, ChannelTree.instrument]
  exact List.nil_prefix

theorem pauliXTreeAt_realized_eq_ofOperation {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C) (value : C) (hs : s.stack = []) :
    embed (realizedInstrument D₀ j₀ realize (pauliXTreeAt s value hs)
      (pauliXTreeAtRealization D₀ j₀ realize s value hs)) =
      embed (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
        (realize value)) := by
  let μ := realizedInstrument D₀ j₀ realize (pauliXTreeAt s value hs)
    (pauliXTreeAtRealization D₀ j₀ realize s value hs)
  let _ : Unique μ.Outcome :=
    { default := ⟨⟨⟩, ⟨⟩⟩
      uniq := by intro o; rcases o with ⟨⟨⟩, ⟨⟩⟩; rfl }
  refine embed_eq_ofOperation_of_unique μ Qubit.pauliXOp (realize value) ?_ ?_
  · intro o
    change payloadLeafValue D₀ j₀ realize
        ((pauliXTreeAt s value hs).instrument.value o) = realize value
    rw [payloadLeafValue_payload D₀ j₀ realize _
      (pauliXTreeAt_leaf_payload s value hs o)]
  · intro o
    rcases o with ⟨⟨⟩, ⟨⟩⟩
    change KrausFamily.comp (KrausFamily.identity 2)
        (channelInternalOperation
          {s with control := .term (.prim (.pauliX value))}).kraus =
      Qubit.pauliXOp.kraus
    simp [channelInternalOperation]

theorem embed_of_pauliX_tree_at {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {value : C}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack = [])
    (tree : ChannelTree C s)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ) :
    embed (restrictedInstrument D₀ j₀ realize tree R selectors i) =
      embed (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
        (realize value)) := by
  cases tree with
  | terminal hterm =>
      have := hterm.control_eq.symm.trans hc
      cases this
  | internal h next =>
      have ht := ChannelInternalStep.eq_of_pauliX h hc
      have hnextctrl := ht.1
      have hnextstack := ht.2.2.1.trans hs
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
                (channelInternalOperation s).kraus =
              Qubit.pauliXOp.kraus
            simp [channelInternalOperation, hc]
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
      exact False.elim (ChannelExternalStep.not_prim h hc)
  | probability _ _ _ _ =>
      cases hc
  | probabilityZero _ =>
      cases hc
  | probabilityOne _ =>
      cases hc
  | measurement _ _ =>
      cases hc

theorem pauliX_empty_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C) (value : C)
    (hs : s.stack = [])
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term (.prim (.pauliX value))}
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.prim (.pauliX value)) semanticEnv) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ k hk
    have hdenote :
        interp (hardwarePrimitive D₀ j₀ realize)
            (.prim (.pauliX value)) semanticEnv =
          taggedEmbed (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
            (realize value)) := by
      simp [hardwarePrimitive_pauliX]
    rw [hdenote, selectPath_taggedEmbed, taggedEmbed_apply]
    refine le_antisymm ?_ ?_
    · apply le_sSup
      refine ⟨1, pauliXTreeAt s value hs,
        pauliXTreeAtRealization D₀ j₀ realize s value hs, ?_, ?_⟩
      · simp [pauliXTreeAt_depth]
      · rw [restrictedResult_eq_embed D₀ j₀ realize
            (pauliXTreeAt s value hs)
            (pauliXTreeAtRealization D₀ j₀ realize s value hs)
            selectors i k
            (by simp [ResultAvailable, resultAvailableAt, pauliXTreeAt]),
          embed_restricted_of_all_compatible D₀ j₀ realize
            (pauliXTreeAt s value hs)
            (pauliXTreeAtRealization D₀ j₀ realize s value hs)
            selectors i (pauliXTreeAt_compatible s value hs selectors i),
          pauliXTreeAt_realized_eq_ofOperation]
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      exact (restrictedResult_le_embed D₀ j₀ realize tree R selectors i k
        ).trans_eq
        (congrArg (fun f => f k)
          (embed_of_pauliX_tree_at D₀ j₀ realize
            (s := {s with control := .term (.prim (.pauliX value))})
            rfl hs tree R selectors i))

/-- Measure-Z at an empty stack, with definitional primitive control. -/
noncomputable def measurementTreeAt {C : Type} (s : ChannelConfig C)
    (zeroValue oneValue : C) (hs : s.stack = []) :
    ChannelTree C
      {s with control := .term (.prim (.measureZ zeroValue oneValue))} :=
  ChannelTree.measurement (s := s)
    (ChannelTree.terminal
      { value := .payload zeroValue, control_eq := rfl, stack_eq := hs })
    (ChannelTree.terminal
      { value := .payload oneValue, control_eq := rfl, stack_eq := hs })

theorem measurementTreeAt_depth {C : Type} (s : ChannelConfig C)
    (zeroValue oneValue : C) (hs : s.stack = []) :
    (measurementTreeAt s zeroValue oneValue hs).depth = 1 :=
  rfl

noncomputable def measurementTreeAtRealization {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C) (zeroValue oneValue : C) (hs : s.stack = []) :
    ChannelTreeRealization D₀ j₀ realize
      (measurementTreeAt s zeroValue oneValue hs) where
  value := payloadLeafValue D₀ j₀ realize
  related := by
    intro o
    obtain ⟨b, hb⟩ := o
    cases b <;> exact ValueRel.payload _

theorem measurementTreeAt_leaf_payload {C : Type} (s : ChannelConfig C)
    (zeroValue oneValue : C) (hs : s.stack = [])
    (o : (measurementTreeAt s zeroValue oneValue hs).instrument.Outcome) :
    ((measurementTreeAt s zeroValue oneValue hs).instrument.value o
      ).isTerminal.value =
      .payload (match o.1 with
        | true => oneValue
        | false => zeroValue) := by
  obtain ⟨b, hb⟩ := o
  cases b <;> (cases hb; rfl)

theorem measurementTreeAt_compatible {C : Type} (s : ChannelConfig C)
    (zeroValue oneValue : C) (hs : s.stack = [])
    (selectors : List Bool) (i : ℕ)
    (o : (measurementTreeAt s zeroValue oneValue hs).instrument.Outcome) :
    OutcomeCompatible (measurementTreeAt s zeroValue oneValue hs)
      selectors i o := by
  obtain ⟨b, hb⟩ := o
  cases b
  · cases hb
    simp [OutcomeCompatible, ChannelTree.instrument]
    exact List.nil_prefix
  · cases hb
    simp [OutcomeCompatible, ChannelTree.instrument]
    exact List.nil_prefix

theorem measurementTreeAt_realized_eq_measureZ {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C) (zeroValue oneValue : C) (hs : s.stack = []) :
    embed (realizedInstrument D₀ j₀ realize
        (measurementTreeAt s zeroValue oneValue hs)
        (measurementTreeAtRealization D₀ j₀ realize s zeroValue oneValue hs)) =
      embed (Qubit.measureZComp.map
        (fun b => if b then realize oneValue else realize zeroValue)) := by
  let μ := realizedInstrument D₀ j₀ realize
    (measurementTreeAt s zeroValue oneValue hs)
    (measurementTreeAtRealization D₀ j₀ realize s zeroValue oneValue hs)
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
          ((measurementTreeAt s zeroValue oneValue hs).instrument.value
            ⟨false, ⟨⟩⟩)
      rw [payloadLeafValue_payload D₀ j₀ realize _
        (measurementTreeAt_leaf_payload s zeroValue oneValue hs
          ⟨false, ⟨⟩⟩)]
    · cases hb
      change realize oneValue =
        payloadLeafValue D₀ j₀ realize
          ((measurementTreeAt s zeroValue oneValue hs).instrument.value
            ⟨true, ⟨⟩⟩)
      rw [payloadLeafValue_payload D₀ j₀ realize _
        (measurementTreeAt_leaf_payload s zeroValue oneValue hs
          ⟨true, ⟨⟩⟩)]

theorem embed_of_measureZ_tree_at {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {zeroValue oneValue : C}
    (hc : s.control = .term (.prim (.measureZ zeroValue oneValue)))
    (hs : s.stack = [])
    (tree : ChannelTree C s)
    (R : ChannelTreeRealization D₀ j₀ realize tree)
    (selectors : List Bool) (i : ℕ) :
    embed (restrictedInstrument D₀ j₀ realize tree R selectors i) =
      embed (Qubit.measureZComp.map
        (fun b => if b then realize oneValue else realize zeroValue)) := by
  cases tree with
  | terminal hterm =>
      have := hterm.control_eq.symm.trans hc
      cases this
  | internal h next =>
      exact False.elim (ChannelInternalStep.not_measureZ h hc)
  | external _ h _ =>
      exact False.elim (ChannelExternalStep.not_prim h hc)
  | probability _ _ _ _ =>
      cases hc
  | probabilityZero _ =>
      cases hc
  | probabilityOne _ =>
      cases hc
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
                source.quantum}).stack = [] := hs
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
                source.quantum}).stack = [] := hs
      cases zeroTree with
      | terminal hz =>
          cases oneTree with
          | terminal ho =>
              have hval0 : hz.value = .payload z' :=
                (by injection hz.control_eq : _ = hz.value).symm
              have hval1 : ho.value = .payload o' :=
                (by injection ho.control_eq : _ = ho.value).symm
              have hzid : z' = zeroValue := by
                cases hc
                rfl
              have hoid : o' = oneValue := by
                cases hc
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

theorem measureZ_empty_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (s : ChannelConfig C) (zeroValue oneValue : C)
    (hs : s.stack = [])
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      {s with control := .term (.prim (.measureZ zeroValue oneValue))}
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.prim (.measureZ zeroValue oneValue)) semanticEnv) where
  selected_result_eq_channelTree_sup_presented := by
    intro selectors i ξ k hk
    have hdenote :
        interp (hardwarePrimitive D₀ j₀ realize)
            (.prim (.measureZ zeroValue oneValue)) semanticEnv =
          taggedEmbed (Qubit.measureZComp.map
            (fun b => if b then realize oneValue else realize zeroValue)) := by
      simp [hardwarePrimitive_measureZ]
    rw [hdenote, selectPath_taggedEmbed, taggedEmbed_apply]
    refine le_antisymm ?_ ?_
    · apply le_sSup
      refine ⟨1, measurementTreeAt s zeroValue oneValue hs,
        measurementTreeAtRealization D₀ j₀ realize s zeroValue oneValue hs,
        ?_, ?_⟩
      · simp [measurementTreeAt_depth]
      · rw [restrictedResult_eq_embed D₀ j₀ realize
            (measurementTreeAt s zeroValue oneValue hs)
            (measurementTreeAtRealization D₀ j₀ realize
              s zeroValue oneValue hs)
            selectors i k
            (by simp [ResultAvailable, resultAvailableAt, measurementTreeAt]),
          embed_restricted_of_all_compatible D₀ j₀ realize
            (measurementTreeAt s zeroValue oneValue hs)
            (measurementTreeAtRealization D₀ j₀ realize
              s zeroValue oneValue hs)
            selectors i
            (measurementTreeAt_compatible s zeroValue oneValue hs
              selectors i),
          measurementTreeAt_realized_eq_measureZ]
    · apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      exact (restrictedResult_le_embed D₀ j₀ realize tree R selectors i k
        ).trans_eq
        (congrArg (fun f => f k)
          (embed_of_measureZ_tree_at D₀ j₀ realize
            (s :=
              {s with
                control := .term (.prim (.measureZ zeroValue oneValue))})
            rfl hs tree R selectors i))

open Classical

/-- Application-free closed terms are presented-complete at every empty
stack, including the scaled quantum states of interior probability. -/
theorem empty_stack_choice_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {semanticEnv : Env (HSemanticValue D₀ j₀)}
    (hclosed : Closed code) (hnoapp : NoApp code)
    (hc : s.control = .term code) (he : s.env = []) (hs : s.stack = [])
    (henv : EnvRel D₀ j₀ realize s.env semanticEnv) :
    PresentedChannelTreeCompleteness D₀ j₀ realize s
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) := by
  induction code generalizing s semanticEnv with
  | var x =>
      exact False.elim
        ((closed_iff_forall_not_mem.mp hclosed x) (by simp [free]))
  | app _ _ =>
      exact False.elim hnoapp
  | lam x body _ih =>
      exact lam_terminal_presentedChannelTreeCompleteness D₀ j₀ realize
        hc hs (empty_env_closed_wellScoped hclosed hc he hs) henv
  | recLam self arg body _ih =>
      exact recLam_terminal_presentedChannelTreeCompleteness D₀ j₀ realize
        hc hs (empty_env_closed_wellScoped hclosed hc he hs) henv
  | intern left right ihL ihR =>
      have ⟨hclL, hclR⟩ := closed_intern hclosed
      have ⟨hnaL, hnaR⟩ := hnoapp
      have hL :=
        ihL hclL hnaL (s := {s with control := .term left})
          (semanticEnv := semanticEnv) rfl he hs henv
      have hR :=
        ihR hclR hnaR (s := {s with control := .term right})
          (semanticEnv := semanticEnv) rfl he hs henv
      exact PresentedChannelTreeCompleteness.congr
        (show {s with control := .term (.intern left right)} = s from
          ChannelConfig.ext hc.symm rfl rfl rfl)
        rfl
        (intern_empty_presentedChannelTreeCompleteness D₀ j₀ realize
          s left right semanticEnv hL hR)
  | extern left right ihL ihR =>
      have ⟨hclL, hclR⟩ := closed_extern hclosed
      have ⟨hnaL, hnaR⟩ := hnoapp
      have hL :=
        ihL hclL hnaL (s := {s with control := .term left})
          (semanticEnv := semanticEnv) rfl he hs henv
      have hR :=
        ihR hclR hnaR (s := {s with control := .term right})
          (semanticEnv := semanticEnv) rfl he hs henv
      exact PresentedChannelTreeCompleteness.congr
        (show {s with control := .term (.extern left right)} = s from
          ChannelConfig.ext hc.symm rfl rfl rfl)
        rfl
        (extern_empty_presentedChannelTreeCompleteness D₀ j₀ realize
          s left right semanticEnv hL hR)
  | prob p left right ihL ihR =>
      have ⟨hclL, hclR⟩ := closed_prob hclosed
      have ⟨hnaL, hnaR⟩ := hnoapp
      if hI : 0 ≤ p ∧ p ≤ 1 then
        if hp0 : p = 0 then
          subst p
          have hR :=
            ihR hclR hnaR (s := {s with control := .term right})
              (semanticEnv := semanticEnv) rfl he hs henv
          exact PresentedChannelTreeCompleteness.congr
            (show {s with control := .term (.prob 0 left right)} = s from
              ChannelConfig.ext hc.symm rfl rfl rfl)
            rfl
            (prob_zero_empty_presentedChannelTreeCompleteness D₀ j₀ realize
              s left right semanticEnv hR)
        else if hp1 : p = 1 then
          subst p
          have hL :=
            ihL hclL hnaL (s := {s with control := .term left})
              (semanticEnv := semanticEnv) rfl he hs henv
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
            ihL hclL hnaL
              (s :=
                { s with
                  control := .term left
                  quantum := applyOperation
                    (sourceProbabilityOperation p hp₀.le hp₁.le)
                    s.quantum })
              (semanticEnv := semanticEnv) rfl he hs henv
          have hR :=
            ihR hclR hnaR
              (s :=
                { s with
                  control := .term right
                  quantum := applyOperation
                    (sourceProbabilityOperation (1 - p)
                      (sub_nonneg.mpr hp₁.le) (by linarith))
                    s.quantum })
              (semanticEnv := semanticEnv) rfl he hs henv
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
            hc hs (empty_env_closed_wellScoped hclosed hc he hs) henv
      | pauliX value =>
          exact PresentedChannelTreeCompleteness.congr
            (show {s with control := .term (.prim (.pauliX value))} = s from
              ChannelConfig.ext hc.symm rfl rfl rfl)
            rfl
            (pauliX_empty_presentedChannelTreeCompleteness D₀ j₀ realize
              s value hs semanticEnv)
      | measureZ zeroValue oneValue =>
          exact PresentedChannelTreeCompleteness.congr
            (show
                {s with
                  control :=
                    .term (.prim (.measureZ zeroValue oneValue))} = s from
              ChannelConfig.ext hc.symm rfl rfl rfl)
            rfl
            (measureZ_empty_presentedChannelTreeCompleteness D₀ j₀ realize
              s zeroValue oneValue hs semanticEnv)

/-- Presented completeness for every syntactically closed application-free
term at a normalized start: ordinary and recursive lambdas, internal and
external choice, probabilistic choice, and hardware primitives. -/
theorem closed_lambda_choice_presented_channelTreeCompleteness {C : Type}
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
  empty_stack_choice_presentedChannelTreeCompleteness D₀ j₀ realize
    hclosed hnoapp rfl rfl rfl (env_nil D₀ j₀ realize semanticEnv)

/-- Token adequacy for the closed lambda-and-choice fragment. -/
theorem closed_lambda_choice_presented_token_adequacy {C : Type}
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
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) i k ↔
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
    (closed_lambda_choice_presented_channelTreeCompleteness D₀ j₀ realize
      code hclosed hnoapp quantum semanticEnv)
    selectors ξ k hk i token

open Classical

/-- Application-free terms that are well-scoped in the current environment
are presented-complete at every empty stack.  After beta the body is
typically not closed, so this is the empty-stack lemma used by stacked
application. -/
theorem empty_stack_noapp_presentedChannelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {semanticEnv : Env (HSemanticValue D₀ j₀)}
    (hnoapp : NoApp code)
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
      exact False.elim hnoapp
  | lam x body _ih =>
      exact lam_terminal_presentedChannelTreeCompleteness D₀ j₀ realize
        hc hs hscoped henv
  | recLam self arg body _ih =>
      exact recLam_terminal_presentedChannelTreeCompleteness D₀ j₀ realize
        hc hs hscoped henv
  | intern left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hnoapp
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
  | extern left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hnoapp
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
        (show {s with control := .term (.extern left right)} = s from
          ChannelConfig.ext hc.symm rfl rfl rfl)
        rfl
        (extern_empty_presentedChannelTreeCompleteness D₀ j₀ realize
          s left right semanticEnv hL hR)
  | prob p left right ihL ihR =>
      have ⟨hnaL, hnaR⟩ := hnoapp
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
      | measureZ zeroValue oneValue =>
          exact PresentedChannelTreeCompleteness.congr
            (show
                {s with
                  control :=
                    .term (.prim (.measureZ zeroValue oneValue))} = s from
              ChannelConfig.ext hc.symm rfl rfl rfl)
            rfl
            (measureZ_empty_presentedChannelTreeCompleteness D₀ j₀ realize
              s zeroValue oneValue hs semanticEnv)

open Classical

def runtimeValueBodySize {C : Type} : RuntimeValue C → ℕ
  | .payload _ => 0
  | .closure _ body _ => termSize body
  | .recClosure _ _ body _ => termSize body

noncomputable def valueProducedSize {C : Type} (value : RuntimeValue C)
    (runtimeEnv : RuntimeEnv C) : ℕ :=
  if ∃ x, RuntimeEnv.lookup x runtimeEnv = some value then
    0
  else
    runtimeValueBodySize value

noncomputable def envCharge {C : Type} : RuntimeEnv C → ℕ
  | [] => 0
  | (_, value) :: rest => valueProducedSize value rest + envCharge rest

noncomputable def stackCharge {C : Type} (runtimeEnv : RuntimeEnv C) :
    EvalStack C → ℕ
  | [] => 0
  | .argument arg _ :: rest =>
      termSize arg + stackCharge runtimeEnv rest
  | .function fn :: rest =>
      valueProducedSize fn runtimeEnv + stackCharge runtimeEnv rest

noncomputable def controlCharge {C : Type} (s : ChannelConfig C) : ℕ :=
  match s.control with
  | .term code => termSize code
  | .value value => valueProducedSize value s.env

def controlPhase {C : Type} (s : ChannelConfig C) : ℕ :=
  match s.control with
  | .term _ => 0
  | .value _ => 1

/-- Environment charge is retained for later stacked-beta accounting, but the
active well-founded measure does not include it: binding a recursive
closure would otherwise double-count the body against the opened control. -/
noncomputable def configMeasure {C : Type} (s : ChannelConfig C) : ℕ :=
  2 * (controlCharge s + stackCharge s.env s.stack) + controlPhase s

@[simp] theorem runtimeValueBodySize_payload {C : Type} (value : C) :
    runtimeValueBodySize (RuntimeValue.payload value) = 0 :=
  rfl

@[simp] theorem runtimeValueBodySize_closure {C : Type}
    (x : Name) (body : Term (QubitPrimitive C)) (runtimeEnv : RuntimeEnv C) :
    runtimeValueBodySize (RuntimeValue.closure x body runtimeEnv) =
      termSize body :=
  rfl

@[simp] theorem runtimeValueBodySize_recClosure {C : Type}
    (self arg : Name) (body : Term (QubitPrimitive C))
    (runtimeEnv : RuntimeEnv C) :
    runtimeValueBodySize
        (RuntimeValue.recClosure self arg body runtimeEnv) =
      termSize body :=
  rfl

theorem valueProducedSize_of_mem {C : Type} {value : RuntimeValue C}
    {runtimeEnv : RuntimeEnv C}
    (h : ∃ x, RuntimeEnv.lookup x runtimeEnv = some value) :
    valueProducedSize value runtimeEnv = 0 := by
  simp [valueProducedSize, h]

theorem valueProducedSize_of_lookup {C : Type}
    {value : RuntimeValue C} {runtimeEnv : RuntimeEnv C} {x : Name}
    (h : RuntimeEnv.lookup x runtimeEnv = some value) :
    valueProducedSize value runtimeEnv = 0 :=
  valueProducedSize_of_mem ⟨x, h⟩

theorem valueProducedSize_le_body {C : Type} (value : RuntimeValue C)
    (runtimeEnv : RuntimeEnv C) :
    valueProducedSize value runtimeEnv ≤ runtimeValueBodySize value := by
  unfold valueProducedSize
  split_ifs <;> omega

theorem valueProducedSize_of_fresh {C : Type} {value : RuntimeValue C}
    {runtimeEnv : RuntimeEnv C}
    (h : ∀ y, RuntimeEnv.lookup y runtimeEnv ≠ some value) :
    valueProducedSize value runtimeEnv = runtimeValueBodySize value := by
  simp [valueProducedSize]
  intro x hx
  exact (h x hx).elim

theorem envCharge_bind {C : Type} (x : Name) (value : RuntimeValue C)
    (runtimeEnv : RuntimeEnv C) :
    envCharge (RuntimeEnv.bind x value runtimeEnv) =
      valueProducedSize value runtimeEnv + envCharge runtimeEnv :=
  rfl

theorem stackCharge_argument {C : Type} (runtimeEnv : RuntimeEnv C)
    (arg : Term (QubitPrimitive C)) (callEnv : RuntimeEnv C)
    (rest : EvalStack C) :
    stackCharge runtimeEnv (.argument arg callEnv :: rest) =
      termSize arg + stackCharge runtimeEnv rest :=
  rfl

theorem stackCharge_function {C : Type} (runtimeEnv : RuntimeEnv C)
    (fn : RuntimeValue C) (rest : EvalStack C) :
    stackCharge runtimeEnv (.function fn :: rest) =
      valueProducedSize fn runtimeEnv + stackCharge runtimeEnv rest :=
  rfl

theorem configMeasure_application {C : Type} {s : ChannelConfig C}
    {fn arg : Term (QubitPrimitive C)}
    (hc : s.control = .term (.app fn arg)) :
    configMeasure
        {s with
          control := .term fn
          stack := .argument arg s.env :: s.stack} <
      configMeasure s := by
  unfold configMeasure controlCharge controlPhase
  rw [hc]
  simp [termSize, stackCharge_argument]
  omega

theorem configMeasure_lambda {C : Type} {s : ChannelConfig C}
    {x : Name} {body : Term (QubitPrimitive C)}
    (hc : s.control = .term (.lam x body)) :
    configMeasure {s with control := .value (.closure x body s.env)} <
      configMeasure s := by
  unfold configMeasure controlCharge controlPhase
  rw [hc]
  simp [termSize]
  have hle :
      valueProducedSize (RuntimeValue.closure x body s.env) s.env ≤
        termSize body :=
    valueProducedSize_le_body _ _
  omega

theorem configMeasure_recLam {C : Type} {s : ChannelConfig C}
    {self arg : Name} {body : Term (QubitPrimitive C)}
    (hc : s.control = .term (.recLam self arg body)) :
    configMeasure
        {s with control := .value (.recClosure self arg body s.env)} <
      configMeasure s := by
  unfold configMeasure controlCharge controlPhase
  rw [hc]
  simp [termSize]
  have hle :
      valueProducedSize
          (RuntimeValue.recClosure self arg body s.env) s.env ≤
        termSize body :=
    valueProducedSize_le_body _ _
  omega

theorem configMeasure_variable {C : Type} {s : ChannelConfig C}
    {x : Name} {v : RuntimeValue C}
    (hc : s.control = .term (.var x))
    (hlookup : RuntimeEnv.lookup x s.env = some v) :
    configMeasure {s with control := .value v} < configMeasure s := by
  simp [configMeasure, controlCharge, controlPhase, hc,
    valueProducedSize_of_lookup hlookup, termSize]
  omega

theorem configMeasure_intern_left {C : Type} {s : ChannelConfig C}
    {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.intern left right)) :
    configMeasure {s with control := .term left} < configMeasure s := by
  simp [configMeasure, controlCharge, controlPhase, hc, termSize]

theorem configMeasure_intern_right {C : Type} {s : ChannelConfig C}
    {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.intern left right)) :
    configMeasure {s with control := .term right} < configMeasure s := by
  simp [configMeasure, controlCharge, controlPhase, hc, termSize]

theorem configMeasure_extern_left {C : Type} {s : ChannelConfig C}
    {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.extern left right)) :
    configMeasure {s with control := .term left} < configMeasure s := by
  simp [configMeasure, controlCharge, controlPhase, hc, termSize]

theorem configMeasure_extern_right {C : Type} {s : ChannelConfig C}
    {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.extern left right)) :
    configMeasure {s with control := .term right} < configMeasure s := by
  simp [configMeasure, controlCharge, controlPhase, hc, termSize]

theorem configMeasure_prob_left {C : Type} {s : ChannelConfig C}
    {p : ℝ} {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.prob p left right)) :
    configMeasure {s with control := .term left} < configMeasure s := by
  simp [configMeasure, controlCharge, controlPhase, hc, termSize]

theorem configMeasure_prob_right {C : Type} {s : ChannelConfig C}
    {p : ℝ} {left right : Term (QubitPrimitive C)}
    (hc : s.control = .term (.prob p left right)) :
    configMeasure {s with control := .term right} < configMeasure s := by
  simp [configMeasure, controlCharge, controlPhase, hc, termSize]

theorem configMeasure_congr_quantum {C : Type} {s : ChannelConfig C}
    (quantum : SubNormalizedDensity 2) :
    configMeasure {s with quantum := quantum} = configMeasure s :=
  rfl

theorem configMeasure_return {C : Type} {s : ChannelConfig C} {value : C}
    (hc : s.control = .term (.prim (.ret value))) :
    configMeasure {s with control := .value (.payload value)} <
      configMeasure s := by
  unfold configMeasure controlCharge controlPhase valueProducedSize
    runtimeValueBodySize
  rw [hc]
  simp [termSize]
  omega

theorem configMeasure_pauliX {C : Type} {s : ChannelConfig C} {value : C}
    (hc : s.control = .term (.prim (.pauliX value))) :
    configMeasure
        {s with
          control := .value (.payload value)
          quantum := applyOperation Qubit.pauliXOp s.quantum} <
      configMeasure s := by
  unfold configMeasure controlCharge controlPhase valueProducedSize
    runtimeValueBodySize
  rw [hc]
  simp [termSize]
  omega

theorem configMeasure_measureZ_zero {C : Type} {s : ChannelConfig C}
    {zeroValue oneValue : C}
    (hc : s.control = .term (.prim (.measureZ zeroValue oneValue))) :
    configMeasure
        {s with
          control := .value (.payload zeroValue)
          quantum := applyOperation (measurementOperation false) s.quantum} <
      configMeasure s := by
  unfold configMeasure controlCharge controlPhase valueProducedSize
    runtimeValueBodySize
  rw [hc]
  simp [termSize]
  omega

theorem configMeasure_measureZ_one {C : Type} {s : ChannelConfig C}
    {zeroValue oneValue : C}
    (hc : s.control = .term (.prim (.measureZ zeroValue oneValue))) :
    configMeasure
        {s with
          control := .value (.payload oneValue)
          quantum := applyOperation (measurementOperation true) s.quantum} <
      configMeasure s := by
  unfold configMeasure controlCharge controlPhase valueProducedSize
    runtimeValueBodySize
  rw [hc]
  simp [termSize]
  omega

theorem configMeasure_evaluateArgument {C : Type} {s : ChannelConfig C}
    {fn : RuntimeValue C} {arg : Term (QubitPrimitive C)}
    {callEnv : RuntimeEnv C} {rest : EvalStack C}
    (hc : s.control = .value fn)
    (hs : s.stack = .argument arg callEnv :: rest)
    (henv : s.env = callEnv) :
    configMeasure
        {s with
          control := .term arg
          env := callEnv
          stack := .function fn :: rest} <
      configMeasure s := by
  unfold configMeasure controlCharge controlPhase
  rw [hc, hs, henv]
  simp [stackCharge_argument, stackCharge_function]
  omega

theorem configMeasure_beta {C : Type} {s : ChannelConfig C} {x : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    {arg : RuntimeValue C} {rest : EvalStack C}
    (hc : s.control = .value arg)
    (hs : s.stack = .function (.closure x body closureEnv) :: rest)
    (hfresh :
      ∀ y, RuntimeEnv.lookup y s.env ≠
        some (.closure x body closureEnv))
    (hrest :
      stackCharge (RuntimeEnv.bind x arg closureEnv) rest ≤
        stackCharge s.env rest) :
    configMeasure
        {s with
          control := .term body
          env := RuntimeEnv.bind x arg closureEnv
          stack := rest} <
      configMeasure s := by
  have hfn :
      valueProducedSize (RuntimeValue.closure x body closureEnv) s.env =
        termSize body := by
    simpa [runtimeValueBodySize] using
      valueProducedSize_of_fresh hfresh
  simp [configMeasure, controlCharge, controlPhase, hc, hs, hfn,
    termSize, stackCharge_function]
  omega

theorem configMeasure_beta_nil {C : Type} {s : ChannelConfig C} {x : Name}
    {body : Term (QubitPrimitive C)} {closureEnv : RuntimeEnv C}
    {arg : RuntimeValue C}
    (hc : s.control = .value arg)
    (hs : s.stack = [.function (.closure x body closureEnv)])
    (hfresh :
      ∀ y, RuntimeEnv.lookup y s.env ≠
        some (.closure x body closureEnv)) :
    configMeasure
        {s with
          control := .term body
          env := RuntimeEnv.bind x arg closureEnv
          stack := []} <
      configMeasure s :=
  configMeasure_beta hc hs hfresh (by simp [stackCharge])

theorem configMeasure_recBeta {C : Type} {s : ChannelConfig C}
    {self x : Name} {body : Term (QubitPrimitive C)}
    {closureEnv : RuntimeEnv C} {arg : RuntimeValue C}
    {rest : EvalStack C}
    (hc : s.control = .value arg)
    (hs : s.stack =
      .function (.recClosure self x body closureEnv) :: rest)
    (hfresh :
      ∀ y, RuntimeEnv.lookup y s.env ≠
        some (.recClosure self x body closureEnv))
    (hrest :
      stackCharge
          (RuntimeEnv.bind x arg
            (RuntimeEnv.bind self
              (.recClosure self x body closureEnv) closureEnv))
          rest ≤
        stackCharge s.env rest) :
    configMeasure
        {s with
          control := .term body
          env :=
            RuntimeEnv.bind x arg
              (RuntimeEnv.bind self
                (.recClosure self x body closureEnv) closureEnv)
          stack := rest} <
      configMeasure s := by
  have hfn :
      valueProducedSize
          (RuntimeValue.recClosure self x body closureEnv) s.env =
        termSize body := by
    simpa [runtimeValueBodySize] using
      valueProducedSize_of_fresh hfresh
  simp [configMeasure, controlCharge, controlPhase, hc, hs, hfn,
    termSize, stackCharge_function]
  omega

theorem configMeasure_recBeta_nil {C : Type} {s : ChannelConfig C}
    {self x : Name} {body : Term (QubitPrimitive C)}
    {closureEnv : RuntimeEnv C} {arg : RuntimeValue C}
    (hc : s.control = .value arg)
    (hs : s.stack = [.function (.recClosure self x body closureEnv)])
    (hfresh :
      ∀ y, RuntimeEnv.lookup y s.env ≠
        some (.recClosure self x body closureEnv)) :
    configMeasure
        {s with
          control := .term body
          env :=
            RuntimeEnv.bind x arg
              (RuntimeEnv.bind self
                (.recClosure self x body closureEnv) closureEnv)
          stack := []} <
      configMeasure s :=
  configMeasure_recBeta hc hs hfresh (by simp [stackCharge])

theorem stackCharge_eq_of_no_function {C : Type}
    (env₁ env₂ : RuntimeEnv C) :
    ∀ rest : EvalStack C,
      (∀ fn, Frame.function fn ∉ rest) →
      stackCharge env₁ rest = stackCharge env₂ rest
  | [], _ => rfl
  | .argument arg callEnv :: rest, h => by
      simp [stackCharge]
      exact stackCharge_eq_of_no_function env₁ env₂ rest
        (fun fn hmem => h fn (by simp [hmem]))
  | .function fn :: _, h =>
      (h fn (by simp)).elim

theorem channelConfigRel_term_inv {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term code)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    ∃ semanticEnv k,
      EnvRel D₀ j₀ realize s.env semanticEnv ∧
      StackRel D₀ j₀ realize s.stack k ∧
      answer =
        k (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) := by
  rcases hrel with ⟨current, k, hcontrol, hstack, rfl⟩
  rw [hc] at hcontrol
  cases hcontrol with
  | term _ _ semanticEnv henv =>
      exact ⟨semanticEnv, k, henv, hstack, rfl⟩

theorem wellScoped_term_child {C : Type}
    {s : ChannelConfig C} {code child : Term (QubitPrimitive C)}
    (hc : s.control = .term code)
    (hscoped : ChannelConfig.WellScoped s)
    (hcover : ∀ x, x ∈ free child → x ∈ free code) :
    ChannelConfig.WellScoped {s with control := .term child} := by
  have ⟨hctl, hstk⟩ := hscoped
  rw [hc] at hctl
  exact ⟨⟨hctl.left, fun x hx => hctl.right x (hcover x hx)⟩, hstk⟩

/-- Internal choice at a related well-scoped state is presented-complete
once both children are, using the stack continuation that preserves intern. -/
theorem intern_related_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.intern left right))
    (hrel : ChannelConfigRel D₀ j₀ realize s answer)
    (hleft :
      ∀ semanticEnv k,
        EnvRel D₀ j₀ realize s.env semanticEnv →
        StackRel D₀ j₀ realize s.stack k →
        PresentedChannelConfigCompleteness D₀ j₀ realize
          {s with control := .term left}
          (k (interp (hardwarePrimitive D₀ j₀ realize) left
            semanticEnv)))
    (hright :
      ∀ semanticEnv k,
        EnvRel D₀ j₀ realize s.env semanticEnv →
        StackRel D₀ j₀ realize s.stack k →
        PresentedChannelConfigCompleteness D₀ j₀ realize
          {s with control := .term right}
          (k (interp (hardwarePrimitive D₀ j₀ realize) right
            semanticEnv))) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  obtain ⟨semanticEnv, k, henv, hstack, rfl⟩ :=
    channelConfigRel_term_inv D₀ j₀ hc hrel
  refine
    { related := hrel
      complete :=
        PresentedChannelTreeCompleteness.congr
          (show {s with control := .term (.intern left right)} = s from
            ChannelConfig.ext hc.symm rfl rfl rfl)
          rfl
          (intern_stacked_presentedChannelTreeCompleteness
            D₀ j₀ realize s left right semanticEnv k
            (HardwareLogicalRelation.stackRel_map_intern
              (D₀ := D₀) (j₀ := j₀) hstack)
            (hleft semanticEnv k henv hstack).complete
            (hright semanticEnv k henv hstack).complete) }

/-- Probability at a related well-scoped state is presented-complete
once both children are, at every residual quantum.  The stack
continuation preserves probabilistic choice. -/
theorem prob_related_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {p : ℝ}
    {left right : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prob p left right))
    (hrel : ChannelConfigRel D₀ j₀ realize s answer)
    (hleft :
      ∀ semanticEnv k (quantum : SubNormalizedDensity 2),
        EnvRel D₀ j₀ realize s.env semanticEnv →
        StackRel D₀ j₀ realize s.stack k →
        PresentedChannelConfigCompleteness D₀ j₀ realize
          {s with control := .term left, quantum := quantum}
          (k (interp (hardwarePrimitive D₀ j₀ realize) left
            semanticEnv)))
    (hright :
      ∀ semanticEnv k (quantum : SubNormalizedDensity 2),
        EnvRel D₀ j₀ realize s.env semanticEnv →
        StackRel D₀ j₀ realize s.stack k →
        PresentedChannelConfigCompleteness D₀ j₀ realize
          {s with control := .term right, quantum := quantum}
          (k (interp (hardwarePrimitive D₀ j₀ realize) right
            semanticEnv))) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  obtain ⟨semanticEnv, k, henv, hstack, rfl⟩ :=
    channelConfigRel_term_inv D₀ j₀ hc hrel
  refine
    { related := hrel
      complete :=
        PresentedChannelTreeCompleteness.congr
          (show {s with control := .term (.prob p left right)} = s from
            ChannelConfig.ext hc.symm rfl rfl rfl)
          rfl ?_ }
  if hI : 0 ≤ p ∧ p ≤ 1 then
    if hp0 : p = 0 then
      subst p
      exact prob_zero_stacked_presentedChannelTreeCompleteness
        D₀ j₀ realize s left right semanticEnv k
        (HardwareLogicalRelation.stackRel_map_prob
          (D₀ := D₀) (j₀ := j₀) hstack 0)
        (hright semanticEnv k s.quantum henv hstack).complete
    else if hp1 : p = 1 then
      subst p
      exact prob_one_stacked_presentedChannelTreeCompleteness
        D₀ j₀ realize s left right semanticEnv k
        (HardwareLogicalRelation.stackRel_map_prob
          (D₀ := D₀) (j₀ := j₀) hstack 1)
        (hleft semanticEnv k s.quantum henv hstack).complete
    else
      have hp₀ : 0 < p := lt_of_le_of_ne hI.1 (Ne.symm hp0)
      have hp₁ : p < 1 := lt_of_le_of_ne hI.2 hp1
      exact prob_stacked_presented_of_presented_children
        D₀ j₀ realize s p hp₀ hp₁ left right semanticEnv k
        (HardwareLogicalRelation.stackRel_map_prob
          (D₀ := D₀) (j₀ := j₀) hstack p)
        (hleft semanticEnv k
          (applyOperation
            (sourceProbabilityOperation p hp₀.le hp₁.le) s.quantum)
          henv hstack).complete
        (hright semanticEnv k
          (applyOperation
            (sourceProbabilityOperation (1 - p)
              (sub_nonneg.mpr hp₁.le) (by linarith))
            s.quantum)
          henv hstack).complete
  else
    exact prob_invalid_stacked_presentedChannelTreeCompleteness
      D₀ j₀ realize s p hI left right semanticEnv k
      (HardwareLogicalRelation.stackRel_map_prob
        (D₀ := D₀) (j₀ := j₀) hstack p)

theorem taggedEmbed_coordinateConstant {D : Type} [CompleteLattice D]
    (μ : FiniteInstrumentComp 2 D) :
    CoordinateConstant (taggedEmbed μ) := by
  intro i j
  rfl

theorem intern_coordinateConstant
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (q r : HSemanticComp D₀ j₀)
    (hq : CoordinateConstant q)
    (hr : CoordinateConstant r) :
    CoordinateConstant
      (HasComputationChoice.intern (q, r)) := by
  intro i j
  rw [TTContinuation.computation_intern_apply,
    TTContinuation.computation_intern_apply, hq i j, hr i j]

theorem prob_coordinateConstant
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (p : Prob) (q r : HSemanticComp D₀ j₀)
    (hq : CoordinateConstant q)
    (hr : CoordinateConstant r) :
    CoordinateConstant
      (HasComputationChoice.prob p (q, r)) := by
  intro i j
  rw [TTContinuation.computation_prob_apply,
    TTContinuation.computation_prob_apply, hq i j, hr i j]

theorem adminNoApp_interp_coordinateConstant {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {code : Term (QubitPrimitive C)}
    (hadmin : AdminNoApp code)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    CoordinateConstant
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) := by
  induction code with
  | var y =>
      intro i j
      rfl
  | app _ _ =>
      exact False.elim hadmin
  | lam _ _ _ =>
      intro i j
      rfl
  | recLam _ _ _ _ =>
      intro i j
      rfl
  | intern left right ihL ihR =>
      have ⟨hL, hR⟩ := hadmin
      exact intern_coordinateConstant D₀ j₀
        (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv)
        (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)
        (ihL hL) (ihR hR)
  | extern _ _ _ _ =>
      exact False.elim hadmin
  | prob p left right ihL ihR =>
      have ⟨hL, hR⟩ := hadmin
      exact prob_coordinateConstant D₀ j₀ p
        (interp (hardwarePrimitive D₀ j₀ realize) left semanticEnv)
        (interp (hardwarePrimitive D₀ j₀ realize) right semanticEnv)
        (ihL hL) (ihR hR)
  | prim prim =>
      cases prim with
      | ret _ =>
          intro i j
          rfl
      | pauliX value =>
          simpa [interp_prim_apply, hardwarePrimitive_pauliX] using
            taggedEmbed_coordinateConstant
              (FiniteInstrumentComp.ofOperation Qubit.pauliXOp
                (realize value))
      | measureZ _ _ =>
          exact False.elim hadmin

theorem semanticUnfold_lambdaValue
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (x : Name)
    (body : ScottMap (Env (HSemanticValue D₀ j₀)) (HSemanticComp D₀ j₀))
    (ρ : Env (HSemanticValue D₀ j₀))
    (d : HSemanticValue D₀ j₀) :
    semanticUnfold (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (lambdaValue (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) x body ρ) d =
      body (envUpdate (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) x (ρ, d)) := by
  change
      qEmbInfInf (QModel (TTExternalContinuationPower 2)) D₀ j₀
        (qProjInfInf (QModel (TTExternalContinuationPower 2)) D₀ j₀
          (scottLambda
            (body.comp
              (envUpdate (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀) x))
            ρ)) d =
        body (envUpdate (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) x (ρ, d))
  rw [qEmbInfInf_qProjInfInf]
  rfl

/-- Unfolding a recursive lambda once exposes its body with both the
recursive self value and the argument installed. -/
theorem semanticUnfold_recLambdaValue
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (self x : Name)
    (body : ScottMap (Env (HSemanticValue D₀ j₀)) (HSemanticComp D₀ j₀))
    (ρ : Env (HSemanticValue D₀ j₀))
    (d : HSemanticValue D₀ j₀) :
    semanticUnfold (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (recLambdaValue (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) self x body ρ) d =
      body
        (envUpdate (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) x
          (envUpdate (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) self
            (ρ,
              recLambdaValue (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀) self x body ρ),
            d)) := by
  rw [recLambdaValue_unfold]
  change
      qEmbInfInf (QModel (TTExternalContinuationPower 2)) D₀ j₀
          (qProjInfInf (QModel (TTExternalContinuationPower 2)) D₀ j₀
            (scottLambda
              (body.comp
                ((envUpdate (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) x).comp
                  (ScottMap.pairMap
                    ((envUpdate (Q := TTExternalContinuationPower 2)
                      (D₀ := D₀) (j₀ := j₀) self).comp
                      ScottMap.fstMap)
                    ScottMap.sndMap)))
              (ρ,
                recLambdaValue (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) self x body ρ))) d =
        _
  rw [qEmbInfInf_qProjInfInf]
  rw [← recLambdaValue_unfold]
  rfl

theorem semanticBind_select_of_unfold_constant
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (f : HSemanticValue D₀ j₀)
    (hf : ∀ d, CoordinateConstant
      (semanticUnfold (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) f d))
    (q : HSemanticComp D₀ j₀)
    (b : Bool) :
    TTContinuation.selectBranch b
        (semanticBind (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (semanticUnfold (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) f) q) =
      semanticBind (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (semanticUnfold (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) f)
        (TTContinuation.selectBranch b q) :=
  TTContinuation.selectBranch_taggedBind_of_coordinateConstant
    (semanticUnfold (Q := TTExternalContinuationPower 2)
      (D₀ := D₀) (j₀ := j₀) f) hf q b

theorem semanticBind_root_bot
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (h : ScottMap (HSemanticValue D₀ j₀) (HSemanticComp D₀ j₀))
    (q : HSemanticComp D₀ j₀)
    (hq : q 0 = ⊥) :
    semanticBind (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) h q 0 =
      ⊥ :=
  TTContinuation.taggedBind_root_bot h q hq

/-- Every stack continuation is root-strict: if the current computation is
`⊥` at the unresolved root, so is its image under the Kleisli stack map. -/
theorem stackRel_root_bot {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    {realize : C → HSemanticValue D₀ j₀}
    {stack : EvalStack C}
    {k : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀}
    (hstack : StackRel D₀ j₀ realize stack k)
    {q : HSemanticComp D₀ j₀} (hq : q 0 = ⊥) :
    k q 0 = ⊥ := by
  induction hstack generalizing q with
  | nil => exact hq
  | argument arg runtimeEnv semanticEnv rest krest henv hrest ih =>
      exact ih (semanticBind_root_bot D₀ j₀
        (applyContinuation (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (interp (hardwarePrimitive D₀ j₀ realize) arg) semanticEnv)
        q hq)
  | function fn f rest krest hfn hrest ih =>
      exact ih (semanticBind_root_bot D₀ j₀
        (semanticUnfold (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) f)
        q hq)

/-- External choice at a related state is presented-complete once both
children are and the stack continuation commutes with selection.
Root-strictness is free from `stackRel_root_bot`. -/
theorem extern_related_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.extern left right))
    (hrel : ChannelConfigRel D₀ j₀ realize s answer)
    (hcommute :
      ∀ semanticEnv k,
        EnvRel D₀ j₀ realize s.env semanticEnv →
        StackRel D₀ j₀ realize s.stack k →
        ∀ selected,
          selectBranch selected
              (k (interp (hardwarePrimitive D₀ j₀ realize)
                (.extern left right) semanticEnv)) =
            k (selectBranch selected
              (interp (hardwarePrimitive D₀ j₀ realize)
                (.extern left right) semanticEnv)))
    (hleft :
      ∀ semanticEnv k,
        EnvRel D₀ j₀ realize s.env semanticEnv →
        StackRel D₀ j₀ realize s.stack k →
        PresentedChannelConfigCompleteness D₀ j₀ realize
          {s with control := .term left}
          (k (interp (hardwarePrimitive D₀ j₀ realize) left
            semanticEnv)))
    (hright :
      ∀ semanticEnv k,
        EnvRel D₀ j₀ realize s.env semanticEnv →
        StackRel D₀ j₀ realize s.stack k →
        PresentedChannelConfigCompleteness D₀ j₀ realize
          {s with control := .term right}
          (k (interp (hardwarePrimitive D₀ j₀ realize) right
            semanticEnv))) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  obtain ⟨semanticEnv, k, henv, hstack, rfl⟩ :=
    channelConfigRel_term_inv D₀ j₀ hc hrel
  have hroot :
      k (interp (hardwarePrimitive D₀ j₀ realize) (.extern left right)
          semanticEnv) 0 =
        ⊥ := by
    have hextern0 :
        interp (hardwarePrimitive D₀ j₀ realize) (.extern left right)
            semanticEnv 0 =
          ⊥ := by
      rw [interp_extern_apply]
      exact TTContinuation.externalChoice_root_bot _ _
    exact stackRel_root_bot D₀ j₀ hstack hextern0
  refine
    { related := hrel
      complete :=
        PresentedChannelTreeCompleteness.congr
          (show {s with control := .term (.extern left right)} = s from
            ChannelConfig.ext hc.symm rfl rfl rfl)
          rfl
          (extern_stacked_presentedChannelTreeCompleteness
            D₀ j₀ realize s left right semanticEnv k
            (hcommute semanticEnv k henv hstack)
            hroot
            (hleft semanticEnv k henv hstack).complete
            (hright semanticEnv k henv hstack).complete) }

/-- Extern under a single closure frame whose body is administrative
NoApp.  The body must not contain `extern`, otherwise selection would
reindex the residual heap through the closure unfolding. -/
theorem extern_under_closure_nil_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
    {x : Name} {body : Term (QubitPrimitive C)} {cloEnv : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.extern left right))
    (hs : s.stack = [.function (.closure x body cloEnv)])
    (hadmin : AdminNoApp body)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer)
    (hleft :
      ∀ semanticEnv k,
        EnvRel D₀ j₀ realize s.env semanticEnv →
        StackRel D₀ j₀ realize s.stack k →
        PresentedChannelConfigCompleteness D₀ j₀ realize
          {s with control := .term left}
          (k (interp (hardwarePrimitive D₀ j₀ realize) left
            semanticEnv)))
    (hright :
      ∀ semanticEnv k,
        EnvRel D₀ j₀ realize s.env semanticEnv →
        StackRel D₀ j₀ realize s.stack k →
        PresentedChannelConfigCompleteness D₀ j₀ realize
          {s with control := .term right}
          (k (interp (hardwarePrimitive D₀ j₀ realize) right
            semanticEnv))) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  refine extern_related_presentedChannelConfigCompleteness
    D₀ j₀ realize hc hrel ?_ hleft hright
  · intro semanticEnv k henv hstack selected
    rw [hs] at hstack
    cases hstack
    case function f krest hfn hrest =>
      cases hrest
      cases hfn
      case closure cloSem _ =>
        have hunfold :
            ∀ d, CoordinateConstant
              (semanticUnfold (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀)
                (lambdaValue (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) x
                  (interp (hardwarePrimitive D₀ j₀ realize) body)
                  cloSem)
                d) := by
          intro d
          rw [semanticUnfold_lambdaValue]
          exact adminNoApp_interp_coordinateConstant D₀ j₀ realize
            hadmin
            (envUpdate (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) x (cloSem, d))
        simp only [id]
        exact semanticBind_select_of_unfold_constant D₀ j₀ _ hunfold
          (interp (hardwarePrimitive D₀ j₀ realize)
            (.extern left right) semanticEnv)
          selected

/-- Extern under a single recursive-closure frame whose body is
administrative NoApp.  This is the recursive analogue of
`extern_under_closure_nil_presentedChannelConfigCompleteness`; the
coordinate-constancy side condition is essential. -/
theorem extern_under_recClosure_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {left right : Term (QubitPrimitive C)}
    {self x : Name} {body : Term (QubitPrimitive C)}
    {cloEnv : RuntimeEnv C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.extern left right))
    (hs : s.stack = [.function (.recClosure self x body cloEnv)])
    (hadmin : AdminNoApp body)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer)
    (hleft :
      ∀ semanticEnv k,
        EnvRel D₀ j₀ realize s.env semanticEnv →
        StackRel D₀ j₀ realize s.stack k →
        PresentedChannelConfigCompleteness D₀ j₀ realize
          {s with control := .term left}
          (k (interp (hardwarePrimitive D₀ j₀ realize) left
            semanticEnv)))
    (hright :
      ∀ semanticEnv k,
        EnvRel D₀ j₀ realize s.env semanticEnv →
        StackRel D₀ j₀ realize s.stack k →
        PresentedChannelConfigCompleteness D₀ j₀ realize
          {s with control := .term right}
          (k (interp (hardwarePrimitive D₀ j₀ realize) right
            semanticEnv))) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  refine extern_related_presentedChannelConfigCompleteness
    D₀ j₀ realize hc hrel ?_ hleft hright
  · intro semanticEnv k henv hstack selected
    rw [hs] at hstack
    cases hstack
    case function f krest hfn hrest =>
      cases hrest
      cases hfn
      case recClosure recSem _ =>
        have hunfold :
            ∀ d, CoordinateConstant
              (semanticUnfold (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀)
                (recLambdaValue (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) self x
                  (interp (hardwarePrimitive D₀ j₀ realize) body)
                  recSem)
                d) := by
          intro d
          rw [semanticUnfold_recLambdaValue]
          exact adminNoApp_interp_coordinateConstant D₀ j₀ realize
            hadmin
            (envUpdate (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) x
              (envUpdate (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀) self
                (recSem,
                  recLambdaValue (Q := TTExternalContinuationPower 2)
                    (D₀ := D₀) (j₀ := j₀) self x
                    (interp (hardwarePrimitive D₀ j₀ realize) body)
                    recSem),
                d))
        simp only [id]
        exact semanticBind_select_of_unfold_constant D₀ j₀ _ hunfold
          (interp (hardwarePrimitive D₀ j₀ realize)
            (.extern left right) semanticEnv)
          selected

/-- A value under a single closure frame betas to the body at the empty
stack.  Application-free bodies are then presented by empty-stack NoApp. -/
theorem value_under_closure_nil_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {arg : RuntimeValue C} {x : Name}
    {body : Term (QubitPrimitive C)} {cloEnv : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .value arg)
    (hs : s.stack = [.function (.closure x body cloEnv)])
    (hnoapp : NoApp body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsEq :
      {s with
        control := .value arg
        stack := .function (.closure x body cloEnv) :: []} = s :=
    ChannelConfig.ext hc.symm rfl hs.symm rfl
  have hrel' : ChannelConfigRel D₀ j₀ realize
      {s with
        control := .value arg
        stack := .function (.closure x body cloEnv) :: []}
      answer :=
    hsEq.symm ▸ hrel
  have hrelBody :=
    channel_config_beta D₀ j₀ (s := s) (x := x) (body := body)
      (closureEnv := cloEnv) (arg := arg) (rest := []) hrel'
  let sBody : ChannelConfig C :=
    {s with
      control := .term body
      env := RuntimeEnv.bind x arg cloEnv
      stack := []}
  have hstepBeta : ChannelInternalStep s sBody := by
    have happ :
        ChannelInternalStep
          {s with
            control := .value arg
            stack := .function (.closure x body cloEnv) :: []}
          sBody :=
      ChannelInternalStep.beta (s := s) (x := x) (body := body)
        (closureEnv := cloEnv) (arg := arg) (rest := [])
    exact hsEq.symm ▸ happ
  have hscopedBody : ChannelConfig.WellScoped sBody :=
    ChannelInternalStep.preserve_wellScoped hstepBeta hscoped
  obtain ⟨semanticEnv, k, henv, hstack, heq⟩ :=
    channelConfigRel_term_inv D₀ j₀ (code := body) rfl hrelBody
  cases hstack
  have hchild :
      PresentedChannelConfigCompleteness D₀ j₀ realize sBody answer :=
    { related := hrelBody
      complete :=
        PresentedChannelTreeCompleteness.congr rfl heq.symm
          (empty_stack_noapp_presentedChannelTreeCompleteness
            D₀ j₀ realize hnoapp (s := sBody) rfl rfl hscopedBody
            henv) }
  exact beta_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := x) (body := body) (closureEnv := cloEnv)
    (arg := arg) (rest := []) hc hs hrel hchild

/-- Pauli-X under a single closure frame applies the operation, then
betas the payload into an application-free body. -/
theorem pauliX_under_closure_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {value : C} {x : Name}
    {body : Term (QubitPrimitive C)} {cloEnv : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack = [.function (.closure x body cloEnv)])
    (hnoapp : NoApp body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsPx :
      {s with control := .term (.prim (.pauliX value))} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  obtain ⟨semanticEnv, kStack, henv, hstack, rfl⟩ :=
    channelConfigRel_term_inv D₀ j₀ hc hrel
  rw [hs] at hstack
  cases hstack
  case function f krest hfn hrest =>
    cases hrest
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
        ((fun ma =>
          id (semanticBind (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)
            (semanticUnfold (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) f) ma))
          (semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) (realize value))) :=
      ⟨semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) (realize value),
        fun ma =>
          id (semanticBind (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)
            (semanticUnfold (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) f) ma),
        ControlRel.value _ _ s.env
          (payload_related D₀ j₀ realize value),
        hs.symm ▸
          StackRel.function (.closure x body cloEnv) f [] id hfn
            StackRel.nil, rfl⟩
    have hval :=
      value_under_closure_nil_presentedChannelConfigCompleteness
        D₀ j₀ realize (s := sVal) (arg := .payload value)
        (x := x) (body := body) (cloEnv := cloEnv) rfl hs
        hnoapp hscopedVal hrelVal
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
    have hchildCoord :
        semanticBind (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)
            (semanticUnfold (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) f)
            (semanticUnit (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) (realize value))
            (HardwareAdequacy.encodePath selectors i) kξ =
          sSup (channelTreeResults D₀ j₀ realize sVal selectors i
            kξ) := by
      simp only [id] at hchildEq
      rw [← selectPath_semanticBind, hchildEq]
    simp only [id]
    rw [hden, selectPath_semanticBind,
      semanticBind_ofOperation_eval D₀ j₀
        (semanticUnfold (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) f)
        Qubit.pauliXOp (realize value),
      hchildCoord, embed_ofOperation_const_sSup]
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

/-- A return under a single closure frame betas to the body at the empty
stack.  Application-free bodies are then presented by empty-stack NoApp. -/
theorem ret_under_closure_nil_presentedChannelConfigCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {value : C} {x : Name}
    {body : Term (QubitPrimitive C)} {cloEnv : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.ret value)))
    (hs : s.stack = [.function (.closure x body cloEnv)])
    (hnoapp : NoApp body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsRet :
      {s with control := .term (.prim (.ret value))} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelRet : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.prim (.ret value))} answer :=
    hsRet.symm ▸ hrel
  have hrelVal :=
    channel_config_return D₀ j₀ hrelRet
  have hstackEq :
      {s with control := .value (.payload value)} =
        {s with
          control := .value (.payload value)
          stack := .function (.closure x body cloEnv) :: []} :=
    ChannelConfig.ext rfl rfl hs rfl
  have hrelVal' : ChannelConfigRel D₀ j₀ realize
      {s with
        control := .value (.payload value)
        stack := .function (.closure x body cloEnv) :: []}
      answer :=
    hstackEq ▸ hrelVal
  have hrelBody :=
    channel_config_beta D₀ j₀ (s := s) (x := x) (body := body)
      (closureEnv := cloEnv) (arg := .payload value) (rest := [])
      hrelVal'
  let sVal : ChannelConfig C :=
    {s with control := .value (.payload value)}
  let sBody : ChannelConfig C :=
    {s with
      control := .term body
      env := RuntimeEnv.bind x (.payload value) cloEnv
      stack := []}
  have hstepRet : ChannelInternalStep s sVal := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.prim (.ret value))} sVal :=
      ChannelInternalStep.returnPrimitive (s := s) (value := value)
    have hsrc : s = {s with control := .term (.prim (.ret value))} :=
      ChannelConfig.ext hc rfl rfl rfl
    exact hsrc.symm ▸ happ
  have hstepBeta : ChannelInternalStep sVal sBody := by
    have happ :
        ChannelInternalStep
          {sVal with
            control := .value (.payload value)
            stack := .function (.closure x body cloEnv) :: []}
          sBody :=
      ChannelInternalStep.beta (s := sVal) (x := x) (body := body)
        (closureEnv := cloEnv) (arg := .payload value) (rest := [])
    have hsrc :
        sVal =
          {sVal with
            control := .value (.payload value)
            stack := .function (.closure x body cloEnv) :: []} :=
      ChannelConfig.ext rfl rfl hs rfl
    exact hsrc.symm ▸ happ
  have hscopedBody : ChannelConfig.WellScoped sBody :=
    ChannelInternalStep.preserve_wellScoped hstepBeta
      (ChannelInternalStep.preserve_wellScoped hstepRet hscoped)
  obtain ⟨semanticEnv, k, henv, hstack, heq⟩ :=
    channelConfigRel_term_inv D₀ j₀ (code := body) rfl hrelBody
  cases hstack
  have hchild :
      PresentedChannelConfigCompleteness D₀ j₀ realize sBody answer :=
    { related := hrelBody
      complete :=
        PresentedChannelTreeCompleteness.congr rfl heq.symm
          (empty_stack_noapp_presentedChannelTreeCompleteness
            D₀ j₀ realize hnoapp (s := sBody) rfl rfl hscopedBody
            henv) }
  have hval :
      PresentedChannelConfigCompleteness D₀ j₀ realize sVal answer :=
    beta_presentedChannelConfigCompleteness D₀ j₀ realize
      (s := sVal) (x := x) (body := body) (closureEnv := cloEnv)
      (arg := .payload value) (rest := []) rfl hs hrelVal hchild
  exact return_presentedChannelConfigCompleteness D₀ j₀ realize
    hc hrel hval

/-- Administrative NoApp terms under a single closure frame are
presented-complete when the body is application-free. -/
theorem admin_noapp_under_closure_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)} {x : Name}
    {body : Term (QubitPrimitive C)} {cloEnv : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack = [.function (.closure x body cloEnv)])
    (hnoapp : NoApp body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  induction code generalizing s answer with
  | var y =>
      have hctl := hscoped.left
      rw [hc] at hctl
      obtain ⟨v, hlookup⟩ := hctl.right y (by simp [free])
      have hsVar :
          {s with control := .term (.var y)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelVar : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.var y)} answer :=
        hsVar.symm ▸ hrel
      have hrelVal :=
        channel_config_variable D₀ j₀ hlookup hrelVar
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value v} :=
        ⟨⟨hctl.left, hctl.left y v hlookup⟩, hscoped.right⟩
      have hval :=
        value_under_closure_nil_presentedChannelConfigCompleteness
          D₀ j₀ realize (s := {s with control := .value v})
          (arg := v) (x := x) (body := body) (cloEnv := cloEnv)
          rfl hs hnoapp hscopedVal hrelVal
      exact variable_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hlookup hrel hval
  | app _ _ =>
      exact False.elim hadmin
  | lam y M _ih =>
      have hsLam :
          {s with control := .term (.lam y M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelLam : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.lam y M)} answer :=
        hsLam.symm ▸ hrel
      have hrelVal :=
        channel_config_lambda D₀ j₀ (s := s) hrelLam
      have hstepLam : ChannelInternalStep s
          {s with control := .value (.closure y M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.lam y M)}
              {s with control := .value (.closure y M s.env)} :=
          ChannelInternalStep.lambda (s := s) (x := y) (body := M)
        exact hsLam.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.closure y M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepLam hscoped
      have hval :=
        value_under_closure_nil_presentedChannelConfigCompleteness
          D₀ j₀ realize
          (s := {s with control := .value (.closure y M s.env)})
          (arg := .closure y M s.env) (x := x) (body := body)
          (cloEnv := cloEnv) rfl hs hnoapp hscopedVal hrelVal
      exact lambda_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hrel hval
  | recLam self y M _ih =>
      have hsRec :
          {s with control := .term (.recLam self y M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelRec : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.recLam self y M)} answer :=
        hsRec.symm ▸ hrel
      have hrelVal :=
        channel_config_recursive D₀ j₀ (s := s) hrelRec
      have hstepRec : ChannelInternalStep s
          {s with control := .value (.recClosure self y M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.recLam self y M)}
              {s with control := .value (.recClosure self y M s.env)} :=
          ChannelInternalStep.recursive (s := s) (self := self)
            (arg := y) (body := M)
        exact hsRec.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.recClosure self y M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepRec hscoped
      have hval :=
        value_under_closure_nil_presentedChannelConfigCompleteness
          D₀ j₀ realize
          (s := {s with control := .value (.recClosure self y M s.env)})
          (arg := .recClosure self y M s.env) (x := x) (body := body)
          (cloEnv := cloEnv) rfl hs hnoapp hscopedVal hrelVal
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
          exact ret_under_closure_nil_presentedChannelConfigCompleteness
            D₀ j₀ realize hc hs hnoapp hscoped hrel
      | pauliX value =>
          exact pauliX_under_closure_nil_presentedChannelConfigCompleteness
            D₀ j₀ realize hc hs hnoapp hscoped hrel
      | measureZ _ _ =>
          exact False.elim hadmin

/-- A value under a single recursive-closure frame recBetas to the body
at the empty stack. -/
theorem value_under_recClosure_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {arg : RuntimeValue C} {self x : Name}
    {body : Term (QubitPrimitive C)} {cloEnv : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .value arg)
    (hs : s.stack = [.function (.recClosure self x body cloEnv)])
    (hnoapp : NoApp body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsEq :
      {s with
        control := .value arg
        stack :=
          .function (.recClosure self x body cloEnv) :: []} = s :=
    ChannelConfig.ext hc.symm rfl hs.symm rfl
  have hrel' : ChannelConfigRel D₀ j₀ realize
      {s with
        control := .value arg
        stack :=
          .function (.recClosure self x body cloEnv) :: []}
      answer :=
    hsEq.symm ▸ hrel
  have hrelBody :=
    channel_config_recBeta D₀ j₀ (s := s) (self := self) (x := x)
      (body := body) (closureEnv := cloEnv) (arg := arg) (rest := [])
      hrel'
  let sBody : ChannelConfig C :=
    {s with
      control := .term body
      env :=
        RuntimeEnv.bind x arg
          (RuntimeEnv.bind self
            (.recClosure self x body cloEnv) cloEnv)
      stack := []}
  have hstepBeta : ChannelInternalStep s sBody := by
    have happ :
        ChannelInternalStep
          {s with
            control := .value arg
            stack :=
              .function (.recClosure self x body cloEnv) :: []}
          sBody :=
      ChannelInternalStep.recBeta (s := s) (self := self) (x := x)
        (body := body) (closureEnv := cloEnv) (arg := arg) (rest := [])
    exact hsEq.symm ▸ happ
  have hscopedBody : ChannelConfig.WellScoped sBody :=
    ChannelInternalStep.preserve_wellScoped hstepBeta hscoped
  obtain ⟨semanticEnv, k, henv, hstack, heq⟩ :=
    channelConfigRel_term_inv D₀ j₀ (code := body) rfl hrelBody
  cases hstack
  have hchild :
      PresentedChannelConfigCompleteness D₀ j₀ realize sBody answer :=
    { related := hrelBody
      complete :=
        PresentedChannelTreeCompleteness.congr rfl heq.symm
          (empty_stack_noapp_presentedChannelTreeCompleteness
            D₀ j₀ realize hnoapp (s := sBody) rfl rfl hscopedBody
            henv) }
  exact recBeta_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (self := self) (x := x) (body := body)
    (closureEnv := cloEnv) (arg := arg) (rest := []) hc hs hrel hchild

theorem ret_under_recClosure_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {value : C} {self x : Name}
    {body : Term (QubitPrimitive C)} {cloEnv : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.ret value)))
    (hs : s.stack = [.function (.recClosure self x body cloEnv)])
    (hnoapp : NoApp body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
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
      ChannelInternalStep.returnPrimitive (s := s) (value := value)
    exact hsRet.symm ▸ happ
  have hscopedVal : ChannelConfig.WellScoped
      {s with control := .value (.payload value)} :=
    ChannelInternalStep.preserve_wellScoped hstepRet hscoped
  have hval :=
    value_under_recClosure_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize
      (s := {s with control := .value (.payload value)})
      (arg := .payload value) (self := self) (x := x) (body := body)
      (cloEnv := cloEnv) rfl hs hnoapp hscopedVal hrelVal
  exact return_presentedChannelConfigCompleteness D₀ j₀ realize
    hc hrel hval

theorem pauliX_under_recClosure_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {value : C} {self x : Name}
    {body : Term (QubitPrimitive C)} {cloEnv : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack = [.function (.recClosure self x body cloEnv)])
    (hnoapp : NoApp body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsPx :
      {s with control := .term (.prim (.pauliX value))} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  obtain ⟨semanticEnv, kStack, henv, hstack, rfl⟩ :=
    channelConfigRel_term_inv D₀ j₀ hc hrel
  rw [hs] at hstack
  cases hstack
  case function f krest hfn hrest =>
    cases hrest
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
        ((fun ma =>
          id (semanticBind (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)
            (semanticUnfold (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) f) ma))
          (semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) (realize value))) :=
      ⟨semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) (realize value),
        fun ma =>
          id (semanticBind (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)
            (semanticUnfold (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) f) ma),
        ControlRel.value _ _ s.env
          (payload_related D₀ j₀ realize value),
        hs.symm ▸
          StackRel.function
            (.recClosure self x body cloEnv) f [] id hfn
            StackRel.nil, rfl⟩
    have hval :=
      value_under_recClosure_nil_presentedChannelConfigCompleteness
        D₀ j₀ realize (s := sVal) (arg := .payload value)
        (self := self) (x := x) (body := body) (cloEnv := cloEnv)
        rfl hs hnoapp hscopedVal hrelVal
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
    have hchildCoord :
        semanticBind (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)
            (semanticUnfold (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) f)
            (semanticUnit (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) (realize value))
            (HardwareAdequacy.encodePath selectors i) kξ =
          sSup (channelTreeResults D₀ j₀ realize sVal selectors i
            kξ) := by
      simp only [id] at hchildEq
      rw [← selectPath_semanticBind, hchildEq]
    simp only [id]
    rw [hden, selectPath_semanticBind,
      semanticBind_ofOperation_eval D₀ j₀
        (semanticUnfold (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) f)
        Qubit.pauliXOp (realize value),
      hchildCoord, embed_ofOperation_const_sSup]
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

/-- Administrative NoApp terms under a single recursive-closure frame. -/
theorem admin_noapp_under_recClosure_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {self x : Name} {body : Term (QubitPrimitive C)}
    {cloEnv : RuntimeEnv C} {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack = [.function (.recClosure self x body cloEnv)])
    (hnoapp : NoApp body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  induction code generalizing s answer with
  | var y =>
      have hctl := hscoped.left
      rw [hc] at hctl
      obtain ⟨v, hlookup⟩ := hctl.right y (by simp [free])
      have hsVar :
          {s with control := .term (.var y)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelVar : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.var y)} answer :=
        hsVar.symm ▸ hrel
      have hrelVal :=
        channel_config_variable D₀ j₀ hlookup hrelVar
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value v} :=
        ⟨⟨hctl.left, hctl.left y v hlookup⟩, hscoped.right⟩
      have hval :=
        value_under_recClosure_nil_presentedChannelConfigCompleteness
          D₀ j₀ realize (s := {s with control := .value v})
          (arg := v) (self := self) (x := x) (body := body)
          (cloEnv := cloEnv) rfl hs hnoapp hscopedVal hrelVal
      exact variable_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hlookup hrel hval
  | app _ _ =>
      exact False.elim hadmin
  | lam y M _ih =>
      have hsLam :
          {s with control := .term (.lam y M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelLam : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.lam y M)} answer :=
        hsLam.symm ▸ hrel
      have hrelVal :=
        channel_config_lambda D₀ j₀ (s := s) hrelLam
      have hstepLam : ChannelInternalStep s
          {s with control := .value (.closure y M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.lam y M)}
              {s with control := .value (.closure y M s.env)} :=
          ChannelInternalStep.lambda (s := s) (x := y) (body := M)
        exact hsLam.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.closure y M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepLam hscoped
      have hval :=
        value_under_recClosure_nil_presentedChannelConfigCompleteness
          D₀ j₀ realize
          (s := {s with control := .value (.closure y M s.env)})
          (arg := .closure y M s.env) (self := self) (x := x)
          (body := body) (cloEnv := cloEnv) rfl hs hnoapp hscopedVal
          hrelVal
      exact lambda_presentedChannelConfigCompleteness D₀ j₀ realize
        hc hrel hval
  | recLam self' y M _ih =>
      have hsRec :
          {s with control := .term (.recLam self' y M)} = s :=
        ChannelConfig.ext hc.symm rfl rfl rfl
      have hrelRec : ChannelConfigRel D₀ j₀ realize
          {s with control := .term (.recLam self' y M)} answer :=
        hsRec.symm ▸ hrel
      have hrelVal :=
        channel_config_recursive D₀ j₀ (s := s) hrelRec
      have hstepRec : ChannelInternalStep s
          {s with control := .value (.recClosure self' y M s.env)} := by
        have happ :
            ChannelInternalStep
              {s with control := .term (.recLam self' y M)}
              {s with
                control := .value (.recClosure self' y M s.env)} :=
          ChannelInternalStep.recursive (s := s) (self := self')
            (arg := y) (body := M)
        exact hsRec.symm ▸ happ
      have hscopedVal : ChannelConfig.WellScoped
          {s with control := .value (.recClosure self' y M s.env)} :=
        ChannelInternalStep.preserve_wellScoped hstepRec hscoped
      have hval :=
        value_under_recClosure_nil_presentedChannelConfigCompleteness
          D₀ j₀ realize
          (s :=
            {s with control := .value (.recClosure self' y M s.env)})
          (arg := .recClosure self' y M s.env) (self := self)
          (x := x) (body := body) (cloEnv := cloEnv) rfl hs hnoapp
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
          exact
            ret_under_recClosure_nil_presentedChannelConfigCompleteness
              D₀ j₀ realize hc hs hnoapp hscoped hrel
      | pauliX value =>
          exact
            pauliX_under_recClosure_nil_presentedChannelConfigCompleteness
              D₀ j₀ realize hc hs hnoapp hscoped hrel
      | measureZ _ _ =>
          exact False.elim hadmin

/-- Closed `app (lam x body) (ret c)` with an application-free body is
presented-complete at a normalized start. -/
theorem closed_lam_ret_noapp_presented_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x : Name) (body : Term (QubitPrimitive C)) (value : C)
    (hclosed : Closed (.app (.lam x body) (.prim (.ret value))))
    (hnoapp : NoApp body)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.app (.lam x body) (.prim (.ret value)))
        quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.lam x body) (.prim (.ret value))) semanticEnv) := by
  let code : Term (QubitPrimitive C) :=
    .app (.lam x body) (.prim (.ret value))
  let s : ChannelConfig C := initialChannelConfig code quantum
  have hc : s.control = .term code := rfl
  have hrel :=
    initialChannelConfig_related D₀ j₀ realize code quantum semanticEnv
  have hscoped :=
    initialChannelConfig_wellScoped hclosed quantum
  have hsApp :
      {s with control := .term (.app (.lam x body) (.prim (.ret value)))} =
        s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app (.lam x body) (.prim (.ret value)))}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    hsApp.symm ▸ hrel
  have hrelLam :=
    channel_config_application D₀ j₀ (s := s)
      (fn := .lam x body) (arg := .prim (.ret value)) hrelApp
  have hrelClo :=
    channel_config_lambda D₀ j₀
      (s := {s with stack := .argument (.prim (.ret value)) s.env :: s.stack})
      hrelLam
  have hrelArg :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {s with
          control := .value (.closure x body s.env)
          stack := .argument (.prim (.ret value)) s.env :: s.stack})
      (fn := .closure x body s.env) (arg := .prim (.ret value))
      (callEnv := s.env) (rest := s.stack) hrelClo
  let sArg : ChannelConfig C :=
    {s with
      control := .term (.prim (.ret value))
      stack := .function (.closure x body s.env) :: s.stack}
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.lam x body)
        stack := .argument (.prim (.ret value)) s.env :: s.stack} := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app (.lam x body) (.prim (.ret value)))}
          {s with
            control := .term (.lam x body)
            stack := .argument (.prim (.ret value)) s.env :: s.stack} :=
      ChannelInternalStep.application (s := s) (fn := .lam x body)
        (arg := .prim (.ret value))
    exact hsApp.symm ▸ happ
  have hstepLam : ChannelInternalStep
      {s with
        control := .term (.lam x body)
        stack := .argument (.prim (.ret value)) s.env :: s.stack}
      {s with
        control := .value (.closure x body s.env)
        stack := .argument (.prim (.ret value)) s.env :: s.stack} :=
    ChannelInternalStep.lambda
      (s := {s with stack := .argument (.prim (.ret value)) s.env :: s.stack})
      (x := x) (body := body)
  have hstepArg : ChannelInternalStep
      {s with
        control := .value (.closure x body s.env)
        stack := .argument (.prim (.ret value)) s.env :: s.stack}
      sArg :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {s with
          control := .value (.closure x body s.env)
          stack := .argument (.prim (.ret value)) s.env :: s.stack})
      (fn := .closure x body s.env) (arg := .prim (.ret value))
      (callEnv := s.env) (rest := s.stack)
  have hscopedArg : ChannelConfig.WellScoped sArg :=
    ChannelInternalStep.preserve_wellScoped hstepArg
      (ChannelInternalStep.preserve_wellScoped hstepLam
        (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
  have hsArg : sArg.stack = [.function (.closure x body s.env)] := by
    simp [sArg, s, initialChannelConfig, ofConfig, initialConfig]
  have harg :
      PresentedChannelConfigCompleteness D₀ j₀ realize sArg
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    ret_under_closure_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize (s := sArg) (value := value) (x := x) (body := body)
      (cloEnv := s.env) rfl hsArg hnoapp hscopedArg
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term (.prim (.ret value))
              env := s.env
              stack := .function (.closure x body s.env) :: s.stack}
            _
        exact hrelArg)
  exact (stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := x) (body := body) (arg := .prim (.ret value))
    hc hrel harg).complete

/-- Token adequacy for closed `app (lam x body) (ret c)` with an
application-free body. -/
theorem closed_lam_ret_noapp_presented_token_adequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x : Name) (body : Term (QubitPrimitive C)) (value : C)
    (hclosed : Closed (.app (.lam x body) (.prim (.ret value))))
    (hnoapp : NoApp body)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize)
          (.app (.lam x body) (.prim (.ret value))) semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig
            (.app (.lam x body) (.prim (.ret value))) quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig (.app (.lam x body) (.prim (.ret value)))
      quantum)
    (interp (hardwarePrimitive D₀ j₀ realize)
      (.app (.lam x body) (.prim (.ret value))) semanticEnv)
    (closed_lam_ret_noapp_presented_channelTreeCompleteness D₀ j₀ realize
      x body value hclosed hnoapp quantum semanticEnv)
    selectors ξ k hk i token

/-- Closed `app (lam x body) arg` is presented-complete when the body is
application-free and the argument evaluates by identity steps and intern. -/
theorem closed_lam_admin_noapp_presented_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x : Name) (body arg : Term (QubitPrimitive C))
    (hclosed : Closed (.app (.lam x body) arg))
    (hnoapp : NoApp body) (hadmin : AdminNoApp arg)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.app (.lam x body) arg) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.lam x body) arg) semanticEnv) := by
  let code : Term (QubitPrimitive C) := .app (.lam x body) arg
  let s : ChannelConfig C := initialChannelConfig code quantum
  have hc : s.control = .term code := rfl
  have hrel :=
    initialChannelConfig_related D₀ j₀ realize code quantum semanticEnv
  have hscoped :=
    initialChannelConfig_wellScoped hclosed quantum
  have hsApp :
      {s with control := .term (.app (.lam x body) arg)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app (.lam x body) arg)}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
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
      ChannelInternalStep.application (s := s) (fn := .lam x body)
        (arg := arg)
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
  have hsArg : sArg.stack = [.function (.closure x body s.env)] := by
    simp [sArg, s, initialChannelConfig, ofConfig, initialConfig]
  have harg :
      PresentedChannelConfigCompleteness D₀ j₀ realize sArg
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    admin_noapp_under_closure_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize (s := sArg) (code := arg) (x := x) (body := body)
      (cloEnv := s.env) hadmin rfl hsArg hnoapp hscopedArg
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term arg
              env := s.env
              stack := .function (.closure x body s.env) :: s.stack}
            _
        exact hrelArg)
  exact (stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := x) (body := body) (arg := arg)
    hc hrel harg).complete

/-- Token adequacy for closed `app (lam x body) arg` with an
application-free body and an administrative NoApp argument. -/
theorem closed_lam_admin_noapp_presented_token_adequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x : Name) (body arg : Term (QubitPrimitive C))
    (hclosed : Closed (.app (.lam x body) arg))
    (hnoapp : NoApp body) (hadmin : AdminNoApp arg)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize)
          (.app (.lam x body) arg) semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig (.app (.lam x body) arg) quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig (.app (.lam x body) arg) quantum)
    (interp (hardwarePrimitive D₀ j₀ realize)
      (.app (.lam x body) arg) semanticEnv)
    (closed_lam_admin_noapp_presented_channelTreeCompleteness
      D₀ j₀ realize x body arg hclosed hnoapp hadmin quantum semanticEnv)
    selectors ξ k hk i token

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

theorem measureZ_map_bind {D : Type} [Preorder D]
    (f : Bool → D) (ν : D → FiniteInstrumentComp 2 PUnit.{1}) :
    (Qubit.measureZComp.map f).bind ν =
      Qubit.measureZComp.bind (fun b => ν (f b)) :=
  rfl

theorem aggregateDerives_measureZ_map_of_measurement {D : Type}
    [CompleteLattice D]
    (f : Bool → D)
    (sources : Bool → TTObservationToken 2)
    (target : TTObservationToken 2)
    (h : MeasurementDerives (sources false) (sources true) target) :
    TTTokenTheory.AggregateDerives (Qubit.measureZComp.map f) sources
      target := by
  intro ν hν
  have hholds :=
    h (ν (f false)) (ν (f true)) (hν false) (hν true)
  have hif :
      (fun b : Bool => if b then ν (f true) else ν (f false)) =
        fun b => ν (f b) := by
    funext b
    cases b <;> rfl
  change TTObservationToken.Holds _ target
    ((Qubit.measureZComp.map f).bind ν)
  rw [measureZ_map_bind, ← hif]
  exact hholds

theorem aggregateDerives_measureZ_map_to_measurement {D : Type}
    [CompleteLattice D]
    (f : Bool → D)
    (hf : f false ≠ f true)
    (sources : Bool → TTObservationToken 2)
    (target : TTObservationToken 2)
    (h : TTTokenTheory.AggregateDerives (Qubit.measureZComp.map f) sources
      target) :
    MeasurementDerives (sources false) (sources true) target := by
  intro μ ν hμ hν
  let g : D → FiniteInstrumentComp 2 PUnit.{1} :=
    fun x => if x = f false then μ else if x = f true then ν else μ
  have hg0 : g (f false) = μ := if_pos rfl
  have hg1 : g (f true) = ν := by
    have hne : ¬ f true = f false := fun heq => hf heq.symm
    simp [g, hne]
  have hholds : ∀ o : Bool,
      TTObservationToken.Holds resultCode (sources o)
        (g (f o)) := by
    intro o
    cases o
    · simpa [hg0] using hμ
    · simpa [hg1] using hν
  have htarget := h g (by
    intro o
    change TTObservationToken.Holds _ (sources o) (g (f o))
    exact hholds o)
  have hbind :
      (Qubit.measureZComp.map f).bind g =
        Qubit.measureZComp.bind
          (fun b => if b then ν else μ) := by
    rw [measureZ_map_bind]
    apply congrArg Qubit.measureZComp.bind
    funext b
    cases b
    · exact hg0
    · exact hg1
  change TTObservationToken.Holds _ target
    (Qubit.measureZComp.bind (fun b => if b then ν else μ))
  rw [← hbind]
  exact htarget

theorem embed_measureZ_map_eq_measurementResult_of_ne {D : Type}
    [CompleteLattice D]
    (f : Bool → D) (hf : f false ≠ f true)
    (k : ScottMap D (TTResult 2)) :
    embed (Qubit.measureZComp.map f) k =
      measurementResult (k (f false)) (k (f true)) := by
  apply RoundedTheory.ext
  ext t
  constructor
  · intro ht
    obtain ⟨sources, hsources, target, hderives, htt⟩ :=
      (TTTokenTheory.mem_aggregateResult
        (Qubit.measureZComp.map f) k t).mp (by
          simpa [embed] using ht)
    apply (mem_measurementResult (k (f false)) (k (f true)) t).2
    refine ⟨sources false, hsources false, sources true, hsources true,
      target, ?_, htt⟩
    exact aggregateDerives_measureZ_map_to_measurement f hf sources
      target hderives
  · intro ht
    obtain ⟨zero, hzero, one, hone, target, hderives, htt⟩ :=
      (mem_measurementResult (k (f false)) (k (f true)) t).mp ht
    apply (TTTokenTheory.mem_aggregateResult
        (Qubit.measureZComp.map f) k t).2
    refine ⟨fun b : Bool => if b then one else zero, ?_, target, ?_, htt⟩
    · intro o
      cases o
      · exact hzero
      · exact hone
    · exact aggregateDerives_measureZ_map_of_measurement f
        (fun b : Bool => if b then one else zero) target hderives

theorem embed_measureZ_map_eq_measurementResult_presented {D : Type}
    [CompleteLattice D]
    (f : Bool → D)
    (ξ : D → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap D (TTResult 2))
    (hk : ∀ x, k x = (ξ x).satisfiedTTTheory resultCode) :
    embed (Qubit.measureZComp.map f) k =
      measurementResult (k (f false)) (k (f true)) := by
  have hsat :=
    TTPhysicalEmbedding.embed_satisfied (Qubit.measureZComp.map f) ξ k
      (fun _ => hk _)
  have hif :
      (fun b : Bool => ξ (f b)) =
        fun b => if b then ξ (f true) else ξ (f false) := by
    funext b
    cases b <;> rfl
  calc
    embed (Qubit.measureZComp.map f) k =
        ((Qubit.measureZComp.map f).bind ξ).satisfiedTTTheory resultCode :=
      hsat
    _ = (Qubit.measureZComp.bind (fun b => ξ (f b))).satisfiedTTTheory
          resultCode := by
      rw [measureZ_map_bind]
    _ = (Qubit.measureZComp.bind
          (fun b => if b then ξ (f true) else ξ (f false))).satisfiedTTTheory
          resultCode := by
      rw [hif]
    _ = measurementResult
          ((ξ (f false)).satisfiedTTTheory resultCode)
          ((ξ (f true)).satisfiedTTTheory resultCode) :=
      (measurementResult_satisfied (ξ (f false)) (ξ (f true))).symm
    _ = measurementResult (k (f false)) (k (f true)) := by
      rw [hk (f false), hk (f true)]

theorem measurementResult_sSup (A B : Set (TTResult 2)) :
    measurementResult (sSup A) (sSup B) =
      sSup ((fun p : TTResult 2 × TTResult 2 =>
        measurementResult p.1 p.2) '' (A ×ˢ B)) := by
  apply RoundedTheory.ext
  ext t
  constructor
  · intro ht
    change t ∈
      (measurementResult (sSup A : TTResult 2) (sSup B : TTResult 2)) at ht
    obtain ⟨zero, hzero, one, hone, target, hderives, htt⟩ :=
      (mem_measurementResult _ _ t).mp ht
    change zero ∈ (sSup A : TTResult 2) at hzero
    change one ∈ (sSup B : TTResult 2) at hone
    rw [RoundedTheory.mem_sSup] at hzero
    rw [RoundedTheory.mem_sSup] at hone
    obtain ⟨a, haA, hza⟩ := hzero
    obtain ⟨b, hbB, hob⟩ := hone
    change t ∈
      (sSup ((fun p : TTResult 2 × TTResult 2 =>
        measurementResult p.1 p.2) '' (A ×ˢ B)) : TTResult 2)
    rw [RoundedTheory.mem_sSup]
    refine ⟨measurementResult a b, ?_, ?_⟩
    · exact ⟨(a, b), ⟨haA, hbB⟩, rfl⟩
    · exact (mem_measurementResult a b t).2
        ⟨zero, hza, one, hob, target, hderives, htt⟩
  · intro ht
    change t ∈
      (sSup ((fun p : TTResult 2 × TTResult 2 =>
        measurementResult p.1 p.2) '' (A ×ˢ B)) : TTResult 2) at ht
    rw [RoundedTheory.mem_sSup] at ht
    obtain ⟨T, ⟨⟨a, b⟩, ⟨haA, hbB⟩, rfl⟩, htT⟩ := ht
    obtain ⟨zero, hza, one, hob, target, hderives, htt⟩ :=
      (mem_measurementResult a b t).mp htT
    apply (mem_measurementResult
        (sSup A : TTResult 2) (sSup B : TTResult 2) t).2
    refine ⟨zero, ?_, one, ?_, target, hderives, htt⟩
    · rw [RoundedTheory.mem_sSup]
      exact ⟨a, haA, hza⟩
    · rw [RoundedTheory.mem_sSup]
      exact ⟨b, hbB, hob⟩

theorem semanticBind_measureZ_eval_of_ne
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (h : ScottMap (HSemanticValue D₀ j₀) (HSemanticComp D₀ j₀))
    (f : Bool → HSemanticValue D₀ j₀)
    (hf : f false ≠ f true)
    (coord : ℕ)
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2)) :
    semanticBind (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) h
        (taggedEmbed (Qubit.measureZComp.map f))
        coord k =
      measurementResult
        (semanticBind (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) h
          (semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) (f false))
          coord k)
        (semanticBind (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) h
          (semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) (f true))
          coord k) := by
  change
      (TTContinuation.atCoordinate coord
        (TTContinuation.taggedBindScott (n := 2) h
          (taggedEmbed (Qubit.measureZComp.map f)))) k =
        measurementResult _ _
  rw [TTContinuation.taggedBind_atCoordinate, TTContinuation.bind_apply]
  change
      embed (Qubit.measureZComp.map f)
          (TTContinuation.continuation
            ((TTContinuation.atCoordinate coord).comp h) k) =
        measurementResult _ _
  rw [embed_measureZ_map_eq_measurementResult_of_ne f hf]
  congr 1

theorem measurementResult_bot_left (B : TTResult 2) :
    measurementResult ⊥ B = ⊥ := by
  apply le_antisymm
  · intro t ht
    obtain ⟨zero, hzero, _⟩ := (mem_measurementResult ⊥ B t).mp ht
    have hbot : (⊥ : TTResult 2) = sSup (∅ : Set (TTResult 2)) :=
      sSup_empty.symm
    rw [hbot, RoundedTheory.mem_sSup] at hzero
    obtain ⟨_, ⟨⟩, _⟩ := hzero
  · exact bot_le

theorem measurementResult_bot_right (A : TTResult 2) :
    measurementResult A ⊥ = ⊥ := by
  apply le_antisymm
  · intro t ht
    obtain ⟨_, _, one, hone, _⟩ := (mem_measurementResult A ⊥ t).mp ht
    have hbot : (⊥ : TTResult 2) = sSup (∅ : Set (TTResult 2)) :=
      sSup_empty.symm
    rw [hbot, RoundedTheory.mem_sSup] at hone
    obtain ⟨_, ⟨⟩, _⟩ := hone
  · exact bot_le

theorem measurementResult_le_embed_measureZ_map {D : Type}
    [CompleteLattice D]
    (f : Bool → D) (k : ScottMap D (TTResult 2)) :
    measurementResult (k (f false)) (k (f true)) ≤
      embed (Qubit.measureZComp.map f) k := by
  intro t ht
  obtain ⟨zero, hzero, one, hone, target, hderives, htt⟩ :=
    (mem_measurementResult (k (f false)) (k (f true)) t).mp ht
  apply (TTTokenTheory.mem_aggregateResult
      (Qubit.measureZComp.map f) k t).2
  refine ⟨fun b : Bool => if b then one else zero, ?_, target, ?_, htt⟩
  · intro o
    cases o
    · exact hzero
    · exact hone
  · exact aggregateDerives_measureZ_map_of_measurement f
      (fun b : Bool => if b then one else zero) target hderives

/-- Measure-Z under a single closure frame splits into the two payload
children, each of which still carries the function frame and then betas
into an application-free body.  The two realized payloads must be
distinct so `measureZ.map` can interpolate the two child instruments
independently. -/
theorem measureZ_under_closure_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {zeroValue oneValue : C} {x : Name}
    {body : Term (QubitPrimitive C)} {cloEnv : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.measureZ zeroValue oneValue)))
    (hs : s.stack = [.function (.closure x body cloEnv)])
    (hnoapp : NoApp body)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer)
    (hne : realize zeroValue ≠ realize oneValue) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  let sMz : ChannelConfig C :=
    {s with control := .term (.prim (.measureZ zeroValue oneValue))}
  have hsMz : sMz = s := ChannelConfig.ext hc.symm rfl rfl rfl
  obtain ⟨semanticEnv, kStack, henv, hstack, rfl⟩ :=
    channelConfigRel_term_inv D₀ j₀ hc hrel
  rw [hs] at hstack
  cases hstack
  case function f krest hfn hrest =>
    cases hrest
    let sZero : ChannelConfig C :=
      {s with
        control := .value (.payload zeroValue)
        quantum := applyOperation (measurementOperation false) s.quantum}
    let sOne : ChannelConfig C :=
      {s with
        control := .value (.payload oneValue)
        quantum := applyOperation (measurementOperation true) s.quantum}
    have hscopedZero : ChannelConfig.WellScoped sZero := by
      have hctl := hscoped.left
      rw [hc] at hctl
      exact ⟨⟨hctl.left, .payload zeroValue⟩, hscoped.right⟩
    have hscopedOne : ChannelConfig.WellScoped sOne := by
      have hctl := hscoped.left
      rw [hc] at hctl
      exact ⟨⟨hctl.left, .payload oneValue⟩, hscoped.right⟩
    have hstackFn : StackRel D₀ j₀ realize
        [.function (.closure x body cloEnv)]
        (fun ma =>
          id (semanticBind (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)
            (semanticUnfold (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) f) ma)) :=
      StackRel.function (.closure x body cloEnv) f [] id hfn
        StackRel.nil
    let childK : HSemanticComp D₀ j₀ → HSemanticComp D₀ j₀ :=
      fun ma =>
        id (semanticBind (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (semanticUnfold (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) f) ma)
    have hrelZero : ChannelConfigRel D₀ j₀ realize sZero
        (childK (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) (realize zeroValue))) :=
      ⟨semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) (realize zeroValue),
        childK,
        ControlRel.value _ _ s.env
          (payload_related D₀ j₀ realize zeroValue),
        hs.symm ▸ hstackFn, rfl⟩
    have hrelOne : ChannelConfigRel D₀ j₀ realize sOne
        (childK (semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) (realize oneValue))) :=
      ⟨semanticUnit (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) (realize oneValue),
        childK,
        ControlRel.value _ _ s.env
          (payload_related D₀ j₀ realize oneValue),
        hs.symm ▸ hstackFn, rfl⟩
    have hzero :=
      value_under_closure_nil_presentedChannelConfigCompleteness
        D₀ j₀ realize (s := sZero) (arg := .payload zeroValue)
        (x := x) (body := body) (cloEnv := cloEnv) rfl hs
        hnoapp hscopedZero hrelZero
    have hone :=
      value_under_closure_nil_presentedChannelConfigCompleteness
        D₀ j₀ realize (s := sOne) (arg := .payload oneValue)
        (x := x) (body := body) (cloEnv := cloEnv) rfl hs
        hnoapp hscopedOne hrelOne
    refine
      { related := hrel
        complete :=
          PresentedChannelTreeCompleteness.congr hsMz rfl
            { selected_result_eq_channelTree_sup_presented := ?_ } }
    intro selectors i ξ kξ hk
    have hzeroEq :=
      hzero.complete.selected_result_eq_channelTree_sup_presented
        selectors i ξ kξ hk
    have honeEq :=
      hone.complete.selected_result_eq_channelTree_sup_presented
        selectors i ξ kξ hk
    have hden :
        interp (hardwarePrimitive D₀ j₀ realize)
            (.prim (.measureZ zeroValue oneValue)) semanticEnv =
          taggedEmbed (Qubit.measureZComp.map
            (fun b => if b then realize oneValue else realize zeroValue)) := by
      simp [hardwarePrimitive_measureZ]
    let payload : Bool → HSemanticValue D₀ j₀ :=
      fun b => if b then realize oneValue else realize zeroValue
    have hzeroCoord :
        semanticBind (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)
            (semanticUnfold (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) f)
            (semanticUnit (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) (realize zeroValue))
            (HardwareAdequacy.encodePath selectors i) kξ =
          sSup (channelTreeResults D₀ j₀ realize sZero selectors i
            kξ) := by
      simpa [childK, id] using
        (selectPath_semanticBind D₀ j₀
          (semanticUnfold (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) f)
          (semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) (realize zeroValue))
          selectors i kξ).symm.trans hzeroEq
    have honeCoord :
        semanticBind (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)
            (semanticUnfold (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) f)
            (semanticUnit (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) (realize oneValue))
            (HardwareAdequacy.encodePath selectors i) kξ =
          sSup (channelTreeResults D₀ j₀ realize sOne selectors i
            kξ) := by
      simpa [childK, id] using
        (selectPath_semanticBind D₀ j₀
          (semanticUnfold (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) f)
          (semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) (realize oneValue))
          selectors i kξ).symm.trans honeEq
    have hpayload0 : payload false = realize zeroValue := rfl
    have hpayload1 : payload true = realize oneValue := rfl
    have hpairs_le_wraps :
        sSup ((fun p : TTResult 2 × TTResult 2 =>
            measurementResult p.1 p.2) ''
          (channelTreeResults D₀ j₀ realize sZero selectors i kξ ×ˢ
            channelTreeResults D₀ j₀ realize sOne selectors i kξ)) ≤
          sSup (channelTreeResults D₀ j₀ realize sMz selectors i kξ) := by
      apply sSup_le
      rintro T ⟨⟨r, q⟩, ⟨hr, hq⟩, rfl⟩
      obtain ⟨fuelz, ztree, zR, hzdepth, rfl⟩ := hr
      obtain ⟨fuelo, otree, oR, hodepth, rfl⟩ := hq
      apply le_sSup
      refine ⟨max fuelz fuelo + 1,
        ChannelTree.measurement ztree otree,
        wrapMeasurementRealization D₀ j₀ realize ztree otree zR oR,
        ?_, ?_⟩
      · change max ztree.depth otree.depth + 1 ≤ max fuelz fuelo + 1
        omega
      · by_cases havail :
            ResultAvailable (ChannelTree.measurement ztree otree)
              selectors i
        · have ⟨hza, hoa⟩ := havail
          let wrapR :=
            wrapMeasurementRealization D₀ j₀ realize ztree otree zR oR
          let zR' :=
            measurementZeroRealization D₀ j₀ realize ztree otree wrapR
          let oR' :=
            measurementOneRealization D₀ j₀ realize ztree otree wrapR
          rw [restrictedResult_measurement_eq_measurementResult D₀ j₀
            realize ztree otree wrapR selectors i hza hoa ξ kξ hk,
            ← restrictedResult_eq_of_wellScoped D₀ j₀ realize ztree
              hscopedZero zR zR' selectors i ξ kξ hk,
            ← restrictedResult_eq_of_wellScoped D₀ j₀ realize otree
              hscopedOne oR oR' selectors i ξ kξ hk]
        · rw [restrictedResult_eq_bot D₀ j₀ realize
            (ChannelTree.measurement ztree otree)
            (wrapMeasurementRealization D₀ j₀ realize ztree otree zR oR)
            selectors i kξ havail]
          by_cases hza : ResultAvailable ztree selectors i
          · by_cases hoa : ResultAvailable otree selectors i
            · exact False.elim (havail ⟨hza, hoa⟩)
            · change measurementResult
                  (restrictedResult D₀ j₀ realize ztree zR selectors i kξ)
                  (restrictedResult D₀ j₀ realize otree oR selectors i kξ) =
                ⊥
              rw [restrictedResult_eq_bot D₀ j₀ realize otree oR
                selectors i kξ hoa, measurementResult_bot_right]
          · change measurementResult
                (restrictedResult D₀ j₀ realize ztree zR selectors i kξ)
                (restrictedResult D₀ j₀ realize otree oR selectors i kξ) =
              ⊥
            rw [restrictedResult_eq_bot D₀ j₀ realize ztree zR
              selectors i kξ hza, measurementResult_bot_left]
    have hwraps_le_pairs :
        sSup (channelTreeResults D₀ j₀ realize sMz selectors i kξ) ≤
          sSup ((fun p : TTResult 2 × TTResult 2 =>
            measurementResult p.1 p.2) ''
          (channelTreeResults D₀ j₀ realize sZero selectors i kξ ×ˢ
            channelTreeResults D₀ j₀ realize sOne selectors i kξ)) := by
      rw [hsMz]
      apply sSup_le
      rintro T ⟨_, tree, R, _, rfl⟩
      cases tree with
      | terminal hterm =>
          cases hterm.control_eq.symm.trans hc
      | internal h next =>
          exact False.elim (ChannelInternalStep.not_measureZ h hc)
      | external _ hex _ =>
          exact False.elim (ChannelExternalStep.not_prim hex hc)
      | probability _ _ _ _ =>
          cases hc
      | probabilityZero _ =>
          cases hc
      | probabilityOne _ =>
          cases hc
      | @measurement source zv ov ztree otree =>
          injection hc with hterm
          injection hterm with hmeasure
          injection hmeasure with hzv hov
          subst zv
          subst ov
          by_cases havail :
              ResultAvailable (ChannelTree.measurement ztree otree)
                selectors i
          · have ⟨hza, hoa⟩ := havail
            rw [restrictedResult_measurement_eq_measurementResult D₀ j₀
              realize ztree otree R selectors i hza hoa ξ kξ hk]
            let a :=
              restrictedResult D₀ j₀ realize ztree
                (measurementZeroRealization D₀ j₀ realize ztree otree R)
                selectors i kξ
            let b :=
              restrictedResult D₀ j₀ realize otree
                (measurementOneRealization D₀ j₀ realize ztree otree R)
                selectors i kξ
            have ha : a ∈ channelTreeResults D₀ j₀ realize sZero
                selectors i kξ :=
              ⟨ztree.depth, ztree,
                measurementZeroRealization D₀ j₀ realize ztree otree R,
                le_rfl, rfl⟩
            have hb : b ∈ channelTreeResults D₀ j₀ realize sOne
                selectors i kξ :=
              ⟨otree.depth, otree,
                measurementOneRealization D₀ j₀ realize ztree otree R,
                le_rfl, rfl⟩
            exact le_sSup ⟨(a, b), ⟨ha, hb⟩, rfl⟩
          · rw [restrictedResult_eq_bot D₀ j₀ realize
              (ChannelTree.measurement ztree otree) R selectors i kξ
              havail]
            exact bot_le
    simp only [id]
    rw [hden, selectPath_semanticBind,
      semanticBind_measureZ_eval_of_ne D₀ j₀
        (semanticUnfold (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) f)
        payload hne, hpayload0, hpayload1, hzeroCoord, honeCoord,
      measurementResult_sSup]
    exact le_antisymm hpairs_le_wraps hwraps_le_pairs

/-- Closed `app (lam x body) (measureZ z o)` with an application-free body
is presented-complete at a normalized start when the realized payloads
are distinct. -/
theorem closed_lam_measureZ_noapp_presented_channelTreeCompleteness {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x : Name) (body : Term (QubitPrimitive C))
    (zeroValue oneValue : C)
    (hclosed : Closed
      (.app (.lam x body) (.prim (.measureZ zeroValue oneValue))))
    (hnoapp : NoApp body)
    (hne : realize zeroValue ≠ realize oneValue)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.app (.lam x body) (.prim (.measureZ zeroValue oneValue)))
        quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.lam x body) (.prim (.measureZ zeroValue oneValue)))
        semanticEnv) := by
  let code : Term (QubitPrimitive C) :=
    .app (.lam x body) (.prim (.measureZ zeroValue oneValue))
  let s : ChannelConfig C := initialChannelConfig code quantum
  have hc : s.control = .term code := rfl
  have hrel :=
    initialChannelConfig_related D₀ j₀ realize code quantum semanticEnv
  have hscoped :=
    initialChannelConfig_wellScoped hclosed quantum
  have hsApp :
      {s with
          control :=
            .term (.app (.lam x body)
              (.prim (.measureZ zeroValue oneValue)))} =
        s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with
        control :=
          .term (.app (.lam x body)
            (.prim (.measureZ zeroValue oneValue)))}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    hsApp.symm ▸ hrel
  have hrelLam :=
    channel_config_application D₀ j₀ (s := s)
      (fn := .lam x body)
      (arg := .prim (.measureZ zeroValue oneValue)) hrelApp
  have hrelClo :=
    channel_config_lambda D₀ j₀
      (s :=
        {s with
          stack :=
            .argument (.prim (.measureZ zeroValue oneValue)) s.env ::
              s.stack})
      hrelLam
  have hrelArg :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {s with
          control := .value (.closure x body s.env)
          stack :=
            .argument (.prim (.measureZ zeroValue oneValue)) s.env ::
              s.stack})
      (fn := .closure x body s.env)
      (arg := .prim (.measureZ zeroValue oneValue))
      (callEnv := s.env) (rest := s.stack) hrelClo
  let sArg : ChannelConfig C :=
    {s with
      control := .term (.prim (.measureZ zeroValue oneValue))
      stack := .function (.closure x body s.env) :: s.stack}
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.lam x body)
        stack :=
          .argument (.prim (.measureZ zeroValue oneValue)) s.env ::
            s.stack} := by
    have happ :
        ChannelInternalStep
          {s with
            control :=
              .term (.app (.lam x body)
                (.prim (.measureZ zeroValue oneValue)))}
          {s with
            control := .term (.lam x body)
            stack :=
              .argument (.prim (.measureZ zeroValue oneValue)) s.env ::
                s.stack} :=
      ChannelInternalStep.application (s := s) (fn := .lam x body)
        (arg := .prim (.measureZ zeroValue oneValue))
    exact hsApp.symm ▸ happ
  have hstepLam : ChannelInternalStep
      {s with
        control := .term (.lam x body)
        stack :=
          .argument (.prim (.measureZ zeroValue oneValue)) s.env ::
            s.stack}
      {s with
        control := .value (.closure x body s.env)
        stack :=
          .argument (.prim (.measureZ zeroValue oneValue)) s.env ::
            s.stack} :=
    ChannelInternalStep.lambda
      (s :=
        {s with
          stack :=
            .argument (.prim (.measureZ zeroValue oneValue)) s.env ::
              s.stack})
      (x := x) (body := body)
  have hstepArg : ChannelInternalStep
      {s with
        control := .value (.closure x body s.env)
        stack :=
          .argument (.prim (.measureZ zeroValue oneValue)) s.env ::
            s.stack}
      sArg :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {s with
          control := .value (.closure x body s.env)
          stack :=
            .argument (.prim (.measureZ zeroValue oneValue)) s.env ::
              s.stack})
      (fn := .closure x body s.env)
      (arg := .prim (.measureZ zeroValue oneValue))
      (callEnv := s.env) (rest := s.stack)
  have hscopedArg : ChannelConfig.WellScoped sArg :=
    ChannelInternalStep.preserve_wellScoped hstepArg
      (ChannelInternalStep.preserve_wellScoped hstepLam
        (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
  have hsArg : sArg.stack = [.function (.closure x body s.env)] := by
    simp [sArg, s, initialChannelConfig, ofConfig, initialConfig]
  have harg :
      PresentedChannelConfigCompleteness D₀ j₀ realize sArg
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    measureZ_under_closure_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize (s := sArg) (zeroValue := zeroValue)
      (oneValue := oneValue) (x := x) (body := body)
      (cloEnv := s.env) rfl hsArg hnoapp hscopedArg
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term (.prim (.measureZ zeroValue oneValue))
              env := s.env
              stack := .function (.closure x body s.env) :: s.stack}
            _
        exact hrelArg)
      hne
  exact (stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := x) (body := body)
    (arg := .prim (.measureZ zeroValue oneValue))
    hc hrel harg).complete

/-- Token adequacy for closed `app (lam x body) (measureZ z o)` with an
application-free body and distinct realized payloads. -/
theorem closed_lam_measureZ_noapp_presented_token_adequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x : Name) (body : Term (QubitPrimitive C))
    (zeroValue oneValue : C)
    (hclosed : Closed
      (.app (.lam x body) (.prim (.measureZ zeroValue oneValue))))
    (hnoapp : NoApp body)
    (hne : realize zeroValue ≠ realize oneValue)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize)
          (.app (.lam x body) (.prim (.measureZ zeroValue oneValue)))
          semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig
            (.app (.lam x body) (.prim (.measureZ zeroValue oneValue)))
            quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig
      (.app (.lam x body) (.prim (.measureZ zeroValue oneValue)))
      quantum)
    (interp (hardwarePrimitive D₀ j₀ realize)
      (.app (.lam x body) (.prim (.measureZ zeroValue oneValue)))
      semanticEnv)
    (closed_lam_measureZ_noapp_presented_channelTreeCompleteness
      D₀ j₀ realize x body zeroValue oneValue hclosed hnoapp hne
      quantum semanticEnv)
    selectors ξ k hk i token

/-- Closed `app (lam x body) (extern M N)` is presented-complete when the
body is administrative NoApp (so selection does not reindex the
closure) and both external children are administrative NoApp. -/
theorem closed_lam_extern_admin_noapp_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x : Name) (body left right : Term (QubitPrimitive C))
    (hclosed : Closed (.app (.lam x body) (.extern left right)))
    (hnoapp : NoApp body) (hadminBody : AdminNoApp body)
    (hadminL : AdminNoApp left) (hadminR : AdminNoApp right)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.app (.lam x body) (.extern left right))
        quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.lam x body) (.extern left right)) semanticEnv) := by
  let code : Term (QubitPrimitive C) :=
    .app (.lam x body) (.extern left right)
  let s : ChannelConfig C := initialChannelConfig code quantum
  have hc : s.control = .term code := rfl
  have hrel :=
    initialChannelConfig_related D₀ j₀ realize code quantum semanticEnv
  have hscoped :=
    initialChannelConfig_wellScoped hclosed quantum
  have hsApp :
      {s with
          control := .term (.app (.lam x body) (.extern left right))} =
        s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with
        control := .term (.app (.lam x body) (.extern left right))}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    hsApp.symm ▸ hrel
  have hrelLam :=
    channel_config_application D₀ j₀ (s := s)
      (fn := .lam x body) (arg := .extern left right) hrelApp
  have hrelClo :=
    channel_config_lambda D₀ j₀
      (s :=
        {s with
          stack := .argument (.extern left right) s.env :: s.stack})
      hrelLam
  have hrelArg :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {s with
          control := .value (.closure x body s.env)
          stack := .argument (.extern left right) s.env :: s.stack})
      (fn := .closure x body s.env) (arg := .extern left right)
      (callEnv := s.env) (rest := s.stack) hrelClo
  let sArg : ChannelConfig C :=
    {s with
      control := .term (.extern left right)
      stack := .function (.closure x body s.env) :: s.stack}
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.lam x body)
        stack := .argument (.extern left right) s.env :: s.stack} := by
    have happ :
        ChannelInternalStep
          {s with
            control :=
              .term (.app (.lam x body) (.extern left right))}
          {s with
            control := .term (.lam x body)
            stack :=
              .argument (.extern left right) s.env :: s.stack} :=
      ChannelInternalStep.application (s := s) (fn := .lam x body)
        (arg := .extern left right)
    exact hsApp.symm ▸ happ
  have hstepLam : ChannelInternalStep
      {s with
        control := .term (.lam x body)
        stack := .argument (.extern left right) s.env :: s.stack}
      {s with
        control := .value (.closure x body s.env)
        stack := .argument (.extern left right) s.env :: s.stack} :=
    ChannelInternalStep.lambda
      (s :=
        {s with
          stack := .argument (.extern left right) s.env :: s.stack})
      (x := x) (body := body)
  have hstepArg : ChannelInternalStep
      {s with
        control := .value (.closure x body s.env)
        stack := .argument (.extern left right) s.env :: s.stack}
      sArg :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {s with
          control := .value (.closure x body s.env)
          stack := .argument (.extern left right) s.env :: s.stack})
      (fn := .closure x body s.env) (arg := .extern left right)
      (callEnv := s.env) (rest := s.stack)
  have hscopedArg : ChannelConfig.WellScoped sArg :=
    ChannelInternalStep.preserve_wellScoped hstepArg
      (ChannelInternalStep.preserve_wellScoped hstepLam
        (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
  have hsArg : sArg.stack = [.function (.closure x body s.env)] := by
    simp [sArg, s, initialChannelConfig, ofConfig, initialConfig]
  have hscopedL : ChannelConfig.WellScoped
      {sArg with control := .term left} :=
    wellScoped_term_child (s := sArg) (code := .extern left right)
      (child := left) rfl hscopedArg fun z hz => by simp [free, hz]
  have hscopedR : ChannelConfig.WellScoped
      {sArg with control := .term right} :=
    wellScoped_term_child (s := sArg) (code := .extern left right)
      (child := right) rfl hscopedArg fun z hz => by simp [free, hz]
  have harg :
      PresentedChannelConfigCompleteness D₀ j₀ realize sArg
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    extern_under_closure_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize (s := sArg) (left := left) (right := right)
      (x := x) (body := body) (cloEnv := s.env) rfl hsArg hadminBody
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term (.extern left right)
              env := s.env
              stack := .function (.closure x body s.env) :: s.stack}
            _
        exact hrelArg)
      (fun childEnv childK henv hstack =>
        admin_noapp_under_closure_nil_presentedChannelConfigCompleteness
          D₀ j₀ realize (s := {sArg with control := .term left})
          (code := left) (x := x) (body := body) (cloEnv := s.env)
          hadminL rfl hsArg hnoapp hscopedL
          ⟨interp (hardwarePrimitive D₀ j₀ realize) left childEnv,
            childK, ControlRel.term left sArg.env childEnv henv,
            hstack, rfl⟩)
      (fun childEnv childK henv hstack =>
        admin_noapp_under_closure_nil_presentedChannelConfigCompleteness
          D₀ j₀ realize (s := {sArg with control := .term right})
          (code := right) (x := x) (body := body) (cloEnv := s.env)
          hadminR rfl hsArg hnoapp hscopedR
          ⟨interp (hardwarePrimitive D₀ j₀ realize) right childEnv,
            childK, ControlRel.term right sArg.env childEnv henv,
            hstack, rfl⟩)
  exact (stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := x) (body := body) (arg := .extern left right)
    hc hrel harg).complete

/-- Token adequacy for closed `app (lam x body) (extern M N)` with an
administrative NoApp body and administrative NoApp children. -/
theorem closed_lam_extern_admin_noapp_presented_token_adequacy {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x : Name) (body left right : Term (QubitPrimitive C))
    (hclosed : Closed (.app (.lam x body) (.extern left right)))
    (hnoapp : NoApp body) (hadminBody : AdminNoApp body)
    (hadminL : AdminNoApp left) (hadminR : AdminNoApp right)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize)
          (.app (.lam x body) (.extern left right)) semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig
            (.app (.lam x body) (.extern left right)) quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig (.app (.lam x body) (.extern left right))
      quantum)
    (interp (hardwarePrimitive D₀ j₀ realize)
      (.app (.lam x body) (.extern left right)) semanticEnv)
    (closed_lam_extern_admin_noapp_presented_channelTreeCompleteness
      D₀ j₀ realize x body left right hclosed hnoapp hadminBody
      hadminL hadminR quantum semanticEnv)
    selectors ξ k hk i token

theorem applyContinuation_lambda_admin_coordinateConstant {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x : Name) (body arg : Term (QubitPrimitive C))
    (hadminBody : AdminNoApp body) (hadminArg : AdminNoApp arg)
    (ρ cloEnv : Env (HSemanticValue D₀ j₀)) :
    CoordinateConstant
      (applyContinuation (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀)
        (interp (hardwarePrimitive D₀ j₀ realize) arg) ρ
        (lambdaValue (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) x
          (interp (hardwarePrimitive D₀ j₀ realize) body) cloEnv)) := by
  intro i j
  let h : ScottMap (HSemanticValue D₀ j₀) (HSemanticComp D₀ j₀) :=
    semanticUnfold (Q := TTExternalContinuationPower 2)
      (D₀ := D₀) (j₀ := j₀)
      (lambdaValue (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) x
        (interp (hardwarePrimitive D₀ j₀ realize) body) cloEnv)
  have hbody :
      ∀ d, CoordinateConstant
        (interp (hardwarePrimitive D₀ j₀ realize) body
          (envUpdate (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) x (cloEnv, d))) :=
    fun d =>
      adminNoApp_interp_coordinateConstant D₀ j₀ realize hadminBody
        (envUpdate (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) x (cloEnv, d))
  have harg :
      CoordinateConstant
        (interp (hardwarePrimitive D₀ j₀ realize) arg ρ) :=
    adminNoApp_interp_coordinateConstant D₀ j₀ realize hadminArg ρ
  rw [applyContinuation_apply]
  change
      TTContinuation.bind ((TTContinuation.atCoordinate i).comp h)
          (interp (hardwarePrimitive D₀ j₀ realize) arg ρ i) =
        TTContinuation.bind ((TTContinuation.atCoordinate j).comp h)
          (interp (hardwarePrimitive D₀ j₀ realize) arg ρ j)
  have hh :
      (TTContinuation.atCoordinate i).comp h =
        (TTContinuation.atCoordinate j).comp h := by
    apply ScottMap.ext
    intro d
    change h d i = h d j
    rw [semanticUnfold_lambdaValue]
    exact hbody d i j
  rw [hh, harg i j]

/-- A lambda under a single argument frame evaluates the argument under
the resulting closure. -/
theorem lam_under_argument_nil_admin_noapp_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x : Name}
    {body arg : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.lam x body))
    (hs : s.stack = [.argument arg s.env])
    (hnoapp : NoApp body) (hadminArg : AdminNoApp arg)
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
          stack := .argument arg s.env :: []} :=
    ChannelConfig.ext rfl rfl hs rfl
  have hrelFn :=
    channel_config_evaluateArgument D₀ j₀
      (s := {s with control := .value (.closure x body s.env)})
      (fn := .closure x body s.env) (arg := arg)
      (callEnv := s.env) (rest := [])
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
        env := s.env
        stack := .function (.closure x body s.env) :: []} := by
    have happ :
        ChannelInternalStep
          {s with
            control := .value (.closure x body s.env)
            stack := .argument arg s.env :: []}
          {s with
            control := .term arg
            env := s.env
            stack := .function (.closure x body s.env) :: []} :=
      ChannelInternalStep.evaluateArgument
        (s := {s with control := .value (.closure x body s.env)})
        (fn := .closure x body s.env) (arg := arg)
        (callEnv := s.env) (rest := [])
    exact hsrcClo.symm ▸ happ
  have hscopedFn : ChannelConfig.WellScoped
      {s with
        control := .term arg
        env := s.env
        stack := .function (.closure x body s.env) :: []} :=
    ChannelInternalStep.preserve_wellScoped hstepArg
      (ChannelInternalStep.preserve_wellScoped hstepLam hscoped)
  have harg :
      PresentedChannelConfigCompleteness D₀ j₀ realize
        {s with
          control := .term arg
          env := s.env
          stack := .function (.closure x body s.env) :: []}
        answer :=
    admin_noapp_under_closure_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize
      (s :=
        {s with
          control := .term arg
          env := s.env
          stack := .function (.closure x body s.env) :: []})
      (code := arg) (x := x) (body := body) (cloEnv := s.env)
      hadminArg rfl rfl hnoapp hscopedFn hrelFn
  have hClo :=
    evaluateArgument_presentedChannelConfigCompleteness D₀ j₀ realize
      (s := {s with control := .value (.closure x body s.env)})
      (fn := .closure x body s.env) (arg := arg)
      (callEnv := s.env) (rest := []) rfl hs hrelClo harg
  exact lambda_presentedChannelConfigCompleteness D₀ j₀ realize
    hc hrel hClo

/-- Extern of two lambdas under a single argument frame.  The argument
and both lambda bodies must be administrative NoApp so apply-continuation
is coordinate-constant at the two lambda values. -/
theorem extern_lams_under_argument_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {xL xR : Name}
    {bodyL bodyR arg : Term (QubitPrimitive C)}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control =
      .term (.extern (.lam xL bodyL) (.lam xR bodyR)))
    (hs : s.stack = [.argument arg s.env])
    (hnoappL : NoApp bodyL) (hnoappR : NoApp bodyR)
    (hadminL : AdminNoApp bodyL) (hadminR : AdminNoApp bodyR)
    (hadminArg : AdminNoApp arg)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hscopedL : ChannelConfig.WellScoped
      {s with control := .term (.lam xL bodyL)} :=
    wellScoped_term_child (s := s)
      (code := .extern (.lam xL bodyL) (.lam xR bodyR))
      (child := .lam xL bodyL) hc hscoped
      fun z hz => List.mem_append.mpr (Or.inl hz)
  have hscopedR : ChannelConfig.WellScoped
      {s with control := .term (.lam xR bodyR)} :=
    wellScoped_term_child (s := s)
      (code := .extern (.lam xL bodyL) (.lam xR bodyR))
      (child := .lam xR bodyR) hc hscoped
      fun z hz => List.mem_append.mpr (Or.inr hz)
  refine extern_related_presentedChannelConfigCompleteness
    D₀ j₀ realize hc hrel ?_ ?_ ?_
  · intro semanticEnv k henv hstack selected
    rw [hs] at hstack
    cases hstack
    case argument semanticEnv' krest henvArg hrest =>
      cases hrest
      simp only [id]
      have hL :=
        applyContinuation_lambda_admin_coordinateConstant D₀ j₀ realize
          xL bodyL arg hadminL hadminArg semanticEnv' semanticEnv
      have hR :=
        applyContinuation_lambda_admin_coordinateConstant D₀ j₀ realize
          xR bodyR arg hadminR hadminArg semanticEnv' semanticEnv
      have hden :
          interp (hardwarePrimitive D₀ j₀ realize)
              (.extern (.lam xL bodyL) (.lam xR bodyR)) semanticEnv =
            HasComputationChoice.extern
              (semanticUnit (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀)
                (lambdaValue (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) xL
                  (interp (hardwarePrimitive D₀ j₀ realize) bodyL)
                  semanticEnv),
                semanticUnit (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀)
                  (lambdaValue (Q := TTExternalContinuationPower 2)
                    (D₀ := D₀) (j₀ := j₀) xR
                    (interp (hardwarePrimitive D₀ j₀ realize) bodyR)
                    semanticEnv)) := by
        simp [interp_extern_apply, interp_lam_apply]
      rw [hden]
      exact TTContinuation.selectBranch_taggedBind_extern_units
        (applyContinuation (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀)
          (interp (hardwarePrimitive D₀ j₀ realize) arg) semanticEnv')
        (lambdaValue (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) xL
          (interp (hardwarePrimitive D₀ j₀ realize) bodyL) semanticEnv)
        (lambdaValue (Q := TTExternalContinuationPower 2)
          (D₀ := D₀) (j₀ := j₀) xR
          (interp (hardwarePrimitive D₀ j₀ realize) bodyR) semanticEnv)
        hL hR selected
  · intro semanticEnv k henv hstack
    exact lam_under_argument_nil_admin_noapp_presentedChannelConfigCompleteness
      D₀ j₀ realize (s := {s with control := .term (.lam xL bodyL)})
      rfl (by simp [hs]) hnoappL hadminArg hscopedL
      ⟨interp (hardwarePrimitive D₀ j₀ realize) (.lam xL bodyL)
          semanticEnv,
        k, ControlRel.term _ s.env semanticEnv henv, hstack, rfl⟩
  · intro semanticEnv k henv hstack
    exact lam_under_argument_nil_admin_noapp_presentedChannelConfigCompleteness
      D₀ j₀ realize (s := {s with control := .term (.lam xR bodyR)})
      rfl (by simp [hs]) hnoappR hadminArg hscopedR
      ⟨interp (hardwarePrimitive D₀ j₀ realize) (.lam xR bodyR)
          semanticEnv,
        k, ControlRel.term _ s.env semanticEnv henv, hstack, rfl⟩

/-- Closed `app (extern (lam x bodyL) (lam y bodyR)) arg` is
presented-complete when the argument and both bodies are administrative
NoApp. -/
theorem closed_app_extern_lams_admin_noapp_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (xL xR : Name) (bodyL bodyR arg : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.extern (.lam xL bodyL) (.lam xR bodyR)) arg))
    (hnoappL : NoApp bodyL) (hnoappR : NoApp bodyR)
    (hadminL : AdminNoApp bodyL) (hadminR : AdminNoApp bodyR)
    (hadminArg : AdminNoApp arg)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.app (.extern (.lam xL bodyL) (.lam xR bodyR)) arg) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.extern (.lam xL bodyL) (.lam xR bodyR)) arg)
        semanticEnv) := by
  let code : Term (QubitPrimitive C) :=
    .app (.extern (.lam xL bodyL) (.lam xR bodyR)) arg
  let s : ChannelConfig C := initialChannelConfig code quantum
  have hc : s.control = .term code := rfl
  have hrel :=
    initialChannelConfig_related D₀ j₀ realize code quantum semanticEnv
  have hscoped :=
    initialChannelConfig_wellScoped hclosed quantum
  have hsApp :
      {s with control := .term code} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term code}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    hsApp.symm ▸ hrel
  have hrelExt :=
    channel_config_application D₀ j₀ (s := s)
      (fn := .extern (.lam xL bodyL) (.lam xR bodyR)) (arg := arg)
      hrelApp
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.extern (.lam xL bodyL) (.lam xR bodyR))
        stack := .argument arg s.env :: s.stack} := by
    have happ :
        ChannelInternalStep
          {s with control := .term code}
          {s with
            control :=
              .term (.extern (.lam xL bodyL) (.lam xR bodyR))
            stack := .argument arg s.env :: s.stack} :=
      ChannelInternalStep.application (s := s)
        (fn := .extern (.lam xL bodyL) (.lam xR bodyR)) (arg := arg)
    exact hsApp.symm ▸ happ
  have hscopedExt : ChannelConfig.WellScoped
      {s with
        control := .term (.extern (.lam xL bodyL) (.lam xR bodyR))
        stack := .argument arg s.env :: s.stack} :=
    ChannelInternalStep.preserve_wellScoped hstepApp hscoped
  have hsExt :
      ({s with
          control := .term (.extern (.lam xL bodyL) (.lam xR bodyR))
          stack := .argument arg s.env :: s.stack}).stack =
        [.argument arg s.env] := by
    simp [s, initialChannelConfig, ofConfig, initialConfig]
  have hext :
      PresentedChannelConfigCompleteness D₀ j₀ realize
        {s with
          control := .term (.extern (.lam xL bodyL) (.lam xR bodyR))
          stack := .argument arg s.env :: s.stack}
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    extern_lams_under_argument_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize
      (s :=
        {s with
          control := .term (.extern (.lam xL bodyL) (.lam xR bodyR))
          stack := .argument arg s.env :: s.stack})
      rfl hsExt hnoappL hnoappR hadminL hadminR hadminArg
      hscopedExt hrelExt
  exact (application_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s)
    (fn := .extern (.lam xL bodyL) (.lam xR bodyR)) (arg := arg)
    hc hrel hext).complete

/-- Token adequacy for closed `app (extern (lam x bodyL) (lam y bodyR)) arg`
with administrative NoApp argument and bodies. -/
theorem closed_app_extern_lams_admin_noapp_presented_token_adequacy
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (xL xR : Name) (bodyL bodyR arg : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.extern (.lam xL bodyL) (.lam xR bodyR)) arg))
    (hnoappL : NoApp bodyL) (hnoappR : NoApp bodyR)
    (hadminL : AdminNoApp bodyL) (hadminR : AdminNoApp bodyR)
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
          (.app (.extern (.lam xL bodyL) (.lam xR bodyR)) arg)
          semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig
            (.app (.extern (.lam xL bodyL) (.lam xR bodyR)) arg)
            quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig
      (.app (.extern (.lam xL bodyL) (.lam xR bodyR)) arg) quantum)
    (interp (hardwarePrimitive D₀ j₀ realize)
      (.app (.extern (.lam xL bodyL) (.lam xR bodyR)) arg) semanticEnv)
    (closed_app_extern_lams_admin_noapp_presented_channelTreeCompleteness
      D₀ j₀ realize xL xR bodyL bodyR arg hclosed hnoappL hnoappR
      hadminL hadminR hadminArg quantum semanticEnv)
    selectors ξ k hk i token

/-- Closed `app (lam x body) (prob p M N)` is presented-complete when
the body is application-free and both probabilistic children are
administrative NoApp. -/
theorem closed_lam_prob_admin_noapp_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x : Name) (body : Term (QubitPrimitive C)) (p : ℝ)
    (left right : Term (QubitPrimitive C))
    (hclosed : Closed (.app (.lam x body) (.prob p left right)))
    (hnoapp : NoApp body)
    (hadminL : AdminNoApp left) (hadminR : AdminNoApp right)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.app (.lam x body) (.prob p left right))
        quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.lam x body) (.prob p left right)) semanticEnv) :=
  closed_lam_admin_noapp_presented_channelTreeCompleteness
    D₀ j₀ realize x body (.prob p left right) hclosed hnoapp
    ⟨hadminL, hadminR⟩ quantum semanticEnv

/-- Token adequacy for closed `app (lam x body) (prob p M N)` with an
application-free body and administrative NoApp children. -/
theorem closed_lam_prob_admin_noapp_presented_token_adequacy
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x : Name) (body : Term (QubitPrimitive C)) (p : ℝ)
    (left right : Term (QubitPrimitive C))
    (hclosed : Closed (.app (.lam x body) (.prob p left right)))
    (hnoapp : NoApp body)
    (hadminL : AdminNoApp left) (hadminR : AdminNoApp right)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize)
          (.app (.lam x body) (.prob p left right)) semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig
            (.app (.lam x body) (.prob p left right)) quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig (.app (.lam x body) (.prob p left right))
      quantum)
    (interp (hardwarePrimitive D₀ j₀ realize)
      (.app (.lam x body) (.prob p left right)) semanticEnv)
    (closed_lam_prob_admin_noapp_presented_channelTreeCompleteness
      D₀ j₀ realize x body p left right hclosed hnoapp hadminL hadminR
      quantum semanticEnv)
    selectors ξ k hk i token

/-- Closed `app (recLam self x body) arg` is presented-complete when the
body is application-free and the argument is administrative NoApp. -/
theorem closed_recLam_admin_noapp_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self x : Name) (body arg : Term (QubitPrimitive C))
    (hclosed : Closed (.app (.recLam self x body) arg))
    (hnoapp : NoApp body) (hadmin : AdminNoApp arg)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig (.app (.recLam self x body) arg) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.recLam self x body) arg) semanticEnv) := by
  let code : Term (QubitPrimitive C) := .app (.recLam self x body) arg
  let s : ChannelConfig C := initialChannelConfig code quantum
  have hc : s.control = .term code := rfl
  have hrel :=
    initialChannelConfig_related D₀ j₀ realize code quantum semanticEnv
  have hscoped :=
    initialChannelConfig_wellScoped hclosed quantum
  have hsApp :
      {s with control := .term (.app (.recLam self x body) arg)} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app (.recLam self x body) arg)}
      (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    hsApp.symm ▸ hrel
  have hrelRec :=
    channel_config_application D₀ j₀ (s := s)
      (fn := .recLam self x body) (arg := arg) hrelApp
  have hrelClo :=
    channel_config_recursive D₀ j₀
      (s := {s with stack := .argument arg s.env :: s.stack})
      hrelRec
  have hrelArg :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {s with
          control := .value (.recClosure self x body s.env)
          stack := .argument arg s.env :: s.stack})
      (fn := .recClosure self x body s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack) hrelClo
  let sArg : ChannelConfig C :=
    {s with
      control := .term arg
      stack := .function (.recClosure self x body s.env) :: s.stack}
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.recLam self x body)
        stack := .argument arg s.env :: s.stack} := by
    have happ :
        ChannelInternalStep
          {s with control := .term (.app (.recLam self x body) arg)}
          {s with
            control := .term (.recLam self x body)
            stack := .argument arg s.env :: s.stack} :=
      ChannelInternalStep.application (s := s)
        (fn := .recLam self x body) (arg := arg)
    exact hsApp.symm ▸ happ
  have hstepRec : ChannelInternalStep
      {s with
        control := .term (.recLam self x body)
        stack := .argument arg s.env :: s.stack}
      {s with
        control := .value (.recClosure self x body s.env)
        stack := .argument arg s.env :: s.stack} :=
    ChannelInternalStep.recursive
      (s := {s with stack := .argument arg s.env :: s.stack})
      (self := self) (arg := x) (body := body)
  have hstepArg : ChannelInternalStep
      {s with
        control := .value (.recClosure self x body s.env)
        stack := .argument arg s.env :: s.stack}
      sArg :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {s with
          control := .value (.recClosure self x body s.env)
          stack := .argument arg s.env :: s.stack})
      (fn := .recClosure self x body s.env) (arg := arg)
      (callEnv := s.env) (rest := s.stack)
  have hscopedArg : ChannelConfig.WellScoped sArg :=
    ChannelInternalStep.preserve_wellScoped hstepArg
      (ChannelInternalStep.preserve_wellScoped hstepRec
        (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
  have hsArg :
      sArg.stack = [.function (.recClosure self x body s.env)] := by
    simp [sArg, s, initialChannelConfig, ofConfig, initialConfig]
  have harg :
      PresentedChannelConfigCompleteness D₀ j₀ realize sArg
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    admin_noapp_under_recClosure_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize (s := sArg) (code := arg) (self := self) (x := x)
      (body := body) (cloEnv := s.env) hadmin rfl hsArg hnoapp
      hscopedArg
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term arg
              env := s.env
              stack :=
                .function (.recClosure self x body s.env) :: s.stack}
            _
        exact hrelArg)
  exact (stacked_recLam_app_presentedChannelConfigCompleteness
    D₀ j₀ realize (s := s) (self := self) (x := x) (body := body)
    (arg := arg) hc hrel harg).complete

/-- Token adequacy for closed `app (recLam self x body) arg` with an
application-free body and an administrative NoApp argument. -/
theorem closed_recLam_admin_noapp_presented_token_adequacy
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (self x : Name) (body arg : Term (QubitPrimitive C))
    (hclosed : Closed (.app (.recLam self x body) arg))
    (hnoapp : NoApp body) (hadmin : AdminNoApp arg)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀))
    (selectors : List Bool)
    (ξ : HSemanticValue D₀ j₀ → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap (HSemanticValue D₀ j₀) (TTResult 2))
    (hk : ∀ d, k d = (ξ d).satisfiedTTTheory resultCode)
    (i : ℕ) (token : TTObservationToken 2) :
    token ∈ HardwareAdequacy.selectPath selectors
        (interp (hardwarePrimitive D₀ j₀ realize)
          (.app (.recLam self x body) arg) semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig
            (.app (.recLam self x body) arg) quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig (.app (.recLam self x body) arg) quantum)
    (interp (hardwarePrimitive D₀ j₀ realize)
      (.app (.recLam self x body) arg) semanticEnv)
    (closed_recLam_admin_noapp_presented_channelTreeCompleteness
      D₀ j₀ realize self x body arg hclosed hnoapp hadmin quantum
      semanticEnv)
    selectors ξ k hk i token

/-- A value under two closure frames betas the inner closure, then the
administrative inner body under the remaining outer frame. -/
theorem value_under_two_closures_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {arg : RuntimeValue C}
    {y x : Name} {bodyY bodyX : Term (QubitPrimitive C)}
    {cloY cloX : RuntimeEnv C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .value arg)
    (hs : s.stack =
      [.function (.closure y bodyY cloY),
        .function (.closure x bodyX cloX)])
    (hadminY : AdminNoApp bodyY) (hnoappX : NoApp bodyX)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsEq :
      {s with
        control := .value arg
        stack :=
          .function (.closure y bodyY cloY) ::
            [.function (.closure x bodyX cloX)]} = s :=
    ChannelConfig.ext hc.symm rfl hs.symm rfl
  have hrel' : ChannelConfigRel D₀ j₀ realize
      {s with
        control := .value arg
        stack :=
          .function (.closure y bodyY cloY) ::
            [.function (.closure x bodyX cloX)]}
      answer :=
    hsEq.symm ▸ hrel
  have hrelBody :=
    channel_config_beta D₀ j₀ (s := s) (x := y) (body := bodyY)
      (closureEnv := cloY) (arg := arg)
      (rest := [.function (.closure x bodyX cloX)]) hrel'
  let sBody : ChannelConfig C :=
    {s with
      control := .term bodyY
      env := RuntimeEnv.bind y arg cloY
      stack := [.function (.closure x bodyX cloX)]}
  have hstepBeta : ChannelInternalStep s sBody := by
    have happ :
        ChannelInternalStep
          {s with
            control := .value arg
            stack :=
              .function (.closure y bodyY cloY) ::
                [.function (.closure x bodyX cloX)]}
          sBody :=
      ChannelInternalStep.beta (s := s) (x := y) (body := bodyY)
        (closureEnv := cloY) (arg := arg)
        (rest := [.function (.closure x bodyX cloX)])
    exact hsEq.symm ▸ happ
  have hscopedBody : ChannelConfig.WellScoped sBody :=
    ChannelInternalStep.preserve_wellScoped hstepBeta hscoped
  have hchild :=
    admin_noapp_under_closure_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize (s := sBody) (code := bodyY) (x := x)
      (body := bodyX) (cloEnv := cloX) hadminY rfl rfl hnoappX
      hscopedBody hrelBody
  exact beta_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := y) (body := bodyY) (closureEnv := cloY)
    (arg := arg) (rest := [.function (.closure x bodyX cloX)])
    hc hs hrel hchild

theorem ret_under_two_closures_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {value : C}
    {y x : Name} {bodyY bodyX : Term (QubitPrimitive C)}
    {cloY cloX : RuntimeEnv C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.ret value)))
    (hs : s.stack =
      [.function (.closure y bodyY cloY),
        .function (.closure x bodyX cloX)])
    (hadminY : AdminNoApp bodyY) (hnoappX : NoApp bodyX)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
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
      ChannelInternalStep.returnPrimitive (s := s) (value := value)
    exact hsRet.symm ▸ happ
  have hscopedVal : ChannelConfig.WellScoped
      {s with control := .value (.payload value)} :=
    ChannelInternalStep.preserve_wellScoped hstepRet hscoped
  have hval :=
    value_under_two_closures_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize
      (s := {s with control := .value (.payload value)})
      (arg := .payload value) (y := y) (x := x)
      (bodyY := bodyY) (bodyX := bodyX) (cloY := cloY) (cloX := cloX)
      rfl hs hadminY hnoappX hscopedVal hrelVal
  exact return_presentedChannelConfigCompleteness D₀ j₀ realize
    hc hrel hval

theorem pauliX_under_two_closures_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {value : C}
    {y x : Name} {bodyY bodyX : Term (QubitPrimitive C)}
    {cloY cloX : RuntimeEnv C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack =
      [.function (.closure y bodyY cloY),
        .function (.closure x bodyX cloX)])
    (hadminY : AdminNoApp bodyY) (hnoappX : NoApp bodyX)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsPx :
      {s with control := .term (.prim (.pauliX value))} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  obtain ⟨semanticEnv, kStack, henv, hstack, rfl⟩ :=
    channelConfigRel_term_inv D₀ j₀ hc hrel
  rw [hs] at hstack
  cases hstack
  case function f krest hfn hrest =>
    cases hrest
    case function f2 krest2 hfn2 hrest2 =>
      cases hrest2
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
          ((fun ma =>
            id (semanticBind (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀)
              (semanticUnfold (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀) f2)
              (semanticBind (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀)
                (semanticUnfold (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) f) ma)))
            (semanticUnit (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) (realize value))) :=
        ⟨semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) (realize value),
          fun ma =>
            id (semanticBind (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀)
              (semanticUnfold (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀) f2)
              (semanticBind (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀)
                (semanticUnfold (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) f) ma)),
          ControlRel.value _ _ s.env
            (payload_related D₀ j₀ realize value),
          hs.symm ▸
            StackRel.function (.closure y bodyY cloY) f
              [.function (.closure x bodyX cloX)]
              (fun ma =>
                id (semanticBind (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀)
                  (semanticUnfold (Q := TTExternalContinuationPower 2)
                    (D₀ := D₀) (j₀ := j₀) f2) ma))
              hfn
              (StackRel.function (.closure x bodyX cloX) f2 [] id hfn2
                StackRel.nil), rfl⟩
      have hval :=
        value_under_two_closures_nil_presentedChannelConfigCompleteness
          D₀ j₀ realize (s := sVal) (arg := .payload value)
          (y := y) (x := x) (bodyY := bodyY) (bodyX := bodyX)
          (cloY := cloY) (cloX := cloX) rfl hs hadminY hnoappX
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
      have hchildCoord :
          semanticBind (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀)
              (semanticUnfold (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀) f2)
              (semanticBind (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀)
                (semanticUnfold (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) f)
                (semanticUnit (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) (realize value)))
              (HardwareAdequacy.encodePath selectors i) kξ =
            sSup (channelTreeResults D₀ j₀ realize sVal selectors i
              kξ) := by
        simp only [id] at hchildEq
        rw [selectPath_semanticBind] at hchildEq
        exact hchildEq
      simp only [id]
      rw [hden, selectPath_semanticBind,
        semanticBind_bind_ofOperation_eval D₀ j₀
          (semanticUnfold (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) f2)
          (semanticUnfold (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) f)
          Qubit.pauliXOp (realize value),
        hchildCoord, embed_ofOperation_const_sSup]
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

/-- Administrative NoApp under two stacked ordinary closures. -/
theorem admin_noapp_under_two_closures_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {y x : Name} {bodyY bodyX : Term (QubitPrimitive C)}
    {cloY cloX : RuntimeEnv C} {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack =
      [.function (.closure y bodyY cloY),
        .function (.closure x bodyX cloX)])
    (hadminY : AdminNoApp bodyY) (hnoappX : NoApp bodyX)
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
        value_under_two_closures_nil_presentedChannelConfigCompleteness
          D₀ j₀ realize (s := {s with control := .value v})
          (arg := v) (y := y) (x := x) (bodyY := bodyY)
          (bodyX := bodyX) (cloY := cloY) (cloX := cloX)
          rfl hs hadminY hnoappX hscopedVal hrelVal
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
        value_under_two_closures_nil_presentedChannelConfigCompleteness
          D₀ j₀ realize
          (s := {s with control := .value (.closure z M s.env)})
          (arg := .closure z M s.env) (y := y) (x := x)
          (bodyY := bodyY) (bodyX := bodyX) (cloY := cloY)
          (cloX := cloX) rfl hs hadminY hnoappX hscopedVal hrelVal
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
        value_under_two_closures_nil_presentedChannelConfigCompleteness
          D₀ j₀ realize
          (s :=
            {s with control := .value (.recClosure self z M s.env)})
          (arg := .recClosure self z M s.env) (y := y) (x := x)
          (bodyY := bodyY) (bodyX := bodyX) (cloY := cloY)
          (cloX := cloX) rfl hs hadminY hnoappX hscopedVal hrelVal
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
          exact
            ret_under_two_closures_nil_presentedChannelConfigCompleteness
              D₀ j₀ realize hc hs hadminY hnoappX hscoped hrel
      | pauliX value =>
          exact
            pauliX_under_two_closures_nil_presentedChannelConfigCompleteness
              D₀ j₀ realize hc hs hadminY hnoappX hscoped hrel
      | measureZ _ _ =>
          exact False.elim hadmin

/-- Inner `app (lam y bodyY) arg` under one outer closure frame. -/
theorem app_lam_under_closure_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {y x : Name}
    {bodyY bodyX arg : Term (QubitPrimitive C)}
    {cloX : RuntimeEnv C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.app (.lam y bodyY) arg))
    (hs : s.stack = [.function (.closure x bodyX cloX)])
    (hadminY : AdminNoApp bodyY) (hadminArg : AdminNoApp arg)
    (hnoappX : NoApp bodyX)
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
      stack :=
        .function (.closure y bodyY s.env) :: s.stack}
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
      ChannelInternalStep.application (s := s) (fn := .lam y bodyY)
        (arg := arg)
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
          .function (.closure x bodyX cloX)] := by
    simp [sArg, hs]
  have harg :
      PresentedChannelConfigCompleteness D₀ j₀ realize sArg answer :=
    admin_noapp_under_two_closures_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize (s := sArg) (code := arg) (y := y) (x := x)
      (bodyY := bodyY) (bodyX := bodyX) (cloY := s.env) (cloX := cloX)
      hadminArg rfl hsArg hadminY hnoappX hscopedArg
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

/-- Closed `app (lam x bodyX) (app (lam y bodyY) arg)` is
presented-complete when `bodyX` is application-free and both `bodyY`
and `arg` are administrative NoApp. -/
theorem closed_nested_lam_admin_noapp_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x y : Name) (bodyX bodyY arg : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.lam x bodyX) (.app (.lam y bodyY) arg)))
    (hnoappX : NoApp bodyX)
    (hadminY : AdminNoApp bodyY) (hadminArg : AdminNoApp arg)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.app (.lam x bodyX) (.app (.lam y bodyY) arg)) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.lam x bodyX) (.app (.lam y bodyY) arg))
        semanticEnv) := by
  let inner : Term (QubitPrimitive C) := .app (.lam y bodyY) arg
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
      ChannelInternalStep.application (s := s) (fn := .lam x bodyX)
        (arg := inner)
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
      sInner.stack = [.function (.closure x bodyX s.env)] := by
    simp [sInner, s, initialChannelConfig, ofConfig, initialConfig]
  have hinner :
      PresentedChannelConfigCompleteness D₀ j₀ realize sInner
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    app_lam_under_closure_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize (s := sInner) (y := y) (x := x)
      (bodyY := bodyY) (bodyX := bodyX) (arg := arg)
      (cloX := s.env) rfl hsInner hadminY hadminArg hnoappX
      hscopedInner
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term inner
              env := s.env
              stack := .function (.closure x bodyX s.env) :: s.stack}
            _
        exact hrelInner)
  exact (stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := x) (body := bodyX) (arg := inner)
    hc hrel hinner).complete

/-- Token adequacy for closed nested `app (lam x bodyX) (app (lam y bodyY) arg)`. -/
theorem closed_nested_lam_admin_noapp_presented_token_adequacy
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x y : Name) (bodyX bodyY arg : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.lam x bodyX) (.app (.lam y bodyY) arg)))
    (hnoappX : NoApp bodyX)
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
          (.app (.lam x bodyX) (.app (.lam y bodyY) arg))
          semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig
            (.app (.lam x bodyX) (.app (.lam y bodyY) arg)) quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig
      (.app (.lam x bodyX) (.app (.lam y bodyY) arg)) quantum)
    (interp (hardwarePrimitive D₀ j₀ realize)
      (.app (.lam x bodyX) (.app (.lam y bodyY) arg)) semanticEnv)
    (closed_nested_lam_admin_noapp_presented_channelTreeCompleteness
      D₀ j₀ realize x y bodyX bodyY arg hclosed hnoappX hadminY
      hadminArg quantum semanticEnv)
    selectors ξ k hk i token

/-- A lambda under an argument frame whose saved env may differ from
the current control env.  After beta of a curried application the
frame still carries the outer call env. -/
theorem lam_under_argument_frame_admin_noapp_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x : Name}
    {body arg : Term (QubitPrimitive C)} {callEnv : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.lam x body))
    (hs : s.stack = [.argument arg callEnv])
    (hnoapp : NoApp body) (hadminArg : AdminNoApp arg)
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
          stack := .argument arg callEnv :: []} :=
    ChannelConfig.ext rfl rfl hs rfl
  have hrelFn :=
    channel_config_evaluateArgument D₀ j₀
      (s := {s with control := .value (.closure x body s.env)})
      (fn := .closure x body s.env) (arg := arg)
      (callEnv := callEnv) (rest := [])
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
        stack := .function (.closure x body s.env) :: []} := by
    have happ :
        ChannelInternalStep
          {s with
            control := .value (.closure x body s.env)
            stack := .argument arg callEnv :: []}
          {s with
            control := .term arg
            env := callEnv
            stack := .function (.closure x body s.env) :: []} :=
      ChannelInternalStep.evaluateArgument
        (s := {s with control := .value (.closure x body s.env)})
        (fn := .closure x body s.env) (arg := arg)
        (callEnv := callEnv) (rest := [])
    exact hsrcClo.symm ▸ happ
  have hscopedFn : ChannelConfig.WellScoped
      {s with
        control := .term arg
        env := callEnv
        stack := .function (.closure x body s.env) :: []} :=
    ChannelInternalStep.preserve_wellScoped hstepArg
      (ChannelInternalStep.preserve_wellScoped hstepLam hscoped)
  have harg :
      PresentedChannelConfigCompleteness D₀ j₀ realize
        {s with
          control := .term arg
          env := callEnv
          stack := .function (.closure x body s.env) :: []}
        answer :=
    admin_noapp_under_closure_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize
      (s :=
        {s with
          control := .term arg
          env := callEnv
          stack := .function (.closure x body s.env) :: []})
      (code := arg) (x := x) (body := body) (cloEnv := s.env)
      hadminArg rfl rfl hnoapp hscopedFn hrelFn
  have hClo :=
    evaluateArgument_presentedChannelConfigCompleteness D₀ j₀ realize
      (s := {s with control := .value (.closure x body s.env)})
      (fn := .closure x body s.env) (arg := arg)
      (callEnv := callEnv) (rest := []) rfl hs hrelClo harg
  exact lambda_presentedChannelConfigCompleteness D₀ j₀ realize
    hc hrel hClo

/-- A value under a curried function frame over a leftover argument
frame betas to the inner lambda, then evaluates that argument. -/
theorem value_under_function_argument_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {arg : RuntimeValue C}
    {x y : Name} {body arg2 : Term (QubitPrimitive C)}
    {cloX callEnv : RuntimeEnv C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .value arg)
    (hs : s.stack =
      [.function (.closure x (.lam y body) cloX),
        .argument arg2 callEnv])
    (hnoapp : NoApp body) (hadminArg2 : AdminNoApp arg2)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsEq :
      {s with
        control := .value arg
        stack :=
          .function (.closure x (.lam y body) cloX) ::
            [.argument arg2 callEnv]} = s :=
    ChannelConfig.ext hc.symm rfl hs.symm rfl
  have hrel' : ChannelConfigRel D₀ j₀ realize
      {s with
        control := .value arg
        stack :=
          .function (.closure x (.lam y body) cloX) ::
            [.argument arg2 callEnv]}
      answer :=
    hsEq.symm ▸ hrel
  have hrelBody :=
    channel_config_beta D₀ j₀ (s := s) (x := x)
      (body := .lam y body) (closureEnv := cloX) (arg := arg)
      (rest := [.argument arg2 callEnv]) hrel'
  let sBody : ChannelConfig C :=
    {s with
      control := .term (.lam y body)
      env := RuntimeEnv.bind x arg cloX
      stack := [.argument arg2 callEnv]}
  have hstepBeta : ChannelInternalStep s sBody := by
    have happ :
        ChannelInternalStep
          {s with
            control := .value arg
            stack :=
              .function (.closure x (.lam y body) cloX) ::
                [.argument arg2 callEnv]}
          sBody :=
      ChannelInternalStep.beta (s := s) (x := x)
        (body := .lam y body) (closureEnv := cloX) (arg := arg)
        (rest := [.argument arg2 callEnv])
    exact hsEq.symm ▸ happ
  have hscopedBody : ChannelConfig.WellScoped sBody :=
    ChannelInternalStep.preserve_wellScoped hstepBeta hscoped
  have hchild :=
    lam_under_argument_frame_admin_noapp_presentedChannelConfigCompleteness
      D₀ j₀ realize (s := sBody) (x := y) (body := body) (arg := arg2)
      (callEnv := callEnv) rfl rfl hnoapp hadminArg2 hscopedBody
      hrelBody
  exact beta_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := x) (body := .lam y body) (closureEnv := cloX)
    (arg := arg) (rest := [.argument arg2 callEnv]) hc hs hrel hchild

theorem ret_under_function_argument_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {value : C}
    {x y : Name} {body arg2 : Term (QubitPrimitive C)}
    {cloX callEnv : RuntimeEnv C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.ret value)))
    (hs : s.stack =
      [.function (.closure x (.lam y body) cloX),
        .argument arg2 callEnv])
    (hnoapp : NoApp body) (hadminArg2 : AdminNoApp arg2)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
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
      ChannelInternalStep.returnPrimitive (s := s) (value := value)
    exact hsRet.symm ▸ happ
  have hscopedVal : ChannelConfig.WellScoped
      {s with control := .value (.payload value)} :=
    ChannelInternalStep.preserve_wellScoped hstepRet hscoped
  have hval :=
    value_under_function_argument_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize
      (s := {s with control := .value (.payload value)})
      (arg := .payload value) (x := x) (y := y) (body := body)
      (arg2 := arg2) (cloX := cloX) (callEnv := callEnv)
      rfl hs hnoapp hadminArg2 hscopedVal hrelVal
  exact return_presentedChannelConfigCompleteness D₀ j₀ realize
    hc hrel hval

theorem pauliX_under_function_argument_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {value : C}
    {x y : Name} {body arg2 : Term (QubitPrimitive C)}
    {cloX callEnv : RuntimeEnv C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack =
      [.function (.closure x (.lam y body) cloX),
        .argument arg2 callEnv])
    (hnoapp : NoApp body) (hadminArg2 : AdminNoApp arg2)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsPx :
      {s with control := .term (.prim (.pauliX value))} = s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  obtain ⟨semanticEnv, kStack, henv, hstack, rfl⟩ :=
    channelConfigRel_term_inv D₀ j₀ hc hrel
  rw [hs] at hstack
  cases hstack
  case function f krest hfn hrest =>
    cases hrest
    case argument semanticEnv' krest2 henvArg hrest2 =>
      cases hrest2
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
          ((fun ma =>
            id (semanticBind (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀)
              (applyContinuation (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀)
                (interp (hardwarePrimitive D₀ j₀ realize) arg2)
                semanticEnv')
              (semanticBind (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀)
                (semanticUnfold (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) f) ma)))
            (semanticUnit (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀) (realize value))) :=
        ⟨semanticUnit (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) (realize value),
          fun ma =>
            id (semanticBind (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀)
              (applyContinuation (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀)
                (interp (hardwarePrimitive D₀ j₀ realize) arg2)
                semanticEnv')
              (semanticBind (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀)
                (semanticUnfold (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) f) ma)),
          ControlRel.value _ _ s.env
            (payload_related D₀ j₀ realize value),
          hs.symm ▸
            StackRel.function (.closure x (.lam y body) cloX) f
              [.argument arg2 callEnv]
              (fun ma =>
                id (semanticBind (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀)
                  (applyContinuation
                    (Q := TTExternalContinuationPower 2)
                    (D₀ := D₀) (j₀ := j₀)
                    (interp (hardwarePrimitive D₀ j₀ realize) arg2)
                    semanticEnv') ma))
              hfn
              (StackRel.argument arg2 callEnv semanticEnv' [] id
                henvArg StackRel.nil), rfl⟩
      have hval :=
        value_under_function_argument_nil_presentedChannelConfigCompleteness
          D₀ j₀ realize (s := sVal) (arg := .payload value)
          (x := x) (y := y) (body := body) (arg2 := arg2)
          (cloX := cloX) (callEnv := callEnv) rfl hs hnoapp
          hadminArg2 hscopedVal hrelVal
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
      have hchildCoord :
          semanticBind (Q := TTExternalContinuationPower 2)
              (D₀ := D₀) (j₀ := j₀)
              (applyContinuation (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀)
                (interp (hardwarePrimitive D₀ j₀ realize) arg2)
                semanticEnv')
              (semanticBind (Q := TTExternalContinuationPower 2)
                (D₀ := D₀) (j₀ := j₀)
                (semanticUnfold (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) f)
                (semanticUnit (Q := TTExternalContinuationPower 2)
                  (D₀ := D₀) (j₀ := j₀) (realize value)))
              (HardwareAdequacy.encodePath selectors i) kξ =
            sSup (channelTreeResults D₀ j₀ realize sVal selectors i
              kξ) := by
        simp only [id] at hchildEq
        rw [selectPath_semanticBind] at hchildEq
        exact hchildEq
      simp only [id]
      rw [hden, selectPath_semanticBind,
        semanticBind_bind_ofOperation_eval D₀ j₀
          (applyContinuation (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀)
            (interp (hardwarePrimitive D₀ j₀ realize) arg2)
            semanticEnv')
          (semanticUnfold (Q := TTExternalContinuationPower 2)
            (D₀ := D₀) (j₀ := j₀) f)
          Qubit.pauliXOp (realize value),
        hchildCoord, embed_ofOperation_const_sSup]
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

/-- Administrative NoApp under a curried function frame over one
argument frame. -/
theorem admin_noapp_under_function_argument_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {code : Term (QubitPrimitive C)}
    {x y : Name} {body arg2 : Term (QubitPrimitive C)}
    {cloX callEnv : RuntimeEnv C} {answer : HSemanticComp D₀ j₀}
    (hadmin : AdminNoApp code)
    (hc : s.control = .term code)
    (hs : s.stack =
      [.function (.closure x (.lam y body) cloX),
        .argument arg2 callEnv])
    (hnoapp : NoApp body) (hadminArg2 : AdminNoApp arg2)
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
        value_under_function_argument_nil_presentedChannelConfigCompleteness
          D₀ j₀ realize (s := {s with control := .value v})
          (arg := v) (x := x) (y := y) (body := body)
          (arg2 := arg2) (cloX := cloX) (callEnv := callEnv)
          rfl hs hnoapp hadminArg2 hscopedVal hrelVal
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
        value_under_function_argument_nil_presentedChannelConfigCompleteness
          D₀ j₀ realize
          (s := {s with control := .value (.closure z M s.env)})
          (arg := .closure z M s.env) (x := x) (y := y)
          (body := body) (arg2 := arg2) (cloX := cloX)
          (callEnv := callEnv) rfl hs hnoapp hadminArg2 hscopedVal
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
        value_under_function_argument_nil_presentedChannelConfigCompleteness
          D₀ j₀ realize
          (s :=
            {s with control := .value (.recClosure self z M s.env)})
          (arg := .recClosure self z M s.env) (x := x) (y := y)
          (body := body) (arg2 := arg2) (cloX := cloX)
          (callEnv := callEnv) rfl hs hnoapp hadminArg2 hscopedVal
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
          exact
            ret_under_function_argument_nil_presentedChannelConfigCompleteness
              D₀ j₀ realize hc hs hnoapp hadminArg2 hscoped hrel
      | pauliX value =>
          exact
            pauliX_under_function_argument_nil_presentedChannelConfigCompleteness
              D₀ j₀ realize hc hs hnoapp hadminArg2 hscoped hrel
      | measureZ _ _ =>
          exact False.elim hadmin

/-- Inner `app (lam x (lam y body)) arg1` under one leftover argument
frame. -/
theorem app_lam_lam_under_argument_nil_presentedChannelConfigCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    {s : ChannelConfig C} {x y : Name}
    {body arg1 arg2 : Term (QubitPrimitive C)}
    {callEnv : RuntimeEnv C} {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.app (.lam x (.lam y body)) arg1))
    (hs : s.stack = [.argument arg2 callEnv])
    (hnoapp : NoApp body)
    (hadmin1 : AdminNoApp arg1) (hadmin2 : AdminNoApp arg2)
    (hscoped : ChannelConfig.WellScoped s)
    (hrel : ChannelConfigRel D₀ j₀ realize s answer) :
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer := by
  have hsApp :
      {s with control := .term (.app (.lam x (.lam y body)) arg1)} =
        s :=
    ChannelConfig.ext hc.symm rfl rfl rfl
  have hrelApp : ChannelConfigRel D₀ j₀ realize
      {s with control := .term (.app (.lam x (.lam y body)) arg1)}
      answer :=
    hsApp.symm ▸ hrel
  have hrelLam :=
    channel_config_application D₀ j₀ (s := s)
      (fn := .lam x (.lam y body)) (arg := arg1) hrelApp
  have hrelClo :=
    channel_config_lambda D₀ j₀
      (s := {s with stack := .argument arg1 s.env :: s.stack})
      hrelLam
  have hrelArg :=
    channel_config_evaluateArgument D₀ j₀
      (s :=
        {s with
          control := .value (.closure x (.lam y body) s.env)
          stack := .argument arg1 s.env :: s.stack})
      (fn := .closure x (.lam y body) s.env) (arg := arg1)
      (callEnv := s.env) (rest := s.stack) hrelClo
  let sArg : ChannelConfig C :=
    {s with
      control := .term arg1
      stack :=
        .function (.closure x (.lam y body) s.env) :: s.stack}
  have hstepApp : ChannelInternalStep s
      {s with
        control := .term (.lam x (.lam y body))
        stack := .argument arg1 s.env :: s.stack} := by
    have happ :
        ChannelInternalStep
          {s with
            control := .term (.app (.lam x (.lam y body)) arg1)}
          {s with
            control := .term (.lam x (.lam y body))
            stack := .argument arg1 s.env :: s.stack} :=
      ChannelInternalStep.application (s := s)
        (fn := .lam x (.lam y body)) (arg := arg1)
    exact hsApp.symm ▸ happ
  have hstepLam : ChannelInternalStep
      {s with
        control := .term (.lam x (.lam y body))
        stack := .argument arg1 s.env :: s.stack}
      {s with
        control := .value (.closure x (.lam y body) s.env)
        stack := .argument arg1 s.env :: s.stack} :=
    ChannelInternalStep.lambda
      (s := {s with stack := .argument arg1 s.env :: s.stack})
      (x := x) (body := .lam y body)
  have hstepArg : ChannelInternalStep
      {s with
        control := .value (.closure x (.lam y body) s.env)
        stack := .argument arg1 s.env :: s.stack}
      sArg :=
    ChannelInternalStep.evaluateArgument
      (s :=
        {s with
          control := .value (.closure x (.lam y body) s.env)
          stack := .argument arg1 s.env :: s.stack})
      (fn := .closure x (.lam y body) s.env) (arg := arg1)
      (callEnv := s.env) (rest := s.stack)
  have hscopedArg : ChannelConfig.WellScoped sArg :=
    ChannelInternalStep.preserve_wellScoped hstepArg
      (ChannelInternalStep.preserve_wellScoped hstepLam
        (ChannelInternalStep.preserve_wellScoped hstepApp hscoped))
  have hsArg :
      sArg.stack =
        [.function (.closure x (.lam y body) s.env),
          .argument arg2 callEnv] := by
    simp [sArg, hs]
  have harg :
      PresentedChannelConfigCompleteness D₀ j₀ realize sArg answer :=
    admin_noapp_under_function_argument_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize (s := sArg) (code := arg1) (x := x) (y := y)
      (body := body) (arg2 := arg2) (cloX := s.env)
      (callEnv := callEnv) hadmin1 rfl hsArg hnoapp hadmin2
      hscopedArg
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term arg1
              env := s.env
              stack :=
                .function (.closure x (.lam y body) s.env) ::
                  s.stack}
            _
        exact hrelArg)
  exact stacked_lam_app_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (x := x) (body := .lam y body) (arg := arg1) hc hrel harg

/-- Closed curried `app (app (lam x (lam y body)) arg1) arg2`. -/
theorem closed_app_app_lam_lam_admin_noapp_presented_channelTreeCompleteness
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x y : Name) (body arg1 arg2 : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.app (.lam x (.lam y body)) arg1) arg2))
    (hnoapp : NoApp body)
    (hadmin1 : AdminNoApp arg1) (hadmin2 : AdminNoApp arg2)
    (quantum : NormalizedDensity 2)
    (semanticEnv : Env (HSemanticValue D₀ j₀)) :
    PresentedChannelTreeCompleteness D₀ j₀ realize
      (initialChannelConfig
        (.app (.app (.lam x (.lam y body)) arg1) arg2) quantum)
      (interp (hardwarePrimitive D₀ j₀ realize)
        (.app (.app (.lam x (.lam y body)) arg1) arg2)
        semanticEnv) := by
  let inner : Term (QubitPrimitive C) :=
    .app (.lam x (.lam y body)) arg1
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
  have hsInner : sInner.stack = [.argument arg2 s.env] := by
    simp [sInner, s, initialChannelConfig, ofConfig, initialConfig]
  have hinner :
      PresentedChannelConfigCompleteness D₀ j₀ realize sInner
        (interp (hardwarePrimitive D₀ j₀ realize) code semanticEnv) :=
    app_lam_lam_under_argument_nil_presentedChannelConfigCompleteness
      D₀ j₀ realize (s := sInner) (x := x) (y := y) (body := body)
      (arg1 := arg1) (arg2 := arg2) (callEnv := s.env) rfl hsInner
      hnoapp hadmin1 hadmin2 hscopedInner
      (by
        change ChannelConfigRel D₀ j₀ realize
            {s with
              control := .term inner
              env := s.env
              stack := .argument arg2 s.env :: s.stack}
            _
        exact hrelInner)
  exact (application_presentedChannelConfigCompleteness D₀ j₀ realize
    (s := s) (fn := inner) (arg := arg2) hc hrel hinner).complete

/-- Token adequacy for closed curried
`app (app (lam x (lam y body)) arg1) arg2`. -/
theorem closed_app_app_lam_lam_admin_noapp_presented_token_adequacy
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (x y : Name) (body arg1 arg2 : Term (QubitPrimitive C))
    (hclosed : Closed
      (.app (.app (.lam x (.lam y body)) arg1) arg2))
    (hnoapp : NoApp body)
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
          (.app (.app (.lam x (.lam y body)) arg1) arg2)
          semanticEnv) i k ↔
      ∃ fuel, ∃ (tree : ChannelTree C
          (initialChannelConfig
            (.app (.app (.lam x (.lam y body)) arg1) arg2) quantum))
          (R : ChannelTreeRealization D₀ j₀ realize tree),
        tree.depth ≤ fuel ∧
        ResultAvailable tree selectors i ∧
          TTObservationToken.Holds resultCode token
            ((restrictedInstrument D₀ j₀ realize tree R selectors i).bind
              ξ) :=
  presented_channel_tree_token_adequacy_iff D₀ j₀ realize
    (initialChannelConfig
      (.app (.app (.lam x (.lam y body)) arg1) arg2) quantum)
    (interp (hardwarePrimitive D₀ j₀ realize)
      (.app (.app (.lam x (.lam y body)) arg1) arg2) semanticEnv)
    (closed_app_app_lam_lam_admin_noapp_presented_channelTreeCompleteness
      D₀ j₀ realize x y body arg1 arg2 hclosed hnoapp hadmin1 hadmin2
      quantum semanticEnv)
    selectors ξ k hk i token

/-- Value completeness under one function frame over leftover argument
frames of a fixed list. -/
def ValueUnderFunctionArgumentFrames {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C)) : Prop :=
  ∀ {s : ChannelConfig C} {arg : RuntimeValue C} {x : Name}
    {body : Term (QubitPrimitive C)} {cloX : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀},
    s.control = .value arg →
    s.stack =
      .function (.closure x body cloX) :: argumentStack frames →
    BodyUnderArgs frames.length body →
    ChannelConfig.WellScoped s →
    ChannelConfigRel D₀ j₀ realize s answer →
    PresentedChannelConfigCompleteness D₀ j₀ realize s answer

/-- Pauli-X under a function frame over leftover argument frames,
given value completeness at that stack. -/
theorem pauliX_under_function_argument_frames_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderFunctionArgumentFrames D₀ j₀ realize frames)
    {s : ChannelConfig C} {value : C} {x : Name}
    {body : Term (QubitPrimitive C)} {cloX : RuntimeEnv C}
    {answer : HSemanticComp D₀ j₀}
    (hc : s.control = .term (.prim (.pauliX value)))
    (hs : s.stack =
      .function (.closure x body cloX) :: argumentStack frames)
    (hbody : BodyUnderArgs frames.length body)
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

/-- Administrative NoApp under a function frame over leftover argument
frames, given value completeness at that stack. -/
theorem admin_noapp_under_function_argument_frames_of_value
    {C : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor (QModel (TTExternalContinuationPower 2)) D₀.carrier))
    (realize : C → HSemanticValue D₀ j₀)
    (frames : List (Term (QubitPrimitive C) × RuntimeEnv C))
    (hVal : ValueUnderFunctionArgumentFrames D₀ j₀ realize frames)
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
            pauliX_under_function_argument_frames_of_value
              D₀ j₀ realize frames hVal hc hs hbody hscoped hrel
      | measureZ _ _ =>
          exact False.elim hadmin


end HardwareChannelSemantics
end QLambda
