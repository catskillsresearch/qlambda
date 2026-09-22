/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.RegFile
import QLambda.Linear.Examples

/-!
# Deterministic CBV staging

This module stages a closed, well-typed, recursion-free source term to the
first-order `Command` normal form.  Lambdas (including higher-order gate
combinators) are evaluated at compile time.  A successful compilation must
return first-order data, so no closure survives into the circuit.

The evaluator is fuelled.  Thus the supported fragment is exact and
executable: closed terms accepted by `infer`, containing no `fix`, `fold`,
`unfold`, `mu`, or free type variables, which reach first-order data within
the supplied fuel and fixed `(q,c)` allocation bounds.  Fuel affects
completeness only; every successful result carries the same static
certificates.

`Linear.Denotation` is not yet present in the repository.  The semantic
agreement proved here is therefore the strongest statement exposed by the
existing APIs: compiling the staged command to Composer has exactly the
command's `CQ` denotation.
-/

namespace QLambda.Linear

namespace Ty

/-- Types admitted in the recursion-free staging fragment. -/
def muFree : Ty → Bool
  | .var _ => false
  | .unit | .bit | .qubit => true
  | .tensor A B => muFree A && muFree B
  | .arrow _ A B => muFree A && muFree B
  | .mu _ => false

/-- Types which may cross the staging boundary into a first-order circuit. -/
inductive FirstOrder : Ty → Prop where
  | unit : FirstOrder .unit
  | bit : FirstOrder .bit
  | qubit : FirstOrder .qubit
  | tensor {A B} : FirstOrder A → FirstOrder B → FirstOrder (.tensor A B)

def firstOrderB : Ty → Bool
  | .unit | .bit | .qubit => true
  | .tensor A B => firstOrderB A && firstOrderB B
  | _ => false

theorem firstOrderB_sound {A : Ty} (h : A.firstOrderB = true) :
    FirstOrder A := by
  induction A with
  | unit => exact .unit
  | bit => exact .bit
  | qubit => exact .qubit
  | tensor A B ihA ihB =>
      simp only [firstOrderB, Bool.and_eq_true] at h
      exact .tensor (ihA h.1) (ihB h.2)
  | var n => simp [firstOrderB] at h
  | arrow κ A B => simp [firstOrderB] at h
  | mu A => simp [firstOrderB] at h

end Ty

namespace Term

/-- Explicit exclusion of recursive terms and recursive-type operations. -/
def recursionFree : Term → Bool
  | .var _ _ | .unit | .bitLit _ | .prim _ => true
  | .lam _ A M => A.muFree && recursionFree M
  | .app F X | .pair F X | .unpair F X => recursionFree F && recursionFree X
  | .ite B T E => recursionFree B && recursionFree T && recursionFree E
  | .measure Q K => recursionFree Q && recursionFree K
  | .fix _ _ | .fold _ _ | .unfold _ => false

@[simp] theorem recursionFree_fix (A M) :
    recursionFree (.fix A M) = false := rfl

@[simp] theorem recursionFree_fold (A M) :
    recursionFree (.fold A M) = false := rfl

@[simp] theorem recursionFree_unfold (M) :
    recursionFree (.unfold M) = false := rfl

end Term

/-- Compile-time values.  Closures and primitive partial applications are
eliminated before a successful result crosses the staging boundary. -/
inductive StagedValue (q c : ℕ) where
  | unit
  | bitLit : Bool → StagedValue q c
  | bitRef : Fin c → StagedValue q c
  | qubit : Fin q → StagedValue q c
  | pair : StagedValue q c → StagedValue q c → StagedValue q c
  | closure : Mode → Ty → Ty → Term →
      List (StagedValue q c) → List (StagedValue q c) → StagedValue q c
  | prim : Prim → StagedValue q c
  | cxControl : Fin q → StagedValue q c

namespace StagedValue

def ty {q c : ℕ} : StagedValue q c → Ty
  | .unit => .unit
  | .bitLit _ | .bitRef _ => .bit
  | .qubit _ => .qubit
  | .pair V W => .tensor V.ty W.ty
  | .closure κ A B _ _ _ => .arrow κ A B
  | .prim p => primTy p
  | .cxControl _ => .arrow .lin .qubit (.tensor .qubit .qubit)

/-- Every wire/slot in a first-order result was allocated by the final file. -/
def Respects {q c : ℕ} (ρ : RegFile q c) : StagedValue q c → Prop
  | .unit | .bitLit _ => True
  | .bitRef b => ρ.AllocatedC b
  | .qubit w => ρ.AllocatedQ w
  | .pair V W => V.Respects ρ ∧ W.Respects ρ
  | .closure _ _ _ _ _ _ | .prim _ | .cxControl _ => False

def respectsB {q c : ℕ} (ρ : RegFile q c) : StagedValue q c → Bool
  | .unit | .bitLit _ => true
  | .bitRef b => ρ.allocatedCB b
  | .qubit w => ρ.allocatedQB w
  | .pair V W => V.respectsB ρ && W.respectsB ρ
  | .closure _ _ _ _ _ _ | .prim _ | .cxControl _ => false

def same {q c : ℕ} : StagedValue q c → StagedValue q c → Bool
  | .unit, .unit => true
  | .bitLit a, .bitLit b => decide (a = b)
  | .bitRef a, .bitRef b => decide (a = b)
  | .qubit a, .qubit b => decide (a = b)
  | .pair A B, .pair A' B' => A.same A' && B.same B'
  | _, _ => false

theorem respectsB_sound {q c : ℕ} {ρ : RegFile q c}
    {V : StagedValue q c} (h : V.respectsB ρ = true) :
    V.Respects ρ := by
  cases V with
  | unit => trivial
  | bitLit b => trivial
  | bitRef b => exact RegFile.allocatedCB_sound h
  | qubit w => exact RegFile.allocatedQB_sound h
  | pair V W =>
      simp only [respectsB, Bool.and_eq_true] at h
      exact ⟨respectsB_sound h.1, respectsB_sound h.2⟩
  | closure κ A B M us ls => simp [respectsB] at h
  | prim p => simp [respectsB] at h
  | cxControl w => simp [respectsB] at h

end StagedValue

namespace Command

/-- Omit administrative skips while retaining source evaluation order. -/
def andThen {q c : ℕ} (A B : Command q c) : Command q c :=
  match A, B with
  | .skip, B => B
  | A, .skip => A
  | A, B => .seq A B

def wellFormedB {q c : ℕ} : Command q c → Bool
  | .skip | .x _ | .h _ | .t _ | .ry _ _ | .measure _ _
  | .reset _ | .store _ _ => true
  | .cx control target => decide (control ≠ target)
  | .seq A B => A.wellFormedB && B.wellFormedB
  | .branch _ yes no => yes.wellFormedB && no.wellFormedB

theorem wellFormedB_sound {q c : ℕ} {C : Command q c}
    (h : C.wellFormedB = true) : C.WellFormed := by
  induction C with
  | skip => exact .skip
  | x w => exact .x
  | h w => exact .h
  | t w => exact .t
  | ry θ w => exact .ry
  | cx control target =>
      exact .cx (by simpa [wellFormedB] using h)
  | measure qbit cbit => exact .measure
  | reset qbit => exact .reset
  | store cbit e => exact .store
  | seq A B ihA ihB =>
      simp only [wellFormedB, Bool.and_eq_true] at h
      exact .seq (ihA h.1) (ihB h.2)
  | branch guard yes no ihYes ihNo =>
      simp only [wellFormedB, Bool.and_eq_true] at h
      exact .branch (ihYes h.1) (ihNo h.2)

theorem andThen_wellFormed {q c : ℕ} {A B : Command q c}
    (hA : A.WellFormed) (hB : B.WellFormed) : (A.andThen B).WellFormed := by
  cases A <;> cases B <;> simp [andThen] at * <;>
    first | assumption | exact .seq hA hB

end Command

/-- Internal output of one staging pass. -/
structure StageResult (q c : ℕ) where
  value : StagedValue q c
  command : Command q c
  regs : RegFile q c

namespace StageResult

def pure {q c : ℕ} (ρ : RegFile q c) (V : StagedValue q c) :
    StageResult q c :=
  ⟨V, .skip, ρ⟩

def prepend {q c : ℕ} (A : Command q c) (r : StageResult q c) :
    StageResult q c :=
  { r with command := A.andThen r.command }

end StageResult

private def envTys {q c : ℕ} (ρ : List (StagedValue q c)) : List Ty :=
  ρ.map StagedValue.ty

private def finish {q c : ℕ} (A : Ty) (r : Option (StageResult q c)) :
    Option (StageResult q c) := do
  let out ← r
  if out.value.ty = A then some out else none

private def joinCommands {q c : ℕ}
    (A B C : Command q c) : Command q c :=
  (A.andThen B).andThen C

/- Fuelled deterministic CBV staging.  Every recursive call spends fuel,
including compile-time beta reduction. -/
mutual

  def stageFuel {q c : ℕ} : Nat → List (StagedValue q c) →
      List (StagedValue q c) → RegFile q c → Term →
      Option (StageResult q c)
    | 0, _, _, _, _ => none
    | fuel + 1, us, ls, ρ, M =>
        match infer (envTys us) (envTys ls) M with
        | none => none
        | some (A, _) =>
          finish A <| match M with
          | .var .unres n => do
              let V ← us[n]?
              pure (.pure ρ V)
          | .var .lin n => do
              let V ← ls[n]?
              pure (.pure ρ V)
          | .lam κ B Body =>
              match A with
              | .arrow κ' B' C =>
                  if κ = κ' ∧ B = B' then
                    some (.pure ρ (.closure κ B C Body us ls))
                  else none
              | _ => none
          | .app F X => do
              let rF ← stageFuel fuel us ls ρ F
              let rX ← stageFuel fuel us ls rF.regs X
              let rA ← applyFuel fuel rX.regs rF.value rX.value
              pure
                { rA with
                  command := joinCommands rF.command rX.command rA.command }
          | .unit => some (.pure ρ .unit)
          | .bitLit b => some (.pure ρ (.bitLit b))
          | .pair M N => do
              let rM ← stageFuel fuel us ls ρ M
              let rN ← stageFuel fuel us ls rM.regs N
              pure
                { value := .pair rM.value rN.value
                  command := rM.command.andThen rN.command
                  regs := rN.regs }
          | .unpair M K => do
              let rM ← stageFuel fuel us ls ρ M
              let (.pair V W) := rM.value | none
              let rK ← stageFuel fuel us ls rM.regs K
              let rV ← applyFuel fuel rK.regs rK.value V
              let rW ← applyFuel fuel rV.regs rV.value W
              pure
                { rW with
                  command :=
                    joinCommands
                      (rM.command.andThen rK.command) rV.command rW.command }
          | .ite B T E => do
              let rB ← stageFuel fuel us ls ρ B
              match rB.value with
              | .bitLit true =>
                  let rT ← stageFuel fuel us ls rB.regs T
                  pure (rT.prepend rB.command)
              | .bitLit false =>
                  let rE ← stageFuel fuel us ls rB.regs E
                  pure (rE.prepend rB.command)
              | .bitRef b =>
                  let rT ← stageFuel fuel us ls rB.regs T
                  let rE ← stageFuel fuel us ls rB.regs E
                  if rT.value.same rE.value &&
                      decide (rT.regs.nextQ = rE.regs.nextQ) &&
                      decide (rT.regs.nextC = rE.regs.nextC) then
                    some
                      { value := rT.value
                        command :=
                          rB.command.andThen
                            (.branch (.bit b) rT.command rE.command)
                        regs := rT.regs }
                  else none
              | _ => none
          | .prim p => some (.pure ρ (.prim p))
          | .measure Q K => do
              let rQ ← stageFuel fuel us ls ρ Q
              let (.qubit w) := rQ.value | none
              let (b, ρ') ← rQ.regs.allocC
              let rK ← stageFuel fuel us ls ρ' K
              let rB ← applyFuel fuel rK.regs rK.value (.bitRef b)
              let rOut ← applyFuel fuel rB.regs rB.value (.qubit w)
              pure
                { rOut with
                  command :=
                    joinCommands
                      (rQ.command.andThen (.measure w b))
                      (rK.command.andThen rB.command) rOut.command }
          | .fix _ _ | .fold _ _ | .unfold _ => none

  def applyFuel {q c : ℕ} : Nat → RegFile q c →
      StagedValue q c → StagedValue q c → Option (StageResult q c)
    | 0, _, _, _ => none
    | fuel + 1, ρ, F, X =>
        match F with
        | .closure κ A B Body us ls =>
            if X.ty = A then
              let out :=
                match κ with
                | .unres => stageFuel fuel (X :: us) ls ρ Body
                | .lin => stageFuel fuel us (X :: ls) ρ Body
              finish B out
            else none
        | .prim .new0 =>
            match X with
            | .unit => do
                let (w, ρ') ← ρ.allocQ
                pure ⟨.qubit w, .reset w, ρ'⟩
            | _ => none
        | .prim .x =>
            match X with
            | .qubit w => some ⟨.qubit w, .x w, ρ⟩
            | _ => none
        | .prim .h =>
            match X with
            | .qubit w => some ⟨.qubit w, .h w, ρ⟩
            | _ => none
        | .prim .t =>
            match X with
            | .qubit w => some ⟨.qubit w, .t w, ρ⟩
            | _ => none
        | .prim (.ry θ) =>
            match X with
            | .qubit w =>
                some ⟨.qubit w, .ry (.rational θ) w, ρ⟩
            | _ => none
        | .prim .reset =>
            match X with
            | .qubit w => some ⟨.qubit w, .reset w, ρ⟩
            | _ => none
        | .prim .cx =>
            match X with
            | .qubit w => some (.pure ρ (.cxControl w))
            | _ => none
        | .cxControl control =>
            match X with
            | .qubit target =>
                if control ≠ target then
                  some
                    ⟨.pair (.qubit control) (.qubit target),
                      .cx control target, ρ⟩
                else none
            | _ => none
        | _ => none

end

/-- A successful compilation is proof-carrying: source typing, first-order
boundary typing, allocated output resources, and target well-formedness are
all retained independently of the evaluator implementation. -/
structure Compilation (q c : ℕ) (M : Term) where
  sourceTy : Ty
  result : StagedValue q c
  command : Command q c
  finalRegs : RegFile q c
  source_typed : infer [] [] M = some (sourceTy, [])
  result_typed : result.ty = sourceTy
  first_order : Ty.FirstOrder sourceTy
  resources_preserved : result.Respects finalRegs
  command_wellFormed : command.WellFormed

/-- Compile a closed term into a fixed finite register file. -/
def elaborate {q c : ℕ} (fuel : Nat) (M : Term) :
    Option (Compilation q c M) :=
  if hfree : M.recursionFree = true then
    match hty : infer [] [] M with
    | none => none
    | some (A, u) =>
        if hu : u = [] then
          match stageFuel fuel [] [] (RegFile.empty q c) M with
          | none => none
          | some out =>
              if hout : out.value.ty = A then
                if hfirst : A.firstOrderB = true then
                  if hresources : out.value.respectsB out.regs = true then
                    if hwf : out.command.wellFormedB = true then
                      some
                        { sourceTy := A
                          result := out.value
                          command := out.command
                          finalRegs := out.regs
                          source_typed := by simpa [hu] using hty
                          result_typed := hout
                          first_order := Ty.firstOrderB_sound hfirst
                          resources_preserved :=
                            StagedValue.respectsB_sound hresources
                          command_wellFormed := Command.wellFormedB_sound hwf }
                    else none
                  else none
                else none
              else none
        else none
  else none

/-- Relational interface used by metatheorems. -/
def Elaborates {q c : ℕ} (fuel : Nat) (M : Term)
    (out : Compilation q c M) : Prop :=
  elaborate fuel M = some out

/-- Staging is deterministic for fixed fuel and register bounds. -/
theorem elaborates_deterministic {q c fuel M}
    {P Q : Compilation q c M}
    (hP : Elaborates fuel M P) (hQ : Elaborates fuel M Q) : P = Q := by
  exact Option.some.inj (hP.symm.trans hQ)

/-- Successful staging preserves the source type at the first-order boundary. -/
theorem elaborates_type_preservation {q c fuel M}
    {P : Compilation q c M} (_h : Elaborates fuel M P) :
    infer [] [] M = some (P.sourceTy, []) ∧
      P.result.ty = P.sourceTy ∧ Ty.FirstOrder P.sourceTy :=
  ⟨P.source_typed, P.result_typed, P.first_order⟩

/-- Every output handle belongs to the final compiler allocation prefix. -/
theorem elaborates_resource_preservation {q c fuel M}
    {P : Compilation q c M} (_h : Elaborates fuel M P) :
    P.result.Respects P.finalRegs :=
  P.resources_preserved

/-- The generated command satisfies target static well-formedness. -/
theorem elaborates_command_wellFormed {q c fuel M}
    {P : Compilation q c M} (_h : Elaborates fuel M P) :
    P.command.WellFormed :=
  P.command_wellFormed

/-- Allocation cursors never exceed the fixed target registers. -/
theorem elaborates_allocation_bounds {q c fuel M}
    {P : Compilation q c M} (_h : Elaborates fuel M P) :
    P.finalRegs.nextQ ≤ q ∧ P.finalRegs.nextC ≤ c :=
  ⟨P.finalRegs.nextQ_le, P.finalRegs.nextC_le⟩

/-- Existing target APIs identify staged-command semantics with the semantics
of its structurally compiled Composer block. -/
theorem elaborates_compile_agreement {q c fuel M}
    {P : Compilation q c M} (_h : Elaborates fuel M P)
    (model : Composer.Model q c) :
    QLambda.CQ.Eq
      (Composer.denoteBlock model P.command.compile)
      (P.command.denote model) :=
  Command.compile_denotation model P.command

/-- Erase certificates when only the generated command is needed. -/
def elaborateCommand {q c : ℕ} (fuel : Nat) (M : Term) :
    Option (Command q c) :=
  (elaborate (q := q) (c := c) fuel M).map Compilation.command

/-! ## Executable regression terms -/

private def newQubit : Term :=
  .app (.prim .new0) .unit

/-- Bell preparation `CX (H new0) new0` with compiler-allocated inputs. -/
def bellProgram : Term :=
  .app
    (.app (.prim .cx) (.app (.prim .h) newQubit))
    newQubit

/-- Measurement followed by classically controlled `X`. -/
def measuredControlProgram : Term :=
  .app measureX newQubit

/-- Reset an already allocated and used wire, demonstrating wire reuse. -/
def resetReuseProgram : Term :=
  .app (.prim .reset) (.app (.prim .x) newQubit)

private def gateTy : Ty :=
  .arrow .lin .qubit .qubit

/-- A compile-time higher-order gate compositor. -/
def gateCompose : Term :=
  .lam .lin gateTy <|
    .lam .lin gateTy <|
      .lam .lin .qubit <|
        .app (.var .lin 2)
          (.app (.var .lin 1) (.var .lin 0))

/-- Higher-order staging leaves only first-order `T; H` commands. -/
def higherOrderGateProgram : Term :=
  .app
    (.app
      (.app gateCompose (.prim .h))
      (.prim .t))
    newQubit

private def w20 : Fin 2 := ⟨0, by decide⟩
private def w21 : Fin 2 := ⟨1, by decide⟩
private def w10 : Fin 1 := ⟨0, by decide⟩
private def b10 : Fin 1 := ⟨0, by decide⟩

def bellExpected : Command 2 0 :=
  (((Command.reset w20).andThen (Command.h w20)).andThen
    (Command.reset w21)).andThen (Command.cx w20 w21)

def measuredControlExpected : Command 1 1 :=
  (Command.reset w10).andThen
    ((Command.measure w10 b10).andThen
      (Command.branch (.bit b10) (.x w10) .skip))

def resetReuseExpected : Command 1 0 :=
  ((Command.reset w10).andThen (Command.x w10)).andThen
    (Command.reset w10)

def higherOrderGateExpected : Command 1 0 :=
  (Command.reset w10).andThen ((Command.t w10).andThen (Command.h w10))

theorem bell_elaboration_test :
    elaborateCommand (q := 2) (c := 0) 10 bellProgram =
      some bellExpected := by
  rfl

theorem measured_control_elaboration_test :
    elaborateCommand (q := 1) (c := 1) 12 measuredControlProgram =
      some measuredControlExpected := by
  rfl

theorem reset_reuse_elaboration_test :
    elaborateCommand (q := 1) (c := 0) 12 resetReuseProgram =
      some resetReuseExpected := by
  rfl

theorem higher_order_gate_elaboration_test :
    elaborateCommand (q := 1) (c := 0) 12 higherOrderGateProgram =
      some higherOrderGateExpected := by
  rfl

/-- Insufficient quantum space fails rather than wrapping or aliasing. -/
theorem bell_allocation_bound_test :
    elaborateCommand (q := 1) (c := 0) 10 bellProgram = none := by
  rfl

/-- Recursion and recursive types are rejected before staging. -/
theorem recursion_excluded_test (A M) :
    elaborateCommand (q := 1) (c := 1) 12 (.fix A M) = none := by
  rfl

end QLambda.Linear
