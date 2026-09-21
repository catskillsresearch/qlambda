/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Composer.Model
import QLambda.Composer.WellFormed

/-!
# Compositional denotation of Composer circuits

The denotation is an ideal classical--quantum instrument, not a graph.
Structured-control signals are internal outcomes consumed by loops; the public
meaning forgets the internal signal and returns only the final classical
store. Barriers, boxes, and delays are semantic identities in this ideal
model, while their syntax remains available to the OpenQASM exporter.
-/

namespace QLambda.Composer

open QLambda.CQ

/-- Internal structured-control signal. -/
inductive Flow where
  | normal
  | break
  | continue
  deriving DecidableEq

abbrev FlowStore (c : ℕ) := CStore c × Flow

abbrev FlowSem (q c : ℕ) :=
  CStore c → FiniteInstrumentComp (QDim q) (FlowStore c)

/-- Regard an instrument as a finite computation returning its outcome index. -/
def instrumentComp {n m outcomes : ℕ} (I : QuantumInstrument n m outcomes)
    (h : n = m) : FiniteInstrumentComp n (Fin outcomes) := by
  subst m
  exact
    { Outcome := Fin outcomes
      branch := I.branch
      value := id
      trace_nonincreasing := I.trace_nonincreasing }

private def flowSkip {q c : ℕ} : FlowSem q c :=
  fun s => FiniteInstrumentComp.unit (s, .normal)

private def flowSeq {q c : ℕ} (F G : FlowSem q c) : FlowSem q c :=
  fun s => (F s).bind fun out =>
    match out.2 with
    | .normal => G out.1
    | signal => FiniteInstrumentComp.unit (out.1, signal)

private def flowSelect {q c : ℕ} (guard : CStore c → Bool)
    (yes no : FlowSem q c) : FlowSem q c :=
  fun s => if guard s then yes s else no s

private def runFor {q c : ℕ} : Nat → FlowSem q c → FlowSem q c
  | 0, _ => flowSkip
  | n + 1, body => fun s =>
      (body s).bind fun out =>
        match out.2 with
        | .break => FiniteInstrumentComp.unit (out.1, .normal)
        | .normal | .continue => runFor n body out.1

private def runWhile {q c : ℕ} : Nat → (CStore c → Bool) → FlowSem q c → FlowSem q c
  | 0, _, _ => flowSkip
  | n + 1, guard, body => fun s =>
      if guard s then
        (body s).bind fun out =>
          match out.2 with
          | .break => FiniteInstrumentComp.unit (out.1, .normal)
          | .normal | .continue => runWhile n guard body out.1
      else
        FiniteInstrumentComp.unit (s, .normal)

mutual

  /-- Internal denotation of a block, retaining structured-control signals. -/
  noncomputable def denoteFlowBlock {q c : ℕ} (model : Model q c) :
      List (Instr q c) → FlowSem q c
    | [] => flowSkip
    | i :: is => flowSeq (denoteFlowInstr model i) (denoteFlowBlock model is)

  /-- Internal denotation of one instruction. -/
  noncomputable def denoteFlowInstr {q c : ℕ} (model : Model q c) :
      Instr q c → FlowSem q c
    | .gate g => fun s =>
        FiniteInstrumentComp.ofOperation (model.gate g) (s, .normal)
    | .measure qbit cbit => fun s =>
        (instrumentComp (model.measure qbit) rfl).map fun outcome =>
          (Function.update s cbit (outcome = 1), .normal)
    | .reset qbit => fun s =>
        FiniteInstrumentComp.ofOperation (model.reset qbit) (s, .normal)
    | .store cbit e => fun s =>
        FiniteInstrumentComp.unit (Function.update s cbit (e.eval s), .normal)
    | .barrier _ => flowSkip
    | .delay _ _ => flowSkip
    | .ite guard yes no =>
        flowSelect (guard.eval ·) (denoteFlowBlock model yes) (denoteFlowBlock model no)
    | .switch guard cases =>
        denoteFlowCases model (guard.eval ·) cases
    | .forLoop count body =>
        runFor count (denoteFlowBlock model body)
    | .whileLoop fuel guard body =>
        runWhile fuel (guard.eval ·) (denoteFlowBlock model body)
    | .box _ body => denoteFlowBlock model body
    | .break => fun s => FiniteInstrumentComp.unit (s, .break)
    | .continue => fun s => FiniteInstrumentComp.unit (s, .continue)

  /-- First matching Boolean switch case; absent case means identity. -/
  noncomputable def denoteFlowCases {q c : ℕ} (model : Model q c)
      (scrutinee : CStore c → Bool) :
      List (Bool × List (Instr q c)) → FlowSem q c
    | [] => flowSkip
    | branch :: rest =>
        flowSelect
          (fun s => scrutinee s == branch.1)
          (denoteFlowBlock model branch.2)
          (denoteFlowCases model scrutinee rest)

end

mutual

  /-- Public denotation of one instruction.

  Branching and boxes use the public block fold directly. Loops retain the
  internal flow semantics so their `break`/`continue` instructions are
  consumed before returning to top-level sequencing. -/
  noncomputable def denoteInstr {q c : ℕ} (model : Model q c) :
      Instr q c → Sem q c
    | .ite guard yes no =>
        CQ.select (guard.eval ·) (denoteBlock model no) (denoteBlock model yes)
    | .switch guard cases =>
        denoteCases model (guard.eval ·) cases
    | .box _ body => denoteBlock model body
    | i => fun s => (denoteFlowInstr model i s).map Prod.fst

  /-- Public, compositional denotation of a top-level block.

  Top-level well-formedness excludes unhandled `break` and `continue`;
  sequencing is precisely CQ Kleisli composition. -/
  noncomputable def denoteBlock {q c : ℕ} (model : Model q c) :
      List (Instr q c) → Sem q c
    | [] => CQ.skip
    | i :: is => CQ.seq (denoteInstr model i) (denoteBlock model is)

  /-- Public denotation of the first matching Boolean switch branch. -/
  noncomputable def denoteCases {q c : ℕ} (model : Model q c)
      (scrutinee : CStore c → Bool) :
      List (Bool × List (Instr q c)) → Sem q c
    | [] => CQ.skip
    | branch :: rest =>
        CQ.select
          (fun s => scrutinee s == branch.1)
          (denoteCases model scrutinee rest)
          (denoteBlock model branch.2)

end

/-- The meaning of a complete circuit is its CQ denotation. -/
noncomputable def Program.denote {v : Version} {q c : ℕ} (model : Model q c)
    (P : Program v q c) : Sem q c :=
  denoteBlock model P.body

@[simp] theorem denoteFlowBlock_nil {q c : ℕ} (model : Model q c) :
    denoteFlowBlock model [] = flowSkip :=
  rfl

@[simp] theorem denoteFlowBlock_cons {q c : ℕ} (model : Model q c)
    (i : Instr q c) (is : List (Instr q c)) :
    denoteFlowBlock model (i :: is) =
      flowSeq (denoteFlowInstr model i) (denoteFlowBlock model is) :=
  rfl

@[simp] theorem denoteFlow_for_zero {q c : ℕ} (model : Model q c)
    (body : List (Instr q c)) :
    denoteFlowInstr model (.forLoop 0 body) = flowSkip :=
  rfl

@[simp] theorem denoteFlow_while_zero {q c : ℕ} (model : Model q c)
    (guard : CExpr c) (body : List (Instr q c)) :
    denoteFlowInstr model (.whileLoop 0 guard body) = flowSkip :=
  rfl

@[simp] theorem denoteBlock_nil {q c : ℕ} (model : Model q c) :
    denoteBlock model [] = CQ.skip :=
  rfl

@[simp] theorem denoteBlock_cons {q c : ℕ} (model : Model q c)
    (i : Instr q c) (is : List (Instr q c)) :
    denoteBlock model (i :: is) =
      CQ.seq (denoteInstr model i) (denoteBlock model is) :=
  rfl

end QLambda.Composer
