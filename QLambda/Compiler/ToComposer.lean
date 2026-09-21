/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Compiler.ChoiceLowering

/-!
# qλ residual command to Composer

Internal choices are resolved by the supplied scheduler, external choices
remain dynamic Composer conditionals, and probabilistic choices use the
reserved final qubit and bit.
-/

namespace QLambda.Compiler

/-- Rename a classical expression into the data portion of a physical store. -/
def liftCExpr {c : ℕ} : Composer.CExpr c → Composer.CExpr (c + 1)
  | .lit b => .lit b
  | .bit i => .bit (CQ.dataBit i)
  | .not e => .not (liftCExpr e)
  | .and e₁ e₂ => .and (liftCExpr e₁) (liftCExpr e₂)
  | .or e₁ e₂ => .or (liftCExpr e₁) (liftCExpr e₂)
  | .xor e₁ e₂ => .xor (liftCExpr e₁) (liftCExpr e₂)

mutual

  /-- Lift one logical normalized-core instruction. -/
  def liftInstr {q c : ℕ} :
      Composer.Instr q c → Composer.Instr (q + 1) (c + 1)
    | .gate g => .gate (g.mapWires CQ.dataWire)
    | .measure qbit cbit => .measure (CQ.dataWire qbit) (CQ.dataBit cbit)
    | .reset qbit => .reset (CQ.dataWire qbit)
    | .store cbit e => .store (CQ.dataBit cbit) (liftCExpr e)
    | .barrier qs => .barrier (qs.map CQ.dataWire)
    | .delay duration qs => .delay duration (qs.map CQ.dataWire)
    | .ite guard yes no =>
        .ite (liftCExpr guard) (liftBlock yes) (liftBlock no)
    | .switch guard cases =>
        .switch (liftCExpr guard) (liftCases cases)
    | .forLoop count body => .forLoop count (liftBlock body)
    | .whileLoop fuel guard body =>
        .whileLoop fuel (liftCExpr guard) (liftBlock body)
    | .box label body => .box label (liftBlock body)
    | .break => .break
    | .continue => .continue
  termination_by i => sizeOf i

  /-- Lift every instruction in a logical block. -/
  def liftBlock {q c : ℕ} :
      List (Composer.Instr q c) → List (Composer.Instr (q + 1) (c + 1))
    | [] => []
    | i :: is => liftInstr i :: liftBlock is
  termination_by is => sizeOf is

  /-- Lift switch branches without hiding recursive calls under `List.map`. -/
  def liftCases {q c : ℕ} :
      List (Bool × List (Composer.Instr q c)) →
        List (Bool × List (Composer.Instr (q + 1) (c + 1)))
    | [] => []
    | (key, body) :: cases => (key, liftBlock body) :: liftCases cases
  termination_by cases => sizeOf cases

end

@[simp] theorem liftBlock_nil {q c : ℕ} :
    liftBlock ([] : List (Composer.Instr q c)) = [] := by
  rw [liftBlock]

@[simp] theorem liftBlock_cons {q c : ℕ} (i : Composer.Instr q c)
    (is : List (Composer.Instr q c)) :
    liftBlock (i :: is) = liftInstr i :: liftBlock is := by
  rw [liftBlock]

@[simp] theorem liftCases_nil {q c : ℕ} :
    liftCases ([] : List (Bool × List (Composer.Instr q c))) = [] := by
  rw [liftCases]

@[simp] theorem liftCases_cons {q c : ℕ} (key : Bool)
    (body : List (Composer.Instr q c))
    (cases : List (Bool × List (Composer.Instr q c))) :
    liftCases ((key, body) :: cases) =
      (key, liftBlock body) :: liftCases cases := by
  rw [liftCases]

theorem liftCases_map_fst {q c : ℕ}
    (cases : List (Bool × List (Composer.Instr q c))) :
    (liftCases cases).map Prod.fst = cases.map Prod.fst := by
  induction cases with
  | nil => simp
  | cons b rest ih =>
      rcases b with ⟨key, body⟩
      simp [ih]

private theorem dataWire_injective {q : ℕ} :
    Function.Injective (@CQ.dataWire q) := by
  intro i j h
  exact Fin.castSucc_injective q h

mutual

  theorem liftInstr_wellFormedAt {q c depth} {i : Composer.Instr q c}
      (h : Composer.Instr.WellFormedAt depth i) :
      Composer.Instr.WellFormedAt depth (liftInstr i) := by
    cases h with
    | @gate _ g hg =>
        simp only [liftInstr]
        apply Composer.Instr.WellFormedAt.gate
        cases g <;>
          simp_all [Composer.Gate.WellFormed, Composer.Gate.mapWires,
            dataWire_injective.eq_iff]
    | measure =>
        simpa only [liftInstr] using Composer.Instr.WellFormedAt.measure
    | reset =>
        simpa only [liftInstr] using Composer.Instr.WellFormedAt.reset
    | store =>
        simpa only [liftInstr] using Composer.Instr.WellFormedAt.store
    | barrier hnodup =>
        simpa only [liftInstr] using Composer.Instr.WellFormedAt.barrier
          (hnodup.map dataWire_injective)
    | delay hnodup =>
        simpa only [liftInstr] using Composer.Instr.WellFormedAt.delay
          (hnodup.map dataWire_injective)
    | ite hyes hno =>
        simpa only [liftInstr] using Composer.Instr.WellFormedAt.ite
          (liftBlock_wellFormedAt hyes) (liftBlock_wellFormedAt hno)
    | switch hkeys hbranches =>
        rename_i guard cases
        simp only [liftInstr]
        apply Composer.Instr.WellFormedAt.switch
        · simpa [liftCases_map_fst] using hkeys
        · exact liftCases_wellFormedAt cases hbranches
    | forLoop hbody =>
        simpa only [liftInstr] using Composer.Instr.WellFormedAt.forLoop
          (liftBlock_wellFormedAt hbody)
    | whileLoop hbody =>
        simpa only [liftInstr] using Composer.Instr.WellFormedAt.whileLoop
          (liftBlock_wellFormedAt hbody)
    | box hlabel hbody =>
        simpa only [liftInstr] using Composer.Instr.WellFormedAt.box hlabel
          (liftBlock_wellFormedAt hbody)

  theorem liftCases_wellFormedAt {q c depth}
      (cases : List (Bool × List (Composer.Instr q c)))
      (h : ∀ branch ∈ cases, Composer.Block.WellFormedAt depth branch.2)
      (branch : Bool × List (Composer.Instr (q + 1) (c + 1)))
      (hbranch : branch ∈ liftCases cases) :
      Composer.Block.WellFormedAt depth branch.2 := by
    match cases with
    | [] => simp at hbranch
    | (key, body) :: rest =>
        simp only [liftCases_cons, List.mem_cons] at hbranch
        rcases hbranch with hhead | htail
        · subst branch
          exact liftBlock_wellFormedAt (h (key, body) (by simp))
        · exact liftCases_wellFormedAt rest
            (fun b hb => h b (by simp [hb])) branch htail

  theorem liftBlock_wellFormedAt {q c depth}
      {is : List (Composer.Instr q c)}
      (h : Composer.Block.WellFormedAt depth is) :
      Composer.Block.WellFormedAt depth (liftBlock is) := by
    cases h with
    | nil =>
        simpa only [liftBlock] using
          (Composer.Block.WellFormedAt.nil :
            Composer.Block.WellFormedAt depth
              ([] : List (Composer.Instr (q + 1) (c + 1))))
    | cons hi his =>
        simpa only [liftBlock] using Composer.Block.WellFormedAt.cons
          (liftInstr_wellFormedAt hi) (liftBlock_wellFormedAt his)

end

theorem block_wellFormedAt_append {q c depth}
    {A B : List (Composer.Instr q c)}
    (hA : Composer.Block.WellFormedAt depth A)
    (hB : Composer.Block.WellFormedAt depth B) :
    Composer.Block.WellFormedAt depth (A ++ B) := by
  induction A with
  | nil =>
      exact hB
  | cons i is ih =>
      cases hA with
      | cons hi his =>
          exact Composer.Block.WellFormedAt.cons hi (ih his)

/-- Compile a terminating logical residual to a physical Composer block. -/
def compile {q c : ℕ} (schedule : Source.Scheduler) :
    Source.Command q c → List (Composer.Instr (q + 1) (c + 1))
  | .skip => []
  | .emit i => [liftInstr i]
  | .seq A B => compile schedule A ++ compile schedule B
  | .prob p A B =>
      physicalCoin p (compile schedule A) (compile schedule B)
  | .intern id A B =>
      if schedule id then compile schedule B else compile schedule A
  | .extern guard A B =>
      [.ite (liftCExpr guard) (compile schedule B) (compile schedule A)]

@[simp] theorem compile_skip {q c : ℕ} (schedule : Source.Scheduler) :
    compile schedule (.skip : Source.Command q c) = [] :=
  rfl

@[simp] theorem compile_emit {q c : ℕ} (schedule : Source.Scheduler)
    (i : Composer.Instr q c) :
    compile schedule (.emit i) = [liftInstr i] :=
  rfl

theorem liftCExpr_eval {c : ℕ} (e : Composer.CExpr c) (s : CQ.CStore (c + 1)) :
    (liftCExpr e).eval s = e.eval (CQ.hideStore s) := by
  induction e with
  | lit b => rfl
  | bit i =>
      simp [liftCExpr, Composer.CExpr.eval, CQ.hideStore, CQ.dataBit]
  | not e ih =>
      simp [liftCExpr, Composer.CExpr.eval, ih]
  | and e₁ e₂ ih₁ ih₂ =>
      simp [liftCExpr, Composer.CExpr.eval, ih₁, ih₂]
  | or e₁ e₂ ih₁ ih₂ =>
      simp [liftCExpr, Composer.CExpr.eval, ih₁, ih₂]
  | xor e₁ e₂ ih₁ ih₂ =>
      simp [liftCExpr, Composer.CExpr.eval, ih₁, ih₂]

theorem liftCExpr_eval_init {c : ℕ} (e : Composer.CExpr c) (s : CQ.CStore c) :
    (liftCExpr e).eval (CQ.initStore s) = e.eval s := by
  simpa [CQ.hideStore_initStore] using liftCExpr_eval e (CQ.initStore s)

@[simp] theorem compile_seq {q c : ℕ} (schedule : Source.Scheduler)
    (A B : Source.Command q c) :
    compile schedule (.seq A B) =
      compile schedule A ++ compile schedule B :=
  rfl

/-- The versioned physical program emitted by the compiler. -/
def compileProgram {q c : ℕ} (schedule : Source.Scheduler)
    (M : Source.Command q c) :
    Composer.Program .openQASM3_0_ibmComposer_2026_09 (q + 1) (c + 1) :=
  ⟨compile schedule M⟩

theorem compile_wellFormed {q c : ℕ} {schedule : Source.Scheduler}
    {M : Source.Command q c} (hM : M.WellFormed) :
    (compileProgram schedule M).WellFormed := by
  induction hM with
  | skip => exact Composer.Block.WellFormedAt.nil
  | emit hi =>
      exact Composer.Block.WellFormedAt.cons
        (liftInstr_wellFormedAt hi) Composer.Block.WellFormedAt.nil
  | seq hA hB ihA ihB =>
      exact block_wellFormedAt_append ihA ihB
  | prob hA hB ihA ihB =>
      exact physicalCoin_wellFormed ihA ihB
  | intern hA hB ihA ihB =>
      simp only [compileProgram, compile]
      split <;> assumption
  | extern hA hB ihA ihB =>
      exact Composer.Block.WellFormedAt.cons
        (Composer.Instr.WellFormedAt.ite ihB ihA)
        Composer.Block.WellFormedAt.nil

end QLambda.Compiler
