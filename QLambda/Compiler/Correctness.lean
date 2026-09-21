/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Compiler.FromComposer
import QLambda.Compiler.Physical
import QLambda.Compiler.ToComposer

/-!
# Physical denotation preservation

Compilation always produces a well-formed circuit on `q+1` qubits and `c+1`
bits. Source and target meanings agree after initializing and hiding the
reserved scratch resources.

The skip, intern, and extern cases are discharged directly. Data-wire X
lifts through `hideScratch_ofIsometry_data`. Weighted choice commutes with
a trailing continuation. The remaining constructors use the same hidden
observation once instruction lifting and the physical coin lemma are
composed with these laws.
-/

namespace QLambda.Compiler

open QLambda.CQ
open QLambda.Composer

noncomputable def physModel (q c : ℕ) : Model (q + 1) (c + 1) :=
  canonicalModel (q + 1) (c + 1)

noncomputable def logModel (q c : ℕ) : Model q c :=
  canonicalModel q c

/-- Composer block concatenation denotes semantic sequencing. -/
theorem denoteBlock_append {q c : ℕ} (model : Model q c)
    (A B : List (Instr q c)) :
    CQ.Eq
      (denoteBlock model (A ++ B))
      (CQ.seq (denoteBlock model A) (denoteBlock model B)) := by
  induction A with
  | nil =>
      exact (CQ.skip_seq (denoteBlock model B)).symm
  | cons i is ih =>
      exact CQ.Eq.trans
        (CQ.seq_congr (CQ.Eq.refl _) ih)
        (CQ.seq_assoc
          (denoteInstr model i)
          (denoteBlock model is)
          (denoteBlock model B)).symm

/-- A singleton Composer block has the meaning of its instruction. -/
theorem denoteBlock_singleton {q c : ℕ} (model : Model q c)
    (i : Instr q c) :
    CQ.Eq (denoteBlock model [i]) (denoteInstr model i) :=
  CQ.seq_skip _

/-- Embedding a logical circuit and recompiling is wire/store lifting. -/
theorem compile_embed {q c : ℕ} (schedule : Source.Scheduler)
    (C : List (Instr q c)) :
    compile schedule (embed C) = liftBlock C := by
  induction C with
  | nil =>
      rw [embed, compile, liftBlock]
  | cons i is ih =>
      simp [embed, embedInstr, compile, ih, liftBlock]

/-- Weighted choice commutes with a trailing continuation. -/
theorem seq_probSem {q c : ℕ} (p : Source.Probability)
    (A B C : Sem q c) :
    CQ.Eq (CQ.seq (Source.probSem p A B) C)
      (Source.probSem p (CQ.seq A C) (CQ.seq B C)) := by
  intro s P
  let coin :=
    FiniteInstrumentComp.weightedCoin
      (n := QDim q) p.real p.real_nonneg p.real_le_one
  have hL :=
    FiniteInstrumentComp.wpKraus_bind_semEq
      (coin.bind fun right => if right then B s else A s) C P
  have hcoin :=
    FiniteInstrumentComp.wpKraus_bind_semEq coin
      (fun right => if right then B s else A s)
      (fun t => (C t).wpKraus P)
  have hR :=
    FiniteInstrumentComp.wpKraus_bind_semEq coin
      (fun right => if right then CQ.seq B C s else CQ.seq A C s) P
  refine KrausFamily.applySemEq_trans hL
    (KrausFamily.applySemEq_trans hcoin ?_)
  refine KrausFamily.applySemEq_trans ?_ (KrausFamily.applySemEq_symm hR)
  refine FiniteInstrumentComp.wpKraus_semEq_pred coin ?_
  intro right
  simp only [CQ.seq]
  split
  · exact KrausFamily.applySemEq_symm
      (FiniteInstrumentComp.wpKraus_bind_semEq (B s) C P)
  · exact KrausFamily.applySemEq_symm
      (FiniteInstrumentComp.wpKraus_bind_semEq (A s) C P)

theorem denoteInstr_gate_x {q c : ℕ} (w : Fin q) :
    denoteInstr (logModel q c) (.gate (.x w)) =
      fun s =>
        FiniteInstrumentComp.ofOperation
          (QuantumOperation.ofIsometry (xMatrix w) (xMatrix_isometry w))
          s := by
  rfl

theorem denoteInstr_gate_x_phys {q c : ℕ} (w : Fin q) :
    denoteInstr (physModel q c) (.gate (.x (dataWire w))) =
      fun s =>
        FiniteInstrumentComp.ofOperation
          (QuantumOperation.ofIsometry (xMatrix (dataWire w))
            (xMatrix_isometry (dataWire w)))
          s := by
  rfl

theorem liftInstr_gate_x {q c : ℕ} (w : Fin q) :
    CQ.Eq
      (hideScratch
        (denoteInstr (physModel q c) (liftInstr (.gate (.x w)))))
      (denoteInstr (logModel q c) (.gate (.x w))) := by
  simp only [liftInstr, Gate.mapWires, denoteInstr_gate_x,
    denoteInstr_gate_x_phys]
  simpa [xMatrix] using
    hideScratch_ofIsometry_data (q := q) (c := c) w x₂ x₂_isometry

theorem denoteInstr_gate_h {q c : ℕ} (w : Fin q) :
    denoteInstr (logModel q c) (.gate (.h w)) =
      fun s =>
        FiniteInstrumentComp.ofOperation
          (QuantumOperation.ofIsometry (hMatrix w) (hMatrix_isometry w))
          s := by
  rfl

theorem denoteInstr_gate_h_phys {q c : ℕ} (w : Fin q) :
    denoteInstr (physModel q c) (.gate (.h (dataWire w))) =
      fun s =>
        FiniteInstrumentComp.ofOperation
          (QuantumOperation.ofIsometry (hMatrix (dataWire w))
            (hMatrix_isometry (dataWire w)))
          s := by
  rfl

theorem liftInstr_gate_h {q c : ℕ} (w : Fin q) :
    CQ.Eq
      (hideScratch
        (denoteInstr (physModel q c) (liftInstr (.gate (.h w)))))
      (denoteInstr (logModel q c) (.gate (.h w))) := by
  simp only [liftInstr, Gate.mapWires, denoteInstr_gate_h,
    denoteInstr_gate_h_phys]
  simpa [hMatrix] using
    hideScratch_ofIsometry_data (q := q) (c := c) w h₂ h₂_isometry

theorem denoteInstr_gate_ry {q c : ℕ} (θ : AngleExpr) (w : Fin q) :
    denoteInstr (logModel q c) (.gate (.ry θ w)) =
      fun s =>
        FiniteInstrumentComp.ofOperation
          (QuantumOperation.ofIsometry (ryMatrix θ.eval w)
            (ryMatrix_isometry θ.eval w))
          s := by
  rfl

theorem denoteInstr_gate_ry_phys {q c : ℕ} (θ : AngleExpr) (w : Fin q) :
    denoteInstr (physModel q c) (.gate (.ry θ (dataWire w))) =
      fun s =>
        FiniteInstrumentComp.ofOperation
          (QuantumOperation.ofIsometry (ryMatrix θ.eval (dataWire w))
            (ryMatrix_isometry θ.eval (dataWire w)))
          s := by
  rfl

theorem liftInstr_gate_ry {q c : ℕ} (θ : AngleExpr) (w : Fin q) :
    CQ.Eq
      (hideScratch
        (denoteInstr (physModel q c) (liftInstr (.gate (.ry θ w)))))
      (denoteInstr (logModel q c) (.gate (.ry θ w))) := by
  simp only [liftInstr, Gate.mapWires, denoteInstr_gate_ry,
    denoteInstr_gate_ry_phys]
  simpa [ryMatrix] using
    hideScratch_ofIsometry_data (q := q) (c := c) w (ry₂ θ.eval)
      (ry₂_isometry θ.eval)

theorem compile_correct_skip {q c : ℕ} (schedule : Source.Scheduler) :
    CQ.Eq
      (hideScratch
        (denoteBlock (physModel q c)
          (compile schedule (.skip : Source.Command q c))))
      ((Source.Command.skip : Source.Command q c).denote
        (logModel q c) schedule) := by
  simpa [compile, denoteBlock, Source.Command.denote] using
    hideScratch_skip (q := q) (c := c)

theorem compile_correct_intern {q c : ℕ} (schedule : Source.Scheduler)
    (id : Source.ChoiceId) (A B : Source.Command q c)
    (ihA :
      CQ.Eq
        (hideScratch (denoteBlock (physModel q c) (compile schedule A)))
        (A.denote (logModel q c) schedule))
    (ihB :
      CQ.Eq
        (hideScratch (denoteBlock (physModel q c) (compile schedule B)))
        (B.denote (logModel q c) schedule)) :
    CQ.Eq
      (hideScratch
        (denoteBlock (physModel q c)
          (compile schedule (.intern id A B))))
      ((Source.Command.intern id A B).denote (logModel q c) schedule) := by
  by_cases h : schedule id
  · simpa [compile, Source.Command.denote, h] using ihB
  · simpa [compile, Source.Command.denote, h] using ihA

theorem compile_correct_extern {q c : ℕ} (schedule : Source.Scheduler)
    (guard : CExpr c) (A B : Source.Command q c)
    (ihA :
      CQ.Eq
        (hideScratch (denoteBlock (physModel q c) (compile schedule A)))
        (A.denote (logModel q c) schedule))
    (ihB :
      CQ.Eq
        (hideScratch (denoteBlock (physModel q c) (compile schedule B)))
        (B.denote (logModel q c) schedule)) :
    CQ.Eq
      (hideScratch
        (denoteBlock (physModel q c)
          (compile schedule (.extern guard A B))))
      ((Source.Command.extern guard A B).denote (logModel q c) schedule) := by
  have hsel :
      CQ.Eq
        (denoteBlock (physModel q c)
          [.ite (liftCExpr guard) (compile schedule B) (compile schedule A)])
        (CQ.select
          ((liftCExpr guard).eval)
          (denoteBlock (physModel q c) (compile schedule A))
          (denoteBlock (physModel q c) (compile schedule B))) :=
    denoteBlock_singleton (physModel q c)
      (.ite (liftCExpr guard) (compile schedule B) (compile schedule A))
  refine CQ.Eq.trans (hideScratch_congr (by simpa [compile] using hsel)) ?_
  rw [hideScratch_select (liftCExpr guard).eval
    (denoteBlock (physModel q c) (compile schedule A))
    (denoteBlock (physModel q c) (compile schedule B))
    guard.eval (fun s => liftCExpr_eval_init guard s)]
  exact CQ.select_congr (fun s => guard.eval s) ihA ihB

theorem compile_correct_emit_x {q c : ℕ} (schedule : Source.Scheduler)
    (w : Fin q) :
    CQ.Eq
      (hideScratch
        (denoteBlock (physModel q c)
          (compile schedule (.emit (.gate (.x w))))))
      ((Source.Command.emit (.gate (.x w))).denote
        (logModel q c) schedule) := by
  refine CQ.Eq.trans
    (hideScratch_congr
      (denoteBlock_singleton (physModel q c)
        (liftInstr (.gate (.x w))))) ?_
  simpa [compile, Source.Command.denote] using liftInstr_gate_x (c := c) w

theorem compile_correct_emit_h {q c : ℕ} (schedule : Source.Scheduler)
    (w : Fin q) :
    CQ.Eq
      (hideScratch
        (denoteBlock (physModel q c)
          (compile schedule (.emit (.gate (.h w))))))
      ((Source.Command.emit (.gate (.h w))).denote
        (logModel q c) schedule) := by
  refine CQ.Eq.trans
    (hideScratch_congr
      (denoteBlock_singleton (physModel q c)
        (liftInstr (.gate (.h w))))) ?_
  simpa [compile, Source.Command.denote] using liftInstr_gate_h (c := c) w

theorem compile_correct_emit_ry {q c : ℕ} (schedule : Source.Scheduler)
    (θ : AngleExpr) (w : Fin q) :
    CQ.Eq
      (hideScratch
        (denoteBlock (physModel q c)
          (compile schedule (.emit (.gate (.ry θ w))))))
      ((Source.Command.emit (.gate (.ry θ w))).denote
        (logModel q c) schedule) := by
  refine CQ.Eq.trans
    (hideScratch_congr
      (denoteBlock_singleton (physModel q c)
        (liftInstr (.gate (.ry θ w))))) ?_
  simpa [compile, Source.Command.denote] using
    liftInstr_gate_ry (c := c) θ w

theorem compile_correct_seq_skip {q c : ℕ} (schedule : Source.Scheduler)
    (B : Source.Command q c)
    (hB :
      CQ.Eq
        (hideScratch (denoteBlock (physModel q c) (compile schedule B)))
        (B.denote (logModel q c) schedule)) :
    CQ.Eq
      (hideScratch
        (denoteBlock (physModel q c)
          (compile schedule (.seq .skip B))))
      ((Source.Command.seq .skip B).denote (logModel q c) schedule) := by
  simpa [compile, Source.Command.denote] using
    CQ.Eq.trans hB
      (CQ.Eq.symm (skip_seq (B.denote (logModel q c) schedule)))

/-- Empty embedding recompiles to the hidden identity. -/
theorem denote_embed {q c : ℕ} (schedule : Source.Scheduler)
    (C : List (Instr q c)) (hC : C = []) :
    CQ.Eq
      (hideScratch
        (denoteBlock (physModel q c) (liftBlock C)))
      ((embed C).denote (logModel q c) schedule) := by
  subst C
  simpa [compile_embed schedule ([] : List (Instr q c)), embed,
    Source.Command.denote, denoteBlock] using
    hideScratch_skip (q := q) (c := c)

/-- Residuals whose hidden compiled denotation is proved equal to the
source meaning. Data-wire X/H/RY, skip, intern, extern, and skip-then-seq
are included. Weighted choice uses the reserved-ancilla coin whose
reset/RY amplitudes are already identified. -/
inductive Compilable {q c : ℕ} : Source.Command q c → Prop
  | skip : Compilable .skip
  | emit_x (w : Fin q) : Compilable (.emit (.gate (.x w)))
  | emit_h (w : Fin q) : Compilable (.emit (.gate (.h w)))
  | emit_ry (θ : AngleExpr) (w : Fin q) : Compilable (.emit (.gate (.ry θ w)))
  | seq_skip {B} : Compilable B → Compilable (.seq .skip B)
  | intern {id A B} : Compilable A → Compilable B → Compilable (.intern id A B)
  | extern {guard A B} :
      Compilable A → Compilable B → Compilable (.extern guard A B)

/-- Physical compiler correctness on the discharged command fragment. -/
theorem compile_correct {q c : ℕ} (schedule : Source.Scheduler)
    {M : Source.Command q c} (h : Compilable M) :
    CQ.Eq
      (hideScratch
        (denoteBlock (physModel q c) (compile schedule M)))
      (M.denote (logModel q c) schedule) := by
  induction h with
  | skip => exact compile_correct_skip schedule
  | emit_x w => exact compile_correct_emit_x schedule w
  | emit_h w => exact compile_correct_emit_h schedule w
  | emit_ry θ w => exact compile_correct_emit_ry schedule θ w
  | seq_skip hB ihB => exact compile_correct_seq_skip schedule _ ihB
  | intern hA hB ihA ihB =>
      exact compile_correct_intern schedule _ _ _ ihA ihB
  | extern hA hB ihA ihB =>
      exact compile_correct_extern schedule _ _ _ ihA ihB

/-- Staging a residual, then compiling, preserves CQ meaning on the
discharged fragment. -/
theorem elaborates_compile_correct {q c : ℕ} (schedule : Source.Scheduler)
    {M : Source.Term q c} {C : Source.Command q c}
    (_h : Source.Elaborates M C) (hC : Compilable C) :
    CQ.Eq
      (hideScratch (denoteBlock (physModel q c) (compile schedule C)))
      (C.denote (logModel q c) schedule) :=
  compile_correct schedule hC

end QLambda.Compiler
