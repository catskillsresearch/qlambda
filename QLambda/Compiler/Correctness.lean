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

On the discharged fragment — supported gates, measurement, reset, store,
sequencing, probabilistic choice, and internal or external choice — the
hidden denotation of the compiled `q+1,c+1` circuit equals the source
meaning. Embedding a block of those instructions and recompiling it agrees
as well.
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

theorem denoteInstr_store_eq {q c : ℕ} (model : Model q c) (b : Fin c)
    (e : CExpr c) :
    CQ.Eq (denoteInstr model (.store b e))
      (fun s => FiniteInstrumentComp.unit (Function.update s b (e.eval s))) := by
  intro s P ρ
  simp only [denoteInstr, denoteFlowInstr, FiniteInstrumentComp.map,
    FiniteInstrumentComp.unit, FiniteInstrumentComp.applyMat_wpKraus,
    Function.comp_apply]

theorem denoteInstr_measure_eq {q c : ℕ} (model : Model q c) (w : Fin q)
    (b : Fin c) :
    CQ.Eq (denoteInstr model (.measure w b))
      (fun s =>
        (instrumentComp (model.measure w) rfl).map
          (fun o : Fin 2 => Function.update s b (o = 1))) := by
  intro s P ρ
  simp only [denoteInstr, denoteFlowInstr, FiniteInstrumentComp.map,
    FiniteInstrumentComp.applyMat_wpKraus, Function.comp_apply]

theorem denoteInstr_gate_cx {q c : ℕ} (control target : Fin q) :
    denoteInstr (logModel q c) (.gate (.cx control target)) =
      fun s =>
        FiniteInstrumentComp.ofOperation
          (QuantumOperation.ofIsometry (cxMatrix control target)
            (cxMatrix_isometry control target)) s := by
  rfl

theorem denoteInstr_gate_cx_phys {q c : ℕ} (control target : Fin q) :
    denoteInstr (physModel q c)
        (.gate (.cx (dataWire control) (dataWire target))) =
      fun s =>
        FiniteInstrumentComp.ofOperation
          (QuantumOperation.ofIsometry
            (cxMatrix (dataWire control) (dataWire target))
            (cxMatrix_isometry (dataWire control) (dataWire target))) s := by
  rfl

theorem liftInstr_gate_cx {q c : ℕ} (control target : Fin q) :
    CQ.Eq
      (hideScratch
        (denoteInstr (physModel q c)
          (liftInstr (.gate (.cx control target)))))
      (denoteInstr (logModel q c) (.gate (.cx control target))) := by
  simp only [liftInstr, Gate.mapWires, denoteInstr_gate_cx,
    denoteInstr_gate_cx_phys]
  exact hideScratch_cx (q := q) (c := c) control target

/-- Hidden observation of a data-bit store is the logical store. -/
theorem hideScratch_store_data (q : ℕ) {c : ℕ} (b : Fin c) (e : CExpr c) :
    CQ.Eq (q := q)
      (hideScratch (q := q) (fun s : CStore (c + 1) =>
        FiniteInstrumentComp.unit (n := QDim (q + 1))
          (Function.update s (dataBit b) ((liftCExpr e).eval s))))
      (fun s : CStore c =>
        FiniteInstrumentComp.unit (n := QDim q)
          (Function.update s b (e.eval s))) := by
  intro s P ρ
  simp only [hideScratch, FiniteInstrumentComp.wpKraus_map]
  rw [hideComp_applyMat_wpKraus, FiniteInstrumentComp.wpKraus_unit_semEq]
  simp only [hidePost, Function.comp_apply, hideStore_initStore,
    liftCExpr_eval_init, hideStore_update_data]
  rw [KrausFamily.applyMat_comp, KrausFamily.applyMat_comp]
  have hcancel :=
    applyMat_discard_initialize q
      (KrausFamily.applyMat (P (Function.update s b (e.eval s)))
        (KrausFamily.applyMat (discardScratch q).kraus
          (KrausFamily.applyMat (initializeScratch q).kraus ρ)))
  rw [KrausFamily.applyMat_comp] at hcancel
  rw [hcancel, initializeScratch_kraus, KrausFamily.applyMat_single]
  have hback := applyMat_discard_initialize q ρ
  rw [KrausFamily.applyMat_comp, initializeScratch_kraus,
    KrausFamily.applyMat_single] at hback
  rw [hback]
  exact (FiniteInstrumentComp.wpKraus_unit_semEq
    (Function.update s b (e.eval s)) P ρ).symm

theorem liftInstr_store {q c : ℕ} (b : Fin c) (e : CExpr c) :
    CQ.Eq
      (hideScratch
        (denoteInstr (physModel q c) (liftInstr (.store b e))))
      (denoteInstr (logModel q c) (.store b e)) := by
  refine CQ.Eq.trans
    (hideScratch_congr (by
      simpa [liftInstr] using
        denoteInstr_store_eq (physModel q c) (dataBit b) (liftCExpr e))) ?_
  refine CQ.Eq.trans (hideScratch_store_data q b e) ?_
  exact CQ.Eq.symm (denoteInstr_store_eq (logModel q c) b e)

/-- Hidden observation of a data-wire measurement is the logical measurement. -/
theorem hideScratch_measure_data {q c : ℕ} (w : Fin q) (b : Fin c) :
    CQ.Eq
      (hideScratch (fun s : CStore (c + 1) =>
        (instrumentComp (measure (dataWire w)) rfl).map
          (fun o : Fin 2 => Function.update s (dataBit b) (o = 1))))
      (fun s : CStore c =>
        (instrumentComp (measure w) rfl).map
          (fun o : Fin 2 => Function.update s b (o = 1))) := by
  intro s P ρ
  simp only [hideScratch, FiniteInstrumentComp.wpKraus_map]
  rw [hideComp_applyMat_wpKraus]
  rw [FiniteInstrumentComp.applyMat_wpKraus, FiniteInstrumentComp.applyMat_wpKraus]
  simp only [instrumentComp, FiniteInstrumentComp.map, hideComp]
  erw [applyMat_sum, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Composer.measure, hidePost, Function.comp_apply,
    hideStore_update_data, id]
  have hfalse : decide ((0 : Fin 2) = 1) = false := by decide
  have htrue : decide ((1 : Fin 2) = 1) = true := by decide
  have hdecide : decide True = true := by decide
  have hne : (1 : Fin 2) ≠ 0 := by decide
  simp only [hfalse, htrue, hdecide, if_true, if_false, if_neg hne]
  rw [KrausFamily.applyMat_comp, KrausFamily.applyMat_comp,
    KrausFamily.applyMat_comp, KrausFamily.applyMat_comp,
    KrausFamily.applyMat_comp, KrausFamily.applyMat_comp]
  have hcancel (v : Bool) :
      KrausFamily.applyMat (discardScratch q).kraus
          (KrausFamily.applyMat (initializeScratch q).kraus
            (KrausFamily.applyMat (P (Function.update s b v))
              (KrausFamily.applyMat (discardScratch q).kraus
                (KrausFamily.applyMat [projector (dataWire w) v]
                  (KrausFamily.applyMat (initializeScratch q).kraus ρ))))) =
        KrausFamily.applyMat (P (Function.update s b v))
          (KrausFamily.applyMat (discardScratch q).kraus
            (KrausFamily.applyMat [projector (dataWire w) v]
              (KrausFamily.applyMat (initializeScratch q).kraus ρ))) := by
    have h :=
      applyMat_discard_initialize q
        (KrausFamily.applyMat (P (Function.update s b v))
          (KrausFamily.applyMat (discardScratch q).kraus
            (KrausFamily.applyMat [projector (dataWire w) v]
              (KrausFamily.applyMat (initializeScratch q).kraus ρ))))
    rw [KrausFamily.applyMat_comp] at h
    exact h
  rw [hcancel false, hcancel true]
  have hembed (v : Bool) :
      KrausFamily.applyMat (discardScratch q).kraus
          (KrausFamily.applyMat [projector (dataWire w) v]
            (KrausFamily.applyMat (initializeScratch q).kraus ρ)) =
        KrausFamily.applyMat [projector w v] ρ := by
    have hinit :
        KrausFamily.applyMat (initializeScratch q).kraus ρ =
          initZero q * ρ * Matrix.conjTranspose (initZero q) := by
      rw [initializeScratch_kraus, KrausFamily.applyMat_single]
    rw [hinit]
    exact applyMat_discard_projector_embedded w v ρ
  rw [hembed false, hembed true]
  rw [← KrausFamily.applyMat_comp, ← KrausFamily.applyMat_comp]

theorem liftInstr_measure {q c : ℕ} (w : Fin q) (b : Fin c) :
    CQ.Eq
      (hideScratch
        (denoteInstr (physModel q c) (liftInstr (.measure w b))))
      (denoteInstr (logModel q c) (.measure w b)) := by
  refine CQ.Eq.trans
    (hideScratch_congr (by
      simpa [liftInstr, physModel] using
        denoteInstr_measure_eq (physModel q c) (dataWire w) (dataBit b))) ?_
  refine CQ.Eq.trans (hideScratch_measure_data w b) ?_
  exact CQ.Eq.symm
    (by simpa [logModel, canonicalModel] using
      denoteInstr_measure_eq (logModel q c) w b)

theorem liftInstr_reset {q c : ℕ} (w : Fin q) :
    CQ.Eq
      (hideScratch
        (denoteInstr (physModel q c) (liftInstr (.reset w))))
      (denoteInstr (logModel q c) (.reset w)) := by
  simp only [liftInstr, denoteInstr, denoteFlowInstr, physModel, logModel,
    canonicalModel, FiniteInstrumentComp.map]
  exact hideScratch_reset_data (q := q) (c := c) w

theorem factors_gate_x {q c : ℕ} (w : Fin q) :
    FactorsScratch
      (denoteInstr (physModel q c) (.gate (.x (dataWire w)))) := by
  rw [denoteInstr_gate_x_phys]
  simpa [xMatrix] using
    factorsScratch_onWire_data (c := c) w x₂ x₂_isometry

theorem factors_gate_h {q c : ℕ} (w : Fin q) :
    FactorsScratch
      (denoteInstr (physModel q c) (.gate (.h (dataWire w)))) := by
  rw [denoteInstr_gate_h_phys]
  simpa [hMatrix] using
    factorsScratch_onWire_data (c := c) w h₂ h₂_isometry

theorem factors_gate_ry {q c : ℕ} (θ : AngleExpr) (w : Fin q) :
    FactorsScratch
      (denoteInstr (physModel q c) (.gate (.ry θ (dataWire w)))) := by
  rw [denoteInstr_gate_ry_phys]
  simpa [ryMatrix] using
    factorsScratch_onWire_data (c := c) w (ry₂ θ.eval) (ry₂_isometry θ.eval)

theorem factors_gate_cx {q c : ℕ} (control target : Fin q) :
    FactorsScratch
      (denoteInstr (physModel q c)
        (.gate (.cx (dataWire control) (dataWire target)))) := by
  rw [denoteInstr_gate_cx_phys]
  exact factorsScratch_cx (c := c) control target

theorem factors_reset {q c : ℕ} (w : Fin q) :
    FactorsScratch (denoteInstr (physModel q c) (.reset (dataWire w))) := by
  simp only [denoteInstr, denoteFlowInstr, physModel, canonicalModel,
    FiniteInstrumentComp.map]
  exact factorsScratch_reset_data (c := c) w

theorem factors_store_unit (q : ℕ) {c : ℕ} (b : Fin c) (e : CExpr c) :
    FactorsScratch (fun s : CStore (c + 1) =>
      FiniteInstrumentComp.unit (n := QDim (q + 1))
        (Function.update s (dataBit b) ((liftCExpr e).eval s))) := by
  intro s P ρ
  rw [FiniteInstrumentComp.wpKraus_unit_semEq]
  have hhide :=
    (hideScratch_store_data q b e (hideStore s) P
      (KrausFamily.applyMat (discardScratch q).kraus ρ)).symm
  dsimp at hhide
  simp only [hidePost, Function.comp_apply, KrausFamily.applyMat_comp]
  rw [hideStore_update_data_any, liftCExpr_eval]
  refine congrArg (KrausFamily.applyMat (initializeScratch q).kraus) ?_
  exact (FiniteInstrumentComp.wpKraus_unit_semEq
      (Function.update (hideStore s) b (e.eval (hideStore s))) P
      (KrausFamily.applyMat (discardScratch q).kraus ρ)).symm.trans hhide

theorem factors_store {q c : ℕ} (b : Fin c) (e : CExpr c) :
    FactorsScratch
      (denoteInstr (physModel q c) (.store (dataBit b) (liftCExpr e))) :=
  factorsScratch_congr
    (denoteInstr_store_eq (physModel q c) (dataBit b) (liftCExpr e))
    (factors_store_unit q b e)

theorem factors_measure_map {q c : ℕ} (w : Fin q) (b : Fin c) :
    FactorsScratch (fun s : CStore (c + 1) =>
      (instrumentComp (measure (dataWire w)) rfl).map
        (fun o : Fin 2 => Function.update s (dataBit b) (o = 1))) := by
  intro s P ρ
  have hhide :=
    hideScratch_measure_data w b (hideStore s) P
      (KrausFamily.applyMat (discardScratch q).kraus ρ)
  rw [FiniteInstrumentComp.wpKraus_map, FiniteInstrumentComp.applyMat_wpKraus]
  simp only [hidePost, Function.comp_apply, KrausFamily.applyMat_comp]
  rw [← applyMat_sum]
  refine congrArg (KrausFamily.applyMat (initializeScratch q).kraus) ?_
  refine _root_.Eq.trans ?_ hhide.symm
  rw [FiniteInstrumentComp.applyMat_wpKraus]
  dsimp only [instrumentComp]
  conv_lhs => erw [Fin.sum_univ_two]
  conv_rhs => erw [Fin.sum_univ_two]
  simp only [instrumentComp, Composer.measure, hideStore_update_data_any,
    Function.comp_apply, id]
  have hfalse : decide ((0 : Fin 2) = 1) = false := by decide
  have htrue : decide ((1 : Fin 2) = 1) = true := by decide
  have hdecide : decide True = true := by decide
  have hne : (1 : Fin 2) ≠ 0 := by decide
  simp only [hfalse, htrue, hdecide, if_true, if_false, if_neg hne,
    KrausFamily.applyMat_comp]
  rw [applyMat_discard_projector_data, applyMat_discard_projector_data]
  simp [FiniteInstrumentComp.map, hfalse, htrue, hdecide, if_true,
    if_pos (rfl : (0 : Fin 2) = 0), if_neg hne, KrausFamily.applyMat_single]

theorem factors_measure {q c : ℕ} (w : Fin q) (b : Fin c) :
    FactorsScratch
      (denoteInstr (physModel q c) (.measure (dataWire w) (dataBit b))) :=
  factorsScratch_congr
    (denoteInstr_measure_eq (physModel q c) (dataWire w) (dataBit b))
    (factors_measure_map w b)

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

theorem compile_correct_emit_cx {q c : ℕ} (schedule : Source.Scheduler)
    (control target : Fin q) :
    CQ.Eq
      (hideScratch
        (denoteBlock (physModel q c)
          (compile schedule (.emit (.gate (.cx control target))))))
      ((Source.Command.emit (.gate (.cx control target))).denote
        (logModel q c) schedule) := by
  refine CQ.Eq.trans
    (hideScratch_congr
      (denoteBlock_singleton (physModel q c)
        (liftInstr (.gate (.cx control target))))) ?_
  simpa [compile, Source.Command.denote] using
    liftInstr_gate_cx (c := c) control target

theorem compile_correct_emit_measure {q c : ℕ} (schedule : Source.Scheduler)
    (w : Fin q) (b : Fin c) :
    CQ.Eq
      (hideScratch
        (denoteBlock (physModel q c)
          (compile schedule (.emit (.measure w b)))))
      ((Source.Command.emit (.measure w b)).denote
        (logModel q c) schedule) := by
  refine CQ.Eq.trans
    (hideScratch_congr
      (denoteBlock_singleton (physModel q c) (liftInstr (.measure w b)))) ?_
  simpa [compile, Source.Command.denote] using liftInstr_measure (c := c) w b

theorem compile_correct_emit_reset {q c : ℕ} (schedule : Source.Scheduler)
    (w : Fin q) :
    CQ.Eq
      (hideScratch
        (denoteBlock (physModel q c)
          (compile schedule (.emit (.reset w)))))
      ((Source.Command.emit (.reset w)).denote
        (logModel q c) schedule) := by
  refine CQ.Eq.trans
    (hideScratch_congr
      (denoteBlock_singleton (physModel q c) (liftInstr (.reset w)))) ?_
  simpa [compile, Source.Command.denote] using liftInstr_reset (c := c) w

theorem compile_correct_emit_store {q c : ℕ} (schedule : Source.Scheduler)
    (b : Fin c) (e : CExpr c) :
    CQ.Eq
      (hideScratch
        (denoteBlock (physModel q c)
          (compile schedule (.emit (.store b e)))))
      ((Source.Command.emit (.store b e)).denote
        (logModel q c) schedule) := by
  refine CQ.Eq.trans
    (hideScratch_congr
      (denoteBlock_singleton (physModel q c) (liftInstr (.store b e)))) ?_
  simpa [compile, Source.Command.denote] using liftInstr_store (c := c) b e

theorem compile_correct_seq {q c : ℕ} (schedule : Source.Scheduler)
    (A B : Source.Command q c)
    (hA :
      CQ.Eq
        (hideScratch (denoteBlock (physModel q c) (compile schedule A)))
        (A.denote (logModel q c) schedule))
    (hB :
      CQ.Eq
        (hideScratch (denoteBlock (physModel q c) (compile schedule B)))
        (B.denote (logModel q c) schedule))
    (hBfac :
      FactorsScratch (denoteBlock (physModel q c) (compile schedule B))) :
    CQ.Eq
      (hideScratch
        (denoteBlock (physModel q c)
          (compile schedule (.seq A B))))
      ((Source.Command.seq A B).denote (logModel q c) schedule) := by
  simp only [compile, Source.Command.denote]
  refine CQ.Eq.trans
    (hideScratch_congr (denoteBlock_append (physModel q c)
      (compile schedule A) (compile schedule B))) ?_
  refine CQ.Eq.trans
    (hideScratch_seq_of_insensitive _ _
      (scratchInsensitive_of_factorsScratch hBfac)) ?_
  exact CQ.seq_congr hA hB

theorem denoteInstr_reset_op {q c : ℕ} (w : Fin (q + 1)) :
    CQ.Eq (denoteInstr (physModel q c) (.reset w))
      (fun s => FiniteInstrumentComp.ofOperation (reset w) s) := by
  intro s P ρ
  simp only [denoteInstr, denoteFlowInstr, physModel, canonicalModel,
    FiniteInstrumentComp.map, FiniteInstrumentComp.ofOperation,
    FiniteInstrumentComp.applyMat_wpKraus, Function.comp_apply]

theorem denoteInstr_ry_op {q c : ℕ} (θ : AngleExpr) (w : Fin (q + 1)) :
    CQ.Eq (denoteInstr (physModel q c) (.gate (.ry θ w)))
      (fun s =>
        FiniteInstrumentComp.ofOperation
          (QuantumOperation.ofIsometry (ryMatrix θ.eval w)
            (ryMatrix_isometry θ.eval w)) s) := by
  intro s P ρ
  simp only [denoteInstr, denoteFlowInstr, physModel, canonicalModel,
    FiniteInstrumentComp.map, FiniteInstrumentComp.ofOperation,
    FiniteInstrumentComp.applyMat_wpKraus, Function.comp_apply]

theorem coin_branch_false {q c : ℕ} (p : Source.Probability)
    (L : Sem (q + 1) (c + 1)) (hL : FactorsScratch L)
    (s : CStore c) (P : CStore c → KrausFamily (QDim q) (QDim q))
    (ρ : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) :
    let amp0 := (Real.sqrt p.real : ℂ)
    let amp1 := (Real.sqrt (1 - p.real) : ℂ)
    let coinVec := amp0 • initZero q + amp1 • initOne q
    KrausFamily.applyMat (discardScratch q).kraus
        (KrausFamily.applyMat
          (((L (Function.update (initStore s) (scratchBit c) false)).wpKraus
              (hidePost (P ∘ hideStore))).comp
            [projector (scratchWire q) false])
          (coinVec * ρ * Matrix.conjTranspose coinVec)) =
      KrausFamily.applyMat
        (((hideScratch L s).wpKraus P).comp
          (KrausFamily.scale amp0 (KrausFamily.identity (QDim q)))) ρ := by
  intro amp0 amp1 coinVec
  rw [KrausFamily.applyMat_comp]
  have hfac := hL (Function.update (initStore s) (scratchBit c) false) P
    (KrausFamily.applyMat [projector (scratchWire q) false]
      (coinVec * ρ * Matrix.conjTranspose coinVec))
  rw [hfac, hideStore_update_init_scratch, applyMat_discard_hidePost,
    KrausFamily.applyMat_single, discard_projector_false_coin]
  rw [KrausFamily.applyMat_comp, KrausFamily.applyMat_scale,
    KrausFamily.applyMat_identity]
  have hscale : amp0 * star amp0 = (p.real : ℂ) := by
    simp only [amp0, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    norm_cast
    simpa [pow_two] using Real.sq_sqrt p.real_nonneg
  rw [hscale]

theorem coin_branch_true {q c : ℕ} (p : Source.Probability)
    (R : Sem (q + 1) (c + 1)) (hR : FactorsScratch R)
    (s : CStore c) (P : CStore c → KrausFamily (QDim q) (QDim q))
    (ρ : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) :
    let amp0 := (Real.sqrt p.real : ℂ)
    let amp1 := (Real.sqrt (1 - p.real) : ℂ)
    let coinVec := amp0 • initZero q + amp1 • initOne q
    KrausFamily.applyMat (discardScratch q).kraus
        (KrausFamily.applyMat
          (((R (Function.update (initStore s) (scratchBit c) true)).wpKraus
              (hidePost (P ∘ hideStore))).comp
            [projector (scratchWire q) true])
          (coinVec * ρ * Matrix.conjTranspose coinVec)) =
      KrausFamily.applyMat
        (((hideScratch R s).wpKraus P).comp
          (KrausFamily.scale amp1 (KrausFamily.identity (QDim q)))) ρ := by
  intro amp0 amp1 coinVec
  rw [KrausFamily.applyMat_comp]
  have hfac := hR (Function.update (initStore s) (scratchBit c) true) P
    (KrausFamily.applyMat [projector (scratchWire q) true]
      (coinVec * ρ * Matrix.conjTranspose coinVec))
  rw [hfac, hideStore_update_init_scratch, applyMat_discard_hidePost,
    KrausFamily.applyMat_single, discard_projector_true_coin]
  rw [KrausFamily.applyMat_comp, KrausFamily.applyMat_scale,
    KrausFamily.applyMat_identity]
  have hscale : amp1 * star amp1 = ((1 - p.real : ℝ) : ℂ) := by
    have hp' : 0 ≤ 1 - p.real := sub_nonneg.mpr p.real_le_one
    simp only [amp1, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    norm_cast
    simpa [pow_two] using Real.sq_sqrt hp'
  rw [hscale]

theorem update_scratchBit_of_hideStore {c : ℕ} (s : CStore (c + 1)) (b : Bool) :
    Function.update s (scratchBit c) b =
      Function.update (initStore (hideStore s)) (scratchBit c) b := by
  funext i
  by_cases hi : i = scratchBit c
  · simp [hi]
  · rw [Function.update_apply, if_neg hi, Function.update_apply, if_neg hi]
    have hlt : i.val < c := by
      have hne : i.val ≠ c := by
        intro h
        apply hi
        apply Fin.ext
        simpa [scratchBit, Fin.val_last] using h
      exact lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) hne
    have hcast : (⟨i.val, hlt⟩ : Fin c).castSucc = i := by
      apply Fin.ext
      simp
    simp [initStore, hideStore, hlt, hcast]

theorem applyMat_wp_hidePost_embedded {q : ℕ} {D : Type*} [Preorder D]
    (μ : FiniteInstrumentComp (QDim (q + 1)) D)
    (P : D → KrausFamily (QDim q) (QDim q))
    (ρ : Matrix (Fin (QDim (q + 1))) (Fin (QDim (q + 1))) ℂ) :
    KrausFamily.applyMat (μ.wpKraus (hidePost P)) ρ =
      KrausFamily.applyMat (initializeScratch q).kraus
        (KrausFamily.applyMat (discardScratch q).kraus
          (KrausFamily.applyMat (μ.wpKraus (hidePost P)) ρ)) := by
  classical
  have hwp := FiniteInstrumentComp.applyMat_wpKraus μ (hidePost P) ρ
  have hterm :
      ∀ o, KrausFamily.applyMat
          (KrausFamily.comp (hidePost P (μ.value o)) (μ.branch o)) ρ =
        KrausFamily.applyMat (initializeScratch q).kraus
          (KrausFamily.applyMat (P (μ.value o))
            (KrausFamily.applyMat (discardScratch q).kraus
              (KrausFamily.applyMat (μ.branch o) ρ))) := by
    intro o
    simp only [hidePost, KrausFamily.applyMat_comp]
  have hsum :
      (∑ o, KrausFamily.applyMat
          (KrausFamily.comp (hidePost P (μ.value o)) (μ.branch o)) ρ) =
        KrausFamily.applyMat (initializeScratch q).kraus
          (∑ o, KrausFamily.applyMat (P (μ.value o))
            (KrausFamily.applyMat (discardScratch q).kraus
              (KrausFamily.applyMat (μ.branch o) ρ))) := by
    simp only [hterm]
    rw [← applyMat_sum]
  have hcancel :=
    applyMat_discard_initialize q
      (∑ o, KrausFamily.applyMat (P (μ.value o))
        (KrausFamily.applyMat (discardScratch q).kraus
          (KrausFamily.applyMat (μ.branch o) ρ)))
  rw [KrausFamily.applyMat_comp, initializeScratch_kraus,
    KrausFamily.applyMat_single] at hcancel
  rw [hwp, hsum]
  refine congrArg (KrausFamily.applyMat (initializeScratch q).kraus) ?_
  rw [initializeScratch_kraus, KrausFamily.applyMat_single]
  exact hcancel.symm

theorem measureSelect_store_agree {q c : ℕ}
    (L R : Sem (q + 1) (c + 1)) (s : CStore (c + 1))
    (Q : CStore (c + 1) → KrausFamily (QDim (q + 1)) (QDim (q + 1)))
    (ρ : Matrix (Fin (QDim (q + 1))) (Fin (QDim (q + 1))) ℂ) :
    let measureAt : CStore (c + 1) →
        FiniteInstrumentComp (QDim (q + 1)) (CStore (c + 1)) :=
      fun u =>
        (instrumentComp (measure (scratchWire q)) rfl).map
          (fun o : Fin 2 => Function.update u (scratchBit c) (o = 1))
    KrausFamily.applyMat
        (((CQ.seq measureAt (CQ.select (fun u => u (scratchBit c)) L R)) s).wpKraus
          Q) ρ =
      KrausFamily.applyMat
        (((CQ.seq measureAt (CQ.select (fun u => u (scratchBit c)) L R))
            (initStore (hideStore s))).wpKraus Q) ρ := by
  intro measureAt
  simp only [CQ.seq, measureAt]
  conv_lhs =>
    rw [FiniteInstrumentComp.wpKraus_bind_semEq, FiniteInstrumentComp.applyMat_wpKraus]
    erw [Fin.sum_univ_two]
  conv_rhs =>
    rw [FiniteInstrumentComp.wpKraus_bind_semEq, FiniteInstrumentComp.applyMat_wpKraus]
    erw [Fin.sum_univ_two]
  have hdecide0 : decide ((0 : Fin 2) = 1) = false := by decide
  have hdecideT : decide True = true := by decide
  simp only [FiniteInstrumentComp.map, instrumentComp, Function.comp_apply, id,
    hdecide0, hdecideT]
  rw [update_scratchBit_of_hideStore s false, update_scratchBit_of_hideStore s true]

theorem coinTail_store_agree {q c : ℕ} (p : Source.Probability)
    (L R : Sem (q + 1) (c + 1)) (s : CStore (c + 1))
    (Q : CStore (c + 1) → KrausFamily (QDim (q + 1)) (QDim (q + 1)))
    (ρ : Matrix (Fin (QDim (q + 1))) (Fin (QDim (q + 1))) ℂ) :
    let tail : Sem (q + 1) (c + 1) :=
      CQ.seq
        (fun u =>
          FiniteInstrumentComp.ofOperation
            (QuantumOperation.ofIsometry
              (ryMatrix (AngleExpr.coin p).eval (scratchWire q))
              (ryMatrix_isometry (AngleExpr.coin p).eval (scratchWire q))) u)
        (CQ.seq
          (fun u =>
            (instrumentComp (measure (scratchWire q)) rfl).map
              (fun o : Fin 2 => Function.update u (scratchBit c) (o = 1)))
          (CQ.select (fun u => u (scratchBit c)) L R))
    KrausFamily.applyMat ((tail s).wpKraus Q) ρ =
      KrausFamily.applyMat ((tail (initStore (hideStore s))).wpKraus Q) ρ := by
  intro tail
  simp only [tail, CQ.seq]
  conv_lhs =>
    rw [FiniteInstrumentComp.wpKraus_bind_semEq,
      FiniteInstrumentComp.wpKraus_ofOperation_semEq, KrausFamily.applyMat_comp]
  conv_rhs =>
    rw [FiniteInstrumentComp.wpKraus_bind_semEq,
      FiniteInstrumentComp.wpKraus_ofOperation_semEq, KrausFamily.applyMat_comp]
  exact measureSelect_store_agree L R s Q _

theorem coin_erases_scratch {q c : ℕ} (p : Source.Probability)
    (L R : Sem (q + 1) (c + 1)) (s : CStore (c + 1))
    (Q : CStore (c + 1) → KrausFamily (QDim (q + 1)) (QDim (q + 1)))
    (ρ : Matrix (Fin (QDim (q + 1))) (Fin (QDim (q + 1))) ℂ) :
    let coin : Sem (q + 1) (c + 1) :=
      CQ.seq (fun u => FiniteInstrumentComp.ofOperation (reset (scratchWire q)) u)
        (CQ.seq
          (fun u =>
            FiniteInstrumentComp.ofOperation
              (QuantumOperation.ofIsometry
                (ryMatrix (AngleExpr.coin p).eval (scratchWire q))
                (ryMatrix_isometry (AngleExpr.coin p).eval (scratchWire q))) u)
          (CQ.seq
            (fun u =>
              (instrumentComp (measure (scratchWire q)) rfl).map
                (fun o : Fin 2 => Function.update u (scratchBit c) (o = 1)))
            (CQ.select (fun u => u (scratchBit c)) L R)))
    KrausFamily.applyMat ((coin s).wpKraus Q) ρ =
      KrausFamily.applyMat ((coin (initStore (hideStore s))).wpKraus Q)
        (KrausFamily.applyMat (initializeScratch q).kraus
          (KrausFamily.applyMat (discardScratch q).kraus ρ)) := by
  intro coin
  simp only [coin, CQ.seq]
  conv_lhs =>
    rw [FiniteInstrumentComp.wpKraus_bind_semEq,
      FiniteInstrumentComp.wpKraus_ofOperation_semEq, KrausFamily.applyMat_comp,
      applyMat_reset_scratch]
  conv_rhs =>
    rw [FiniteInstrumentComp.wpKraus_bind_semEq,
      FiniteInstrumentComp.wpKraus_ofOperation_semEq, KrausFamily.applyMat_comp,
      applyMat_reset_scratch]
  have hback :=
    applyMat_discard_initialize q
      (KrausFamily.applyMat (discardScratch q).kraus ρ)
  rw [KrausFamily.applyMat_comp, initializeScratch_kraus,
    KrausFamily.applyMat_single] at hback
  rw [initializeScratch_kraus, KrausFamily.applyMat_single, hback]
  conv_rhs => rw [KrausFamily.applyMat_single]
  exact coinTail_store_agree p L R s Q _

theorem factorsScratch_of_insensitive {q c : ℕ}
    {G : Sem (q + 1) (c + 1)} (hG : ScratchInsensitive G) :
    FactorsScratch G := by
  intro s P ρ
  have hembed :=
    applyMat_wp_hidePost_embedded (G s) (P ∘ hideStore) ρ
  rw [hembed]
  conv_rhs => simp only [hidePost, KrausFamily.applyMat_comp]
  refine congrArg (KrausFamily.applyMat (initializeScratch q).kraus) (hG s P ρ)

theorem scratchInsensitive_coin {q c : ℕ} (p : Source.Probability)
    (L R : Sem (q + 1) (c + 1)) :
    let coin : Sem (q + 1) (c + 1) :=
      CQ.seq (fun u => FiniteInstrumentComp.ofOperation (reset (scratchWire q)) u)
        (CQ.seq
          (fun u =>
            FiniteInstrumentComp.ofOperation
              (QuantumOperation.ofIsometry
                (ryMatrix (AngleExpr.coin p).eval (scratchWire q))
                (ryMatrix_isometry (AngleExpr.coin p).eval (scratchWire q))) u)
          (CQ.seq
            (fun u =>
              (instrumentComp (measure (scratchWire q)) rfl).map
                (fun o : Fin 2 => Function.update u (scratchBit c) (o = 1)))
            (CQ.select (fun u => u (scratchBit c)) L R)))
    ScratchInsensitive coin := by
  intro coin s P ρ
  have herase :=
    coin_erases_scratch p L R s (hidePost (P ∘ hideStore)) ρ
  have herase' :=
    congrArg (KrausFamily.applyMat (discardScratch q).kraus) herase
  rw [herase']
  have hhide :=
    hideComp_applyMat_wpKraus (coin (initStore (hideStore s))) (P ∘ hideStore)
      (KrausFamily.applyMat (discardScratch q).kraus ρ)
  rw [hideScratch, FiniteInstrumentComp.wpKraus_map]
  exact hhide.symm

set_option maxHeartbeats 800000 in
theorem hideScratch_coin_op {q c : ℕ} (p : Source.Probability)
    (L R : Sem (q + 1) (c + 1))
    (hL : FactorsScratch L) (hR : FactorsScratch R) :
    CQ.Eq
      (hideScratch
        (CQ.seq (fun s => FiniteInstrumentComp.ofOperation (reset (scratchWire q)) s)
          (CQ.seq
            (fun s =>
              FiniteInstrumentComp.ofOperation
                (QuantumOperation.ofIsometry
                  (ryMatrix (AngleExpr.coin p).eval (scratchWire q))
                  (ryMatrix_isometry (AngleExpr.coin p).eval (scratchWire q))) s)
            (CQ.seq
              (fun s =>
                (instrumentComp (measure (scratchWire q)) rfl).map
                  (fun o : Fin 2 => Function.update s (scratchBit c) (o = 1)))
              (CQ.select (fun s => s (scratchBit c)) L R)))))
      (Source.probSem p (hideScratch L) (hideScratch R)) := by
  intro s P ρ
  simp only [hideScratch, FiniteInstrumentComp.wpKraus_map, CQ.seq, Source.probSem]
  rw [hideComp_applyMat_wpKraus, FiniteInstrumentComp.wpKraus_bind_semEq,
    FiniteInstrumentComp.wpKraus_ofOperation_semEq, KrausFamily.applyMat_comp,
    initializeScratch_kraus, KrausFamily.applyMat_single, applyMat_reset_scratch_init]
  simp only [CQ.seq]
  conv_lhs =>
    rw [FiniteInstrumentComp.wpKraus_bind_semEq,
      FiniteInstrumentComp.wpKraus_ofOperation_semEq, KrausFamily.applyMat_comp,
      QuantumOperation.ofIsometry, KrausFamily.applyMat_single,
      ← applyMat_reset_scratch_init, physicalCoin_amplitudes]
  simp only [CQ.seq]
  conv_lhs =>
    rw [FiniteInstrumentComp.wpKraus_bind_semEq, FiniteInstrumentComp.applyMat_wpKraus,
      applyMat_sum]
    erw [Fin.sum_univ_two]
  conv_rhs =>
    rw [FiniteInstrumentComp.wpKraus_bind_semEq, FiniteInstrumentComp.applyMat_wpKraus]
    erw [Fintype.sum_bool]
  have hdecide0 : decide ((0 : Fin 2) = 1) = false := by decide
  have hdecideT : decide True = true := by decide
  have hne : (1 : Fin 2) ≠ 0 := by decide
  simp only [FiniteInstrumentComp.map, instrumentComp, Function.comp_apply, id,
    Composer.measure, FiniteInstrumentComp.weightedCoin, select,
    Function.update_apply, hdecide0, hdecideT, hne, if_false, if_true,
    if_neg hne, Bool.false_eq_true]
  rw [coin_branch_false p L hL s P ρ, coin_branch_true p R hR s P ρ, add_comm]
  simp only [hideScratch, FiniteInstrumentComp.map]

theorem denote_physicalCoin {q c : ℕ} (p : Source.Probability)
    (left right : List (Instr (q + 1) (c + 1))) :
    CQ.Eq
      (denoteBlock (physModel q c) (physicalCoin p left right))
      (CQ.seq (fun s => FiniteInstrumentComp.ofOperation (reset (scratchWire q)) s)
        (CQ.seq
          (fun s =>
            FiniteInstrumentComp.ofOperation
              (QuantumOperation.ofIsometry
                (ryMatrix (AngleExpr.coin p).eval (scratchWire q))
                (ryMatrix_isometry (AngleExpr.coin p).eval (scratchWire q))) s)
          (CQ.seq
            (fun s =>
              (instrumentComp (measure (scratchWire q)) rfl).map
                (fun o : Fin 2 => Function.update s (scratchBit c) (o = 1)))
            (CQ.select (fun s => s (scratchBit c))
              (denoteBlock (physModel q c) left)
              (denoteBlock (physModel q c) right))))) := by
  simp only [physicalCoin, denoteBlock]
  refine CQ.seq_congr (denoteInstr_reset_op (scratchWire q)) ?_
  refine CQ.seq_congr (denoteInstr_ry_op (.coin p) (scratchWire q)) ?_
  refine CQ.seq_congr ?_ ?_
  · simpa [physModel, canonicalModel] using
      denoteInstr_measure_eq (physModel q c) (scratchWire q) (scratchBit c)
  · refine CQ.Eq.trans (CQ.seq_skip _) ?_
    simp only [denoteInstr, CExpr.eval]
    exact CQ.Eq.refl _

theorem compile_correct_prob {q c : ℕ} (schedule : Source.Scheduler)
    (p : Source.Probability) (A B : Source.Command q c)
    (hA :
      CQ.Eq
        (hideScratch (denoteBlock (physModel q c) (compile schedule A)))
        (A.denote (logModel q c) schedule))
    (hB :
      CQ.Eq
        (hideScratch (denoteBlock (physModel q c) (compile schedule B)))
        (B.denote (logModel q c) schedule))
    (hAfac :
      FactorsScratch (denoteBlock (physModel q c) (compile schedule A)))
    (hBfac :
      FactorsScratch (denoteBlock (physModel q c) (compile schedule B))) :
    CQ.Eq
      (hideScratch
        (denoteBlock (physModel q c) (compile schedule (.prob p A B))))
      ((Source.Command.prob p A B).denote (logModel q c) schedule) := by
  simp only [compile, Source.Command.denote]
  refine CQ.Eq.trans
    (hideScratch_congr
      (denote_physicalCoin p (compile schedule A) (compile schedule B))) ?_
  refine CQ.Eq.trans (hideScratch_coin_op p _ _ hAfac hBfac) ?_
  exact Source.probSem_congr p hA hB

/-- Residuals whose hidden compiled denotation equals the source meaning.
Supported gates, measurement, reset, store, sequencing, probabilistic choice,
internal choice, and external choice are included. -/
inductive Compilable {q c : ℕ} : Source.Command q c → Prop
  | skip : Compilable .skip
  | emit_x (w : Fin q) : Compilable (.emit (.gate (.x w)))
  | emit_h (w : Fin q) : Compilable (.emit (.gate (.h w)))
  | emit_ry (θ : AngleExpr) (w : Fin q) : Compilable (.emit (.gate (.ry θ w)))
  | emit_cx (control target : Fin q) :
      Compilable (.emit (.gate (.cx control target)))
  | emit_measure (w : Fin q) (b : Fin c) : Compilable (.emit (.measure w b))
  | emit_reset (w : Fin q) : Compilable (.emit (.reset w))
  | emit_store (b : Fin c) (e : CExpr c) : Compilable (.emit (.store b e))
  | seq {A B} : Compilable A → Compilable B → Compilable (.seq A B)
  | prob {p A B} : Compilable A → Compilable B → Compilable (.prob p A B)
  | intern {id A B} : Compilable A → Compilable B → Compilable (.intern id A B)
  | extern {guard A B} :
      Compilable A → Compilable B → Compilable (.extern guard A B)

theorem compilable_factors {q c : ℕ} (schedule : Source.Scheduler)
    {M : Source.Command q c} (h : Compilable M) :
    FactorsScratch (denoteBlock (physModel q c) (compile schedule M)) := by
  match h with
  | .skip =>
      simpa [compile, denoteBlock] using factorsScratch_skip (q := q) (c := c)
  | .emit_x w =>
      simp only [compile, denoteBlock, liftInstr, Gate.mapWires]
      exact factorsScratch_seq _ _ (factors_gate_x (c := c) w) factorsScratch_skip
  | .emit_h w =>
      simp only [compile, denoteBlock, liftInstr, Gate.mapWires]
      exact factorsScratch_seq _ _ (factors_gate_h (c := c) w) factorsScratch_skip
  | .emit_ry θ w =>
      simp only [compile, denoteBlock, liftInstr, Gate.mapWires]
      exact factorsScratch_seq _ _ (factors_gate_ry (c := c) θ w) factorsScratch_skip
  | .emit_cx control target =>
      simp only [compile, denoteBlock, liftInstr, Gate.mapWires]
      exact factorsScratch_seq _ _ (factors_gate_cx (c := c) control target)
        factorsScratch_skip
  | .emit_measure w b =>
      simp only [compile, denoteBlock, liftInstr]
      exact factorsScratch_seq _ _ (factors_measure (c := c) w b) factorsScratch_skip
  | .emit_reset w =>
      simp only [compile, denoteBlock, liftInstr]
      exact factorsScratch_seq _ _ (factors_reset (c := c) w) factorsScratch_skip
  | .emit_store b e =>
      simp only [compile, denoteBlock, liftInstr]
      exact factorsScratch_seq _ _ (factors_store (c := c) b e) factorsScratch_skip
  | .seq hA hB =>
      rename_i A B
      simp only [compile]
      exact factorsScratch_congr
        (CQ.Eq.symm (denoteBlock_append (physModel q c)
          (compile schedule A) (compile schedule B)))
        (factorsScratch_seq _ _
          (compilable_factors schedule hA) (compilable_factors schedule hB))
  | .prob hA hB =>
      rename_i p A B
      simp only [compile]
      exact factorsScratch_congr
        (CQ.Eq.symm (denote_physicalCoin p
          (compile schedule A) (compile schedule B)))
        (factorsScratch_of_insensitive
          (scratchInsensitive_coin p
            (denoteBlock (physModel q c) (compile schedule A))
            (denoteBlock (physModel q c) (compile schedule B))))
  | .intern hA hB =>
      rename_i id A B
      by_cases hsch : schedule id
      · simpa [compile, hsch] using compilable_factors schedule hB
      · simpa [compile, hsch] using compilable_factors schedule hA
  | .extern hA hB =>
      rename_i guard A B
      exact factorsScratch_congr
        (CQ.Eq.symm (denoteBlock_singleton (physModel q c)
          (.ite (liftCExpr guard) (compile schedule B) (compile schedule A))))
        (by
          simpa [denoteInstr] using
            factorsScratch_select ((liftCExpr guard).eval)
              (denoteBlock (physModel q c) (compile schedule A))
              (denoteBlock (physModel q c) (compile schedule B))
              (fun s => by
                rw [liftCExpr_eval, liftCExpr_eval, hideStore_initStore])
              (compilable_factors schedule hA) (compilable_factors schedule hB))

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
  | emit_cx control target =>
      exact compile_correct_emit_cx schedule control target
  | emit_measure w b => exact compile_correct_emit_measure schedule w b
  | emit_reset w => exact compile_correct_emit_reset schedule w
  | emit_store b e => exact compile_correct_emit_store schedule b e
  | seq hA hB ihA ihB =>
      exact compile_correct_seq schedule _ _ ihA ihB (compilable_factors schedule hB)
  | prob hA hB ihA ihB =>
      exact compile_correct_prob schedule _ _ _ ihA ihB
        (compilable_factors schedule hA) (compilable_factors schedule hB)
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

/-- Logical instructions whose embedding is in the discharged compiler fragment. -/
inductive InstrCompilable {q c : ℕ} : Instr q c → Prop
  | gate_x (w : Fin q) : InstrCompilable (.gate (.x w))
  | gate_h (w : Fin q) : InstrCompilable (.gate (.h w))
  | gate_ry (θ : AngleExpr) (w : Fin q) : InstrCompilable (.gate (.ry θ w))
  | gate_cx (control target : Fin q) : InstrCompilable (.gate (.cx control target))
  | measure (w : Fin q) (b : Fin c) : InstrCompilable (.measure w b)
  | reset (w : Fin q) : InstrCompilable (.reset w)
  | store (b : Fin c) (e : CExpr c) : InstrCompilable (.store b e)

/-- Logical blocks built from those instructions. -/
inductive BlockCompilable {q c : ℕ} : List (Instr q c) → Prop
  | nil : BlockCompilable []
  | cons {i is} : InstrCompilable i → BlockCompilable is → BlockCompilable (i :: is)

theorem embedInstr_compilable {q c : ℕ} {i : Instr q c}
    (h : InstrCompilable i) : Compilable (embedInstr i) := by
  cases h with
  | gate_x w => exact Compilable.emit_x w
  | gate_h w => exact Compilable.emit_h w
  | gate_ry θ w => exact Compilable.emit_ry θ w
  | gate_cx control target => exact Compilable.emit_cx control target
  | measure w b => exact Compilable.emit_measure w b
  | reset w => exact Compilable.emit_reset w
  | store b e => exact Compilable.emit_store b e

theorem embed_compilable {q c : ℕ} {C : List (Instr q c)}
    (h : BlockCompilable C) : Compilable (embed C) := by
  induction h with
  | nil => exact Compilable.skip
  | cons hi _ ih => exact Compilable.seq (embedInstr_compilable hi) ih

/-- Recompiling a supported logical block preserves meaning after hiding scratch. -/
theorem denote_embed {q c : ℕ} (schedule : Source.Scheduler)
    {C : List (Instr q c)} (hC : BlockCompilable C) :
    CQ.Eq
      (hideScratch (denoteBlock (physModel q c) (liftBlock C)))
      ((embed C).denote (logModel q c) schedule) := by
  simpa [compile_embed schedule C] using
    compile_correct schedule (embed_compilable hC)

/-- A one-half coin between CX and H, used as a fragment regression. -/
def coinCX : Source.Command 2 0 :=
  .prob ⟨(1 : ℚ) / 2, by norm_num, by norm_num⟩
    (.emit (.gate (.cx 0 1)))
    (.emit (.gate (.h 0)))

theorem coinCX_compilable : Compilable coinCX :=
  Compilable.prob (Compilable.emit_cx 0 1) (Compilable.emit_h 0)

theorem coinCX_wellFormed : Source.Command.WellFormed coinCX :=
  Source.Command.WellFormed.prob
    (Source.Command.WellFormed.emit
      (Composer.Instr.WellFormedAt.gate (by decide : (0 : Fin 2) ≠ 1)))
    (Source.Command.WellFormed.emit
      (Composer.Instr.WellFormedAt.gate trivial))

theorem coinCX_compile_wellFormed (schedule : Source.Scheduler) :
    (compileProgram schedule coinCX).WellFormed :=
  compile_wellFormed coinCX_wellFormed

end QLambda.Compiler
