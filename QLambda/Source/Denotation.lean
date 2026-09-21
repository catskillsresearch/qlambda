/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Composer.Denotation
import QLambda.Source.Syntax
import QLambda.TTWeightedAggregation

/-!
# Denotation of staged qλ commands

The higher-order surface term is evaluated/staged to a finite `Command`.
Commands then denote the same CQ instruments as Composer circuits:

* `emit I` uses exactly `Composer.denoteInstr I`;
* probabilistic choice uses a physical weighted instrument (not lattice join);
* internal choice is resolved by the compiler scheduler;
* external choice reads the classical selector expression at run time.
-/

namespace QLambda.Source

open QLambda.CQ

/-- Compile-time resolution of named internal choices. -/
abbrev Scheduler := ChoiceId → Bool

/-- Physical weighted combination of two CQ computations. -/
noncomputable def probSem {q c : ℕ} (p : Probability)
    (A B : Sem q c) : Sem q c :=
  fun s =>
    (FiniteInstrumentComp.weightedCoin
      (n := QDim q) p.val p.nonneg p.le_one).bind fun right =>
        if right then B s else A s

/-- Physical probabilistic aggregation respects branch denotations. -/
theorem probSem_congr {q c : ℕ} (p : Probability)
    {A A' B B' : Sem q c} (hA : CQ.Eq A A') (hB : CQ.Eq B B') :
    CQ.Eq (probSem p A B) (probSem p A' B') := by
  intro s P
  let coin :=
    FiniteInstrumentComp.weightedCoin
      (n := QDim q) p.val p.nonneg p.le_one
  let left : Bool → FiniteInstrumentComp (QDim q) (CStore c) :=
    fun right => if right then B s else A s
  let right : Bool → FiniteInstrumentComp (QDim q) (CStore c) :=
    fun chooseRight => if chooseRight then B' s else A' s
  exact KrausFamily.applySemEq_trans
    (FiniteInstrumentComp.wpKraus_bind_semEq coin left P)
    (KrausFamily.applySemEq_trans
      (FiniteInstrumentComp.wpKraus_semEq_pred coin fun chooseRight => by
        simp only [left, right]
        split
        · exact hB s P
        · exact hA s P)
      (KrausFamily.applySemEq_symm
        (FiniteInstrumentComp.wpKraus_bind_semEq coin right P)))

/-- Compositional meaning of a finite source command. -/
noncomputable def Command.denote {q c : ℕ}
    (model : Composer.Model q c) (schedule : Scheduler) :
    Command q c → Sem q c
  | .skip => CQ.skip
  | .emit i => Composer.denoteInstr model i
  | .seq A B => CQ.seq (A.denote model schedule) (B.denote model schedule)
  | .prob p A B =>
      probSem p (A.denote model schedule) (B.denote model schedule)
  | .intern id A B =>
      if schedule id then B.denote model schedule else A.denote model schedule
  | .extern guard A B =>
      CQ.select (guard.eval ·) (A.denote model schedule) (B.denote model schedule)

/-- The source/target semantic boundary is definitionally shared. -/
@[simp] theorem denote_emit {q c : ℕ} (model : Composer.Model q c)
    (schedule : Scheduler) (i : Composer.Instr q c) :
    (Command.emit i).denote model schedule = Composer.denoteInstr model i :=
  rfl

@[simp] theorem denote_seq {q c : ℕ} (model : Composer.Model q c)
    (schedule : Scheduler) (A B : Command q c) :
    (Command.seq A B).denote model schedule =
      CQ.seq (A.denote model schedule) (B.denote model schedule) :=
  rfl

@[simp] theorem denote_intern_false {q c : ℕ} (model : Composer.Model q c)
    (schedule : Scheduler) (id : ChoiceId) (A B : Command q c)
    (h : schedule id = false) :
    (Command.intern id A B).denote model schedule = A.denote model schedule := by
  simp [Command.denote, h]

@[simp] theorem denote_intern_true {q c : ℕ} (model : Composer.Model q c)
    (schedule : Scheduler) (id : ChoiceId) (A B : Command q c)
    (h : schedule id = true) :
    (Command.intern id A B).denote model schedule = B.denote model schedule := by
  simp [Command.denote, h]

@[simp] theorem denote_extern_true {q c : ℕ} (model : Composer.Model q c)
    (schedule : Scheduler) (A B : Command q c) :
    (Command.extern (.lit true) A B).denote model schedule =
      B.denote model schedule := by
  simp [Command.denote, Composer.CExpr.eval, CQ.select]

@[simp] theorem denote_extern_false {q c : ℕ} (model : Composer.Model q c)
    (schedule : Scheduler) (A B : Command q c) :
    (Command.extern (.lit false) A B).denote model schedule =
      A.denote model schedule := by
  simp [Command.denote, Composer.CExpr.eval, CQ.select]

end QLambda.Source
