/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Compiler.FromComposer
import QLambda.Compiler.ToComposer

/-!
# Denotation preservation and round trips

Correctness is equality in the shared CQ instrument semantics. AST equality is
used only for the total Composer-to-source-to-Composer round trip.
-/

namespace QLambda.Compiler

open QLambda.CQ

/-- Composer block concatenation denotes semantic sequencing. -/
theorem denoteBlock_append {q c : ℕ} (model : Composer.Model q c)
    (A B : List (Composer.Instr q c)) :
    CQ.Eq
      (Composer.denoteBlock model (A ++ B))
      (CQ.seq (Composer.denoteBlock model A) (Composer.denoteBlock model B)) := by
  induction A with
  | nil =>
      exact (CQ.skip_seq (Composer.denoteBlock model B)).symm
  | cons i is ih =>
      exact CQ.Eq.trans
        (CQ.seq_congr (CQ.Eq.refl _) ih)
        (CQ.seq_assoc
          (Composer.denoteInstr model i)
          (Composer.denoteBlock model is)
          (Composer.denoteBlock model B)).symm

/-- A singleton Composer block has the meaning of its instruction. -/
theorem denoteBlock_singleton {q c : ℕ} (model : Composer.Model q c)
    (i : Composer.Instr q c) :
    CQ.Eq (Composer.denoteBlock model [i]) (Composer.denoteInstr model i) :=
  CQ.seq_skip _

/-- Main source-to-Composer denotation preservation theorem. -/
theorem compile_correct {q c : ℕ} (model : Composer.Model q c)
    (L : ProbLowering q c) (hL : LawfulProbLowering model L)
    (schedule : Source.Scheduler) (M : Source.Command q c) :
    CQ.Eq
      (Composer.denoteBlock model (compile L schedule M))
      (M.denote model schedule) := by
  induction M with
  | skip =>
      exact CQ.Eq.refl _
  | emit i =>
      exact denoteBlock_singleton model i
  | seq A B ihA ihB =>
      exact CQ.Eq.trans
        (denoteBlock_append model (compile L schedule A) (compile L schedule B))
        (CQ.seq_congr ihA ihB)
  | prob p A B ihA ihB =>
      exact CQ.Eq.trans
        (hL.sound p (compile L schedule A) (compile L schedule B))
        (Source.probSem_congr p ihA ihB)
  | intern id A B ihA ihB =>
      by_cases h : schedule id
      · simpa [compile, Source.Command.denote, h] using ihB
      · simpa [compile, Source.Command.denote, h] using ihA
  | extern guard A B ihA ihB =>
      exact CQ.Eq.trans
        (CQ.seq_skip
          (CQ.select (guard.eval ·)
            (Composer.denoteBlock model (compile L schedule A))
            (Composer.denoteBlock model (compile L schedule B))))
        (CQ.select_congr (guard.eval ·) ihA ihB)

/-- Structural round trip: embedding a circuit and recompiling changes no AST. -/
theorem compile_embed {q c : ℕ} (L : ProbLowering q c)
    (schedule : Source.Scheduler) (C : List (Composer.Instr q c)) :
    compile L schedule (embed C) = C := by
  induction C with
  | nil => rfl
  | cons i is ih =>
      simp [embed, embedInstr, compile, ih]

/-- Total Composer embedding preserves the circuit denotation. -/
theorem denote_embed {q c : ℕ} (model : Composer.Model q c)
    (L : ProbLowering q c) (hL : LawfulProbLowering model L)
    (schedule : Source.Scheduler) (C : List (Composer.Instr q c)) :
    CQ.Eq
      (Composer.denoteBlock model C)
      ((embed C).denote model schedule) := by
  simpa [compile_embed L schedule C] using
    compile_correct model L hL schedule (embed C)

/-- The source round trip is contextually represented here by CQ equality. -/
theorem embed_compile_correct {q c : ℕ} (model : Composer.Model q c)
    (L : ProbLowering q c) (hL : LawfulProbLowering model L)
    (schedule : Source.Scheduler) (M : Source.Command q c) :
    CQ.Eq
      ((embed (compile L schedule M)).denote model schedule)
      (M.denote model schedule) := by
  exact CQ.Eq.trans
    (denote_embed model L hL schedule (compile L schedule M)).symm
    (compile_correct model L hL schedule M)

end QLambda.Compiler
