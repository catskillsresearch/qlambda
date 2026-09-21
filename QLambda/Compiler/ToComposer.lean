/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Compiler.ChoiceLowering

/-!
# qλ residual command to Composer

Internal choices are resolved by the supplied scheduler, external choices
remain dynamic Composer conditionals, and probabilistic choices are delegated
to the law-carrying ancilla lowering.
-/

namespace QLambda.Compiler

/-- Compile a terminating first-order qλ residual to one Composer block. -/
def compile {q c : ℕ} (L : ProbLowering q c) (schedule : Source.Scheduler) :
    Source.Command q c → List (Composer.Instr q c)
  | .skip => []
  | .emit i => [i]
  | .seq A B => compile L schedule A ++ compile L schedule B
  | .prob p A B =>
      L.lower p (compile L schedule A) (compile L schedule B)
  | .intern id A B =>
      if schedule id then compile L schedule B else compile L schedule A
  | .extern guard A B =>
      [.ite guard (compile L schedule B) (compile L schedule A)]

@[simp] theorem compile_skip {q c : ℕ} (L : ProbLowering q c)
    (schedule : Source.Scheduler) :
    compile L schedule (.skip : Source.Command q c) = [] :=
  rfl

@[simp] theorem compile_emit {q c : ℕ} (L : ProbLowering q c)
    (schedule : Source.Scheduler) (i : Composer.Instr q c) :
    compile L schedule (.emit i) = [i] :=
  rfl

@[simp] theorem compile_seq {q c : ℕ} (L : ProbLowering q c)
    (schedule : Source.Scheduler) (A B : Source.Command q c) :
    compile L schedule (.seq A B) =
      compile L schedule A ++ compile L schedule B :=
  rfl

end QLambda.Compiler
