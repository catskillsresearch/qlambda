/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Composer.OpenQASM
import QLambda.Composer.WellFormed

/-!
# Frozen Composer fixtures

Small representative circuits pin the AST and OpenQASM presentation used by
the compiler tests.
-/

namespace QLambda.Composer.Fixtures

open QLambda.Composer

def bell : Program .openQASM3_0_ibmComposer_2026_09 2 2 where
  body :=
    [ .gate (.h 0),
      .gate (.cx 0 1),
      .measure 0 0,
      .measure 1 1 ]

def dynamicX : Program .openQASM3_0_ibmComposer_2026_09 1 1 where
  body :=
    [ .measure 0 0,
      .ite (.bit 0)
        [.gate (.x 0)]
        [.barrier [0]] ]

theorem bell_wellFormed : bell.WellFormed := by
  unfold Program.WellFormed bell
  apply Block.WellFormedAt.cons
  · apply Instr.WellFormedAt.gate
    trivial
  apply Block.WellFormedAt.cons
  · apply Instr.WellFormedAt.gate
    simp [Gate.WellFormed]
  apply Block.WellFormedAt.cons
  · apply Instr.WellFormedAt.measure
  apply Block.WellFormedAt.cons
  · apply Instr.WellFormedAt.measure
  exact Block.WellFormedAt.nil

example :
    bell.toOpenQASM bell_wellFormed =
      "OPENQASM 3.0;\ninclude \"stdgates.inc\";\nqubit[2] q;\nbit[2] c;\n" ++
      "h q[0];\ncx q[0], q[1];\nc[0] = measure q[0];\nc[1] = measure q[1];" := by
  native_decide

end QLambda.Composer.Fixtures
