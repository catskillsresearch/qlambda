/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.CQ.Scratch
import QLambda.Source.Denotation

/-!
# Physical probabilistic-choice lowering

The source has `q,c` logical resources. Compilation always targets `q+1,c+1`;
the final wire and bit are reserved by their types, so source branches cannot
refer to them.
-/

namespace QLambda.Compiler

/-- RY--measurement--conditional lowering used for probabilistic choice.

The reserved ancilla is reset, rotated, measured, and then dispatches to the
right branch on one and the left branch on zero. -/
def physicalCoin {q c : ℕ} (p : Source.Probability)
    (left right : List (Composer.Instr (q + 1) (c + 1))) :
    List (Composer.Instr (q + 1) (c + 1)) :=
  [ .reset (CQ.scratchWire q),
    .gate (.ry (.coin p) (CQ.scratchWire q)),
    .measure (CQ.scratchWire q) (CQ.scratchBit c),
    .ite (.bit (CQ.scratchBit c)) right left ]

theorem physicalCoin_wellFormed {q c : ℕ} {p : Source.Probability}
    {left right : List (Composer.Instr (q + 1) (c + 1))}
    (hleft : Composer.Block.WellFormedAt 0 left)
    (hright : Composer.Block.WellFormedAt 0 right) :
    Composer.Block.WellFormedAt 0 (physicalCoin p left right) := by
  repeat' apply Composer.Block.WellFormedAt.cons
  · exact Composer.Instr.WellFormedAt.reset
  · exact Composer.Instr.WellFormedAt.gate (by trivial)
  · exact Composer.Instr.WellFormedAt.measure
  · exact Composer.Instr.WellFormedAt.ite hright hleft
  · exact Composer.Block.WellFormedAt.nil

end QLambda.Compiler
