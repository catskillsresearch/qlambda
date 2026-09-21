/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Source.Denotation

/-!
# Probabilistic-choice lowering contract

An ancilla implementation depends on a selected fresh wire, reset policy,
gate model, and parameter encoding.  The compiler therefore takes a concrete
lowering and requires the exact semantic law it must prove.  This prevents a
syntactic RY/measure pattern from being called correct without a gate model.
-/

namespace QLambda.Compiler

/-- Syntax-level lowering of a weighted branch to a Composer block. -/
structure ProbLowering (q c : ℕ) where
  lower :
    Source.Probability →
    List (Composer.Instr q c) →
    List (Composer.Instr q c) →
    List (Composer.Instr q c)

/-- The required ancilla-coin correctness equation. -/
structure LawfulProbLowering {q c : ℕ} (model : Composer.Model q c)
    (L : ProbLowering q c) : Prop where
  sound :
    ∀ p A B,
      CQ.Eq
        (Composer.denoteBlock model (L.lower p A B))
        (Source.probSem p
          (Composer.denoteBlock model A)
          (Composer.denoteBlock model B))

/-- Resources and parameter encoder for the concrete Composer ancilla pattern.

`angleForFalseWeight p` must encode an RY angle whose measurement-zero
probability is `p`. The semantic proof remains `LawfulProbLowering`: the
compiler never assumes an unchecked relationship between parameter text and
the model's gate operation. -/
structure AncillaResources (q c : ℕ) where
  qubit : Fin q
  bit : Fin c
  angleForFalseWeight : Source.Probability → String

/-- RY--measurement--conditional lowering used for probabilistic choice.

The selected ancilla is reset, rotated, measured, and then dispatches to the
right branch on one and the left branch on zero. -/
def ancillaLowering {q c : ℕ} (r : AncillaResources q c) :
    ProbLowering q c where
  lower p left right :=
    [ .reset r.qubit,
      .gate
        { name := "ry"
          params := [r.angleForFalseWeight p]
          qubits := [r.qubit] },
      .measure r.qubit r.bit,
      .ite (.bit r.bit) right left ]

end QLambda.Compiler
