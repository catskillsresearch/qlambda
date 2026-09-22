/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.Typing

/-!
# Checked linear examples

These terms use lambda binding, linear gates, and measurement. They do not use
probabilistic, internal, or external choice.
-/

namespace QLambda.Linear

/-- `λ¹(q : Qubit). q` -/
def idQ : Term :=
  .lam .lin .qubit (.var .lin 0)

def idQTy : Ty :=
  .arrow .lin .qubit .qubit

/-- Identity at the gate type, used for a closed β-reduction regression. -/
def idGate : Term :=
  .lam .lin (.arrow .lin .qubit .qubit) (.var .lin 0)

def idGateTy : Ty :=
  .arrow .lin (.arrow .lin .qubit .qubit) (.arrow .lin .qubit .qubit)

/-- `λ¹(a : Qubit). λ¹(b : Qubit). CX (H a) b`, with the pair repackaged. -/
def bell : Term :=
  .lam .lin .qubit <|
    .lam .lin .qubit <|
      .unpair
        (.app (.app (.prim .cx) (.app (.prim .h) (.var .lin 1))) (.var .lin 0))
        (.lam .lin .qubit <|
          .lam .lin .qubit <|
            .pair (.var .lin 1) (.var .lin 0))

def bellTy : Ty :=
  .arrow .lin .qubit (.arrow .lin .qubit (.tensor .qubit .qubit))

/-- Measure, then apply `X` when the classical bit is true. -/
def measureX : Term :=
  .lam .lin .qubit <|
    .measure (.var .lin 0) <|
      .lam .unres .bit <|
        .lam .lin .qubit <|
          .ite (.var .unres 0)
            (.app (.prim .x) (.var .lin 0))
            (.var .lin 0)

theorem idQ_infer : infer [] [] idQ = some (idQTy, []) := by
  rfl

theorem idGate_infer : infer [] [] idGate = some (idGateTy, []) := by
  rfl

theorem bell_infer : infer [] [] bell = some (bellTy, []) := by
  rfl

theorem measureX_infer : infer [] [] measureX = some (idQTy, []) := by
  rfl

theorem idQ_typed : HasType [] [] idQ idQTy :=
  (infer_sound idQ_infer).1

theorem bell_typed : HasType [] [] bell bellTy :=
  (infer_sound bell_infer).1

theorem measureX_typed : HasType [] [] measureX idQTy :=
  (infer_sound measureX_infer).1

/-- An unrestricted qubit binder would permit cloning and is rejected. -/
def rejectedClone : Term :=
  .lam .unres .qubit <|
    .pair (.var .unres 0) (.var .unres 0)

theorem rejectedClone_infer : infer [] [] rejectedClone = none := by
  rfl

/-- An unrestricted closure may not capture a linear qubit. -/
def rejectedCapture : Term :=
  .lam .lin .qubit <|
    .lam .unres .bit (.var .lin 0)

theorem rejectedCapture_infer : infer [] [] rejectedCapture = none := by
  rfl

/-- The degenerate recursive type `μα. α` is scoped and strictly positive. -/
def recursiveIdTy : Ty :=
  .mu (.var 0)

theorem recursiveIdTy_admissible : Ty.Admissible recursiveIdTy := by
  decide

/-- Folding after unfolding at an admissible recursive type is accepted. -/
def recursiveFoldUnfold : Term :=
  .lam .lin recursiveIdTy <|
    .fold (.var 0) (.unfold (.var .lin 0))

theorem recursiveFoldUnfold_infer :
    infer [] [] recursiveFoldUnfold =
      some (.arrow .lin recursiveIdTy recursiveIdTy, []) := by
  rfl

theorem recursiveFoldUnfold_typed :
    HasType [] [] recursiveFoldUnfold
      (.arrow .lin recursiveIdTy recursiveIdTy) :=
  (infer_sound recursiveFoldUnfold_infer).1

/-- A recursive occurrence in a function domain is not strictly positive. -/
def negativeRecursiveTy : Ty :=
  .mu (.arrow .lin (.var 0) .unit)

theorem negativeRecursiveTy_rejected :
    Ty.admissible negativeRecursiveTy = false := by
  rfl

end QLambda.Linear
