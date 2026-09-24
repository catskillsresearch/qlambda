/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Rat.Defs

/-!
# Serializable source probabilities
-/

namespace QLambda

namespace Composer

/-- Exactly serializable probability used by the physical compiler. -/
structure Probability where
  val : ℚ
  nonneg : 0 ≤ val
  le_one : val ≤ 1
  deriving DecidableEq, Repr

namespace Probability

/-- Real denotation of a rational source probability. -/
noncomputable def real (p : Probability) : ℝ :=
  (p.val : ℝ)

theorem real_nonneg (p : Probability) : 0 ≤ p.real := by
  change (0 : ℝ) ≤ (p.val : ℝ)
  exact_mod_cast p.nonneg

theorem real_le_one (p : Probability) : p.real ≤ 1 := by
  change (p.val : ℝ) ≤ (1 : ℝ)
  exact_mod_cast p.le_one

end Probability

end Composer

end QLambda
