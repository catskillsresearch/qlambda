/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Effects
import QLambda.TTContinuationMonad

/-!
# Internal choice for TT continuations

This module implements only internal choice.  It is pointwise join of TT
continuations, represented by `ScottMap.sup`; no probabilistic or external
operation, and hence no `HasComputationChoice` instance, is asserted here.
-/

namespace QLambda

open Scott1972.ContinuousLattice

universe u

namespace TTContinuation

variable {n : ℕ}
variable {D E : Type u}
variable [CompleteLattice D] [CompleteLattice E]

private noncomputable def fstContinuation :
    ScottMap
      (TTContinuationPower n D × TTContinuationPower n D)
      (TTContinuationPower n D) :=
  ⟨Prod.fst, continuous_of_preservesDirectedSup fun S _ _ =>
    Prod.fst_sSup S⟩

private noncomputable def sndContinuation :
    ScottMap
      (TTContinuationPower n D × TTContinuationPower n D)
      (TTContinuationPower n D) :=
  ⟨Prod.snd, continuous_of_preservesDirectedSup fun S _ _ =>
    Prod.snd_sSup S⟩

/-- Internal choice of TT continuations is their pointwise `ScottMap.sup`. -/
noncomputable def internalChoice :
    ScottMap
      (TTContinuationPower n D × TTContinuationPower n D)
      (TTContinuationPower n D) :=
  ScottMap.sup fstContinuation sndContinuation

@[simp]
theorem internalChoice_eq_sup (q r : TTContinuationPower n D) :
    internalChoice (q, r) = q ⊔ r := by
  rfl

/-- Applying an internal choice to a continuation joins the two results. -/
@[simp]
theorem internalChoice_apply (q r : TTContinuationPower n D)
    (k : ScottMap D (TTResult n)) :
    internalChoice (q, r) k = q k ⊔ r k := by
  rw [internalChoice_eq_sup, ScottMap.sup_apply]

theorem le_internalChoice_left (q r : TTContinuationPower n D) :
    q ≤ internalChoice (q, r) := by
  rw [internalChoice_eq_sup]
  exact le_sup_left

theorem le_internalChoice_right (q r : TTContinuationPower n D) :
    r ≤ internalChoice (q, r) := by
  rw [internalChoice_eq_sup]
  exact le_sup_right

theorem internalChoice_comm (q r : TTContinuationPower n D) :
    internalChoice (q, r) = internalChoice (r, q) := by
  simp only [internalChoice_eq_sup, sup_comm]

theorem internalChoice_assoc (q r s : TTContinuationPower n D) :
    internalChoice (internalChoice (q, r), s) =
      internalChoice (q, internalChoice (r, s)) := by
  simp only [internalChoice_eq_sup, sup_assoc]

@[simp]
theorem internalChoice_idem (q : TTContinuationPower n D) :
    internalChoice (q, q) = q := by
  simp only [internalChoice_eq_sup, sup_idem]

@[simp]
theorem internalChoice_bot_left (q : TTContinuationPower n D) :
    internalChoice (⊥, q) = q := by
  simp only [internalChoice_eq_sup, bot_sup_eq]

@[simp]
theorem internalChoice_bot_right (q : TTContinuationPower n D) :
    internalChoice (q, ⊥) = q := by
  simp only [internalChoice_eq_sup, sup_bot_eq]

/-- Kleisli extension preserves TT internal choice exactly in its computation
argument. -/
theorem bind_internalChoice (h : ScottMap D (TTContinuationPower n E))
    (q r : TTContinuationPower n D) :
    bind h (internalChoice (q, r)) =
      internalChoice (bind h q, bind h r) := by
  apply ScottMap.ext
  intro k
  simp only [bind_apply, internalChoice_apply]

end TTContinuation

end QLambda
