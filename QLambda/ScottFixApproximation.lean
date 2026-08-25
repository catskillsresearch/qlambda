/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Scott1972.ContinuousLattice.FunctionSpaces

/-!
# Finite approximations to Scott fixed points

The least fixed point of a Scott-continuous endomap is the supremum of its
finite iterates from bottom.  The accompanying chain and pre-fixed-point
lemmas are intended for induction arguments in recursive operational
adequacy proofs.
-/

namespace QLambda

open Scott1972.ContinuousLattice

namespace ScottFixApproximation

universe u

variable {D : Type u} [CompleteLattice D]

/-- The `n`th finite approximation to the least fixed point of `f`. -/
def iterateBot (f : ScottMap D D) (n : ℕ) : D :=
  ((f : D → D)^[n]) ⊥

@[simp] theorem iterateBot_zero (f : ScottMap D D) :
    iterateBot f 0 = ⊥ :=
  rfl

@[simp] theorem iterateBot_succ (f : ScottMap D D) (n : ℕ) :
    iterateBot f (n + 1) = f (iterateBot f n) := by
  change ((f : D → D)^[n + 1]) ⊥ =
    (f : D → D) (((f : D → D)^[n]) ⊥)
  rw [Function.iterate_succ_apply]
  exact ((Function.Commute.self_iterate (f : D → D) n).eq ⊥).symm

/-- Successive finite approximations form an increasing chain. -/
theorem iterateBot_le_succ (f : ScottMap D D) (n : ℕ) :
    iterateBot f n ≤ iterateBot f (n + 1) := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
      simpa only [iterateBot_succ] using f.monotone ih

/-- Finite approximation from bottom is monotone in the iteration count. -/
theorem iterateBot_monotone (f : ScottMap D D) :
    Monotone (iterateBot f) :=
  monotone_nat_of_le_succ (iterateBot_le_succ f)

/-- The range of finite approximations is nonempty. -/
theorem iterateBot_range_nonempty (f : ScottMap D D) :
    (Set.range (iterateBot f)).Nonempty :=
  Set.range_nonempty _

/-- The range of finite approximations is directed. -/
theorem iterateBot_range_directed (f : ScottMap D D) :
    DirectedOn (· ≤ ·) (Set.range (iterateBot f)) :=
  directedOn_range.2 fun m n =>
    ⟨max m n, iterateBot_monotone f (le_max_left _ _),
      iterateBot_monotone f (le_max_right _ _)⟩

/-- Every finite approximation lies below every pre-fixed point. -/
theorem iterateBot_le_of_prefixed (f : ScottMap D D) {x : D}
    (hx : f x ≤ x) (n : ℕ) :
    iterateBot f n ≤ x := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
      rw [iterateBot_succ]
      exact (f.monotone ih).trans hx

/-- Every finite approximation lies below Scott's least fixed point. -/
theorem iterateBot_le_fix (f : ScottMap D D) (n : ℕ) :
    iterateBot f n ≤ Proposition314.fix f :=
  iterateBot_le_of_prefixed f (le_of_eq (Proposition314.fix_eq f)) n

/-- The supremum of all finite approximations from bottom. -/
noncomputable def iterateBotSup (f : ScottMap D D) : D :=
  ⨆ n, iterateBot f n

/-- Scott continuity moves `f` through the supremum of its finite approximations. -/
theorem map_iterateBotSup (f : ScottMap D D) :
    f (iterateBotSup f) = ⨆ n, f (iterateBot f n) := by
  unfold iterateBotSup
  rw [← sSup_range,
    f.preservesDirectedSup_coe (Set.range (iterateBot f))
      (iterateBot_range_nonempty f) (iterateBot_range_directed f),
    ← Set.range_comp, sSup_range]
  rfl

/-- The supremum of the finite approximations is itself a fixed point. -/
theorem iterateBotSup_fixed (f : ScottMap D D) :
    f (iterateBotSup f) = iterateBotSup f := by
  rw [map_iterateBotSup]
  apply le_antisymm
  · refine iSup_le fun n => ?_
    rw [← iterateBot_succ]
    exact le_iSup (iterateBot f) (n + 1)
  · refine iSup_le fun n => ?_
    cases n with
    | zero => exact bot_le
    | succ n =>
        rw [iterateBot_succ]
        exact le_iSup (fun k => f (iterateBot f k)) n

/-- Scott's least fixed point is the supremum of the finite iterates from bottom. -/
theorem fix_eq_iSup_iterateBot (f : ScottMap D D) :
    Proposition314.fix f = ⨆ n, iterateBot f n := by
  symm
  apply Proposition314.fix_unique (iterateBotSup_fixed f)
  intro x hx
  exact iSup_le fun n => iterateBot_le_of_prefixed f hx n

/-- Range formulation of finite-iterate approximation to Scott's least fixed point. -/
theorem fix_eq_sSup_range_iterateBot (f : ScottMap D D) :
    Proposition314.fix f = sSup (Set.range (iterateBot f)) := by
  rw [sSup_range]
  exact fix_eq_iSup_iterateBot f

/-- Expanded formulation using `Function.iterate` directly. -/
theorem fix_eq_iSup_iterate (f : ScottMap D D) :
    Proposition314.fix f = ⨆ n : ℕ, ((f : D → D)^[n]) ⊥ :=
  fix_eq_iSup_iterateBot f

end ScottFixApproximation

end QLambda
