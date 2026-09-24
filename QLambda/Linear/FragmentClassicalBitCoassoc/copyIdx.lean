/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitChannels

/-!
# Copy intermediate index `3 · k`
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped BigOperators

/-- The unique `Fin 4` index with value `3 · k`. -/
def copyIdx (k : Fin 2) : Fin 4 := ⟨k.val * 3, by fin_omega⟩

theorem eq_copyIdx_iff (x : Fin 4) (i : Fin 2) :
    x.val = i.val * 3 ↔ x = copyIdx i :=
  ⟨fun h => Fin.ext h, fun h => h ▸ rfl⟩

/-- Copy's Choi selects a single intermediate pair, collapsing composition sums. -/
theorem sum_bitCopy_selector (F : Fin 4 → Fin 4 → ℂ) (i j : Fin 2) :
    (∑ x : Fin 4, ∑ y : Fin 4,
        F x y * (if x.val = i.val * 3 ∧ y.val = j.val * 3 then (1 : ℂ) else 0)) =
      F (copyIdx i) (copyIdx j) := by
  classical
  have hsel (x y : Fin 4) :
      (if x.val = i.val * 3 ∧ y.val = j.val * 3 then (1 : ℂ) else 0) =
        (if x = copyIdx i ∧ y = copyIdx j then 1 else 0) := by
    simp [eq_copyIdx_iff]
  simp_rw [hsel]
  rw [Finset.sum_eq_single (copyIdx i)]
  · rw [Finset.sum_eq_single (copyIdx j)]
    · simp
    · intro y _ hy; simp [hy]
    · simp
  · intro x _ hx; simp [hx]
  · simp

end QLambda.Linear
