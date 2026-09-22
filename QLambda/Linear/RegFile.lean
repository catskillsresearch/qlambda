/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.Circuit

/-!
# Finite register allocation

The staging compiler allocates prefixes of fixed finite quantum and classical
registers.  A register is allocated exactly when its index is below the
corresponding cursor.  Consequently the next successful allocation is fresh,
two consecutive allocations are distinct, and every cursor remains in bounds.
-/

namespace QLambda.Linear

/-- Compiler-owned allocation state for fixed target registers. -/
structure RegFile (q c : ℕ) where
  nextQ : ℕ
  nextC : ℕ
  nextQ_le : nextQ ≤ q
  nextC_le : nextC ≤ c

namespace RegFile

/-- No target register has yet been allocated. -/
def empty (q c : ℕ) : RegFile q c :=
  ⟨0, 0, Nat.zero_le _, Nat.zero_le _⟩

/-- The allocated quantum wires form the prefix below `nextQ`. -/
def AllocatedQ {q c : ℕ} (ρ : RegFile q c) (w : Fin q) : Prop :=
  w.1 < ρ.nextQ

/-- The allocated classical slots form the prefix below `nextC`. -/
def AllocatedC {q c : ℕ} (ρ : RegFile q c) (b : Fin c) : Prop :=
  b.1 < ρ.nextC

/-- Allocate the next quantum wire, if the fixed register has room. -/
def allocQ {q c : ℕ} (ρ : RegFile q c) :
    Option (Fin q × RegFile q c) :=
  if h : ρ.nextQ < q then
    some
      (⟨ρ.nextQ, h⟩,
        ⟨ρ.nextQ + 1, ρ.nextC, Nat.succ_le_iff.mpr h, ρ.nextC_le⟩)
  else
    none

/-- Allocate the next classical slot, if the fixed register has room. -/
def allocC {q c : ℕ} (ρ : RegFile q c) :
    Option (Fin c × RegFile q c) :=
  if h : ρ.nextC < c then
    some
      (⟨ρ.nextC, h⟩,
        ⟨ρ.nextQ, ρ.nextC + 1, ρ.nextQ_le, Nat.succ_le_iff.mpr h⟩)
  else
    none

theorem allocQ_fresh {q c : ℕ} {ρ ρ' : RegFile q c} {w : Fin q}
    (h : ρ.allocQ = some (w, ρ')) : ¬ρ.AllocatedQ w := by
  simp only [allocQ] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [AllocatedQ]
  · contradiction

theorem allocC_fresh {q c : ℕ} {ρ ρ' : RegFile q c} {b : Fin c}
    (h : ρ.allocC = some (b, ρ')) : ¬ρ.AllocatedC b := by
  simp only [allocC] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [AllocatedC]
  · contradiction

theorem allocQ_new_allocated {q c : ℕ} {ρ ρ' : RegFile q c} {w : Fin q}
    (h : ρ.allocQ = some (w, ρ')) : ρ'.AllocatedQ w := by
  simp only [allocQ] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [AllocatedQ]
  · contradiction

theorem allocC_new_allocated {q c : ℕ} {ρ ρ' : RegFile q c} {b : Fin c}
    (h : ρ.allocC = some (b, ρ')) : ρ'.AllocatedC b := by
  simp only [allocC] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [AllocatedC]
  · contradiction

theorem allocQ_preserves {q c : ℕ} {ρ ρ' : RegFile q c} {new old : Fin q}
    (h : ρ.allocQ = some (new, ρ')) (hold : ρ.AllocatedQ old) :
    ρ'.AllocatedQ old := by
  simp only [allocQ] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact Nat.lt_succ_of_lt hold
  · contradiction

theorem allocC_preserves {q c : ℕ} {ρ ρ' : RegFile q c} {new old : Fin c}
    (h : ρ.allocC = some (new, ρ')) (hold : ρ.AllocatedC old) :
    ρ'.AllocatedC old := by
  simp only [allocC] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact Nat.lt_succ_of_lt hold
  · contradiction

/-- Consecutive successful quantum allocations cannot alias. -/
theorem allocQ_distinct {q c : ℕ}
    {ρ ρ₁ ρ₂ : RegFile q c} {w₁ w₂ : Fin q}
    (h₁ : ρ.allocQ = some (w₁, ρ₁))
    (h₂ : ρ₁.allocQ = some (w₂, ρ₂)) : w₁ ≠ w₂ := by
  intro heq
  have hfresh := allocQ_fresh h₂
  apply hfresh
  rw [← heq]
  exact allocQ_new_allocated h₁

/-- Consecutive successful classical allocations cannot alias. -/
theorem allocC_distinct {q c : ℕ}
    {ρ ρ₁ ρ₂ : RegFile q c} {b₁ b₂ : Fin c}
    (h₁ : ρ.allocC = some (b₁, ρ₁))
    (h₂ : ρ₁.allocC = some (b₂, ρ₂)) : b₁ ≠ b₂ := by
  intro heq
  have hfresh := allocC_fresh h₂
  apply hfresh
  rw [← heq]
  exact allocC_new_allocated h₁

theorem allocQ_bounds {q c : ℕ} {ρ ρ' : RegFile q c} {w : Fin q}
    (_h : ρ.allocQ = some (w, ρ')) :
    w.1 < q ∧ ρ'.nextQ ≤ q ∧ ρ'.nextC ≤ c :=
  ⟨w.2, ρ'.nextQ_le, ρ'.nextC_le⟩

theorem allocC_bounds {q c : ℕ} {ρ ρ' : RegFile q c} {b : Fin c}
    (_h : ρ.allocC = some (b, ρ')) :
    b.1 < c ∧ ρ'.nextQ ≤ q ∧ ρ'.nextC ≤ c :=
  ⟨b.2, ρ'.nextQ_le, ρ'.nextC_le⟩

/-- Executable allocated-wire check used by the compiler certificate. -/
def allocatedQB {q c : ℕ} (ρ : RegFile q c) (w : Fin q) : Bool :=
  decide (w.1 < ρ.nextQ)

/-- Executable allocated-slot check used by the compiler certificate. -/
def allocatedCB {q c : ℕ} (ρ : RegFile q c) (b : Fin c) : Bool :=
  decide (b.1 < ρ.nextC)

theorem allocatedQB_sound {q c : ℕ} {ρ : RegFile q c} {w : Fin q}
    (h : ρ.allocatedQB w = true) : ρ.AllocatedQ w := by
  change w.1 < ρ.nextQ
  simpa [allocatedQB] using h

theorem allocatedCB_sound {q c : ℕ} {ρ : RegFile q c} {b : Fin c}
    (h : ρ.allocatedCB b = true) : ρ.AllocatedC b := by
  change b.1 < ρ.nextC
  simpa [allocatedCB] using h

end RegFile

end QLambda.Linear
