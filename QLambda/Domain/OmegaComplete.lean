/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints

/-!
# ω-complete partial orders
-/

namespace QLambda.Domain

universe u v

/-- A partial order with suprema of increasing `ℕ`-chains.  Pointedness is
separate: only least-fixed-point constructions require `OrderBot`. -/
class OmegaComplete (D : Type u) [PartialOrder D] where
  ωSup : (c : ℕ → D) → Monotone c → D
  le_ωSup : ∀ (c : ℕ → D) (hc : Monotone c) (n : ℕ), c n ≤ ωSup c hc
  ωSup_le : ∀ (c : ℕ → D) (hc : Monotone c) (x : D),
    (∀ n, c n ≤ x) → ωSup c hc ≤ x

namespace OmegaComplete

variable {D : Type u} [PartialOrder D] [OmegaComplete D]

theorem ωSup_unique (c : ℕ → D) (hc : Monotone c) {x : D}
    (hupper : ∀ n, c n ≤ x) (hleast : ∀ y, (∀ n, c n ≤ y) → x ≤ y) :
    OmegaComplete.ωSup c hc = x := by
  apply le_antisymm
  · exact OmegaComplete.ωSup_le c hc x hupper
  · exact hleast _ (OmegaComplete.le_ωSup c hc)

theorem ωSup_mono {c d : ℕ → D} (hc : Monotone c) (hd : Monotone d)
    (hcd : ∀ n, c n ≤ d n) :
    OmegaComplete.ωSup c hc ≤ OmegaComplete.ωSup d hd := by
  apply OmegaComplete.ωSup_le
  intro n
  exact (hcd n).trans (OmegaComplete.le_ωSup d hd n)

theorem ωSup_const (x : D) :
    OmegaComplete.ωSup (fun _ : ℕ => x) monotone_const = x := by
  apply ωSup_unique
  · exact fun _ => le_rfl
  · intro y hy
    exact hy 0

end OmegaComplete

end QLambda.Domain
