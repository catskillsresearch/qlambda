/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.SubNormalizedDensity
import QLambda.instPartialOrderSubNormalizedDensity

/-!
# Instance `instOrderBotSubNormalizedDensity`
-/

namespace SubNormalizedDensity

open Matrix
open scoped MatrixOrder ComplexOrder
variable {n : ℕ}

instance instOrderBotSubNormalizedDensity : OrderBot (SubNormalizedDensity n) where
  bot := ⟨0, PosSemidef.zero, by simp [Matrix.trace_zero]⟩
  bot_le ρ := by
    change (ρ.mat - 0).PosSemidef
    simpa using ρ.posSemidef

theorem mat_bot : (⊥ : SubNormalizedDensity n).mat = 0 := rfl

theorem spectralErode_mono {t : ℝ} (_ht : 0 ≤ t) {ρ σ : SubNormalizedDensity n}
    (h : ρ ≤ σ) : spectralErode t ρ ≤ spectralErode t σ := by
  change ((spectralErode t σ).mat - (spectralErode t ρ).mat).PosSemidef
  have : (spectralErode t σ).mat - (spectralErode t ρ).mat =
      spectralScale t • (σ.mat - ρ.mat) := by
    simp [spectralErode_mat, smul_sub]
  rw [this]
  exact (le_iff.mp h).smul (spectralScale_nonneg t)

end SubNormalizedDensity
