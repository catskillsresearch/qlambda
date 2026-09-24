/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.SubNormalizedDensity

/-!
# Instance `instPartialOrderSubNormalizedDensity`
-/

namespace SubNormalizedDensity

open Matrix
open scoped MatrixOrder ComplexOrder
variable {n : ℕ}

/-- Loewner order: `ρ ≤ σ` iff `σ − ρ` is positive semidefinite. -/
instance instPartialOrderSubNormalizedDensity : PartialOrder (SubNormalizedDensity n) where
  le ρ σ := ρ.mat ≤ σ.mat
  le_refl ρ := le_refl ρ.mat
  le_trans ρ σ τ := le_trans
  le_antisymm ρ σ hρσ hσρ := ext (le_antisymm hρσ hσρ)

theorem le_def {ρ σ : SubNormalizedDensity n} :
    ρ ≤ σ ↔ ρ.mat ≤ σ.mat :=
  Iff.rfl

theorem le_iff {ρ σ : SubNormalizedDensity n} :
    ρ ≤ σ ↔ (σ.mat - ρ.mat).PosSemidef :=
  Iff.rfl

end SubNormalizedDensity
