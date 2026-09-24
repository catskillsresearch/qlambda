/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitChannels

/-!
# Expand `∑ : Fin 4`
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators


theorem sum_fin4_coassoc (f : Fin 4 → ℂ) :
    (∑ x : Fin 4, f x) = f 0 + f 1 + f 2 + f 3 := by
  rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  simp [Finset.sum_insert]
  ring

end QLambda.Linear
