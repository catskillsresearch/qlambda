/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.Hom
import QLambda.Domain.Presheaf.instZeroHom

/-!
# Instances from `Hom`

Barrel re-exporting `QLambda.Domain.Presheaf.Hom` and its typeclass instances.
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule
namespace Hom

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

universe u v w

@[simp]
theorem zero_app (M : Module.{u}) (N : Module.{v})
    (n : ℕ) (x : (M.obj n).Carrier) :
    (0 : Hom M N).app n x = 0 :=
  rfl

theorem hasSum_empty (M : Module.{u}) (N : Module.{v}) :
    HasSum (fun i : Empty => nomatch i) (0 : Hom M N) := by
  intro n x
  convert (N.obj n).summation.empty using 1
  change (zero M N).app n x = 0
  rfl

theorem hasSum_remove_zero {M : Module.{u}} {N : Module.{v}}
    {ι : Type} [Countable ι] (f : ι → Hom M N) (s : Set ι)
    (g : Hom M N) (hzero : ∀ i, i ∉ s → f i = 0) :
    HasSum (fun i : s => f i) g ↔ HasSum f g := by
  constructor <;> intro h n x
  · apply ((N.obj n).summation.remove_zero
      (fun i => (f i).app n x) s (g.app n x) ?_).mp
    · exact h n x
    · intro i hi
      rw [hzero i hi]
      rfl
  · apply ((N.obj n).summation.remove_zero
      (fun i => (f i).app n x) s (g.app n x) ?_).mpr
    · exact h n x
    · intro i hi
      rw [hzero i hi]
      rfl


end Hom
end SuperoperatorModule
end QLambda.Domain.Presheaf
