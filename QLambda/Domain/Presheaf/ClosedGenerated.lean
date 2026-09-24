/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.ClosedBasis

/-!
# Closed-generated modules
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

/-- A module with an exhibited basis from the concrete closed coefficient
fragment. -/
structure ClosedGenerated where
  module : Module
  basis : ClosedBasis module

/-- A symmetric tensor power is a concrete one-coefficient generated
object. -/
noncomputable def closedSymmetricPower (A k : ℕ) : ClosedGenerated where
  module := symmetricPower A k
  basis :=
    { Index := PUnit
      countableIndex := inferInstance
      coeff := fun _ => .symmetricPower A k
      ket := fun _ => Hom.id _
      bra := fun _ => Hom.id _
      resolves := by
        intro n x
        change ((symmetricPower A k).obj n).HasSum
          (fun _ : PUnit => x) x
        exact ((symmetricPower A k).obj n).summation.singleton x }

/-- Every representable belongs to the concretely closed generated
subcategory. -/
noncomputable def closedRepresentable (A : ℕ) : ClosedGenerated where
  module := representable A
  basis :=
    { Index := PUnit
      countableIndex := inferInstance
      coeff := fun _ => .representable A
      ket := fun _ => Hom.id _
      bra := fun _ => Hom.id _
      resolves := by
        intro n x
        change ((representable A).obj n).HasSum
          (fun _ : PUnit => x) x
        exact ((representable A).obj n).summation.singleton x }

/-- The Day tensor of two representables is again a closed-generated object. -/
noncomputable def closedTensorRepresentable (A B : ℕ) : ClosedGenerated :=
  closedRepresentable (A * B)

@[simp]
theorem closedTensorRepresentable_module (A B : ℕ) :
    (closedTensorRepresentable A B).module =
      dayTensorRepresentable A B :=
  rfl

/-- Internal hom from a representable to a generated coefficient is itself a
closed-generated one-coefficient object. -/
noncomputable def closedInternalHomRepresentable
    (A : ℕ) (B : ClosedCoefficient) : ClosedGenerated where
  module := internalHomRepresentable A B.toModule
  basis :=
    { Index := PUnit
      countableIndex := inferInstance
      coeff := fun _ => B.hom A
      ket := fun _ => Hom.id _
      bra := fun _ => Hom.id _
      resolves := by
        intro n x
        change ((internalHomRepresentable A B.toModule).obj n).HasSum
          (fun _ : PUnit => x) x
        exact
          ((internalHomRepresentable A B.toModule).obj n).summation.singleton x }

@[simp]
theorem closedInternalHomRepresentable_module
    (A : ℕ) (B : ClosedCoefficient) :
    (closedInternalHomRepresentable A B).module =
      internalHomRepresentable A B.toModule :=
  rfl

end SuperoperatorModule

end QLambda.Domain.Presheaf
