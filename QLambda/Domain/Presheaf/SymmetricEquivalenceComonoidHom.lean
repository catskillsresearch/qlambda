/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.ExponentialCore

/-!
# Equivalence-induced concrete comonoid morphisms
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

set_option maxHeartbeats 8000000

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-! ## Equivalence-induced structural promotions -/

/-- Concrete comonoid morphisms supported by the present tensor
construction.  The sole datum is a finite basis equivalence; all comonoid
laws are theorems about its promoted map, not assumptions stored in fields. -/
structure SymmetricEquivalenceComonoidHom (A B : ℕ) where
  equivalence : Fin A ≃ Fin B

namespace SymmetricEquivalenceComonoidHom

@[ext]
theorem ext {A B : ℕ}
    {f g : SymmetricEquivalenceComonoidHom A B}
    (h : f.equivalence = g.equivalence) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Underlying promoted module map. -/
noncomputable def hom {A B : ℕ}
    (f : SymmetricEquivalenceComonoidHom A B) :
    Hom (symmetricFormalPowerSeries A)
      (symmetricFormalPowerSeries B) :=
  symmetricEquivalencePromotion f.equivalence

/-- Induced map on tensor squares. -/
noncomputable def tensorHom {A B : ℕ}
    (f : SymmetricEquivalenceComonoidHom A B) :
    Hom (symmetricFormalTensorSquare A)
      (symmetricFormalTensorSquare B) :=
  symmetricTensorSquareEquivalenceMap f.equivalence

theorem preserves_contraction {A B : ℕ}
    (f : SymmetricEquivalenceComonoidHom A B) :
    Hom.comp (symmetricContraction B) f.hom =
      Hom.comp f.tensorHom (symmetricContraction A) :=
  symmetricContraction_promotion f.equivalence

theorem preserves_weakening {A B : ℕ}
    (f : SymmetricEquivalenceComonoidHom A B) :
    Hom.comp (symmetricWeakening B) f.hom =
      symmetricWeakening A :=
  symmetricWeakening_promotion f.equivalence

theorem dereliction_hom {A B : ℕ}
    (f : SymmetricEquivalenceComonoidHom A B) :
    Hom.comp (symmetricDereliction B) f.hom =
      Hom.comp
        (yonedaMap
          (Superoperator.ofEquivalence
            (symmetricPromotionLinearPart f.equivalence)))
        (symmetricDereliction A) :=
  symmetricDereliction_promotion f.equivalence

end SymmetricEquivalenceComonoidHom

end SuperoperatorModule

end QLambda.Domain.Presheaf
