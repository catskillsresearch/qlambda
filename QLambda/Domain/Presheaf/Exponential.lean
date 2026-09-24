/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.ExponentialCore
import QLambda.Domain.Presheaf.SymmetricEquivalenceComonoidHom

/-!
# Countable formal power series

Barrel: series constructions plus `SymmetricEquivalenceComonoidHom`.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

set_option maxHeartbeats 8000000

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder


/-- Promotion into the restricted concrete comonoid-morphism class. -/
def symmetricEquivalencePromote {A B : ℕ} (e : Fin A ≃ Fin B) :
    SymmetricEquivalenceComonoidHom A B :=
  ⟨e⟩

/-- Recover the cogenerating basis equivalence. -/
def symmetricEquivalenceGenerator {A B : ℕ}
    (f : SymmetricEquivalenceComonoidHom A B) :
    Fin A ≃ Fin B :=
  f.equivalence

@[simp]
theorem symmetricEquivalenceGenerator_promote {A B : ℕ}
    (e : Fin A ≃ Fin B) :
    symmetricEquivalenceGenerator (symmetricEquivalencePromote e) = e :=
  rfl

@[simp]
theorem symmetricEquivalencePromote_generator {A B : ℕ}
    (f : SymmetricEquivalenceComonoidHom A B) :
    symmetricEquivalencePromote (symmetricEquivalenceGenerator f) = f := by
  cases f
  rfl

/-- Equivalence between finite basis maps and the structural promotions they
induce.  This is not the unrestricted cofree correspondence. -/
def symmetricEquivalencePromotionEquiv (A B : ℕ) :
    (Fin A ≃ Fin B) ≃ SymmetricEquivalenceComonoidHom A B where
  toFun := symmetricEquivalencePromote
  invFun := symmetricEquivalenceGenerator
  left_inv := symmetricEquivalenceGenerator_promote
  right_inv := symmetricEquivalencePromote_generator

/-- Uniqueness of restricted promotion. -/
theorem symmetricEquivalencePromotion_unique {A B : ℕ}
    (e : Fin A ≃ Fin B) (f : SymmetricEquivalenceComonoidHom A B)
    (hf : symmetricEquivalenceGenerator f = e) :
    f = symmetricEquivalencePromote e := by
  apply SymmetricEquivalenceComonoidHom.ext
  exact hf

/-- The fully typed coefficientwise composite
`(weakening ⊗ id) ∘ contraction`. -/
noncomputable def symmetricLeftCounitComposite (A : ℕ) :
    Hom (symmetricFormalPowerSeries A)
      (symmetricFormalPowerSeries A) where
  app := fun _ x q =>
    { val := Superoperator.comp
        (Superoperator.ofEquivalence (homogeneousLeftUnitorEquiv A q))
        (Superoperator.comp
          (Superoperator.ofEquivalence (tensorSplitEquiv A 0 q))
          (x (0 + q)).val)
      invariant := by
        intro σ
        rw [SymmetricElement.left_counit x]
        exact (x q).invariant σ }
  map_zero := by
    intro n
    funext q
    apply SymmetricElement.ext
    exact SymmetricElement.left_counit
      (fun k => (0 : SymmetricElement A k n))
  map_sum := by
    intro ι _ n f x h q
    exact SigmaMon.ChoiSum.comp_left
      (Superoperator.ofEquivalence (homogeneousLeftUnitorEquiv A q))
      (SigmaMon.ChoiSum.comp_left
        (Superoperator.ofEquivalence (tensorSplitEquiv A 0 q))
        (h (0 + q)))
  naturality := by
    intro m n x f
    funext q
    apply SymmetricElement.ext
    change
      Superoperator.comp
          (Superoperator.ofEquivalence (homogeneousLeftUnitorEquiv A q))
          (Superoperator.comp
            (Superoperator.ofEquivalence (tensorSplitEquiv A 0 q))
            (Superoperator.comp (x (0 + q)).val f)) =
        Superoperator.comp
          (Superoperator.comp
            (Superoperator.ofEquivalence (homogeneousLeftUnitorEquiv A q))
            (Superoperator.comp
              (Superoperator.ofEquivalence (tensorSplitEquiv A 0 q))
              (x (0 + q)).val)) f
    simp only [Superoperator.comp_assoc]

/-- The fully typed coefficientwise composite
`(id ⊗ weakening) ∘ contraction`. -/
noncomputable def symmetricRightCounitComposite (A : ℕ) :
    Hom (symmetricFormalPowerSeries A)
      (symmetricFormalPowerSeries A) where
  app := fun _ x p =>
    { val := Superoperator.comp
        (Superoperator.ofEquivalence (homogeneousRightUnitorEquiv A p))
        (Superoperator.comp
          (Superoperator.ofEquivalence (tensorSplitEquiv A p 0))
          (x (p + 0)).val)
      invariant := by
        intro σ
        rw [SymmetricElement.right_counit x]
        exact (x p).invariant σ }
  map_zero := by
    intro n
    funext p
    apply SymmetricElement.ext
    exact SymmetricElement.right_counit
      (fun k => (0 : SymmetricElement A k n))
  map_sum := by
    intro ι _ n f x h p
    exact SigmaMon.ChoiSum.comp_left
      (Superoperator.ofEquivalence (homogeneousRightUnitorEquiv A p))
      (SigmaMon.ChoiSum.comp_left
        (Superoperator.ofEquivalence (tensorSplitEquiv A p 0))
        (h (p + 0)))
  naturality := by
    intro m n x f
    funext p
    apply SymmetricElement.ext
    change
      Superoperator.comp
          (Superoperator.ofEquivalence (homogeneousRightUnitorEquiv A p))
          (Superoperator.comp
            (Superoperator.ofEquivalence (tensorSplitEquiv A p 0))
            (Superoperator.comp (x (p + 0)).val f)) =
        Superoperator.comp
          (Superoperator.comp
            (Superoperator.ofEquivalence (homogeneousRightUnitorEquiv A p))
            (Superoperator.comp
              (Superoperator.ofEquivalence (tensorSplitEquiv A p 0))
              (x (p + 0)).val)) f
    simp only [Superoperator.comp_assoc]

@[simp]
theorem symmetricLeftCounit_contraction (A : ℕ) :
    symmetricLeftCounitComposite A =
      Hom.id (symmetricFormalPowerSeries A) := by
  ext n x
  funext q
  apply SymmetricElement.ext
  exact SymmetricElement.left_counit x

@[simp]
theorem symmetricRightCounit_contraction (A : ℕ) :
    symmetricRightCounitComposite A =
      Hom.id (symmetricFormalPowerSeries A) := by
  ext n x
  funext p
  apply SymmetricElement.ext
  exact SymmetricElement.right_counit x

/-- The left-associated coefficientwise Day tensor cube. -/
noncomputable def symmetricFormalTensorCube (A : ℕ) : Module :=
  countableProduct (fun p =>
    countableProduct (fun q =>
      countableProduct (fun r =>
        representable
          ((tensorPowerDimension A p * tensorPowerDimension A q) *
            tensorPowerDimension A r))))

/-- The coefficientwise composite `(contraction ⊗ id) ∘ contraction`. -/
noncomputable def symmetricLeftIteratedContraction (A : ℕ) :
    Hom (symmetricFormalPowerSeries A)
      (symmetricFormalTensorCube A) where
  app := fun _ x p q r =>
    Superoperator.comp
      (Superoperator.ofEquivalence
        (contractionLeftRefinementEquiv A p q r))
      (Superoperator.comp
        (Superoperator.ofEquivalence
          (tensorSplitEquiv A (p + q) r))
        (x ((p + q) + r)).val)
  map_zero := by
    intro n
    funext p q r
    change
      Superoperator.comp
          (Superoperator.ofEquivalence
            (contractionLeftRefinementEquiv A p q r))
          (Superoperator.comp
            (Superoperator.ofEquivalence
              (tensorSplitEquiv A (p + q) r))
            (0 : Superoperator n
              (tensorPowerDimension A ((p + q) + r)))) =
        (0 : Superoperator n
          ((tensorPowerDimension A p * tensorPowerDimension A q) *
            tensorPowerDimension A r))
    rw [Superoperator.comp_zero_right, Superoperator.comp_zero_right]
  map_sum := by
    intro ι _ n f x h p q r
    exact SigmaMon.ChoiSum.comp_left
      (Superoperator.ofEquivalence
        (contractionLeftRefinementEquiv A p q r))
      (SigmaMon.ChoiSum.comp_left
        (Superoperator.ofEquivalence
          (tensorSplitEquiv A (p + q) r))
        (h ((p + q) + r)))
  naturality := by
    intro m n x f
    funext p q r
    change
      Superoperator.comp
          (Superoperator.ofEquivalence
            (contractionLeftRefinementEquiv A p q r))
          (Superoperator.comp
            (Superoperator.ofEquivalence
              (tensorSplitEquiv A (p + q) r))
            (Superoperator.comp (x ((p + q) + r)).val f)) =
        Superoperator.comp
          (Superoperator.comp
            (Superoperator.ofEquivalence
              (contractionLeftRefinementEquiv A p q r))
            (Superoperator.comp
              (Superoperator.ofEquivalence
                (tensorSplitEquiv A (p + q) r))
              (x ((p + q) + r)).val)) f
    simp only [Superoperator.comp_assoc]

/-- The coefficientwise composite `(id ⊗ contraction) ∘ contraction`,
transported to the left-associated tensor cube. -/
noncomputable def symmetricRightIteratedContraction (A : ℕ) :
    Hom (symmetricFormalPowerSeries A)
      (symmetricFormalTensorCube A) where
  app := fun _ x p q r =>
    Superoperator.comp
      (Superoperator.ofEquivalence
        (contractionRightRefinementEquiv A p q r))
      (Superoperator.comp
        (Superoperator.ofEquivalence
          (tensorSplitEquiv A p (q + r)))
        (x (p + (q + r))).val)
  map_zero := by
    intro n
    funext p q r
    change
      Superoperator.comp
          (Superoperator.ofEquivalence
            (contractionRightRefinementEquiv A p q r))
          (Superoperator.comp
            (Superoperator.ofEquivalence
              (tensorSplitEquiv A p (q + r)))
            (0 : Superoperator n
              (tensorPowerDimension A (p + (q + r))))) =
        (0 : Superoperator n
          ((tensorPowerDimension A p * tensorPowerDimension A q) *
            tensorPowerDimension A r))
    rw [Superoperator.comp_zero_right, Superoperator.comp_zero_right]
  map_sum := by
    intro ι _ n f x h p q r
    exact SigmaMon.ChoiSum.comp_left
      (Superoperator.ofEquivalence
        (contractionRightRefinementEquiv A p q r))
      (SigmaMon.ChoiSum.comp_left
        (Superoperator.ofEquivalence
          (tensorSplitEquiv A p (q + r)))
        (h (p + (q + r))))
  naturality := by
    intro m n x f
    funext p q r
    change
      Superoperator.comp
          (Superoperator.ofEquivalence
            (contractionRightRefinementEquiv A p q r))
          (Superoperator.comp
            (Superoperator.ofEquivalence
              (tensorSplitEquiv A p (q + r)))
            (Superoperator.comp (x (p + (q + r))).val f)) =
        Superoperator.comp
          (Superoperator.comp
            (Superoperator.ofEquivalence
              (contractionRightRefinementEquiv A p q r))
            (Superoperator.comp
              (Superoperator.ofEquivalence
                (tensorSplitEquiv A p (q + r)))
              (x (p + (q + r))).val)) f
    simp only [Superoperator.comp_assoc]

@[simp]
theorem symmetricContraction_coassociative (A : ℕ) :
    symmetricLeftIteratedContraction A =
      symmetricRightIteratedContraction A := by
  ext n x
  funext p q r
  exact SymmetricElement.contraction_coassociative x

/-! ## Formal power series on tensor powers -/

/-- Formal power series whose degree-`k` coefficient lies in the
representable `k`-fold tensor power. -/
noncomputable def formalPowerSeries (A : ℕ) : Module :=
  countableProduct (fun k => (exponentialDegree A k).toModule)

/-- The formal-series product remains in the closed-generated fragment: its
degree projections and injections form a countable resolution of identity. -/
noncomputable def closedFormalPowerSeries (A : ℕ) : ClosedGenerated where
  module := formalPowerSeries A
  basis :=
    { Index := ℕ
      countableIndex := inferInstance
      coeff := exponentialDegree A
      ket := fun k =>
        countableProductInjection
          (fun j => (exponentialDegree A j).toModule) k
      bra := fun k =>
        countableProductProjection
          (fun j => (exponentialDegree A j).toModule) k
      resolves := by
        intro n x k
        change ((exponentialDegree A k).toModule.obj n).HasSum
          (fun i => if h : k = i then h ▸ x i else 0) (x k)
        have hs := Fiber.hasSum_singleCoordinate
          ((exponentialDegree A k).toModule.obj n) k (x k)
        convert hs using 1
        funext i
        by_cases h : k = i
        · subst i
          simp
        · simp [h, Ne.symm h] }

@[simp]
theorem closedFormalPowerSeries_module (A : ℕ) :
    (closedFormalPowerSeries A).module = formalPowerSeries A :=
  rfl

/-- Functorial action on formal power series, coefficient by coefficient. -/
noncomputable def formalPowerSeriesMap {A B : ℕ}
    (f : Superoperator A B) :
    Hom (formalPowerSeries A) (formalPowerSeries B) :=
  countableProductMap (fun k => exponentialDegreeMap f k)

@[simp]
theorem formalPowerSeriesMap_identity (A : ℕ) :
    formalPowerSeriesMap (Superoperator.identity A) =
      Hom.id (formalPowerSeries A) := by
  have h :
      (fun k => exponentialDegreeMap (Superoperator.identity A) k) =
        (fun k => Hom.id (exponentialDegree A k).toModule) := by
    funext k
    exact exponentialDegreeMap_identity A k
  rw [formalPowerSeriesMap, h]
  exact countableProductMap_id
    (fun k => (exponentialDegree A k).toModule)

@[simp]
theorem formalPowerSeriesMap_comp {A B C : ℕ}
    (g : Superoperator B C) (f : Superoperator A B) :
    formalPowerSeriesMap (Superoperator.comp g f) =
      Hom.comp (formalPowerSeriesMap g) (formalPowerSeriesMap f) := by
  have h :
      (fun k => exponentialDegreeMap (Superoperator.comp g f) k) =
        (fun k => Hom.comp (exponentialDegreeMap g k)
          (exponentialDegreeMap f k)) := by
    funext k
    exact exponentialDegreeMap_comp g f k
  rw [formalPowerSeriesMap, formalPowerSeriesMap, formalPowerSeriesMap, h]
  exact countableProductMap_comp
    (fun k => exponentialDegreeMap g k)
    (fun k => exponentialDegreeMap f k)

/-- Weakening is extraction of the constant coefficient. -/
noncomputable def formalPowerSeriesWeakening (A : ℕ) :
    Hom (formalPowerSeries A) (representable 1) :=
  by
    simpa [formalPowerSeries, exponentialDegree,
      ClosedCoefficient.toModule] using
      (countableProductProjection
        (fun k => (exponentialDegree A k).toModule) 0)

/-- Dereliction is extraction of the linear coefficient. -/
noncomputable def formalPowerSeriesDereliction (A : ℕ) :
    Hom (formalPowerSeries A) (representable A) :=
  by
    simpa [formalPowerSeries, exponentialDegree,
      ClosedCoefficient.toModule] using
      (countableProductProjection
        (fun k => (exponentialDegree A k).toModule) 1)

/-- Maps into formal power series are exactly coefficientwise families of
maps.  This is the premise-free formal-series universal property available
before constructing a Day tensor with a non-representable input. -/
noncomputable def formalPowerSeriesEquiv (M : Module.{u}) (A : ℕ) :
    Hom M (formalPowerSeries A) ≃
      ∀ k, Hom M (exponentialDegree A k).toModule :=
  countableProductEquiv M
    (fun k => (exponentialDegree A k).toModule)

end SuperoperatorModule

end QLambda.Domain.Presheaf
