/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.ClosedGenerated

/-!
# Countable formal power series

This file assembles homogeneous coefficients into countable products in
partial-countable-sum modules.  It includes both the raw tensor-power series
and the actual finite-permutation-invariant symmetric series.

The countable product has its premise-free universal property and a concrete
closed basis.  Countable products of representables have a coefficientwise
Day tensor and canonical bilinear map.  For symmetric series, weakening,
dereliction, contraction, genuine tensor-factor braiding, both counit laws,
cocommutativity, and coassociativity are all constructed and proved.

Functorial structural promotion is proved for maps induced by finite basis
equivalences.  This class is nontrivial and preserves weakening and
contraction, but it is not cofree promotion and it is not used as one.  The
cofree universal property would be
`ComonoidHom C (!A) ≃ Hom C A`; its induced co-Kleisli operation has type
`Hom (!B) A → Hom (!B) (!A)`, not `Hom M (!A) → Hom (!M) (!A)`.
`tensorPowerDimension_mul_add` shows that a partition of a fixed total degree
lands in one common tensor-power dimension, so the missing fact is not a
dimension mismatch.  `ChoiSum.tensor_finite_subfamily_cp_sum` supplies joint
trace-nonincrease only for the tensor of two families that are already
summable at two fixed dimensions.  It does not transport the homogeneous
branch bound
`countableProductHom_finite_components_tni` across a sum of tensors whose
factors lie in different symmetric-power degrees.

This does not make the identity-in-every-degree series a counterexample:
cofreeness over the tensor unit requires precisely that series, and the
different degree splits are coordinates of a Day tensor rather than branches
to be added.  The actual unresolved gate is categorical.  The object named
`symmetricFormalTensorSquare` below is an ambient coefficientwise product; it
has not been proved to be the genuine Day tensor of two symmetric-series
modules, and the coordinatewise split has not been proved to factor through
such a tensor.  The published abstract cofree object exists by local
presentability and an adjoint-functor theorem; its later formal-series
description assumes that existence and is not an independent construction.
General Day closure, hereditary factorization, the cofree universal property,
double-dual classical closure, and the resulting comonad are all still
required.  No cofree promotion, comonad multiplication, or `LNLModel`
instance is defined from the equivalence action.  See
`QLambda.Domain.Presheaf.Comonoid` for the Day-comonoid interface, the
series→square comparison, and the ambient obstruction
`factorPermutationEquiv_swap_ne_refl`; Day factorization of contraction
remains the open Prop `SymmetricContractionDayFactorization`.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u v w

/-- Tensor a superoperator with itself a specified number of times. -/
noncomputable def tensorPowerMap {A B : ℕ}
    (f : Superoperator A B) :
    (k : ℕ) →
      Superoperator (tensorPowerDimension A k)
        (tensorPowerDimension B k)
  | 0 => Superoperator.identity 1
  | k + 1 => Superoperator.tensor f (tensorPowerMap f k)

@[simp]
theorem tensorPowerMap_zero {A B : ℕ} (f : Superoperator A B) :
    tensorPowerMap f 0 = Superoperator.identity 1 :=
  rfl

@[simp]
theorem tensorPowerMap_succ {A B : ℕ} (f : Superoperator A B) (k : ℕ) :
    tensorPowerMap f (k + 1) =
      Superoperator.tensor f (tensorPowerMap f k) :=
  rfl

@[simp]
theorem tensorPowerMap_identity (A k : ℕ) :
    tensorPowerMap (Superoperator.identity A) k =
      Superoperator.identity (tensorPowerDimension A k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [tensorPowerMap_succ, ih, Superoperator.tensor_identity]
      rfl

@[simp]
theorem tensorPowerMap_comp {A B C : ℕ}
    (g : Superoperator B C) (f : Superoperator A B) (k : ℕ) :
    tensorPowerMap (Superoperator.comp g f) k =
      Superoperator.comp (tensorPowerMap g k) (tensorPowerMap f k) := by
  induction k with
  | zero => exact (Superoperator.identity_comp _).symm
  | succ k ih =>
      rw [tensorPowerMap_succ, tensorPowerMap_succ,
        tensorPowerMap_succ, ih, Superoperator.tensor_comp]
      rfl

/-- The degree-`k` homogeneous coefficient of the representable exponential
skeleton. -/
def exponentialDegree (A k : ℕ) : ClosedCoefficient :=
  .representable (tensorPowerDimension A k)

/-- All homogeneous coefficients, indexed countably by degree. -/
def exponentialSkeleton (A : ℕ) : ℕ → ClosedCoefficient :=
  exponentialDegree A

@[simp]
theorem exponentialSkeleton_zero (A : ℕ) :
    exponentialSkeleton A 0 = .representable 1 :=
  rfl

@[simp]
theorem exponentialSkeleton_one (A : ℕ) :
    exponentialSkeleton A 1 = .representable A := by
  simp [exponentialSkeleton, exponentialDegree]

@[simp]
theorem exponentialSkeleton_succ (A k : ℕ) :
    exponentialSkeleton A (k + 1) =
      .representable (A * tensorPowerDimension A k) :=
  rfl

/-- Functorial action on each homogeneous coefficient. -/
noncomputable def exponentialDegreeMap {A B : ℕ}
    (f : Superoperator A B) (k : ℕ) :
    Hom (exponentialDegree A k).toModule
      (exponentialDegree B k).toModule :=
  yonedaMap (tensorPowerMap f k)

@[simp]
theorem exponentialDegreeMap_identity (A k : ℕ) :
    exponentialDegreeMap (Superoperator.identity A) k =
      Hom.id (exponentialDegree A k).toModule := by
  rw [exponentialDegreeMap, tensorPowerMap_identity, yonedaMap_id]
  ext n x
  rfl

@[simp]
theorem exponentialDegreeMap_comp {A B C : ℕ}
    (g : Superoperator B C) (f : Superoperator A B) (k : ℕ) :
    exponentialDegreeMap (Superoperator.comp g f) k =
      Hom.comp (exponentialDegreeMap g k)
        (exponentialDegreeMap f k) := by
  rw [exponentialDegreeMap, tensorPowerMap_comp, yonedaMap_comp]
  ext n x
  rfl

/-! ## Countable products of concrete modules -/

/-- The countable product of fibers, with partial sums defined
coefficientwise. -/
noncomputable def countableProductFiber
    (X : ℕ → Fiber.{u}) : Fiber.{u} where
  Carrier := ∀ k, (X k).Carrier
  zero := fun _ => 0
  summation :=
    { HasSum := fun f x =>
        ∀ k, (X k).HasSum (fun i => f i k) (x k)
      unique := by
        intro ι _ f x y hx hy
        funext k
        exact (X k).summation.unique (hx k) (hy k)
      empty := by
        intro k
        convert (X k).summation.empty using 1
        rfl
      singleton := by
        intro x k
        exact (X k).summation.singleton (x k)
      remove_zero := by
        intro ι _ f s x hzero
        constructor <;> intro h k
        · exact ((X k).summation.remove_zero
            (fun i => f i k) s (x k)
            (fun i hi => congrFun (hzero i hi) k)).mp (h k)
        · exact ((X k).summation.remove_zero
            (fun i => f i k) s (x k)
            (fun i hi => congrFun (hzero i hi) k)).mpr (h k)
      reindex := by
        intro ι κ _ _ e f x
        constructor <;> intro h k
        · exact ((X k).summation.reindex e
            (fun i => f i k) (x k)).mp (h k)
        · exact ((X k).summation.reindex e
            (fun i => f i k) (x k)).mpr (h k)
      flatten := by
        classical
        intro ι _ κ _ f x
        constructor
        · intro h
          have hk : ∀ k, ∃ g : ι → (X k).Carrier,
              (∀ i, (X k).HasSum (fun j => f i j k) (g i)) ∧
                (X k).HasSum g (x k) := by
            intro k
            exact ((X k).summation.flatten
              (fun i j => f i j k) (x k)).mp (h k)
          choose g hrows hsum using hk
          refine ⟨fun i k => g k i, ?_, ?_⟩
          · intro i k
            exact hrows k i
          · intro k
            exact hsum k
        · rintro ⟨g, hrows, hsum⟩ k
          exact ((X k).summation.flatten
            (fun i j => f i j k) (x k)).mpr
              ⟨fun i => g i k, fun i => hrows i k, hsum k⟩ }

/-- A family indexed by `ℕ` with exactly one nonzero coordinate has the
expected sum in every partial-countable-sum fiber. -/
theorem Fiber.hasSum_singleCoordinate (X : Fiber.{u}) (k : ℕ)
    (a : X.Carrier) :
    X.HasSum (fun i : ℕ => if i = k then a else 0) a := by
  let e : PUnit ≃ ({k} : Set ℕ) := (Equiv.Set.singleton k).symm
  have hs : X.HasSum
      (fun i : ({k} : Set ℕ) =>
        if (i : ℕ) = k then a else 0) a := by
    apply (X.summation.reindex e
      (fun i : ({k} : Set ℕ) =>
        if (i : ℕ) = k then a else 0) a).mp
    convert X.summation.singleton a using 1
    funext p
    have hp : (e p : ℕ) = k := (e p).property
    simp [hp]
  exact (X.summation.remove_zero
    (fun i : ℕ => if i = k then a else 0)
    ({k} : Set ℕ) a (by
      intro i hi
      simp only [Set.mem_singleton_iff] at hi
      simp [hi])).mp hs

/-- A one-supported family over any countable decidable index has its
nonzero value as sum. -/
theorem Fiber.hasSum_singleAt (X : Fiber.{u}) {ι : Type}
    [Countable ι] [DecidableEq ι] (k : ι) (a : X.Carrier) :
    X.HasSum (fun i : ι => if i = k then a else 0) a := by
  let e : PUnit ≃ ({k} : Set ι) := (Equiv.Set.singleton k).symm
  have hs : X.HasSum
      (fun i : ({k} : Set ι) =>
        if (i : ι) = k then a else 0) a := by
    apply (X.summation.reindex e
      (fun i : ({k} : Set ι) =>
        if (i : ι) = k then a else 0) a).mp
    convert X.summation.singleton a using 1
    funext p
    have hp : (e p : ι) = k := (e p).property
    simp [hp]
  exact (X.summation.remove_zero
    (fun i : ι => if i = k then a else 0)
    ({k} : Set ι) a (by
      intro i hi
      simp only [Set.mem_singleton_iff] at hi
      simp [hi])).mp hs

/-- The constantly-zero family has a sum over every countable index type. -/
theorem Fiber.hasSum_zero (X : Fiber.{u}) {ι : Type} [Countable ι] :
    X.HasSum (fun _ : ι => 0) 0 := by
  have hEmpty :
      X.HasSum (fun i : (∅ : Set ι) => 0) 0 := by
    convert ((X.summation.reindex (Equiv.Set.empty ι)
      (fun i : Empty => nomatch i) 0).mpr
        X.summation.empty) using 1
    funext i
    exact i.property.elim
  exact (X.summation.remove_zero
    (fun _ : ι => 0) ∅ 0 (by simp)).mp hEmpty

theorem Fiber.hasSum_congr (X : Fiber.{u}) {ι : Type} [Countable ι]
    {f g : ι → X.Carrier} {x : X.Carrier}
    (h : ∀ i, f i = g i) :
    X.HasSum f x ↔ X.HasSum g x := by
  have hfg : f = g := funext h
  subst g
  rfl

/-- The countable product of modules.  Both the base action and all partial
sums are pointwise in the coefficient index. -/
noncomputable def countableProduct
    (F : ℕ → Module.{u}) : Module.{u} where
  obj n := countableProductFiber (fun k => (F k).obj n)
  act := fun x f k => (F k).act (x k) f
  act_zero_element := by
    intro m n f
    funext k
    exact (F k).act_zero_element f
  act_zero_map := by
    intro m n x
    funext k
    exact (F k).act_zero_map (x k)
  act_id := by
    intro n x
    funext k
    exact (F k).act_id (x k)
  act_comp := by
    intro ℓ m n x f g
    funext k
    exact (F k).act_comp (x k) f g
  act_sum_element := by
    intro ι _ m n x s f h k
    exact (F k).act_sum_element f (h k)
  act_sum_map := by
    intro ι _ m n x f s h k
    exact (F k).act_sum_map (x k) h

/-- Projection from a countable product to one coefficient. -/
noncomputable def countableProductProjection
    (F : ℕ → Module.{u}) (k : ℕ) :
    Hom (countableProduct F) (F k) where
  app := fun _ x => x k
  map_zero := fun _ => rfl
  map_sum := fun h => h k
  naturality := fun _ _ => rfl

/-- Injection of one coefficient into a countable product. -/
noncomputable def countableProductInjection
    (F : ℕ → Module.{u}) (k : ℕ) :
    Hom (F k) (countableProduct F) where
  app := fun _ x j =>
    if h : j = k then h.symm ▸ x else 0
  map_zero := by
    intro n
    funext j
    change (if h : j = k then h.symm ▸ (0 : (F k).obj n |>.Carrier)
      else 0) = (0 : (F j).obj n |>.Carrier)
    by_cases hj : j = k
    · subst j
      simp
    · simp [hj]
  map_sum := by
    intro ι _ n f x h j
    by_cases hj : j = k
    · subst j
      simpa using h
    · simpa [hj] using Fiber.hasSum_zero ((F j).obj n)
  naturality := by
    intro m n x f
    funext j
    change
      (if h : j = k then h.symm ▸ (F k).act x f else 0) =
        (F j).act (if h : j = k then h.symm ▸ x else 0) f
    by_cases hj : j = k
    · subst j
      simp
    · simp only [hj, dite_false]
      exact ((F j).act_zero_element f).symm

/-- Every element of a countable product is the partial sum of its coordinate
injections. -/
theorem countableProduct_hasSum_coordinates
    (F : ℕ → Module.{u}) (n : ℕ)
    (x : (countableProduct F).obj n |>.Carrier) :
    (countableProduct F).obj n |>.HasSum
      (fun k => (countableProductInjection F k).app n (x k)) x := by
  intro j
  change (F j).obj n |>.HasSum
    (fun k => if h : j = k then h ▸ x k else 0) (x j)
  have hs := Fiber.hasSum_singleCoordinate ((F j).obj n) j (x j)
  convert hs using 1
  funext k
  by_cases h : j = k
  · subst k
    simp
  · simp [h, Ne.symm h]

/-- Maps out of a countable product are determined by all coordinate
inclusions.  This is the maps-out uniqueness half that does not require any
additional summability premise. -/
theorem countableProductHom_ext {F : ℕ → Module.{u}} {L : Module.{v}}
    {f g : Hom (countableProduct F) L}
    (h : ∀ k,
      Hom.comp f (countableProductInjection F k) =
        Hom.comp g (countableProductInjection F k)) :
    f = g := by
  apply Hom.ext
  intro n x
  have hf := f.map_sum (countableProduct_hasSum_coordinates F n x)
  have hg := g.map_sum (countableProduct_hasSum_coordinates F n x)
  apply (L.obj n).summation.unique hf
  convert hg using 1
  funext k
  exact congrArg (fun η => η.app n (x k)) (h k)

/-- Uniform varying-domain budget supplied by the product universal
property.  The maps in the homogeneous components may have unrelated
codomain dimensions internally; after choosing all precomposition elements
in one product fiber over `n`, every resulting branch has the common type
`Superoperator n B`, and `Hom.map_sum` proves their joint Choi sum. -/
theorem countableProductHom_components_hasSum
    {F : ℕ → Module.{u}} {B n : ℕ}
    (f : Hom (countableProduct F) (representable B))
    (x : (countableProduct F).obj n |>.Carrier) :
    SigmaMon.ChoiSum.HasSum
      (fun k =>
        (Hom.comp f (countableProductInjection F k)).app n (x k))
      (f.app n x) := by
  have h := f.map_sum (countableProduct_hasSum_coordinates F n x)
  change SigmaMon.ChoiSum.HasSum
    (fun k => f.app n ((countableProductInjection F k).app n (x k)))
    (f.app n x) at h
  simpa [Hom.comp] using h

/-- Every finite collection of homogeneous branches of a map from a
countable product to a representable has a jointly TNI CP aggregate. -/
theorem countableProductHom_finite_components_tni
    {F : ℕ → Module.{u}} {B n : ℕ}
    (f : Hom (countableProduct F) (representable B))
    (x : (countableProduct F).obj n |>.Carrier) (s : Finset ℕ) :
    ∃ Ψ : Superoperator n B,
      Ψ.cp =
        ∑ k ∈ s,
          ((Hom.comp f (countableProductInjection F k)).app n
            (x k)).cp := by
  exact SigmaMon.ChoiSum.finite_subfamily_cp_sum
    (countableProductHom_components_hasSum f x) s

/-- A family of maps into the coefficients induces a map into the countable
product. -/
noncomputable def countableProductLift {M : Module.{u}}
    (F : ℕ → Module.{v}) (f : ∀ k, Hom M (F k)) :
    Hom M (countableProduct F) where
  app := fun n x k => (f k).app n x
  map_zero := by
    intro n
    funext k
    exact (f k).map_zero n
  map_sum := by
    intro ι _ n g x h k
    exact (f k).map_sum h
  naturality := by
    intro m n x g
    funext k
    exact (f k).naturality x g

/-- The concrete universal property of the countable product. -/
noncomputable def countableProductEquiv (M : Module.{u})
    (F : ℕ → Module.{v}) :
    Hom M (countableProduct F) ≃ ∀ k, Hom M (F k) where
  toFun f k := Hom.comp (countableProductProjection F k) f
  invFun := countableProductLift F
  left_inv := by
    intro f
    ext n x
    funext k
    rfl
  right_inv := by
    intro f
    funext k
    ext n x
    rfl

/-- Pointwise action of a family of maps on countable products. -/
noncomputable def countableProductMap {F : ℕ → Module.{u}}
    {G : ℕ → Module.{v}} (f : ∀ k, Hom (F k) (G k)) :
    Hom (countableProduct F) (countableProduct G) :=
  countableProductLift G
    (fun k => Hom.comp (f k) (countableProductProjection F k))

@[simp]
theorem countableProductMap_id (F : ℕ → Module.{u}) :
    countableProductMap (fun k => Hom.id (F k)) =
      Hom.id (countableProduct F) := by
  ext n x
  funext k
  rfl

@[simp]
theorem countableProductMap_comp
    {F : ℕ → Module.{u}} {G : ℕ → Module.{v}}
    {H : ℕ → Module.{w}} (g : ∀ k, Hom (G k) (H k))
    (f : ∀ k, Hom (F k) (G k)) :
    countableProductMap (fun k => Hom.comp (g k) (f k)) =
      Hom.comp (countableProductMap g) (countableProductMap f) := by
  ext n x
  funext k
  rfl

/-! ## Symmetric formal power series and their tensor square -/

/-- The degree-`k` symmetric homogeneous coefficient. -/
def symmetricExponentialDegree (A k : ℕ) : ClosedCoefficient :=
  .symmetricPower A k

/-- Formal power series on the concrete symmetric-power invariants. -/
noncomputable def symmetricFormalPowerSeries (A : ℕ) : Module :=
  countableProduct (fun k => symmetricPower A k)

/-- Restrict a map out of symmetric formal series to one homogeneous
coefficient. -/
noncomputable def symmetricHomogeneousComponent {A B : ℕ}
    (f : Hom (symmetricFormalPowerSeries A) (representable B))
    (k : ℕ) :
    Hom (symmetricPower A k) (representable B) :=
  Hom.comp f
    (countableProductInjection (fun j => symmetricPower A j) k)

/-- Extend a homogeneous component of a map out of symmetric series to the
entire ambient representable tensor power. -/
noncomputable def symmetricHomogeneousComponentExtension {A B : ℕ}
    (f : Hom (symmetricFormalPowerSeries A) (representable B))
    (k : ℕ) :
    Hom (representable (tensorPowerDimension A k)) (representable B) :=
  extendFromSymmetricPower (symmetricHomogeneousComponent f k)

@[simp]
theorem symmetricHomogeneousComponentExtension_restrict {A B : ℕ}
    (f : Hom (symmetricFormalPowerSeries A) (representable B))
    (k : ℕ) :
    Hom.comp (symmetricHomogeneousComponentExtension f k)
        (symmetricPowerInclusion A k) =
      symmetricHomogeneousComponent f k :=
  extendFromSymmetricPower_inclusion _

/-- The symmetric formal-series object belongs to the extended
closed-generated fragment. -/
noncomputable def closedSymmetricFormalPowerSeries
    (A : ℕ) : ClosedGenerated where
  module := symmetricFormalPowerSeries A
  basis :=
    { Index := ℕ
      countableIndex := inferInstance
      coeff := symmetricExponentialDegree A
      ket := fun k =>
        countableProductInjection (fun j => symmetricPower A j) k
      bra := fun k =>
        countableProductProjection (fun j => symmetricPower A j) k
      resolves := by
        intro n x k
        change ((symmetricPower A k).obj n).HasSum
          (fun i => if h : k = i then h ▸ x i else 0) (x k)
        have hs := Fiber.hasSum_singleCoordinate
          ((symmetricPower A k).obj n) k (x k)
        convert hs using 1
        funext i
        by_cases h : k = i
        · subst i
          simp
        · simp [h, Ne.symm h] }

/-- Promotion of a finite basis equivalence to all symmetric homogeneous
degrees. -/
noncomputable def symmetricEquivalencePromotion {A B : ℕ}
    (e : Fin A ≃ Fin B) :
    Hom (symmetricFormalPowerSeries A)
      (symmetricFormalPowerSeries B) :=
  countableProductMap (fun k => symmetricPowerEquivalenceMap e k)

@[simp]
theorem symmetricEquivalencePromotion_refl (A : ℕ) :
    symmetricEquivalencePromotion (Equiv.refl (Fin A)) =
      Hom.id (symmetricFormalPowerSeries A) := by
  have h :
      (fun k => symmetricPowerEquivalenceMap
        (Equiv.refl (Fin A)) k) =
        (fun k => Hom.id (symmetricPower A k)) := by
    funext k
    exact symmetricPowerEquivalenceMap_refl A k
  rw [symmetricEquivalencePromotion, h]
  exact countableProductMap_id (fun k => symmetricPower A k)

@[simp]
theorem symmetricEquivalencePromotion_trans {A B C : ℕ}
    (e : Fin A ≃ Fin B) (f : Fin B ≃ Fin C) :
    symmetricEquivalencePromotion (e.trans f) =
      Hom.comp (symmetricEquivalencePromotion f)
        (symmetricEquivalencePromotion e) := by
  have h :
      (fun k => symmetricPowerEquivalenceMap (e.trans f) k) =
        (fun k => Hom.comp (symmetricPowerEquivalenceMap f k)
          (symmetricPowerEquivalenceMap e k)) := by
    funext k
    exact symmetricPowerEquivalenceMap_trans e f k
  rw [symmetricEquivalencePromotion, symmetricEquivalencePromotion,
    symmetricEquivalencePromotion, h]
  exact countableProductMap_comp
    (fun k => symmetricPowerEquivalenceMap f k)
    (fun k => symmetricPowerEquivalenceMap e k)

/-- The degree-one basis equivalence observed by dereliction. -/
noncomputable def symmetricPromotionLinearPart {A B : ℕ}
    (e : Fin A ≃ Fin B) : Fin A ≃ Fin B :=
  (finCongr (tensorPowerDimension_one A)).symm |>.trans
    ((tensorTupleMapEquiv e 1).trans
      (finCongr (tensorPowerDimension_one B)))

/-- Coefficientwise Day tensor of two countable products of representables. -/
noncomputable def countableRepresentableDayTensor
    (F G : ℕ → ℕ) : Module :=
  countableProduct (fun p =>
    countableProduct (fun q => dayTensorRepresentable (F p) (G q)))

/-- The coefficientwise Day tensor of two countable representable products
is again closed-generated, with the product basis indexed by `ℕ × ℕ`. -/
noncomputable def closedCountableRepresentableDayTensor
    (F G : ℕ → ℕ) : ClosedGenerated where
  module := countableRepresentableDayTensor F G
  basis :=
    { Index := ℕ × ℕ
      countableIndex := inferInstance
      coeff := fun i => .representable (F i.1 * G i.2)
      ket := fun i =>
        Hom.comp
          (countableProductInjection
            (fun p => countableProduct
              (fun q => dayTensorRepresentable (F p) (G q))) i.1)
          (countableProductInjection
            (fun q => dayTensorRepresentable (F i.1) (G q)) i.2)
      bra := fun i =>
        Hom.comp
          (countableProductProjection
            (fun q => dayTensorRepresentable (F i.1) (G q)) i.2)
          (countableProductProjection
            (fun p => countableProduct
              (fun q => dayTensorRepresentable (F p) (G q))) i.1)
      resolves := by
        intro n x p q
        have hs := Fiber.hasSum_singleAt
          ((representable (F p * G q)).obj n) (p, q) (x p q)
        convert hs using 1
        · funext i
          rcases i with ⟨i, j⟩
          by_cases hp : p = i
          · subst i
            by_cases hq : q = j
            · subst j
              simp [Hom.comp, countableProductInjection,
                countableProductProjection,
                countableRepresentableDayTensor]
              rfl
            · simp [Hom.comp, countableProductInjection,
                countableProductProjection,
                countableRepresentableDayTensor, hq, Ne.symm hq]
              rfl
          · simp [Hom.comp, countableProductInjection,
              countableProductProjection, countableRepresentableDayTensor,
              hp, Ne.symm hp]
            rfl
        · rfl }

/-- Inclusion of one homogeneous pair into the coefficientwise Day tensor. -/
noncomputable def countableRepresentableDayTensorInjection
    (F G : ℕ → ℕ) (p q : ℕ) :
    Hom (dayTensorRepresentable (F p) (G q))
      (countableRepresentableDayTensor F G) :=
  Hom.comp
    (countableProductInjection
      (fun i => countableProduct
        (fun j => dayTensorRepresentable (F i) (G j))) p)
    (countableProductInjection
      (fun j => dayTensorRepresentable (F p) (G j)) q)

/-- Every coefficientwise tensor element is the sum of its pair
coordinates. -/
theorem countableRepresentableDayTensor_hasSum_coordinates
    (F G : ℕ → ℕ) (n : ℕ)
    (x : (countableRepresentableDayTensor F G).obj n |>.Carrier) :
    (countableRepresentableDayTensor F G).obj n |>.HasSum
      (fun i : ℕ × ℕ =>
        (countableRepresentableDayTensorInjection F G i.1 i.2).app
          n (x i.1 i.2))
      x := by
  intro p q
  have hs := Fiber.hasSum_singleAt
    ((representable (F p * G q)).obj n) (p, q) (x p q)
  convert hs using 1
  funext i
  rcases i with ⟨i, j⟩
  by_cases hp : p = i
  · subst i
    by_cases hq : q = j
    · subst j
      simp [countableRepresentableDayTensorInjection, Hom.comp,
        countableProductInjection]
      rfl
    · simp [countableRepresentableDayTensorInjection, Hom.comp,
        countableProductInjection, hq, Ne.symm hq]
      rfl
  · simp [countableRepresentableDayTensorInjection, Hom.comp,
      countableProductInjection, hp, Ne.symm hp]
    rfl

/-- Maps out of the coefficientwise tensor are uniquely determined by all
homogeneous pair inclusions. -/
theorem countableRepresentableDayTensorHom_ext
    {F G : ℕ → ℕ} {L : Module.{u}}
    {f g : Hom (countableRepresentableDayTensor F G) L}
    (h : ∀ p q,
      Hom.comp f (countableRepresentableDayTensorInjection F G p q) =
        Hom.comp g
          (countableRepresentableDayTensorInjection F G p q)) :
    f = g := by
  apply Hom.ext
  intro n x
  have hf := f.map_sum
    (countableRepresentableDayTensor_hasSum_coordinates F G n x)
  have hg := g.map_sum
    (countableRepresentableDayTensor_hasSum_coordinates F G n x)
  apply (L.obj n).summation.unique hf
  convert hg using 1
  funext i
  exact congrArg (fun η => η.app n (x i.1 i.2)) (h i.1 i.2)

/-- Homogeneous maps-out coefficients. -/
def CountableDayTensorComponents
    (F G : ℕ → ℕ) (L : Module.{u}) :=
  ∀ p q, Hom (dayTensorRepresentable (F p) (G q)) L

/-- Restrict a map out of the coefficientwise tensor to every homogeneous
pair. -/
noncomputable def countableDayTensorComponents
    {F G : ℕ → ℕ} {L : Module.{u}}
    (f : Hom (countableRepresentableDayTensor F G) L) :
    CountableDayTensorComponents F G L :=
  fun p q =>
    Hom.comp f (countableRepresentableDayTensorInjection F G p q)

/-- Exact global admissibility condition required of a family of homogeneous
maps before it can define a map out of the countable tensor. -/
def CountableDayTensorComponentsAdmissible
    {F G : ℕ → ℕ} {L : Module.{u}}
    (c : CountableDayTensorComponents F G L) : Prop :=
  ∀ n (x : (countableRepresentableDayTensor F G).obj n |>.Carrier),
    ∃ s : (L.obj n).Carrier,
      (L.obj n).HasSum
        (fun i : ℕ × ℕ => (c i.1 i.2).app n (x i.1 i.2)) s

/-- Components of every existing map out satisfy global admissibility. -/
theorem countableDayTensorComponents_admissible
    {F G : ℕ → ℕ} {L : Module.{u}}
    (f : Hom (countableRepresentableDayTensor F G) L) :
    CountableDayTensorComponentsAdmissible
      (countableDayTensorComponents f) := by
  intro n x
  refine ⟨f.app n x, ?_⟩
  convert f.map_sum
    (countableRepresentableDayTensor_hasSum_coordinates F G n x) using 1
  funext i
  rfl

/-- The unique sum selected by an admissible component family. -/
noncomputable def countableDayTensorComponentSum
    {F G : ℕ → ℕ} {L : Module.{u}}
    (c : CountableDayTensorComponents F G L)
    (hc : CountableDayTensorComponentsAdmissible c)
    (n : ℕ)
    (x : (countableRepresentableDayTensor F G).obj n |>.Carrier) :
    (L.obj n).Carrier :=
  Classical.choose (hc n x)

theorem countableDayTensorComponentSum_spec
    {F G : ℕ → ℕ} {L : Module.{u}}
    (c : CountableDayTensorComponents F G L)
    (hc : CountableDayTensorComponentsAdmissible c)
    (n : ℕ)
    (x : (countableRepresentableDayTensor F G).obj n |>.Carrier) :
    (L.obj n).HasSum
      (fun i : ℕ × ℕ => (c i.1 i.2).app n (x i.1 i.2))
      (countableDayTensorComponentSum c hc n x) :=
  Classical.choose_spec (hc n x)

/-- Exchange the two indices of a nondependent sigma type. -/
def sigmaSwapEquiv (α β : Type) : (Σ _ : α, β) ≃ (Σ _ : β, α) where
  toFun p := ⟨p.2, p.1⟩
  invFun p := ⟨p.2, p.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- An admissible homogeneous component family defines a genuine map out of
the countable coefficientwise Day tensor. -/
noncomputable def countableDayTensorHomOfComponents
    {F G : ℕ → ℕ} {L : Module.{u}}
    (c : CountableDayTensorComponents F G L)
    (hc : CountableDayTensorComponentsAdmissible c) :
    Hom (countableRepresentableDayTensor F G) L where
  app := countableDayTensorComponentSum c hc
  map_zero := by
    intro n
    apply (L.obj n).summation.unique
      (countableDayTensorComponentSum_spec c hc n 0)
    have hz := Fiber.hasSum_zero (L.obj n) (ι := ℕ × ℕ)
    convert hz using 1
    funext i
    exact (c i.1 i.2).map_zero n
  map_sum := by
    intro ι _ n f s h
    let a : (i : ι) → (ℕ × ℕ) → (L.obj n).Carrier :=
      fun i pq => (c pq.1 pq.2).app n (f i pq.1 pq.2)
    have hcols (pq : ℕ × ℕ) :
        (L.obj n).HasSum (fun i => a i pq)
          ((c pq.1 pq.2).app n (s pq.1 pq.2)) :=
      (c pq.1 pq.2).map_sum (h pq.1 pq.2)
    have htotal :
        (L.obj n).HasSum
          (fun pq : ℕ × ℕ =>
            (c pq.1 pq.2).app n (s pq.1 pq.2))
          (countableDayTensorComponentSum c hc n s) :=
      countableDayTensorComponentSum_spec c hc n s
    have hflat :
        (L.obj n).HasSum
          (fun p : Σ _ : ℕ × ℕ, ι => a p.2 p.1)
          (countableDayTensorComponentSum c hc n s) :=
      ((L.obj n).summation.flatten
        (fun pq i => a i pq)
        (countableDayTensorComponentSum c hc n s)).mpr
          ⟨fun pq => (c pq.1 pq.2).app n (s pq.1 pq.2),
            hcols, htotal⟩
    have hflat' :
        (L.obj n).HasSum
          (fun p : Σ _ : ι, ℕ × ℕ => a p.1 p.2)
          (countableDayTensorComponentSum c hc n s) := by
      exact ((L.obj n).summation.reindex
        (sigmaSwapEquiv ι (ℕ × ℕ))
        (fun p : Σ _ : ℕ × ℕ, ι => a p.2 p.1)
        (countableDayTensorComponentSum c hc n s)).mpr hflat
    rcases ((L.obj n).summation.flatten
        (fun i pq => a i pq)
        (countableDayTensorComponentSum c hc n s)).mp hflat' with
      ⟨g, hrows, hgsum⟩
    apply (L.obj n).hasSum_congr (x :=
      countableDayTensorComponentSum c hc n s) ?_ |>.mpr hgsum
    intro i
    exact (L.obj n).summation.unique
      (countableDayTensorComponentSum_spec c hc n (f i))
      (hrows i)
  naturality := by
    intro m n x f
    have hleft :
        (L.obj m).HasSum
          (fun i : ℕ × ℕ =>
            (c i.1 i.2).app m
              (((countableRepresentableDayTensor F G).act x f)
                i.1 i.2))
          (countableDayTensorComponentSum c hc m
            ((countableRepresentableDayTensor F G).act x f)) :=
      countableDayTensorComponentSum_spec c hc m _
    have hright :
        (L.obj m).HasSum
          (fun i : ℕ × ℕ =>
            (c i.1 i.2).app m
              (((countableRepresentableDayTensor F G).act x f)
                i.1 i.2))
          (L.act (countableDayTensorComponentSum c hc n x) f) := by
      have hs := L.act_sum_element f
        (countableDayTensorComponentSum_spec c hc n x)
      convert hs using 1
      funext i
      exact (c i.1 i.2).naturality (x i.1 i.2) f
    exact (L.obj m).summation.unique hleft hright

/-- Restriction to homogeneous components is injective. -/
theorem countableDayTensorComponents_injective
    {F G : ℕ → ℕ} {L : Module.{u}} :
    Function.Injective
      (countableDayTensorComponents :
        Hom (countableRepresentableDayTensor F G) L →
          CountableDayTensorComponents F G L) := by
  intro f g h
  apply countableRepresentableDayTensorHom_ext
  intro p q
  exact congrFun (congrFun h p) q

@[simp]
theorem countableDayTensorHomOfComponents_components
    {F G : ℕ → ℕ} {L : Module.{u}}
    (f : Hom (countableRepresentableDayTensor F G) L) :
    countableDayTensorHomOfComponents
        (countableDayTensorComponents f)
        (countableDayTensorComponents_admissible f) =
      f := by
  apply Hom.ext
  intro n x
  apply (L.obj n).summation.unique
    (countableDayTensorComponentSum_spec
      (countableDayTensorComponents f)
      (countableDayTensorComponents_admissible f) n x)
  convert f.map_sum
    (countableRepresentableDayTensor_hasSum_coordinates F G n x) using 1
  funext i
  rfl

/-- The canonical bilinear map into the coefficientwise Day tensor. -/
noncomputable def countableRepresentableDayTensorIntro
    (F G : ℕ → ℕ) :
    Bilinear
      (countableProduct (fun p => representable (F p)))
      (countableProduct (fun q => representable (G q)))
      (countableRepresentableDayTensor F G) where
  app := fun x y p q => Superoperator.tensor (x p) (y q)
  map_zero_left := by
    intro m n y
    funext p q
    exact Superoperator.tensor_zero_left (y q)
  map_zero_right := by
    intro m n x
    funext p q
    exact Superoperator.tensor_zero_right (x p)
  map_sum_left := by
    intro ι _ m n x s y h p q
    exact SigmaMon.ChoiSum.tensor_hasSum_left (h p) (y q)
  map_sum_right := by
    intro ι _ m n x y s h p q
    exact SigmaMon.ChoiSum.tensor_hasSum_right (x p) (h q)
  naturality := by
    intro m' m n' n x y f g
    funext p q
    exact Superoperator.tensor_comp (x p) f (y q) g

/-- The coefficientwise Day tensor square of symmetric formal series.  Its
`(p,q)` coefficient is the already-proved Day tensor of the two ambient
representable tensor powers. -/
noncomputable def symmetricFormalTensorSquare (A : ℕ) : Module :=
  countableRepresentableDayTensor
    (tensorPowerDimension A) (tensorPowerDimension A)

/-- The tensor square used by contraction is itself in the generated
fragment. -/
noncomputable def closedSymmetricFormalTensorSquare
    (A : ℕ) : ClosedGenerated :=
  closedCountableRepresentableDayTensor
    (tensorPowerDimension A) (tensorPowerDimension A)

@[simp]
theorem closedSymmetricFormalTensorSquare_module (A : ℕ) :
    (closedSymmetricFormalTensorSquare A).module =
      symmetricFormalTensorSquare A :=
  rfl

/-- Promotion on the coefficientwise tensor square. -/
noncomputable def symmetricTensorSquareEquivalenceMap {A B : ℕ}
    (e : Fin A ≃ Fin B) :
    Hom (symmetricFormalTensorSquare A)
      (symmetricFormalTensorSquare B) where
  app := fun _ x p q =>
    Superoperator.comp
      (Superoperator.ofEquivalence (homogeneousPairMapEquiv e p q))
      (x p q)
  map_zero := by
    intro n
    funext p q
    exact Superoperator.comp_zero_right _
  map_sum := by
    intro ι _ n f x h p q
    exact SigmaMon.ChoiSum.comp_left
      (Superoperator.ofEquivalence (homogeneousPairMapEquiv e p q))
      (h p q)
  naturality := by
    intro m n x f
    funext p q
    exact Superoperator.comp_assoc _ _ _

/-- Contraction splits every symmetric homogeneous coefficient into all
ordered pairs of degrees. -/
noncomputable def symmetricContraction (A : ℕ) :
    Hom (symmetricFormalPowerSeries A)
      (symmetricFormalTensorSquare A) where
  app := fun _ x p q =>
    Superoperator.comp
      (Superoperator.ofEquivalence (tensorSplitEquiv A p q))
      (x (p + q)).val
  map_zero := by
    intro n
    funext p q
    exact Superoperator.comp_zero_right _
  map_sum := by
    intro ι _ n f x h p q
    exact SigmaMon.ChoiSum.comp_left
      (Superoperator.ofEquivalence (tensorSplitEquiv A p q))
      (h (p + q))
  naturality := by
    intro m n x f
    funext p q
    exact Superoperator.comp_assoc _ _ _

/-- Braiding of the coefficientwise tensor square, implemented by the
genuine block permutation of tensor factors. -/
noncomputable def symmetricTensorBraiding (A : ℕ) :
    Hom (symmetricFormalTensorSquare A)
      (symmetricFormalTensorSquare A) where
  app := fun _ x p q =>
    Superoperator.comp
      (Superoperator.ofEquivalence (homogeneousBraidingEquiv A q p))
      (x q p)
  map_zero := by
    intro n
    funext p q
    exact Superoperator.comp_zero_right _
  map_sum := by
    intro ι _ n f x h p q
    exact SigmaMon.ChoiSum.comp_left
      (Superoperator.ofEquivalence (homogeneousBraidingEquiv A q p))
      (h q p)
  naturality := by
    intro m n x f
    funext p q
    exact Superoperator.comp_assoc _ _ _

/-- Contraction is cocommutative with respect to the homogeneous
tensor-factor braiding. -/
theorem symmetricContraction_cocommutative (A : ℕ) :
    Hom.comp (symmetricTensorBraiding A) (symmetricContraction A) =
      symmetricContraction A := by
  ext n x
  funext p q
  change
    Superoperator.comp
        (Superoperator.ofEquivalence (homogeneousBraidingEquiv A q p))
        (Superoperator.comp
          (Superoperator.ofEquivalence (tensorSplitEquiv A q p))
          (x (q + p)).val) =
      Superoperator.comp
        (Superoperator.ofEquivalence (tensorSplitEquiv A p q))
        (x (p + q)).val
  calc
    _ = Superoperator.comp
          (Superoperator.ofEquivalence
            (oppositeTensorSplitEquiv A q p))
          (x (q + p)).val :=
        SymmetricElement.split_braiding (x (q + p))
    _ = _ := by
      let h : q + p = p + q := Nat.add_comm q p
      change
        Superoperator.comp
            (Superoperator.ofEquivalence
              ((finCongr
                (congrArg (tensorPowerDimension A) h)).trans
                  (tensorSplitEquiv A p q)))
            (x (q + p)).val =
          _
      rw [← Superoperator.ofEquivalence_comp,
        ← Superoperator.comp_assoc]
      apply congrArg (fun z =>
        Superoperator.comp
          (Superoperator.ofEquivalence (tensorSplitEquiv A p q)) z)
      calc
        Superoperator.comp
            (Superoperator.ofEquivalence
              (finCongr (congrArg (tensorPowerDimension A) h)))
            (x (q + p)).val =
            (h ▸ x (q + p)).val :=
          SymmetricElement.val_degreeCast h (x (q + p))
        _ = (x (p + q)).val :=
          congrArg SymmetricElement.val
            (SymmetricElement.family_degreeCast x h)

/-- Promotion induced by a basis equivalence preserves contraction. -/
theorem symmetricContraction_promotion {A B : ℕ}
    (e : Fin A ≃ Fin B) :
    Hom.comp (symmetricContraction B)
        (symmetricEquivalencePromotion e) =
      Hom.comp (symmetricTensorSquareEquivalenceMap e)
        (symmetricContraction A) := by
  ext n x
  funext p q
  change
    Superoperator.comp
        (Superoperator.ofEquivalence (tensorSplitEquiv B p q))
        (Superoperator.comp
          (Superoperator.ofEquivalence
            (tensorTupleMapEquiv e (p + q)))
          (x (p + q)).val) =
      Superoperator.comp
        (Superoperator.ofEquivalence (homogeneousPairMapEquiv e p q))
        (Superoperator.comp
          (Superoperator.ofEquivalence (tensorSplitEquiv A p q))
          (x (p + q)).val)
  rw [Superoperator.comp_assoc, Superoperator.ofEquivalence_comp]
  rw [Superoperator.comp_assoc, Superoperator.ofEquivalence_comp]
  congr 2
  exact (tensorSplitEquiv_natural e p q).symm

/-- Weakening extracts the invariant degree-zero coefficient. -/
noncomputable def symmetricWeakening (A : ℕ) :
    Hom (symmetricFormalPowerSeries A) (representable 1) where
  app := fun _ x => (x 0).val
  map_zero := fun _ => rfl
  map_sum := fun h => h 0
  naturality := fun _ _ => rfl

/-- Promotion induced by a basis equivalence preserves weakening. -/
theorem symmetricWeakening_promotion {A B : ℕ}
    (e : Fin A ≃ Fin B) :
    Hom.comp (symmetricWeakening B)
        (symmetricEquivalencePromotion e) =
      symmetricWeakening A := by
  ext n x
  change
    Superoperator.comp
        (Superoperator.ofEquivalence (tensorTupleMapEquiv e 0))
        (x 0).val =
      (x 0).val
  have he :
      tensorTupleMapEquiv e 0 = Equiv.refl (Fin 1) := by
    apply Equiv.ext
    intro i
    exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
  rw [he]
  change
    Superoperator.comp
        (Superoperator.ofEquivalence (Equiv.refl (Fin 1)))
        (x 0).val =
      (x 0).val
  rw [Superoperator.ofEquivalence_refl]
  exact Superoperator.identity_comp (x 0).val

/-- Dereliction extracts the invariant degree-one coefficient. -/
noncomputable def symmetricDereliction (A : ℕ) :
    Hom (symmetricFormalPowerSeries A) (representable A) where
  app := fun _ x =>
    Superoperator.comp
      (Superoperator.ofEquivalence
        (finCongr (tensorPowerDimension_one A))) (x 1).val
  map_zero := fun _ => Superoperator.comp_zero_right _
  map_sum := fun h =>
    SigmaMon.ChoiSum.comp_left
      (Superoperator.ofEquivalence
        (finCongr (tensorPowerDimension_one A))) (h 1)
  naturality := fun _ _ => Superoperator.comp_assoc _ _ _

/-- Dereliction after promotion is exactly the induced linear basis map. -/
theorem symmetricDereliction_promotion {A B : ℕ}
    (e : Fin A ≃ Fin B) :
    Hom.comp (symmetricDereliction B)
        (symmetricEquivalencePromotion e) =
      Hom.comp
        (yonedaMap
          (Superoperator.ofEquivalence (symmetricPromotionLinearPart e)))
        (symmetricDereliction A) := by
  ext n x
  change
    Superoperator.comp
        (Superoperator.ofEquivalence
          (finCongr (tensorPowerDimension_one B)))
        (Superoperator.comp
          (Superoperator.ofEquivalence (tensorTupleMapEquiv e 1))
          (x 1).val) =
      Superoperator.comp
        (Superoperator.ofEquivalence (symmetricPromotionLinearPart e))
        (Superoperator.comp
          (Superoperator.ofEquivalence
            (finCongr (tensorPowerDimension_one A)))
          (x 1).val)
  rw [Superoperator.comp_assoc, Superoperator.ofEquivalence_comp]
  rw [Superoperator.comp_assoc, Superoperator.ofEquivalence_comp]
  congr 2

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
