/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Generated

/-!
# Representable Day tensor and internal hom

This file constructs the Day tensor universal property when both inputs are
representable.  It also constructs the corresponding right adjoint
`[y(A), N]` for an arbitrary specialized module `N`.  This is the largest
closed fragment obtainable without constructing the general coend quotient.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u v w

/-- A bilinear, action-preserving map of specialized modules. -/
structure Bilinear (M : Module.{u}) (N : Module.{v}) (L : Module.{w}) where
  app :
    {m n : ℕ} →
      (M.obj m).Carrier → (N.obj n).Carrier → (L.obj (m * n)).Carrier
  map_zero_left :
    ∀ {m n} (y : (N.obj n).Carrier), app (0 : (M.obj m).Carrier) y = 0
  map_zero_right :
    ∀ {m n} (x : (M.obj m).Carrier), app x (0 : (N.obj n).Carrier) = 0
  map_sum_left :
    ∀ {ι : Type} [Countable ι] {m n}
      {x : ι → (M.obj m).Carrier} {s : (M.obj m).Carrier}
      (y : (N.obj n).Carrier),
      (M.obj m).HasSum x s →
        (L.obj (m * n)).HasSum (fun i => app (x i) y) (app s y)
  map_sum_right :
    ∀ {ι : Type} [Countable ι] {m n}
      (x : (M.obj m).Carrier)
      {y : ι → (N.obj n).Carrier} {s : (N.obj n).Carrier},
      (N.obj n).HasSum y s →
        (L.obj (m * n)).HasSum (fun i => app x (y i)) (app x s)
  naturality :
    ∀ {m' m n' n}
      (x : (M.obj m).Carrier) (y : (N.obj n).Carrier)
      (f : Superoperator m' m) (g : Superoperator n' n),
      app (M.act x f) (N.act y g) =
        L.act (app x y) (Superoperator.tensor f g)

namespace Bilinear

@[ext]
theorem ext {M : Module.{u}} {N : Module.{v}} {L : Module.{w}}
    {b c : Bilinear M N L}
    (h : ∀ m n x y, @b.app m n x y = @c.app m n x y) :
    b = c := by
  cases b
  cases c
  congr
  funext m n x y
  exact h m n x y

end Bilinear

/-- Postcomposition of a bilinear map by a module morphism. -/
def Bilinear.postcomp {M : Module.{u}} {N : Module.{v}}
    {L : Module.{w}} {K : Module.{u}}
    (f : Hom L K) (b : Bilinear M N L) : Bilinear M N K where
  app := fun x y => f.app _ (b.app x y)
  map_zero_left := by
    intro m n y
    rw [b.map_zero_left, f.map_zero]
  map_zero_right := by
    intro m n x
    rw [b.map_zero_right, f.map_zero]
  map_sum_left := by
    intro ι _ m n xs s y h
    exact f.map_sum (b.map_sum_left y h)
  map_sum_right := by
    intro ι _ m n x ys s h
    exact f.map_sum (b.map_sum_right x h)
  naturality := by
    intro m' m n' n x y g h
    rw [b.naturality, f.naturality]

/-- Universal-property package for one genuine Day tensor.  Constructing this
for all modules is the categorical gate not supplied by the representable
fragment below. -/
structure DayTensorPresentation (M : Module.{u}) (N : Module.{v}) where
  object : Module.{w}
  intro : Bilinear M N object
  universal : ∀ L : Module.{u}, Hom object L ≃ Bilinear M N L
  universal_apply :
    ∀ (L : Module.{u}) (f : Hom object L),
      universal L f = Bilinear.postcomp f intro

/-- Tensoring representables is represented by multiplication of their finite
dimensions. -/
noncomputable abbrev dayTensorRepresentable (A B : ℕ) : Module :=
  representable (A * B)

/-- The universal bilinear map into the representable Day tensor. -/
noncomputable def dayTensorIntro (A B : ℕ) :
    Bilinear (representable A) (representable B)
      (dayTensorRepresentable A B) where
  app := fun x y => Superoperator.tensor x y
  map_zero_left := Superoperator.tensor_zero_left
  map_zero_right := Superoperator.tensor_zero_right
  map_sum_left := by
    intro ι _ m n x s y h
    exact SigmaMon.ChoiSum.tensor_hasSum_left h y
  map_sum_right := by
    intro ι _ m n x y s h
    exact SigmaMon.ChoiSum.tensor_hasSum_right x h
  naturality := by
    intro m' m n' n x y f g
    exact Superoperator.tensor_comp x f y g

/-- A map out of the representable Day tensor gives a bilinear map. -/
noncomputable def dayTensorToBilinear {A B : ℕ} {L : Module.{u}}
    (η : Hom (dayTensorRepresentable A B) L) :
    Bilinear (representable A) (representable B) L where
  app := fun x y => η.app _ (Superoperator.tensor x y)
  map_zero_left := by
    intro m n y
    change Superoperator n B at y
    change η.app (m * n)
      (Superoperator.tensor (0 : Superoperator m A) y) = 0
    rw [Superoperator.tensor_zero_left]
    exact η.map_zero (m * n)
  map_zero_right := by
    intro m n x
    change Superoperator m A at x
    change η.app (m * n)
      (Superoperator.tensor x (0 : Superoperator n B)) = 0
    rw [Superoperator.tensor_zero_right]
    exact η.map_zero (m * n)
  map_sum_left := by
    intro ι _ m n x s y h
    exact η.map_sum (SigmaMon.ChoiSum.tensor_hasSum_left h y)
  map_sum_right := by
    intro ι _ m n x y s h
    exact η.map_sum (SigmaMon.ChoiSum.tensor_hasSum_right x h)
  naturality := by
    intro m' m n' n x y f g
    change Superoperator m A at x
    change Superoperator n B at y
    change
      η.app (m' * n')
          (Superoperator.tensor (Superoperator.comp x f)
            (Superoperator.comp y g)) =
        L.act (η.app (m * n) (Superoperator.tensor x y))
          (Superoperator.tensor f g)
    rw [Superoperator.tensor_comp]
    exact η.naturality (Superoperator.tensor x y)
      (Superoperator.tensor f g)

/-- A bilinear map out of two representables is determined by its value on
the two identities. -/
noncomputable def bilinearToDayTensor {A B : ℕ} {L : Module.{u}}
    (b : Bilinear (representable A) (representable B) L) :
    Hom (dayTensorRepresentable A B) L :=
  fromElement L (b.app (Superoperator.identity A)
    (Superoperator.identity B))

@[simp]
theorem bilinearToDayTensor_toBilinear {A B : ℕ} {L : Module.{u}}
    (η : Hom (dayTensorRepresentable A B) L) :
    bilinearToDayTensor (dayTensorToBilinear η) = η := by
  change
    fromElement L
        (η.app (A * B)
          (Superoperator.tensor (Superoperator.identity A)
            (Superoperator.identity B))) =
      η
  rw [Superoperator.tensor_identity]
  exact fromElement_toElement L η

@[simp]
theorem dayTensorToBilinear_bilinearToDayTensor
    {A B : ℕ} {L : Module.{u}}
    (b : Bilinear (representable A) (representable B) L) :
    dayTensorToBilinear (bilinearToDayTensor b) = b := by
  ext m n x y
  change Superoperator m A at x
  change Superoperator n B at y
  change
    L.act
        (b.app (Superoperator.identity A) (Superoperator.identity B))
        (Superoperator.tensor x y) =
      b.app x y
  symm
  have h :=
    b.naturality (Superoperator.identity A)
      (Superoperator.identity B) x y
  change
    b.app
        (Superoperator.comp (Superoperator.identity A) x)
        (Superoperator.comp (Superoperator.identity B) y) =
      L.act
        (b.app (Superoperator.identity A) (Superoperator.identity B))
        (Superoperator.tensor x y) at h
  rw [Superoperator.identity_comp, Superoperator.identity_comp] at h
  exact h

/-- The specialized Day universal property for representables. -/
noncomputable def dayTensorRepresentableEquiv
    (A B : ℕ) (L : Module.{u}) :
    Hom (dayTensorRepresentable A B) L ≃
      Bilinear (representable A) (representable B) L where
  toFun := dayTensorToBilinear
  invFun := bilinearToDayTensor
  left_inv := bilinearToDayTensor_toBilinear
  right_inv := dayTensorToBilinear_bilinearToDayTensor

/-- The representable construction packaged as an actual Day tensor. -/
noncomputable def dayTensorRepresentablePresentation (A B : ℕ) :
    DayTensorPresentation (representable A) (representable B) where
  object := dayTensorRepresentable A B
  intro := dayTensorIntro A B
  universal := fun L => dayTensorRepresentableEquiv A B L
  universal_apply := by
    intro L f
    ext m n x y
    rfl

/-- Concrete right adjoint to tensoring by a representable:
`[y(A), N](n) = N(n*A)`. -/
noncomputable def internalHomRepresentable (A : ℕ) (N : Module.{u}) :
    Module.{u} where
  obj n := N.obj (n * A)
  act := fun x f =>
    N.act x (Superoperator.tensor f (Superoperator.identity A))
  act_zero_element := by
    intro m n f
    exact N.act_zero_element _
  act_zero_map := by
    intro m n x
    rw [Superoperator.tensor_zero_left]
    exact N.act_zero_map x
  act_id := by
    intro n x
    rw [Superoperator.tensor_identity]
    exact N.act_id x
  act_comp := by
    intro ℓ m n x f g
    rw [N.act_comp, ← Superoperator.tensor_comp,
      Superoperator.comp_identity]
  act_sum_element := by
    intro ι _ m n x s f h
    exact N.act_sum_element _ h
  act_sum_map := by
    intro ι _ m n x f s h
    exact N.act_sum_map x
      (SigmaMon.ChoiSum.tensor_hasSum_left h
        (Superoperator.identity A))
  act_sum_from_one := by
    intro ι _ m x s f h
    exact N.act_sum_tensor_from_one f h
  act_sum_tensor_from_one := by
    intro ι _ m B x s f h
    -- Reassociate `(f ⊗ id_B) ⊗ id_A` via the tensor associator, then apply
    -- `N.act_sum_tensor_from_one` at ancillary dimension `B * A`.
    let α₁ : Superoperator (1 * (B * A)) ((1 * B) * A) :=
      Superoperator.tensorAssociatorInv 1 B A
    let α₂ : Superoperator ((m * B) * A) (m * (B * A)) :=
      Superoperator.tensorAssociator m B A
    let x' : ι → (N.obj (1 * (B * A))).Carrier :=
      fun i => N.act (x i) α₁
    let s' : (N.obj (1 * (B * A))).Carrier := N.act s α₁
    have hs' : (N.obj (1 * (B * A))).HasSum x' s' :=
      N.act_sum_element α₁ h
    obtain ⟨z', hz'⟩ := N.act_sum_tensor_from_one (A := B * A) f hs'
    refine ⟨N.act z' α₂, ?_⟩
    have hten (g : Superoperator m 1) :
        Superoperator.tensor
            (Superoperator.tensor g (Superoperator.identity B))
            (Superoperator.identity A) =
          Superoperator.comp α₁
            (Superoperator.comp
              (Superoperator.tensor g (Superoperator.identity (B * A)))
              α₂) := by
      have hnat :=
        Superoperator.tensorAssociator_naturality g
          (Superoperator.identity B) (Superoperator.identity A)
      -- `α₂' ∘ ((g ⊗ id_B) ⊗ id_A) = (g ⊗ (id_B ⊗ id_A)) ∘ α₂`
      -- with `α₂' = tensorAssociator 1 B A`.
      have h :=
        congrArg (Superoperator.comp
          (Superoperator.tensorAssociatorInv 1 B A)) hnat
      simpa [Superoperator.comp_assoc,
        Superoperator.tensorAssociator_inv_hom,
        Superoperator.identity_comp, Superoperator.tensor_identity,
        α₁, α₂] using h
    have hfam :
        (fun i =>
          N.act (x i)
            (Superoperator.tensor
              (Superoperator.tensor (f i) (Superoperator.identity B))
              (Superoperator.identity A))) =
          fun i =>
            N.act
              (N.act (x' i)
                (Superoperator.tensor (f i)
                  (Superoperator.identity (B * A))))
              α₂ := by
      funext i
      -- `act x (α₁ ∘ (f⊗id) ∘ α₂) = act (act (act x α₁) (f⊗id)) α₂`
      rw [hten, ← N.act_comp, ← N.act_comp]
    have hzα :
        (N.obj ((m * B) * A)).HasSum
          (fun i =>
            N.act
              (N.act (x' i)
                (Superoperator.tensor (f i)
                  (Superoperator.identity (B * A))))
              α₂)
          (N.act z' α₂) :=
      N.act_sum_element α₂ hz'
    rw [hfam]
    exact hzα

/-- Closed adjunction on representable left arguments. -/
noncomputable def closedRepresentableEquiv
    (X A : ℕ) (N : Module.{u}) :
    Hom (dayTensorRepresentable X A) N ≃
      Hom (representable X) (internalHomRepresentable A N) :=
  (yonedaEquiv N (X * A)).trans
    (yonedaEquiv (internalHomRepresentable A N) X).symm

/-- Currying is evaluation of the two Yoneda correspondences. -/
noncomputable def curryRepresentable {X A : ℕ} {N : Module.{u}}
    (f : Hom (dayTensorRepresentable X A) N) :
    Hom (representable X) (internalHomRepresentable A N) :=
  closedRepresentableEquiv X A N f

/-- Uncurrying is the inverse closed correspondence. -/
noncomputable def uncurryRepresentable {X A : ℕ} {N : Module.{u}}
    (f : Hom (representable X) (internalHomRepresentable A N)) :
    Hom (dayTensorRepresentable X A) N :=
  (closedRepresentableEquiv X A N).symm f

@[simp]
theorem curry_uncurry_representable {X A : ℕ} {N : Module.{u}}
    (f : Hom (representable X) (internalHomRepresentable A N)) :
    curryRepresentable (uncurryRepresentable f) = f :=
  (closedRepresentableEquiv X A N).apply_symm_apply f

@[simp]
theorem uncurry_curry_representable {X A : ℕ} {N : Module.{u}}
    (f : Hom (dayTensorRepresentable X A) N) :
    uncurryRepresentable (curryRepresentable f) = f :=
  (closedRepresentableEquiv X A N).symm_apply_apply f

/-- Exact interface for general Day monoidal closure.

The representable results above instantiate each field on the elementary
fragment.  `DayCoend.lean` constructs the general enriched coend quotient and
provides a concrete value of this structure. -/
structure DayClosedPresentation where
  tensor :
    (M N : Module) → DayTensorPresentation M N
  internalHom :
    Module → Module → Module
  closed :
    ∀ (X A N : Module),
      Hom (tensor X A).object N ≃ Hom X (internalHom A N)

end SuperoperatorModule

end QLambda.Domain.Presheaf
