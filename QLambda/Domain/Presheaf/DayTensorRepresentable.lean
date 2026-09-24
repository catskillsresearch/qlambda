/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.DayTensorPresentation

/-!
# Representable Day tensor
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u

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

end SuperoperatorModule

end QLambda.Domain.Presheaf
