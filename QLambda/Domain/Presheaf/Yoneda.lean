/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Module

/-!
# Representable superoperator modules and Yoneda

The proofs are elementary and use the concrete Choi-sum preservation of
composition.  Thus the Yoneda correspondence below has no categorical
existence premise.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u

/-- The representable module `Q(-, A)`. -/
noncomputable def representable (A : ℕ) : Module where
  obj n :=
    { Carrier := Superoperator n A
      zero := 0
      summation := SigmaMon.superoperatorPartialCountableSum }
  act := fun x f => Superoperator.comp x f
  act_zero_element := by
    intro m n f
    exact Superoperator.comp_zero_left f
  act_zero_map := by
    intro m n x
    exact Superoperator.comp_zero_right x
  act_id := by
    intro n x
    exact Superoperator.comp_identity x
  act_comp := by
    intro ℓ m n x f g
    exact (Superoperator.comp_assoc x f g).symm
  act_sum_element := by
    intro ι _ m n x s f h
    exact SigmaMon.ChoiSum.comp_right f h
  act_sum_map := by
    intro ι _ m n x f s h
    exact SigmaMon.ChoiSum.comp_left x h

@[simp]
theorem representable_obj (A n : ℕ) :
    ((representable A).obj n).Carrier = Superoperator n A :=
  rfl

@[simp]
theorem representable_act {A m n : ℕ}
    (x : Superoperator n A) (f : Superoperator m n) :
    (representable A).act x f = Superoperator.comp x f :=
  rfl

/-- Yoneda sends a base superoperator to postcomposition by that map. -/
noncomputable def yonedaMap {A B : ℕ} (f : Superoperator A B) :
    Hom (representable A) (representable B) where
  app := fun _ x => Superoperator.comp f x
  map_zero := fun _ => Superoperator.comp_zero_right f
  map_sum := by
    intro ι _ n x s h
    exact SigmaMon.ChoiSum.comp_left f h
  naturality := by
    intro m n x g
    exact Superoperator.comp_assoc f x g

@[simp]
theorem yonedaMap_app {A B n : ℕ} (f : Superoperator A B)
    (x : Superoperator n A) :
    (yonedaMap f).app n x = Superoperator.comp f x :=
  rfl

@[simp]
theorem yonedaMap_id (A : ℕ) :
    yonedaMap (Superoperator.identity A) = Hom.id (representable A) := by
  ext n x
  exact Superoperator.identity_comp x

@[simp]
theorem yonedaMap_comp {A B C : ℕ}
    (g : Superoperator B C) (f : Superoperator A B) :
    yonedaMap (Superoperator.comp g f) =
      Hom.comp (yonedaMap g) (yonedaMap f) := by
  ext n x
  exact (Superoperator.comp_assoc g f x).symm

/-- A module element determines a natural map out of a representable. -/
def fromElement (M : Module.{u}) {A : ℕ} (x : (M.obj A).Carrier) :
    Hom (representable A) M where
  app := fun _ f => M.act x f
  map_zero := fun _ => M.act_zero_map x
  map_sum := by
    intro ι _ n f s h
    exact M.act_sum_map x h
  naturality := by
    intro m n f g
    exact (M.act_comp x f g).symm

/-- Evaluation of a natural map at the identity element. -/
def toElement (M : Module.{u}) {A : ℕ}
    (η : Hom (representable A) M) : (M.obj A).Carrier :=
  η.app A (Superoperator.identity A)

@[simp]
theorem toElement_fromElement (M : Module.{u}) {A : ℕ}
    (x : (M.obj A).Carrier) :
    toElement M (fromElement M x) = x :=
  M.act_id x

@[simp]
theorem fromElement_toElement (M : Module.{u}) {A : ℕ}
    (η : Hom (representable A) M) :
    fromElement M (toElement M η) = η := by
  ext n f
  change M.act (η.app A (Superoperator.identity A)) f = η.app n f
  rw [show M.act (η.app A (Superoperator.identity A)) f =
      η.app n
        ((representable A).act (Superoperator.identity A) f) from
        (η.naturality (Superoperator.identity A) f).symm]
  have hf :
      (representable A).act (Superoperator.identity A) f = f :=
    Superoperator.identity_comp f
  exact congrArg (η.app n) hf

/-- The concrete enriched Yoneda correspondence. -/
def yonedaEquiv (M : Module.{u}) (A : ℕ) :
    Hom (representable A) M ≃ (M.obj A).Carrier where
  toFun := toElement M
  invFun := fromElement M
  left_inv := fromElement_toElement M
  right_inv := toElement_fromElement M

@[simp]
theorem yonedaEquiv_apply (M : Module.{u}) (A : ℕ)
    (η : Hom (representable A) M) :
    yonedaEquiv M A η = η.app A (Superoperator.identity A) :=
  rfl

@[simp]
theorem yonedaEquiv_symm_apply (M : Module.{u}) (A : ℕ)
    (x : (M.obj A).Carrier) (n : ℕ) (f : Superoperator n A) :
    ((yonedaEquiv M A).symm x).app n f = M.act x f :=
  rfl

end SuperoperatorModule

end QLambda.Domain.Presheaf
