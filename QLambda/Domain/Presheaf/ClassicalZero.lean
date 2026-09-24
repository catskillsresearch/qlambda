/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.ClassicalRepresentableOne

/-!
# Zero module and `y(0)` classical objects
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u

/-- The zero partial-sum fiber.  Every countable family has its unique value
because the carrier is a singleton. -/
noncomputable def zeroFiber : Fiber where
  Carrier := PUnit
  zero := PUnit.unit
  summation :=
    { HasSum := fun _ _ => True
      unique := fun _ _ => Subsingleton.elim _ _
      empty := trivial
      singleton := fun _ => trivial
      remove_zero := fun _ _ _ _ => iff_true_intro trivial
      reindex := fun _ _ _ => iff_true_intro trivial
      flatten := by
        intro ι _ κ _ f a
        constructor
        · intro _
          exact ⟨fun _ => PUnit.unit, fun _ => trivial, trivial⟩
        · intro _
          trivial }

theorem zeroFiber_subsingleton : Subsingleton zeroFiber.Carrier := by
  change Subsingleton PUnit
  infer_instance

/-- There is only one CP map into the zero-dimensional output. -/
theorem cpMap_to_zero_subsingleton (n : ℕ) :
    Subsingleton (CPMap n 0) where
  allEq _Φ _Ψ := by
    apply CPMap.ext
    ext i
    exact Fin.elim0 i.1

/-- Consequently every superoperator into dimension zero is the zero map. -/
theorem superoperator_to_zero_subsingleton (n : ℕ) :
    Subsingleton (Superoperator n 0) where
  allEq _Φ _Ψ :=
    Superoperator.ext ((cpMap_to_zero_subsingleton n).allEq _ _)

/-- Every fiber of the zero-dimensional representable is a singleton. -/
theorem representableZero_subsingleton (n : ℕ) :
    Subsingleton (((representable 0).obj n).Carrier) :=
  superoperator_to_zero_subsingleton n

/-- Zero specialized module. -/
noncomputable def zeroModule : Module where
  obj := fun _ => zeroFiber
  act := fun _ _ => (0 : zeroFiber.Carrier)
  act_zero_element := fun _ => rfl
  act_zero_map := fun _ => rfl
  act_id := fun _ => rfl
  act_comp := fun _ _ _ => rfl
  act_sum_element := by
    intros
    trivial
  act_sum_map := by
    intros
    trivial
  act_sum_from_one := by
    intros
    exact ⟨0, trivial⟩
  act_sum_tensor_from_one := by
    intros
    exact ⟨0, trivial⟩

/-- Negation of a fiberwise subsingleton module is fiberwise subsingleton. -/
theorem neg_subsingleton (M : Module)
    (hM : ∀ n, Subsingleton (M.obj n).Carrier) (n : ℕ) :
    Subsingleton ((DayNegation.neg M).obj n).Carrier where
  allEq b c := by
    change Bilinear (representable n) M dayTensorUnit at b c
    apply Bilinear.ext
    intro p q x y
    have hy : y = 0 := (hM q).allEq _ _
    subst y
    exact (b.map_zero_right x).trans (c.map_zero_right x).symm

/-- Canonical pseudo-basis of the zero module. -/
noncomputable def zeroPseudoBasis : PseudoBasis zeroModule where
  Index := PUnit
  countableIndex := inferInstance
  coeff := fun _ => PseudoRepresentable.representable 1 Nat.zero_lt_one
  ket := fun _ => 0
  bra := fun _ => 0
  resolves := by
    intro n x
    change True
    trivial

/-- The zero module is genuinely fixed by Day double negation. -/
noncomputable def zeroDoubleDualIso :
    Iso zeroModule
      (DayNegation.data.doubleDual zeroModule) where
  hom := DayNegation.unit zeroModule
  inv := 0
  hom_inv := by
    apply Hom.ext
    intro n x
    exact
      (neg_subsingleton (DayNegation.neg zeroModule)
        (neg_subsingleton zeroModule
          (fun _ => zeroFiber_subsingleton)) n).allEq _ _
  inv_hom := by
    apply Hom.ext
    intro n x
    exact zeroFiber_subsingleton.allEq _ _

/-- A concrete inhabitant of the biorthogonal category. -/
noncomputable def zeroBiorthogonalObject :
    ClassicalObject (DayNegation.data) where
  module := zeroModule
  basis := zeroPseudoBasis
  reflexive := zeroDoubleDualIso
  canonical := rfl

/-- The canonical pseudo-basis of the zero-dimensional representable.  Its
single coefficient factors through zero; this is the positive-dimensional
coefficient required by `PseudoBasis`, not a positivity assumption on the
represented dimension. -/
noncomputable def representableZeroPseudoBasis :
    PseudoBasis (representable 0) where
  Index := PUnit
  countableIndex := inferInstance
  coeff := fun _ => PseudoRepresentable.representable 1 Nat.zero_lt_one
  ket := fun _ => 0
  bra := fun _ => 0
  resolves := by
    intro n x
    have hx : x = 0 := (representableZero_subsingleton n).allEq _ _
    subst x
    change ((representable 0).obj n).HasSum (fun _ : PUnit => 0) 0
    simpa using ((representable 0).obj n).summation.singleton
      (0 : ((representable 0).obj n).Carrier)

/-- The zero-dimensional representable is canonically Day-reflexive. -/
noncomputable def representableZeroReflexivity :
    RepresentableReflexivity 0 where
  inv := 0
  hom_inv := by
    apply Hom.ext
    intro n x
    exact
      (neg_subsingleton (DayNegation.neg (representable 0))
        (neg_subsingleton (representable 0)
          representableZero_subsingleton) n).allEq _ _
  inv_hom := by
    apply Hom.ext
    intro n x
    exact (representableZero_subsingleton n).allEq _ _

/-- Concrete classical object for `y(0)`. -/
noncomputable def representableZeroBiorthogonalObject :
    ClassicalObject (DayNegation.data) where
  module := representable 0
  basis := representableZeroPseudoBasis
  reflexive := representableZeroReflexivity.iso
  canonical := rfl


end SuperoperatorModule

end QLambda.Domain.Presheaf
