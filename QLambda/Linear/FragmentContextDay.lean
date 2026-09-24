/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentContextObjects

/-!
# Fragment context Day closed structure

Day curry/eval, first-order abstraction, argument moves, and
pair/unpair maps for fragment modules.
-/

namespace QLambda.Linear
namespace FragmentContext

set_option maxHeartbeats 8000000

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open DayTensor

/-- Curry a morphism through the concrete Day closed structure. -/
noncomputable def dayCurry {X A N : Module}
    (f : Hom (dayTensor X A) N) :
    Hom X (dayInternalHom A N) :=
  dayClosedPresentation.closed X A N f

/-- Evaluation for the concrete Day internal hom. -/
noncomputable def dayEval (A N : Module) :
    Hom (dayTensor (dayInternalHom A N) A) N :=
  (dayClosedPresentation.closed (dayInternalHom A N) A N).symm
    (Hom.id (dayInternalHom A N))

/-- Uncurrying through Day closedness is evaluation after applying the
curried map in the first Day factor. -/
theorem dayUncurry_eq_eval_comp {X A N : Module}
    (g : Hom X (dayInternalHom A N)) :
    (dayClosedPresentation.closed X A N).symm g =
      Hom.comp (dayEval A N) (DayTensor.map g (Hom.id A)) := by
  apply DayTensor.hom_ext
  intro m n x y
  -- Both sides act on coend generators by `(g.app m x).app id y`.
  change
      ((dayClosedPresentation.closed X A N).symm g).app (m * n)
          ((DayCoend.intro X A).app x y) =
        (dayEval A N).app (m * n)
          ((DayTensor.map g (Hom.id A)).app (m * n)
            ((DayCoend.intro X A).app x y))
  have hmap := DayTensor.map_intro g (Hom.id A) x y
  rw [hmap, Hom.id_app]
  -- `closed.symm g = lift (uncurry g)` and `dayEval = lift (uncurry id)`.
  change
      DayCoend.evaluate N (DayInternalHom.uncurry g)
          ((DayCoend.intro X A).app x y) =
        DayCoend.evaluate N
          (DayInternalHom.uncurry (Hom.id (dayInternalHom A N)))
          ((DayCoend.intro (dayInternalHom A N) A).app (g.app m x) y)
  rw [DayCoend.evaluate_intro, DayCoend.evaluate_intro]
  rfl

/-- Day β: evaluating a curried Day morphism recovers the original. -/
theorem dayEval_dayCurry {X A N : Module}
    (f : Hom (dayTensor X A) N) :
    Hom.comp (dayEval A N)
      (DayTensor.map (dayCurry f) (Hom.id A)) = f := by
  rw [← dayUncurry_eq_eval_comp]
  exact (dayClosedPresentation.closed X A N).symm_apply_apply f

/-- Day η: currying an evaluated Day morphism recovers the original. -/
theorem dayCurry_dayEval {X A N : Module}
    (g : Hom X (dayInternalHom A N)) :
    dayCurry
        (Hom.comp (dayEval A N) (DayTensor.map g (Hom.id A))) =
      g := by
  rw [← dayUncurry_eq_eval_comp]
  exact (dayClosedPresentation.closed X A N).apply_symm_apply g

/-- Curry over a first-order representable domain and transport to the
specialized representable internal hom used by linear arrows. -/
noncomputable def curryFirstOrder {X N : Module} (A : ℕ)
    (f : Hom (dayTensor X (representable A)) N) :
    Hom X (internalHomRepresentable A N) :=
  Hom.comp (dayInternalHomRepresentableIso A N).hom (dayCurry f)

/-- Evaluation for the specialized representable internal hom. -/
noncomputable def evalFirstOrder (A : ℕ) (N : Module) :
    Hom (dayTensor (internalHomRepresentable A N) (representable A)) N :=
  Hom.comp (dayEval (representable A) N)
    (map (dayInternalHomRepresentableIso A N).inv
      (Hom.id (representable A)))

/-- First-order Day β: evaluating a FO-curried morphism recovers the original. -/
theorem evalFirstOrder_curryFirstOrder (d : ℕ) {X N : Module}
    (f : Hom (dayTensor X (representable d)) N) :
    Hom.comp (evalFirstOrder d N)
      (DayTensor.map (curryFirstOrder d f) (Hom.id (representable d))) = f := by
  unfold evalFirstOrder curryFirstOrder
  rw [← Hom.comp_assoc]
  have hmap :
      Hom.comp
        (DayTensor.map (dayInternalHomRepresentableIso d N).inv
          (Hom.id (representable d)))
        (DayTensor.map
          (Hom.comp (dayInternalHomRepresentableIso d N).hom (dayCurry f))
          (Hom.id (representable d))) =
      DayTensor.map
        (Hom.comp (dayInternalHomRepresentableIso d N).inv
          (Hom.comp (dayInternalHomRepresentableIso d N).hom (dayCurry f)))
        (Hom.id (representable d)) := by
    have h :=
      (DayTensor.map_comp
        (dayInternalHomRepresentableIso d N).inv
        (Hom.comp (dayInternalHomRepresentableIso d N).hom (dayCurry f))
        (Hom.id (representable d))
        (Hom.id (representable d))).symm
    simpa only [Hom.comp_id] using h
  rw [hmap]
  have hiso :
      Hom.comp (dayInternalHomRepresentableIso d N).inv
        (Hom.comp (dayInternalHomRepresentableIso d N).hom (dayCurry f)) =
      dayCurry f := by
    rw [Hom.comp_assoc, (dayInternalHomRepresentableIso d N).inv_hom, Hom.id_comp]
  rw [hiso]
  exact dayEval_dayCurry f

/-- `λ = ρ ∘ σ` as Fin equivalences on the unit factor. -/
private theorem tensorLeftUnitor_eq_rightUnitor_swap (a : ℕ) :
    Superoperator.comp (Superoperator.tensorRightUnitor a)
        (Superoperator.tensorSwap 1 a) =
      Superoperator.tensorLeftUnitor a := by
  simp only [Superoperator.tensorLeftUnitor, Superoperator.tensorRightUnitor,
    Superoperator.tensorSwap, ← Superoperator.ofEquivalence_refl,
    Superoperator.ofEquivalence_comp]
  congr 1
  ext x
  simp [Superoperator.tensorLeftUnitorEquiv,
    Superoperator.tensorRightUnitorEquiv, Superoperator.tensorSwapEquiv]

/-- Left and right unitors agree after braiding the unit past `A`. -/
theorem rightUnitor_comp_braiding (A : Module) :
    Hom.comp (rightUnitor A) (braiding dayTensorUnit A) =
      leftUnitor A := by
  apply DayTensor.hom_ext
  intro m n q x
  change
      (rightUnitor A).app (m * n)
          ((braiding dayTensorUnit A).app (m * n)
            ((DayCoend.intro dayTensorUnit A).app q x)) =
        (leftUnitor A).app (m * n)
          ((DayCoend.intro dayTensorUnit A).app q x)
  rw [braiding_intro, (rightUnitor A).naturality]
  -- After naturality the intermediate fiber is indexed by `n * m`.
  rw [rightUnitor_intro (M := A) (m := n) (n := m) x q]
  rw [leftUnitor_intro (M := A) q x, A.act_comp]
  congr 1
  change Superoperator m 1 at q
  calc
    Superoperator.comp
        (Superoperator.comp (Superoperator.tensorRightUnitor n)
          (Superoperator.tensor (Superoperator.identity n) q))
        (Superoperator.tensorSwap m n) =
      Superoperator.comp (Superoperator.tensorRightUnitor n)
        (Superoperator.comp
          (Superoperator.tensor (Superoperator.identity n) q)
          (Superoperator.tensorSwap m n)) := by
        rw [Superoperator.comp_assoc]
    _ = Superoperator.comp (Superoperator.tensorRightUnitor n)
          (Superoperator.comp (Superoperator.tensorSwap 1 n)
            (Superoperator.tensor q (Superoperator.identity n))) := by
        rw [← Superoperator.tensorSwap_naturality]
    _ = Superoperator.comp
          (Superoperator.comp (Superoperator.tensorRightUnitor n)
            (Superoperator.tensorSwap 1 n))
          (Superoperator.tensor q (Superoperator.identity n)) := by
        rw [← Superoperator.comp_assoc]
    _ = Superoperator.comp (Superoperator.tensorLeftUnitor n)
          (Superoperator.tensor q (Superoperator.identity n)) := by
        rw [tensorLeftUnitor_eq_rightUnitor_swap]

/-- Cancel `ρ ∘ λ⁻¹` on the Day unit. -/
theorem rightUnitor_comp_leftUnitorInv_unit :
    Hom.comp (rightUnitor dayTensorUnit) (leftUnitorInv dayTensorUnit) =
      Hom.id dayTensorUnit := by
  rw [← leftUnitor_unit_eq_rightUnitor_unit, leftUnitor_hom_inv]

/-- Reorder `(U ⊗ L) ⊗ A` to `U ⊗ (A ⊗ L)`. -/
noncomputable def moveArgumentIntoLinear (U L A : Module) :
    Hom (dayTensor (dayTensor U L) A) (dayTensor U (dayTensor A L)) :=
  Hom.comp (map (Hom.id U) (braiding L A)) (associator U L A)

/-- Identity-body projection composed with `moveArgumentIntoLinear` reduces to
`λ ∘ (ρ ⊗ id)`. -/
theorem identity_body_move_eq (A : Module) :
    Hom.comp
      (Hom.comp (leftUnitor A)
        (map (Hom.id dayTensorUnit) (rightUnitor A)))
      (moveArgumentIntoLinear dayTensorUnit dayTensorUnit A) =
    Hom.comp (leftUnitor A)
      (map (rightUnitor dayTensorUnit) (Hom.id A)) := by
  unfold moveArgumentIntoLinear
  have hmap :
      Hom.comp
          (map (Hom.id dayTensorUnit) (rightUnitor A))
          (map (Hom.id dayTensorUnit) (braiding dayTensorUnit A)) =
        map (Hom.id dayTensorUnit)
          (Hom.comp (rightUnitor A) (braiding dayTensorUnit A)) := by
    simpa only [Hom.comp_id] using
      (DayTensor.map_comp (Hom.id dayTensorUnit) (Hom.id dayTensorUnit)
        (rightUnitor A) (braiding dayTensorUnit A)).symm
  rw [← Hom.comp_assoc (leftUnitor A), Hom.comp_assoc
    (map (Hom.id dayTensorUnit) (rightUnitor A)), hmap,
    rightUnitor_comp_braiding]
  exact congrArg (Hom.comp (leftUnitor A)) (DayTensor.triangle dayTensorUnit A)

/-- Reorder `(U ⊗ L) ⊗ A` to `(A ⊗ U) ⊗ L`. -/
noncomputable def moveArgumentIntoUnrestricted (U L A : Module) :
    Hom (dayTensor (dayTensor U L) A) (dayTensor (dayTensor A U) L) :=
  Hom.comp (map (braiding U A) (Hom.id L))
    (Hom.comp (associatorInv U A L)
      (Hom.comp (map (Hom.id U) (braiding L A))
        (associator U L A)))

/-- Identity unrestricted body composed with `moveArgumentIntoUnrestricted`
reduces to `λ ∘ (ρ ⊗ id)` (same residual as the linear identity move). -/
theorem identity_body_unres_move_eq (A : Module) :
    Hom.comp
      (Hom.comp (rightUnitor A)
        (rightUnitor (dayTensor A dayTensorUnit)))
      (moveArgumentIntoUnrestricted dayTensorUnit dayTensorUnit A) =
    Hom.comp (leftUnitor A)
      (map (rightUnitor dayTensorUnit) (Hom.id A)) := by
  unfold moveArgumentIntoUnrestricted
  -- Goal shape after unfold:
  -- ρ ∘ ρ' ∘ (σ ⊗ id) ∘ α⁻¹ ∘ (id ⊗ σ) ∘ α = λ ∘ (ρ ⊗ id)
  have hρσ :
      Hom.comp (rightUnitor (dayTensor A dayTensorUnit))
          (map (braiding dayTensorUnit A) (Hom.id dayTensorUnit)) =
        Hom.comp (braiding dayTensorUnit A)
          (rightUnitor (dayTensor dayTensorUnit A)) :=
    rightUnitor_natural (braiding dayTensorUnit A)
  -- Collapse `ρ ∘ (σ ⊗ id)` against the outer right unitor.
  have h1 :
      Hom.comp (rightUnitor A)
          (Hom.comp (rightUnitor (dayTensor A dayTensorUnit))
            (map (braiding dayTensorUnit A) (Hom.id dayTensorUnit))) =
        Hom.comp (leftUnitor A)
          (rightUnitor (dayTensor dayTensorUnit A)) := by
    calc
      Hom.comp (rightUnitor A)
          (Hom.comp (rightUnitor (dayTensor A dayTensorUnit))
            (map (braiding dayTensorUnit A) (Hom.id dayTensorUnit))) =
        Hom.comp (rightUnitor A)
          (Hom.comp (braiding dayTensorUnit A)
            (rightUnitor (dayTensor dayTensorUnit A))) := by
              exact congrArg (Hom.comp (rightUnitor A)) hρσ
      _ = Hom.comp
            (Hom.comp (rightUnitor A) (braiding dayTensorUnit A))
            (rightUnitor (dayTensor dayTensorUnit A)) := by
              exact Hom.comp_assoc _ _ _
      _ = Hom.comp (leftUnitor A)
            (rightUnitor (dayTensor dayTensorUnit A)) := by
              exact congrArg
                (fun g => Hom.comp g
                  (rightUnitor (dayTensor dayTensorUnit A)))
                (rightUnitor_comp_braiding A)
  -- Rewrite the outer `ρ ∘ ρ' ∘ (σ ⊗ id)` block.
  have h2 :
      Hom.comp
          (Hom.comp (rightUnitor A)
            (rightUnitor (dayTensor A dayTensorUnit)))
          (Hom.comp (map (braiding dayTensorUnit A) (Hom.id dayTensorUnit))
            (Hom.comp (associatorInv dayTensorUnit A dayTensorUnit)
              (Hom.comp (map (Hom.id dayTensorUnit) (braiding dayTensorUnit A))
                (associator dayTensorUnit dayTensorUnit A)))) =
        Hom.comp (leftUnitor A)
          (Hom.comp (rightUnitor (dayTensor dayTensorUnit A))
            (Hom.comp (associatorInv dayTensorUnit A dayTensorUnit)
              (Hom.comp (map (Hom.id dayTensorUnit) (braiding dayTensorUnit A))
                (associator dayTensorUnit dayTensorUnit A)))) := by
    -- Reassociate to expose `ρ ∘ ρ' ∘ (σ ⊗ id)`, then apply `h1`.
    have hre :
        Hom.comp
            (Hom.comp (rightUnitor A)
              (rightUnitor (dayTensor A dayTensorUnit)))
            (Hom.comp (map (braiding dayTensorUnit A) (Hom.id dayTensorUnit))
              (Hom.comp (associatorInv dayTensorUnit A dayTensorUnit)
                (Hom.comp
                  (map (Hom.id dayTensorUnit) (braiding dayTensorUnit A))
                  (associator dayTensorUnit dayTensorUnit A)))) =
          Hom.comp
            (Hom.comp (rightUnitor A)
              (Hom.comp (rightUnitor (dayTensor A dayTensorUnit))
                (map (braiding dayTensorUnit A) (Hom.id dayTensorUnit))))
            (Hom.comp (associatorInv dayTensorUnit A dayTensorUnit)
              (Hom.comp (map (Hom.id dayTensorUnit) (braiding dayTensorUnit A))
                (associator dayTensorUnit dayTensorUnit A))) := by
      simp only [Hom.comp_assoc]
    refine Eq.trans hre ?_
    exact congrArg
      (fun g => Hom.comp g
        (Hom.comp (associatorInv dayTensorUnit A dayTensorUnit)
          (Hom.comp (map (Hom.id dayTensorUnit) (braiding dayTensorUnit A))
            (associator dayTensorUnit dayTensorUnit A))))
      h1
  refine Eq.trans h2 ?_
  -- `ρ ∘ α⁻¹ = id ⊗ ρ`
  have hρα := DayTensor.rightUnitor_associatorInv dayTensorUnit A
  have h3 :
      Hom.comp (leftUnitor A)
          (Hom.comp (rightUnitor (dayTensor dayTensorUnit A))
            (Hom.comp (associatorInv dayTensorUnit A dayTensorUnit)
              (Hom.comp (map (Hom.id dayTensorUnit) (braiding dayTensorUnit A))
                (associator dayTensorUnit dayTensorUnit A)))) =
        Hom.comp (leftUnitor A)
          (Hom.comp (map (Hom.id dayTensorUnit) (rightUnitor A))
            (Hom.comp (map (Hom.id dayTensorUnit) (braiding dayTensorUnit A))
              (associator dayTensorUnit dayTensorUnit A))) := by
    have hre :
        Hom.comp (rightUnitor (dayTensor dayTensorUnit A))
            (Hom.comp (associatorInv dayTensorUnit A dayTensorUnit)
              (Hom.comp (map (Hom.id dayTensorUnit) (braiding dayTensorUnit A))
                (associator dayTensorUnit dayTensorUnit A))) =
          Hom.comp
            (Hom.comp (rightUnitor (dayTensor dayTensorUnit A))
              (associatorInv dayTensorUnit A dayTensorUnit))
            (Hom.comp (map (Hom.id dayTensorUnit) (braiding dayTensorUnit A))
              (associator dayTensorUnit dayTensorUnit A)) := by
      simp only [Hom.comp_assoc]
    refine congrArg (Hom.comp (leftUnitor A)) ?_
    refine Eq.trans hre ?_
    exact congrArg
      (fun g => Hom.comp g
        (Hom.comp (map (Hom.id dayTensorUnit) (braiding dayTensorUnit A))
          (associator dayTensorUnit dayTensorUnit A)))
      hρα
  refine Eq.trans h3 ?_
  -- `(id ⊗ ρ) ∘ (id ⊗ σ) = id ⊗ (ρ ∘ σ) = id ⊗ λ`
  have hmapσ :
      Hom.comp
          (map (Hom.id dayTensorUnit) (rightUnitor A))
          (map (Hom.id dayTensorUnit) (braiding dayTensorUnit A)) =
        map (Hom.id dayTensorUnit)
          (Hom.comp (rightUnitor A) (braiding dayTensorUnit A)) := by
    simpa only [Hom.comp_id] using
      (DayTensor.map_comp (Hom.id dayTensorUnit) (Hom.id dayTensorUnit)
        (rightUnitor A) (braiding dayTensorUnit A)).symm
  have h4 :
      Hom.comp (leftUnitor A)
          (Hom.comp (map (Hom.id dayTensorUnit) (rightUnitor A))
            (Hom.comp (map (Hom.id dayTensorUnit) (braiding dayTensorUnit A))
              (associator dayTensorUnit dayTensorUnit A))) =
        Hom.comp (leftUnitor A)
          (Hom.comp
            (map (Hom.id dayTensorUnit)
              (Hom.comp (rightUnitor A) (braiding dayTensorUnit A)))
            (associator dayTensorUnit dayTensorUnit A)) := by
    have hre :
        Hom.comp (map (Hom.id dayTensorUnit) (rightUnitor A))
            (Hom.comp (map (Hom.id dayTensorUnit) (braiding dayTensorUnit A))
              (associator dayTensorUnit dayTensorUnit A)) =
          Hom.comp
            (Hom.comp (map (Hom.id dayTensorUnit) (rightUnitor A))
              (map (Hom.id dayTensorUnit) (braiding dayTensorUnit A)))
            (associator dayTensorUnit dayTensorUnit A) := by
      simp only [Hom.comp_assoc]
    refine congrArg (Hom.comp (leftUnitor A)) ?_
    refine Eq.trans hre ?_
    exact congrArg (fun g => Hom.comp g
        (associator dayTensorUnit dayTensorUnit A)) hmapσ
  refine Eq.trans h4 ?_
  rw [rightUnitor_comp_braiding]
  exact congrArg (Hom.comp (leftUnitor A))
    (DayTensor.triangle dayTensorUnit A)

/-- Unrestricted abstraction over the genuine classical-bit carrier. -/
noncomputable def abstractUnrestricted {U L N : Module}
    (body : Hom (dayTensor (dayTensor classicalBitModule U) L) N) :
    Hom (dayTensor U L) (dayInternalHom classicalBitModule N) :=
  dayCurry
    (Hom.comp body
      (moveArgumentIntoUnrestricted U L classicalBitModule))

private noncomputable def castHom {M N : Module} (h : M = N) : Hom M N := by
  subst N
  exact Hom.id M

private noncomputable def castHomInv {M N : Module} (h : M = N) : Hom N M := by
  subst N
  exact Hom.id M

/-- A first-order fragment object as its representing Yoneda module. -/
noncomputable def firstOrderToRep {A : Ty} (hA : Ty.FirstOrder A) :
    Hom (fragmentModule A) (representable A.hilbertDim) :=
  castHom (by
    simpa [Ty.FirstOrder.dimension] using fragmentModule_of_firstOrder hA)

/-- Inverse representable transport for a first-order fragment object. -/
noncomputable def firstOrderFromRep {A : Ty} (hA : Ty.FirstOrder A) :
    Hom (representable A.hilbertDim) (fragmentModule A) :=
  castHomInv (by
    simpa [Ty.FirstOrder.dimension] using fragmentModule_of_firstOrder hA)

theorem firstOrderToRep_comp_fromRep {A : Ty} (hA : Ty.FirstOrder A) :
    Hom.comp (firstOrderToRep hA) (firstOrderFromRep hA) =
      Hom.id (representable A.hilbertDim) := by
  cases hA <;> rfl

theorem firstOrderFromRep_comp_toRep {A : Ty} (hA : Ty.FirstOrder A) :
    Hom.comp (firstOrderFromRep hA) (firstOrderToRep hA) =
      Hom.id (fragmentModule A) := by
  cases hA <;> rfl

/-- Linear abstraction over a first-order representable domain. -/
noncomputable def abstractLinear {U L N : Module} {A : Ty}
    (hA : Ty.FirstOrder A)
    (body : Hom (dayTensor U (dayTensor (fragmentModule A) L)) N) :
    Hom (dayTensor U L)
      (internalHomRepresentable A.hilbertDim N) := by
  have e : fragmentModule A = representable hA.dimension :=
    fragmentModule_of_firstOrder hA
  have hd : hA.dimension = A.hilbertDim := by
    induction hA <;> simp_all [Ty.FirstOrder.dimension, Ty.hilbertDim]
  rw [← hd]
  rw [e] at body
  exact curryFirstOrder hA.dimension
    (Hom.comp body
      (moveArgumentIntoLinear U L (representable hA.dimension)))

/-- Evaluation specialized to a first-order source type. -/
noncomputable def evalFragmentFirstOrder {A : Ty}
    (hA : Ty.FirstOrder A) (N : Module) :
    Hom
      (dayTensor (internalHomRepresentable A.hilbertDim N)
        (fragmentModule A)) N :=
  Hom.comp (evalFirstOrder A.hilbertDim N)
    (map (Hom.id _) (firstOrderToRep hA))

@[simp] theorem abstractLinear_unit {U L N : Module}
    (body : Hom (dayTensor U (dayTensor (fragmentModule .unit) L)) N) :
    abstractLinear .unit body =
      curryFirstOrder 1
        (Hom.comp body (moveArgumentIntoLinear U L (representable 1))) :=
  rfl

@[simp] theorem abstractLinear_bit {U L N : Module}
    (body : Hom (dayTensor U (dayTensor (fragmentModule .bit) L)) N) :
    abstractLinear .bit body =
      curryFirstOrder 2
        (Hom.comp body (moveArgumentIntoLinear U L (representable 2))) :=
  rfl

@[simp] theorem abstractLinear_qubit {U L N : Module}
    (body : Hom (dayTensor U (dayTensor (fragmentModule .qubit) L)) N) :
    abstractLinear .qubit body =
      curryFirstOrder 2
        (Hom.comp body (moveArgumentIntoLinear U L (representable 2))) :=
  rfl

@[simp] theorem evalFragmentFirstOrder_unit (N : Module) :
    evalFragmentFirstOrder .unit N = evalFirstOrder 1 N := by
  change Hom.comp (evalFirstOrder 1 N)
      (DayTensor.map (Hom.id _) (Hom.id (representable 1))) =
    evalFirstOrder 1 N
  rw [DayTensor.map_id, Hom.comp_id]

@[simp] theorem evalFragmentFirstOrder_bit (N : Module) :
    evalFragmentFirstOrder .bit N = evalFirstOrder 2 N := by
  change Hom.comp (evalFirstOrder 2 N)
      (DayTensor.map (Hom.id _) (Hom.id (representable 2))) =
    evalFirstOrder 2 N
  rw [DayTensor.map_id, Hom.comp_id]

@[simp] theorem evalFragmentFirstOrder_qubit (N : Module) :
    evalFragmentFirstOrder .qubit N = evalFirstOrder 2 N := by
  change Hom.comp (evalFirstOrder 2 N)
      (DayTensor.map (Hom.id _) (Hom.id (representable 2))) =
    evalFirstOrder 2 N
  rw [DayTensor.map_id, Hom.comp_id]

/-- Fragment Day β: evaluating an FO-abstracted body recovers the moved body. -/
theorem evalFragmentFirstOrder_abstractLinear {U L N : Module} {A : Ty}
    (hA : Ty.FirstOrder A)
    (body : Hom (dayTensor U (dayTensor (fragmentModule A) L)) N) :
    Hom.comp (evalFragmentFirstOrder hA N)
      (DayTensor.map (abstractLinear hA body) (Hom.id (fragmentModule A))) =
    Hom.comp body (moveArgumentIntoLinear U L (fragmentModule A)) := by
  cases hA with
  | unit =>
      simp only [evalFragmentFirstOrder_unit, abstractLinear_unit]
      exact evalFirstOrder_curryFirstOrder 1 _
  | bit =>
      simp only [evalFragmentFirstOrder_bit, abstractLinear_bit]
      exact evalFirstOrder_curryFirstOrder 2 _
  | qubit =>
      simp only [evalFragmentFirstOrder_qubit, abstractLinear_qubit]
      exact evalFirstOrder_curryFirstOrder 2 _
  | @tensor A B hA hB =>
      have hAbs :
          abstractLinear (.tensor hA hB) body =
            curryFirstOrder (A.hilbertDim * B.hilbertDim)
              (Hom.comp body
                (moveArgumentIntoLinear U L
                  (representable (A.hilbertDim * B.hilbertDim)))) :=
        rfl
      have hEv :
          evalFragmentFirstOrder (.tensor hA hB) N =
            evalFirstOrder (A.hilbertDim * B.hilbertDim) N := by
        change Hom.comp (evalFirstOrder (A.hilbertDim * B.hilbertDim) N)
            (DayTensor.map (Hom.id _)
              (Hom.id (representable (A.hilbertDim * B.hilbertDim)))) =
          evalFirstOrder (A.hilbertDim * B.hilbertDim) N
        rw [DayTensor.map_id, Hom.comp_id]
      simp only [hAbs, hEv]
      exact evalFirstOrder_curryFirstOrder (A.hilbertDim * B.hilbertDim) _

/-- Evaluation of an unrestricted function after classicalizing its physical
term-level bit argument. -/
noncomputable def evalUnrestrictedBit (N : Module) :
    Hom
      (dayTensor (dayInternalHom classicalBitModule N)
        (fragmentModule .bit)) N :=
  Hom.comp (dayEval classicalBitModule N)
    (map (Hom.id _) bitClassicalize)

/-- Unrestricted Day β: evaluating an abstracted body recovers the moved body
after classicalizing the physical bit argument. -/
theorem evalUnrestrictedBit_abstractUnrestricted {U L N : Module}
    (body : Hom (dayTensor (dayTensor classicalBitModule U) L) N) :
    Hom.comp (evalUnrestrictedBit N)
      (DayTensor.map (abstractUnrestricted body)
        (Hom.id (fragmentModule .bit))) =
    Hom.comp body
      (Hom.comp (moveArgumentIntoUnrestricted U L classicalBitModule)
        (DayTensor.map (Hom.id (dayTensor U L)) bitClassicalize)) := by
  unfold evalUnrestrictedBit abstractUnrestricted
  -- Align `fragmentModule .bit` with the stated domain of `bitClassicalize`.
  simp only [fragmentModule_bit]
  have hmap :
      Hom.comp
          (DayTensor.map (Hom.id (dayInternalHom classicalBitModule N))
            bitClassicalize)
          (DayTensor.map (dayCurry
              (Hom.comp body
                (moveArgumentIntoUnrestricted U L classicalBitModule)))
            (Hom.id (representable 2))) =
        DayTensor.map
          (dayCurry
            (Hom.comp body
              (moveArgumentIntoUnrestricted U L classicalBitModule)))
          bitClassicalize := by
    simpa only [Hom.id_comp, Hom.comp_id] using
      (DayTensor.map_comp
        (Hom.id (dayInternalHom classicalBitModule N))
        (dayCurry
          (Hom.comp body
            (moveArgumentIntoUnrestricted U L classicalBitModule)))
        bitClassicalize
        (Hom.id (representable 2))).symm
  rw [← Hom.comp_assoc, hmap]
  have hfactor :
      DayTensor.map
          (dayCurry
            (Hom.comp body
              (moveArgumentIntoUnrestricted U L classicalBitModule)))
          bitClassicalize =
        Hom.comp
          (DayTensor.map
            (dayCurry
              (Hom.comp body
                (moveArgumentIntoUnrestricted U L classicalBitModule)))
            (Hom.id classicalBitModule))
          (DayTensor.map (Hom.id (dayTensor U L)) bitClassicalize) := by
    simpa only [Hom.comp_id, Hom.id_comp] using
      DayTensor.map_comp
        (dayCurry
          (Hom.comp body
            (moveArgumentIntoUnrestricted U L classicalBitModule)))
        (Hom.id (dayTensor U L))
        (Hom.id classicalBitModule)
        bitClassicalize
  rw [hfactor]
  -- `Hom.comp` is definitionally associative, so Day β applies under postcomposition.
  exact congrArg (fun g => Hom.comp g
      (DayTensor.map (Hom.id (dayTensor U L)) bitClassicalize))
    (dayEval_dayCurry _)

/-- Pair introduction for first-order fragment objects. -/
noncomputable def tensorIntro {A B : Ty}
    (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B) :
    Hom (dayTensor (fragmentModule A) (fragmentModule B))
      (fragmentModule (.tensor A B)) :=
  Hom.comp (firstOrderFromRep (Ty.FirstOrder.tensor hA hB))
    (Hom.comp
      (dayTensorRepresentableIso A.hilbertDim B.hilbertDim).hom
      (map (firstOrderToRep hA) (firstOrderToRep hB)))

/-- Pair elimination for first-order fragment objects. -/
noncomputable def tensorElim {A B : Ty}
    (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B) :
    Hom (fragmentModule (.tensor A B))
      (dayTensor (fragmentModule A) (fragmentModule B)) :=
  Hom.comp (map (firstOrderFromRep hA) (firstOrderFromRep hB))
    (Hom.comp
      (dayTensorRepresentableIso A.hilbertDim B.hilbertDim).inv
      (firstOrderToRep (Ty.FirstOrder.tensor hA hB)))

/-- Apply a curried two-argument continuation to an unpacked first-order
tensor, preserving source order. -/
noncomputable def unpairApply {A B : Ty}
    (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B) (N : Module) :
    Hom
      (dayTensor (fragmentModule (.tensor A B))
        (internalHomRepresentable A.hilbertDim
          (internalHomRepresentable B.hilbertDim N)))
      N :=
  Hom.comp (evalFragmentFirstOrder hB N)
    (Hom.comp
      (map
        (evalFragmentFirstOrder hA
          (internalHomRepresentable B.hilbertDim N))
        (Hom.id (fragmentModule B)))
      (Hom.comp
        (associatorInv
          (internalHomRepresentable A.hilbertDim
            (internalHomRepresentable B.hilbertDim N))
          (fragmentModule A) (fragmentModule B))
        (Hom.comp
          (map (Hom.id _) (tensorElim hA hB))
          (braiding (fragmentModule (.tensor A B))
            (internalHomRepresentable A.hilbertDim
              (internalHomRepresentable B.hilbertDim N))))))


end FragmentContext
end QLambda.Linear
