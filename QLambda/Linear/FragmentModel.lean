/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.SemanticFragment
import QLambda.Linear.TypeInterpretation
import QLambda.Linear.PrimitiveSuperoperator
import QLambda.Domain.Presheaf.Yoneda
import QLambda.Domain.Presheaf.ClosedGenerated
import QLambda.Domain.Presheaf.DayCoend
import QLambda.Domain.Presheaf.Module

/-!
# Presheaf fragment model and Route A direct semantics

`PresheafFragmentModel` is the minimum semantic interface for
`Ty.SemanticFragment`.  Because `SemanticFragment` is a `Prop`, objects are
assigned by recursion on the underlying `Ty` (via `fragmentModule`), and
agreement on fragment types is proved by induction into `Prop`.

Route A supplies classical-bit weaken/contract maps directly (not via
`bang 2`) together with primitive and measurement Yoneda embeddings.
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators

/-- Module interpretation of a type in the fragment shape.  Outside the
fragment this is an inert fallback; only fragment types are used by the
model. -/
noncomputable def fragmentModule : Ty → Module
  | .unit => representable 1
  | .bit | .qubit => representable 2
  | .tensor A B => representable (A.hilbertDim * B.hilbertDim)
  | .arrow .lin A B =>
      internalHomRepresentable A.hilbertDim (fragmentModule B)
  | .arrow .unres .bit B =>
      internalHomRepresentable 2 (fragmentModule B)
  | .arrow .unres _ _ => representable 1
  | .var _ | .mu _ => representable 1

@[simp] theorem fragmentModule_unit : fragmentModule .unit = representable 1 := rfl
@[simp] theorem fragmentModule_bit : fragmentModule .bit = representable 2 := rfl
@[simp] theorem fragmentModule_qubit : fragmentModule .qubit = representable 2 := rfl

theorem fragmentModule_of_firstOrder {A : Ty} (h : Ty.FirstOrder A) :
    fragmentModule A = representable h.dimension := by
  induction h with
  | unit => rfl
  | bit => rfl
  | qubit => rfl
  | tensor hA hB =>
      -- `FirstOrder.dimension (.tensor ..) = hilbertDim A * hilbertDim B`
      simp only [fragmentModule]
      rfl

/-- Classical-bit discard `Bit → I` (Yoneda of `discardTwo`). -/
noncomputable def bitDiscard :
    Hom (representable 2) dayTensorUnit :=
  yonedaMap SigmaMon.ChoiSum.discardTwo

/-- Isometric classical copy embedding `|i⟩ ↦ |ii⟩` (`0 ↦ 0`, `1 ↦ 3`). -/
noncomputable def classicalCopyMatrix : Matrix (Fin 4) (Fin 2) ℂ :=
  fun pq j => if pq.val = j.val * 3 then 1 else 0

private theorem sum_fin4 (f : Fin 4 → ℂ) :
    (∑ x : Fin 4, f x) = f 0 + f 1 + f 2 + f 3 := by
  have huniv : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by
    decide
  rw [huniv]
  simp [Finset.sum_insert]
  abel

theorem classicalCopyMatrix_isometry :
    classicalCopyMatrix.conjTranspose * classicalCopyMatrix =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, classicalCopyMatrix,
      Matrix.one_apply]
    rw [sum_fin4]; simp
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, classicalCopyMatrix,
      Matrix.one_apply]
    rw [sum_fin4]; simp
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, classicalCopyMatrix,
      Matrix.one_apply]
    rw [sum_fin4]; simp
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, classicalCopyMatrix,
      Matrix.one_apply]
    rw [sum_fin4]; simp

/-- Classical-bit copy as an isometric superoperator `2 → 4`. -/
noncomputable def bitCopySuperoperator : Superoperator 2 4 :=
  Superoperator.ofIsometry classicalCopyMatrix classicalCopyMatrix_isometry

/-- Classical-bit copy into the representable tensor square. -/
noncomputable def bitCopy :
    Hom (representable 2) (dayTensorRepresentable 2 2) :=
  yonedaMap bitCopySuperoperator

/-- Bit preparation from a Boolean literal. -/
noncomputable def bitPrepare (b : Bool) : Superoperator 1 2 :=
  if b then SigmaMon.ChoiSum.isometricBasisPrep 1
  else SigmaMon.ChoiSum.isometricBasisPrep 0

noncomputable def bitLitHom (b : Bool) :
    Hom dayTensorUnit (representable 2) :=
  yonedaMap (bitPrepare b)

/-- Primitive as a Yoneda map on its Hilbert IO dimensions. -/
noncomputable def primYoneda (p : Prim) :
    Hom (representable (CQ.QDim p.inputQ))
      (representable (CQ.QDim p.outputQ)) :=
  yonedaMap (Prim.superoperator p)

/-- Measurement instrument branches as Yoneda maps. -/
noncomputable def measureBranchYoneda (b : Bool) :
    Hom (representable 2) (representable 2) :=
  yonedaMap
    ((Instrument.measure (0 : Fin 1)).branchSuperoperator (if b then 1 else 0))

/-- Minimum semantic interface for the fragment (no global bang / LNL). -/
structure PresheafFragmentModel where
  /-- Object assignment for every fragment type. -/
  ty : ∀ {A}, Ty.SemanticFragment A → Module
  /-- Classical-bit discard. -/
  bitDiscard : Hom (representable 2) dayTensorUnit
  /-- Classical-bit copy into the representable tensor square. -/
  bitCopy : Hom (representable 2) (dayTensorRepresentable 2 2)
  /-- Boolean constants. -/
  bitLit : Bool → Hom dayTensorUnit (representable 2)
  /-- Unit point. -/
  unitIntro : Hom dayTensorUnit (representable 1)
  /-- Primitive embeddings on Hilbert dimensions. -/
  primMap : ∀ p : Prim,
    Hom (representable (CQ.QDim p.inputQ))
      (representable (CQ.QDim p.outputQ))
  /-- Measurement branch maps. -/
  measureBranch : Bool → Hom (representable 2) (representable 2)
  /-- Agreement with the intrinsic superoperator presentation. -/
  prim_agrees :
    ∀ p, primMap p = yonedaMap (Prim.superoperator p)
  /-- Fragment objects are the syntactic `fragmentModule`. -/
  ty_eq_fragmentModule :
    ∀ {A} (h : Ty.SemanticFragment A), ty h = fragmentModule A

/-- Route A model: direct fragment semantics. -/
noncomputable def routeAFragmentModel : PresheafFragmentModel where
  ty := fun {A} _ => fragmentModule A
  bitDiscard := bitDiscard
  bitCopy := bitCopy
  bitLit := bitLitHom
  unitIntro := yonedaMap (Superoperator.identity 1)
  primMap := primYoneda
  measureBranch := measureBranchYoneda
  prim_agrees := fun _ => rfl
  ty_eq_fragmentModule := fun _ => rfl

/-- Route A acceptance: fragment objects and structural maps exist without a
global bang. -/
theorem routeA_fragment_acceptance :
    (∀ {A : Ty} (h : Ty.SemanticFragment A),
      routeAFragmentModel.ty h = fragmentModule A) ∧
    (∀ p, routeAFragmentModel.primMap p =
      yonedaMap (Prim.superoperator p)) ∧
    (routeAFragmentModel.bitDiscard =
      yonedaMap SigmaMon.ChoiSum.discardTwo) :=
  ⟨routeAFragmentModel.ty_eq_fragmentModule,
    routeAFragmentModel.prim_agrees, rfl⟩

/-- Named Route A success marker for the ordered blocker tree. -/
def RouteASucceeded : Prop :=
  Nonempty PresheafFragmentModel

theorem routeA_succeeded : RouteASucceeded :=
  ⟨routeAFragmentModel⟩

/-- Routes B–F are not entered: Route A already meets the minimum interface. -/
def RoutesBtoFSkipped : String :=
  "Route A acceptance closed; Routes B–F skipped per ordered decision tree."

end QLambda.Linear
