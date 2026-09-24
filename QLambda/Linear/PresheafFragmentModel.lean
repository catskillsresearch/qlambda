/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitModule

/-!
# Route A fragment model interface

`fragmentModule`, bit/prim/measure Yoneda maps, and
`routeAFragmentModel` / acceptance.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000
open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators

/-- Module interpretation of a type in the fragment shape.  Linear
first-order domains retain the representable closed structure.  An
unrestricted bit arrow is instead closed over the dephasing-fixed classical
bit carrier, matching the interpretation of unrestricted context cells.
Outside the admitted fragment this is an inert fallback. -/
noncomputable def fragmentModule : Ty → Module
  | .unit => representable 1
  | .bit | .qubit => representable 2
  | .tensor A B => representable (A.hilbertDim * B.hilbertDim)
  | .arrow .lin A B =>
      internalHomRepresentable A.hilbertDim (fragmentModule B)
  | .arrow .unres .bit B =>
      dayInternalHom classicalBitModule (fragmentModule B)
  | .arrow .unres _ _ => representable 1
  | .var _ | .mu _ => representable 1

@[simp] theorem fragmentModule_unit :
    fragmentModule .unit = representable 1 := rfl

@[simp] theorem fragmentModule_bit :
    fragmentModule .bit = representable 2 := rfl

@[simp] theorem fragmentModule_qubit :
    fragmentModule .qubit = representable 2 := rfl

theorem fragmentModule_of_firstOrder {A : Ty} (h : Ty.FirstOrder A) :
    fragmentModule A = representable h.dimension := by
  induction h with
  | unit => rfl
  | bit => rfl
  | qubit => rfl
  | tensor hA hB =>
      simp only [fragmentModule]
      rfl

/-- Bit preparation from a Boolean literal. -/
noncomputable def bitPrepare (b : Bool) : Superoperator 1 2 :=
  if b then SigmaMon.ChoiSum.isometricBasisPrep 1
  else SigmaMon.ChoiSum.isometricBasisPrep 0

noncomputable def bitLitHom (b : Bool) :
    Hom dayTensorUnit (representable 2) :=
  yonedaMap (bitPrepare b)

theorem bitDephase_comp_bitPrepare (b : Bool) :
    Superoperator.comp bitDephaseSuperoperator (bitPrepare b) =
      bitPrepare b := by
  cases b <;> simp only [bitPrepare]
  · exact bitDephase_comp_isometricBasisPrep 0
  · exact bitDephase_comp_isometricBasisPrep 1

/-- Forgetting then classicalizing is computational-basis dephasing. -/
theorem classicalBitInclusion_comp_bitClassicalize :
    Hom.comp classicalBitInclusion bitClassicalize =
      yonedaMap bitDephaseSuperoperator := by
  ext n x
  rfl

/-- Bit literals are already classical: inclusion recovers them after
classicalization. -/
theorem classicalBitInclusion_comp_bitClassicalize_bitLit (b : Bool) :
    Hom.comp classicalBitInclusion
        (Hom.comp bitClassicalize (bitLitHom b)) =
      bitLitHom b := by
  change Hom.comp
      (Hom.comp classicalBitInclusion bitClassicalize) (bitLitHom b) =
    bitLitHom b
  rw [classicalBitInclusion_comp_bitClassicalize]
  -- `yonedaMap dephase ∘ yonedaMap prep = yonedaMap (dephase ∘ prep)`
  simp only [bitLitHom, ← yonedaMap_comp, bitDephase_comp_bitPrepare]

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
  /-- Classical-bit copy into the actual coend Day tensor square. -/
  bitCopy :
    Hom (representable 2) (dayTensor (representable 2) (representable 2))
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
  bitCopy := Hom.comp (dayTensorRepresentableIso 2 2).inv bitCopy
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

/-- Named Route A success marker: a concrete `PresheafFragmentModel` exists
(type objects, bit discard/copy, prim/measure maps).  This does **not**
include open-context denotation or runtime adequacy. -/
def RouteASucceeded : Prop :=
  Nonempty PresheafFragmentModel

theorem routeA_succeeded : RouteASucceeded :=
  ⟨routeAFragmentModel⟩

/-- Mathematical record that Route A supplies the maps required by the
minimum type/constant interface, so the ordered B–F tree is not entered for
that gate. -/
theorem routeA_skips_ordered_bang_routes :
    (∀ {A : Ty} (h : Ty.SemanticFragment A),
      ∃ M : Module, routeAFragmentModel.ty h = M) ∧
    (∃ δ : Hom (representable 2) dayTensorUnit,
      δ = routeAFragmentModel.bitDiscard) ∧
    (∃ γ : Hom (representable 2)
        (dayTensor (representable 2) (representable 2)),
      γ = routeAFragmentModel.bitCopy) :=
  ⟨fun h => ⟨routeAFragmentModel.ty h, rfl⟩,
    ⟨routeAFragmentModel.bitDiscard, rfl⟩,
    ⟨routeAFragmentModel.bitCopy, rfl⟩⟩


end QLambda.Linear
