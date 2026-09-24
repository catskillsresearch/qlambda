/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentIteBranching

/-!
# `FragCert.denote` constructor equations and independence

Computation equations, closed FO `ite` Step soundness, and
proof-witness independence; `routeAFragmentDenotationModel`.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000
open Domain.Presheaf
open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf.SigmaMon
open DayTensor
open scoped ComplexOrder MatrixOrder BigOperators

/-! ## Constructor computation equations -/

theorem FragCert.denote_unit_eq {Γ Δ}
    (hΓ : CtxUAllBit Γ) (hL : CtxLAllSomeFragment Δ) (hΔ : AllNone Δ) :
    FragCert.denote (.unit hΓ hL hΔ) =
      FragmentContext.combinedPoint hΓ hΔ routeAFragmentModel.unitIntro :=
  rfl

theorem FragCert.denote_bitLit_eq {Γ Δ b}
    (hΓ : CtxUAllBit Γ) (hL : CtxLAllSomeFragment Δ) (hΔ : AllNone Δ) :
    FragCert.denote (.bitLit hΓ hL b hΔ) =
      FragmentContext.combinedPoint hΓ hΔ (routeAFragmentModel.bitLit b) :=
  rfl

/-! ## Closed first-order `ite` helpers -/

/-- Closed bit-literal certificates denote as `closedPoint (bitLitHom _)`. -/
theorem FragCert.closed_bitLit_denote_eq (b : Bool) :
    FragCert.denote (FragCert.closed_bitLit_cert b) =
      FragmentContext.closedPoint (bitLitHom b) := by
  simp only [FragmentContext.closedPoint]
  rfl

theorem additivePair_comp {L M N P : Module}
    (f : Hom L M) (g : Hom L N) (h : Hom P L) :
    Hom.comp (additivePair f g) h =
      additivePair (Hom.comp f h) (Hom.comp g h) := by
  ext n x
  rfl

/-- Day-unit inverse unitor as a map into the empty combined context. -/
noncomputable def FragmentContext.closedLeftUnitorInv :
    Hom dayTensorUnit (FragmentContext.combined [] []) :=
  DayTensor.leftUnitorInv dayTensorUnit

theorem FragmentContext.closedLeftUnitorInv_eq :
    FragmentContext.closedLeftUnitorInv =
      DayTensor.leftUnitorInv dayTensorUnit :=
  rfl

theorem FragmentContext.combinedClosedCollapse_leftUnitorInv :
    Hom.comp FragmentContext.combinedClosedCollapse
      FragmentContext.closedLeftUnitorInv =
    Hom.id dayTensorUnit := by
  change Hom.comp
      (Hom.comp (DayTensor.leftUnitor dayTensorUnit)
        (DayTensor.map (Hom.id dayTensorUnit) (Hom.id dayTensorUnit)))
      (DayTensor.leftUnitorInv dayTensorUnit) =
    Hom.id dayTensorUnit
  rw [DayTensor.map_id, Hom.comp_id, DayTensor.leftUnitor_hom_inv]

theorem FragCert.denote_prim_eq {Γ Δ p}
    (hΓ : CtxUAllBit Γ) (hL : CtxLAllSomeFragment Δ) (hΔ : AllNone Δ) :
    FragCert.denote (.prim hΓ hL p hΔ) =
      FragmentContext.combinedPoint hΓ hΔ (FragCert.denotePrimPoint p) :=
  rfl

theorem FragCert.denote_ite_eq {Γ Δ Δ₁ Δ₂ A B T E}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
    (cB : FragCert Γ Δ₁ B .bit) (cT : FragCert Γ Δ₂ T A)
    (cE : FragCert Γ Δ₂ E A) :
    FragCert.denote (.ite hΓ hΔ hs hA cB cT cE) =
      Hom.comp (routeAFragmentBranching.iteElim hA)
        (Hom.comp
          (DayTensor.map (FragCert.denote cB)
            (additivePair (FragCert.denote cT) (FragCert.denote cE)))
          (FragmentContext.combinedOSplit hΓ hs)) :=
  rfl

/-! ## Closed first-order `ite` Step soundness -/

/-- Representable-level closed `ite` β after packing through `λ⁻¹ ⊗ λ⁻¹`. -/
private theorem iteElimRepresentable_closed_bitLit_aux (d : ℕ) (b : Bool)
    (T E : Hom (FragmentContext.combined [] []) (representable d)) :
    Hom.comp (iteElimRepresentable d)
      (Hom.comp
        (DayTensor.map
          (Hom.comp (bitLitHom b) FragmentContext.combinedClosedCollapse)
          (additivePair T E))
        (DayTensor.map FragmentContext.closedLeftUnitorInv
          FragmentContext.closedLeftUnitorInv)) =
      (bif b then T else E) := by
  have hsplit :
      Hom.comp
          (DayTensor.map
            (Hom.comp (bitLitHom b) FragmentContext.combinedClosedCollapse)
            (additivePair T E))
          (DayTensor.map FragmentContext.closedLeftUnitorInv
            FragmentContext.closedLeftUnitorInv) =
        DayTensor.map (bitLitHom b)
          (additivePair
            (Hom.comp T FragmentContext.closedLeftUnitorInv)
            (Hom.comp E FragmentContext.closedLeftUnitorInv)) := by
    have h :=
      (DayTensor.map_comp
        (Hom.comp (bitLitHom b) FragmentContext.combinedClosedCollapse)
        FragmentContext.closedLeftUnitorInv
        (additivePair T E)
        FragmentContext.closedLeftUnitorInv).symm
    refine h.trans ?_
    have hb :
        Hom.comp
            (Hom.comp (bitLitHom b) FragmentContext.combinedClosedCollapse)
            FragmentContext.closedLeftUnitorInv =
          bitLitHom b := by
      change Hom.comp (bitLitHom b)
          (Hom.comp FragmentContext.combinedClosedCollapse
            FragmentContext.closedLeftUnitorInv) =
        bitLitHom b
      rw [FragmentContext.combinedClosedCollapse_leftUnitorInv, Hom.comp_id]
    have hp :
        Hom.comp (additivePair T E) FragmentContext.closedLeftUnitorInv =
          additivePair
            (Hom.comp T FragmentContext.closedLeftUnitorInv)
            (Hom.comp E FragmentContext.closedLeftUnitorInv) :=
      additivePair_comp T E _
    rw [hb, hp]
  rw [hsplit, iteElimRepresentable_comp_bitLit d b
    (Hom.comp T FragmentContext.closedLeftUnitorInv)
    (Hom.comp E FragmentContext.closedLeftUnitorInv)]
  have hinj :
      Hom.comp FragmentContext.closedLeftUnitorInv
        (DayTensor.leftUnitor dayTensorUnit) =
      Hom.id (FragmentContext.combined [] []) :=
    (DayTensor.leftUnitorIso dayTensorUnit).inv_hom
  cases b with
  | true =>
      have h1 :
          Hom.comp T
              (Hom.comp FragmentContext.closedLeftUnitorInv
                (DayTensor.leftUnitor dayTensorUnit)) =
            Hom.comp T (Hom.id _) :=
        congrArg (Hom.comp T) hinj
      have h2 :
          Hom.comp
              (Hom.comp T FragmentContext.closedLeftUnitorInv)
              (DayTensor.leftUnitor dayTensorUnit) =
            Hom.comp T
              (Hom.comp FragmentContext.closedLeftUnitorInv
                (DayTensor.leftUnitor dayTensorUnit)) :=
        (Hom.comp_assoc _ _ _).symm
      exact h2.trans (h1.trans (Hom.comp_id T))
  | false =>
      have h1 :
          Hom.comp E
              (Hom.comp FragmentContext.closedLeftUnitorInv
                (DayTensor.leftUnitor dayTensorUnit)) =
            Hom.comp E (Hom.id _) :=
        congrArg (Hom.comp E) hinj
      have h2 :
          Hom.comp
              (Hom.comp E FragmentContext.closedLeftUnitorInv)
              (DayTensor.leftUnitor dayTensorUnit) =
            Hom.comp E
              (Hom.comp FragmentContext.closedLeftUnitorInv
                (DayTensor.leftUnitor dayTensorUnit)) :=
        (Hom.comp_assoc _ _ _).symm
      exact h2.trans (h1.trans (Hom.comp_id E))

/-- Unconditional closed FO `ite true` Step soundness. -/
theorem FragCert.denote_ite_true_closed {A : Ty}
    (hFO : Ty.FirstOrder A)
    {T E : Term}
    (cT : FragCert.Closed T A) (cE : FragCert.Closed E A) :
    FragCert.denote
        (.ite CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
          (Ty.SemanticFragment.ofFirstOrder hFO)
          (FragCert.closed_bitLit_cert true) cT cE) =
      FragCert.denote cT := by
  rw [FragCert.denote_ite_eq, FragCert.closed_bitLit_denote_eq,
    FragmentContext.combinedOSplit_nil, FragmentContext.closedPoint,
    routeAFragmentBranching]
  change Hom.comp (iteElimFragment (Ty.SemanticFragment.ofFirstOrder hFO))
      (Hom.comp
        (DayTensor.map
          (Hom.comp (bitLitHom true) FragmentContext.combinedClosedCollapse)
          (additivePair (FragCert.denote cT) (FragCert.denote cE)))
        (DayTensor.map FragmentContext.closedLeftUnitorInv
          FragmentContext.closedLeftUnitorInv)) =
    FragCert.denote cT
  cases hFO with
  | unit =>
      change Hom.comp (iteElimRepresentable 1)
          (Hom.comp
            (DayTensor.map
              (Hom.comp (bitLitHom true) FragmentContext.combinedClosedCollapse)
              (additivePair (FragCert.denote cT) (FragCert.denote cE)))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv)) =
        FragCert.denote cT
      exact iteElimRepresentable_closed_bitLit_aux 1 true
        (FragCert.denote cT) (FragCert.denote cE)
  | bit =>
      change Hom.comp (iteElimRepresentable 2)
          (Hom.comp
            (DayTensor.map
              (Hom.comp (bitLitHom true) FragmentContext.combinedClosedCollapse)
              (additivePair (FragCert.denote cT) (FragCert.denote cE)))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv)) =
        FragCert.denote cT
      exact iteElimRepresentable_closed_bitLit_aux 2 true
        (FragCert.denote cT) (FragCert.denote cE)
  | qubit =>
      change Hom.comp (iteElimRepresentable 2)
          (Hom.comp
            (DayTensor.map
              (Hom.comp (bitLitHom true) FragmentContext.combinedClosedCollapse)
              (additivePair (FragCert.denote cT) (FragCert.denote cE)))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv)) =
        FragCert.denote cT
      exact iteElimRepresentable_closed_bitLit_aux 2 true
        (FragCert.denote cT) (FragCert.denote cE)
  | tensor hA hB =>
      change Hom.comp
          (iteElimRepresentable (Ty.FirstOrder.dimension (.tensor hA hB)))
          (Hom.comp
            (DayTensor.map
              (Hom.comp (bitLitHom true) FragmentContext.combinedClosedCollapse)
              (additivePair (FragCert.denote cT) (FragCert.denote cE)))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv)) =
        FragCert.denote cT
      exact iteElimRepresentable_closed_bitLit_aux _
        true (FragCert.denote cT) (FragCert.denote cE)

/-- Unconditional closed FO `ite false` Step soundness. -/
theorem FragCert.denote_ite_false_closed {A : Ty}
    (hFO : Ty.FirstOrder A)
    {T E : Term}
    (cT : FragCert.Closed T A) (cE : FragCert.Closed E A) :
    FragCert.denote
        (.ite CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
          (Ty.SemanticFragment.ofFirstOrder hFO)
          (FragCert.closed_bitLit_cert false) cT cE) =
      FragCert.denote cE := by
  rw [FragCert.denote_ite_eq, FragCert.closed_bitLit_denote_eq,
    FragmentContext.combinedOSplit_nil, FragmentContext.closedPoint,
    routeAFragmentBranching]
  change Hom.comp (iteElimFragment (Ty.SemanticFragment.ofFirstOrder hFO))
      (Hom.comp
        (DayTensor.map
          (Hom.comp (bitLitHom false) FragmentContext.combinedClosedCollapse)
          (additivePair (FragCert.denote cT) (FragCert.denote cE)))
        (DayTensor.map FragmentContext.closedLeftUnitorInv
          FragmentContext.closedLeftUnitorInv)) =
    FragCert.denote cE
  cases hFO with
  | unit =>
      change Hom.comp (iteElimRepresentable 1)
          (Hom.comp
            (DayTensor.map
              (Hom.comp (bitLitHom false) FragmentContext.combinedClosedCollapse)
              (additivePair (FragCert.denote cT) (FragCert.denote cE)))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv)) =
        FragCert.denote cE
      exact iteElimRepresentable_closed_bitLit_aux 1 false
        (FragCert.denote cT) (FragCert.denote cE)
  | bit =>
      change Hom.comp (iteElimRepresentable 2)
          (Hom.comp
            (DayTensor.map
              (Hom.comp (bitLitHom false) FragmentContext.combinedClosedCollapse)
              (additivePair (FragCert.denote cT) (FragCert.denote cE)))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv)) =
        FragCert.denote cE
      exact iteElimRepresentable_closed_bitLit_aux 2 false
        (FragCert.denote cT) (FragCert.denote cE)
  | qubit =>
      change Hom.comp (iteElimRepresentable 2)
          (Hom.comp
            (DayTensor.map
              (Hom.comp (bitLitHom false) FragmentContext.combinedClosedCollapse)
              (additivePair (FragCert.denote cT) (FragCert.denote cE)))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv)) =
        FragCert.denote cE
      exact iteElimRepresentable_closed_bitLit_aux 2 false
        (FragCert.denote cT) (FragCert.denote cE)
  | tensor hA hB =>
      change Hom.comp
          (iteElimRepresentable (Ty.FirstOrder.dimension (.tensor hA hB)))
          (Hom.comp
            (DayTensor.map
              (Hom.comp (bitLitHom false) FragmentContext.combinedClosedCollapse)
              (additivePair (FragCert.denote cT) (FragCert.denote cE)))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv)) =
        FragCert.denote cE
      exact iteElimRepresentable_closed_bitLit_aux _
        false (FragCert.denote cT) (FragCert.denote cE)

/-- Legacy alias retained for citations that still mention the gap packaging. -/
theorem FragCert.denote_ite_true_closed_gap (d : ℕ) :
    (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil =
        DayTensor.map (DayTensor.leftUnitorInv dayTensorUnit)
          (DayTensor.leftUnitorInv dayTensorUnit)) →
      ∀ (T E : Hom dayTensorUnit (representable d)),
        Hom.comp (iteElimRepresentable d)
            (Hom.comp
              (DayTensor.map (bitLitHom true) (additivePair T E))
              (DayTensor.leftUnitorInv dayTensorUnit)) =
          T := fun _ T E =>
  iteElimRepresentable_bitLit_true d T E

theorem FragCert.denote_measure_eq {Γ Δ Δ₁ Δ₂ A Q K}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
    (cQ : FragCert Γ Δ₁ Q .qubit)
    (cK : FragCert Γ Δ₂ K (.arrow .unres .bit (.arrow .lin .qubit A))) :
    FragCert.denote (.measure hΓ hΔ hs hA cQ cK) =
      Hom.comp (FragCert.measureElim _)
        (Hom.comp
          (DayTensor.map (FragCert.denote cQ) (FragCert.denote cK))
          (FragmentContext.combinedOSplit hΓ hs)) :=
  rfl

theorem FragCert.denote_varU_eq {Γ Δ n A}
    (hΓ : CtxUAllBit Γ) (hL : CtxLAllSomeFragment Δ)
    (hl : Lookup Γ n A) (hD : Ty.Duplicable A) (hΔ : AllNone Δ)
    (hA : Ty.SemanticFragment A) :
    FragCert.denote (.varU hΓ hL hl hD hΔ hA) =
      FragmentContext.combinedLookupUnrestricted hΓ hl hΔ :=
  rfl

theorem FragCert.denote_varL_eq {Γ Δ n A}
    (hΓ : CtxUAllBit Γ) (hL : CtxLAllSomeFragment Δ)
    (hl : Lookup Δ n (some A)) (ho : OnlySomeAt Δ n)
    (hA : Ty.SemanticFragment A) :
    FragCert.denote (.varL hΓ hL hl ho hA) =
      FragmentContext.combinedLookupLinear hΓ hl ho :=
  rfl

theorem FragCert.denote_lamL_eq {Γ Δ A B M}
    (hΓ : CtxUAllBit Γ) (hL : CtxLAllSomeFragment Δ)
    (hAd : Ty.Admissible A) (hFO : Ty.FirstOrder A)
    (hB : Ty.SemanticFragment B) (c : FragCert Γ (some A :: Δ) M B) :
    FragCert.denote (.lamL hΓ hL hAd hFO hB c) =
      FragmentContext.abstractLinear hFO (FragCert.denote c) :=
  rfl

theorem FragCert.denote_lamU_eq {Γ Δ B M}
    (hΓ : CtxUAllBit Γ) (hL : CtxLAllSomeFragment Δ)
    (hAd : Ty.Admissible .bit) (hDup : Ty.Duplicable .bit)
    (hΔ : AllNone Δ) (hArr : Ty.SemanticFragment (.arrow .unres .bit B))
    (c : FragCert (.bit :: Γ) Δ M B) :
    FragCert.denote (.lamU hΓ hL hAd hDup hΔ hArr c) =
      FragmentContext.abstractUnrestricted (FragCert.denote c) :=
  rfl

theorem FragCert.denote_appL_eq {Γ Δ Δ₁ Δ₂ A B F X}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hFO : Ty.FirstOrder A)
    (hB : Ty.SemanticFragment B)
    (cF : FragCert Γ Δ₁ F (.arrow .lin A B)) (cX : FragCert Γ Δ₂ X A) :
    FragCert.denote (.appL hΓ hΔ hs hFO hB cF cX) =
      Hom.comp (FragmentContext.evalFragmentFirstOrder hFO _)
        (Hom.comp
          (DayTensor.map (FragCert.denote cF) (FragCert.denote cX))
          (FragmentContext.combinedOSplit hΓ hs)) :=
  rfl

theorem FragCert.denote_appU_eq {Γ Δ ΔF ΔX B F X}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ ΔF ΔX) (hN : AllNone ΔX) (hB : Ty.SemanticFragment B)
    (cF : FragCert Γ ΔF F (.arrow .unres .bit B))
    (cX : FragCert Γ ΔX X .bit) :
    FragCert.denote (.appU hΓ hΔ hs hN hB cF cX) =
      Hom.comp (FragmentContext.evalUnrestrictedBit _)
        (Hom.comp
          (DayTensor.map (FragCert.denote cF) (FragCert.denote cX))
          (FragmentContext.combinedOSplit hΓ hs)) :=
  rfl

theorem FragCert.denote_pair_eq {Γ Δ Δ₁ Δ₂ A B M N}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B)
    (cM : FragCert Γ Δ₁ M A) (cN : FragCert Γ Δ₂ N B) :
    FragCert.denote (.pair hΓ hΔ hs hA hB cM cN) =
      Hom.comp (FragmentContext.tensorIntro hA hB)
        (Hom.comp
          (DayTensor.map (FragCert.denote cM) (FragCert.denote cN))
          (FragmentContext.combinedOSplit hΓ hs)) :=
  rfl

theorem FragCert.denote_unpair_eq {Γ Δ Δ₁ Δ₂ A B C M K}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B)
    (hC : Ty.SemanticFragment C)
    (cM : FragCert Γ Δ₁ M (.tensor A B))
    (cK : FragCert Γ Δ₂ K (.arrow .lin A (.arrow .lin B C))) :
    FragCert.denote (.unpair hΓ hΔ hs hA hB hC cM cK) =
      Hom.comp (FragmentContext.unpairApply hA hB _)
        (Hom.comp
          (DayTensor.map (FragCert.denote cM) (FragCert.denote cK))
          (FragmentContext.combinedOSplit hΓ hs)) :=
  rfl

/-! ## Proof-witness independence -/

theorem FragCert.denote_unit_proof_independent {Γ Δ}
    (hΓ hΓ' : CtxUAllBit Γ) (hL hL' : CtxLAllSomeFragment Δ)
    (hΔ hΔ' : AllNone Δ) :
    FragCert.denote (.unit hΓ hL hΔ) =
      FragCert.denote (.unit hΓ' hL' hΔ') := by
  congr

theorem FragCert.denote_bitLit_proof_independent {Γ Δ b}
    (hΓ hΓ' : CtxUAllBit Γ) (hL hL' : CtxLAllSomeFragment Δ)
    (hΔ hΔ' : AllNone Δ) :
    FragCert.denote (.bitLit hΓ hL b hΔ) =
      FragCert.denote (.bitLit hΓ' hL' b hΔ') := by
  congr

theorem FragCert.denote_prim_proof_independent {Γ Δ p}
    (hΓ hΓ' : CtxUAllBit Γ) (hL hL' : CtxLAllSomeFragment Δ)
    (hΔ hΔ' : AllNone Δ) :
    FragCert.denote (.prim hΓ hL p hΔ) =
      FragCert.denote (.prim hΓ' hL' p hΔ') := by
  congr

theorem FragCert.denote_varU_proof_independent {Γ Δ n A}
    (hΓ hΓ' : CtxUAllBit Γ) (hL hL' : CtxLAllSomeFragment Δ)
    (hl hl' : Lookup Γ n A) (hD hD' : Ty.Duplicable A)
    (hΔ hΔ' : AllNone Δ) (hA hA' : Ty.SemanticFragment A) :
    FragCert.denote (.varU hΓ hL hl hD hΔ hA) =
      FragCert.denote (.varU hΓ' hL' hl' hD' hΔ' hA') := by
  congr

theorem FragCert.denote_varL_proof_independent {Γ Δ n A}
    (hΓ hΓ' : CtxUAllBit Γ) (hL hL' : CtxLAllSomeFragment Δ)
    (hl hl' : Lookup Δ n (some A)) (ho ho' : OnlySomeAt Δ n)
    (hA hA' : Ty.SemanticFragment A) :
    FragCert.denote (.varL hΓ hL hl ho hA) =
      FragCert.denote (.varL hΓ' hL' hl' ho' hA') := by
  congr

theorem FragCert.denote_lamL_proof_independent {Γ Δ A B M}
    (hΓ hΓ' : CtxUAllBit Γ) (hL hL' : CtxLAllSomeFragment Δ)
    (hAd hAd' : Ty.Admissible A) (hFO hFO' : Ty.FirstOrder A)
    (hB hB' : Ty.SemanticFragment B)
    (c : FragCert Γ (some A :: Δ) M B) :
    FragCert.denote (.lamL hΓ hL hAd hFO hB c) =
      FragCert.denote (.lamL hΓ' hL' hAd' hFO' hB' c) := by
  congr

theorem FragCert.denote_lamU_proof_independent {Γ Δ B M}
    (hΓ hΓ' : CtxUAllBit Γ) (hL hL' : CtxLAllSomeFragment Δ)
    (hAd hAd' : Ty.Admissible .bit) (hDup hDup' : Ty.Duplicable .bit)
    (hΔ hΔ' : AllNone Δ)
    (hArr hArr' : Ty.SemanticFragment (.arrow .unres .bit B))
    (c : FragCert (.bit :: Γ) Δ M B) :
    FragCert.denote (.lamU hΓ hL hAd hDup hΔ hArr c) =
      FragCert.denote (.lamU hΓ' hL' hAd' hDup' hΔ' hArr' c) := by
  congr

theorem FragCert.denote_appL_proof_independent {Γ Δ Δ₁ Δ₂ A B F X}
    (hΓ hΓ' : CtxUAllBit Γ) (hΔ hΔ' : CtxLAllSomeFragment Δ)
    (hs hs' : OSplit Δ Δ₁ Δ₂) (hFO hFO' : Ty.FirstOrder A)
    (hB hB' : Ty.SemanticFragment B)
    (cF : FragCert Γ Δ₁ F (.arrow .lin A B)) (cX : FragCert Γ Δ₂ X A) :
    FragCert.denote (.appL hΓ hΔ hs hFO hB cF cX) =
      FragCert.denote (.appL hΓ' hΔ' hs' hFO' hB' cF cX) := by
  congr

theorem FragCert.denote_appU_proof_independent {Γ Δ ΔF ΔX B F X}
    (hΓ hΓ' : CtxUAllBit Γ) (hΔ hΔ' : CtxLAllSomeFragment Δ)
    (hs hs' : OSplit Δ ΔF ΔX) (hN hN' : AllNone ΔX)
    (hB hB' : Ty.SemanticFragment B)
    (cF : FragCert Γ ΔF F (.arrow .unres .bit B))
    (cX : FragCert Γ ΔX X .bit) :
    FragCert.denote (.appU hΓ hΔ hs hN hB cF cX) =
      FragCert.denote (.appU hΓ' hΔ' hs' hN' hB' cF cX) := by
  congr

theorem FragCert.denote_pair_proof_independent {Γ Δ Δ₁ Δ₂ A B M N}
    (hΓ hΓ' : CtxUAllBit Γ) (hΔ hΔ' : CtxLAllSomeFragment Δ)
    (hs hs' : OSplit Δ Δ₁ Δ₂) (hA hA' : Ty.FirstOrder A)
    (hB hB' : Ty.FirstOrder B)
    (cM : FragCert Γ Δ₁ M A) (cN : FragCert Γ Δ₂ N B) :
    FragCert.denote (.pair hΓ hΔ hs hA hB cM cN) =
      FragCert.denote (.pair hΓ' hΔ' hs' hA' hB' cM cN) := by
  congr

theorem FragCert.denote_unpair_proof_independent {Γ Δ Δ₁ Δ₂ A B C M K}
    (hΓ hΓ' : CtxUAllBit Γ) (hΔ hΔ' : CtxLAllSomeFragment Δ)
    (hs hs' : OSplit Δ Δ₁ Δ₂) (hA hA' : Ty.FirstOrder A)
    (hB hB' : Ty.FirstOrder B) (hC hC' : Ty.SemanticFragment C)
    (cM : FragCert Γ Δ₁ M (.tensor A B))
    (cK : FragCert Γ Δ₂ K (.arrow .lin A (.arrow .lin B C))) :
    FragCert.denote (.unpair hΓ hΔ hs hA hB hC cM cK) =
      FragCert.denote (.unpair hΓ' hΔ' hs' hA' hB' hC' cM cK) := by
  congr

theorem FragCert.denote_ite_proof_independent {Γ Δ Δ₁ Δ₂ A B T E}
    (hΓ hΓ' : CtxUAllBit Γ) (hΔ hΔ' : CtxLAllSomeFragment Δ)
    (hs hs' : OSplit Δ Δ₁ Δ₂) (hA hA' : Ty.SemanticFragment A)
    (cB : FragCert Γ Δ₁ B .bit) (cT : FragCert Γ Δ₂ T A)
    (cE : FragCert Γ Δ₂ E A) :
    FragCert.denote (.ite hΓ hΔ hs hA cB cT cE) =
      FragCert.denote (.ite hΓ' hΔ' hs' hA' cB cT cE) := by
  congr

theorem FragCert.denote_measure_proof_independent {Γ Δ Δ₁ Δ₂ A Q K}
    (hΓ hΓ' : CtxUAllBit Γ) (hΔ hΔ' : CtxLAllSomeFragment Δ)
    (hs hs' : OSplit Δ Δ₁ Δ₂) (hA hA' : Ty.SemanticFragment A)
    (cQ : FragCert Γ Δ₁ Q .qubit)
    (cK : FragCert Γ Δ₂ K (.arrow .unres .bit (.arrow .lin .qubit A))) :
    FragCert.denote (.measure hΓ hΔ hs hA cQ cK) =
      FragCert.denote (.measure hΓ' hΔ' hs' hA' cQ cK) := by
  congr

/-- Full Route-A denotation model. -/
noncomputable def routeAFragmentDenotationModel : FragmentDenotationModel where
  denote := FragCert.denote
  denote_unit := by
    intro c
    cases c with
    | unit hΓ _ hΔ =>
        change FragmentContext.combinedPoint hΓ hΔ
            routeAFragmentModel.unitIntro =
          FragmentContext.closedPoint routeAFragmentModel.unitIntro
        simp only [FragmentContext.combinedPoint, FragmentContext.closedPoint,
          combinedAllDiscard_nil]
  denote_bitLit := by
    intro b c
    cases c with
    | bitLit hΓ _ _ hΔ =>
        change FragmentContext.combinedPoint hΓ hΔ
            (routeAFragmentModel.bitLit b) =
          FragmentContext.closedPoint (routeAFragmentModel.bitLit b)
        simp only [FragmentContext.combinedPoint, FragmentContext.closedPoint,
          combinedAllDiscard_nil]

/-- Route A supplies compositional open-term denotation for every `FragCert`. -/
theorem routeA_fragment_denotation_exists :
    Nonempty FragmentDenotationModel :=
  ⟨routeAFragmentDenotationModel⟩


end QLambda.Linear
