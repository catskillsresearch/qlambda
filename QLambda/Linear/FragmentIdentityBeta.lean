/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentCoherenceCore

/-!
# Closed identity β on `FragCert.denote`

Certificate constructors and redex=contractum proofs for closed linear
identity application; spines for unrestricted identity β.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf

/-! ## Closed identity β certificate constructors

Closed linear identity β (`fragment_betaL_id_unit` / `fragment_betaL_id_bit`)
is proved via FO Day β plus Day unitor/braiding cancellation against
`combinedOSplit_nil` / `closedPoint`.  Unrestricted identity β follows the
same spine once the unrestricted move cancels. -/

theorem fragment_unit_admissible : Ty.Admissible .unit := by
  decide

theorem fragment_bit_admissible : Ty.Admissible .bit := by
  decide

theorem fragment_bit_duplicable : Ty.Duplicable .bit := by
  decide

theorem fragment_ctxU_bit_nil : CtxUAllBit [.bit] := by
  intro A hm
  simp only [List.mem_cons] at hm
  rcases hm with rfl | hm
  · rfl
  · cases hm

/-- Linear identity body `varL 0` in a singleton unit context. -/
noncomputable def fragCert_varL0_unit :
    FragCert [] [some .unit] (.var .lin 0) .unit :=
  .varL CtxUAllBit.nil
    (CtxLAllSomeFragment.cons_some Ty.SemanticFragment.unit
      CtxLAllSomeFragment.nil)
    Lookup.zero trivial Ty.SemanticFragment.unit

/-- Closed linear identity combinator `λx. x` at unit. -/
noncomputable def fragCert_lamL_id_unit :
    FragCert [] [] (.lam .lin .unit (.var .lin 0))
      (.arrow .lin .unit .unit) :=
  .lamL CtxUAllBit.nil CtxLAllSomeFragment.nil fragment_unit_admissible
    Ty.FirstOrder.unit Ty.SemanticFragment.unit fragCert_varL0_unit

/-- Closed β-redex `app (λx. x) unit`. -/
noncomputable def fragCert_appL_id_unit :
    FragCert [] []
      (.app (.lam .lin .unit (.var .lin 0)) .unit) .unit :=
  .appL CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
    Ty.FirstOrder.unit Ty.SemanticFragment.unit
    fragCert_lamL_id_unit FragCert.closed_unit_cert

/-- Linear identity body `varL 0` in a singleton bit context. -/
noncomputable def fragCert_varL0_bit :
    FragCert [] [some .bit] (.var .lin 0) .bit :=
  .varL CtxUAllBit.nil
    (CtxLAllSomeFragment.cons_some Ty.SemanticFragment.bit
      CtxLAllSomeFragment.nil)
    Lookup.zero trivial Ty.SemanticFragment.bit

/-- Closed linear identity combinator `λx. x` at bit. -/
noncomputable def fragCert_lamL_id_bit :
    FragCert [] [] (.lam .lin .bit (.var .lin 0))
      (.arrow .lin .bit .bit) :=
  .lamL CtxUAllBit.nil CtxLAllSomeFragment.nil fragment_bit_admissible
    Ty.FirstOrder.bit Ty.SemanticFragment.bit fragCert_varL0_bit

/-- Closed β-redex `app (λx. x) (bitLit b)`. -/
noncomputable def fragCert_appL_id_bit (b : Bool) :
    FragCert [] []
      (.app (.lam .lin .bit (.var .lin 0)) (.bitLit b)) .bit :=
  .appL CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
    Ty.FirstOrder.bit Ty.SemanticFragment.bit
    fragCert_lamL_id_bit (FragCert.closed_bitLit_cert b)

/-- Unrestricted identity body `varU 0`. -/
noncomputable def fragCert_varU0_bit :
    FragCert [.bit] [] (.var .unres 0) .bit :=
  .varU fragment_ctxU_bit_nil CtxLAllSomeFragment.nil Lookup.zero
    fragment_bit_duplicable trivial Ty.SemanticFragment.bit

/-- Closed unrestricted identity combinator `λx. x` at bit. -/
noncomputable def fragCert_lamU_id_bit :
    FragCert [] [] (.lam .unres .bit (.var .unres 0))
      (.arrow .unres .bit .bit) :=
  .lamU CtxUAllBit.nil CtxLAllSomeFragment.nil fragment_bit_admissible fragment_bit_duplicable
    trivial (.arrowUnresBit Ty.SemanticFragment.bit) fragCert_varU0_bit

/-- Closed β-redex `appU (λx. x) (bitLit b)`. -/
noncomputable def fragCert_appU_id_bit (b : Bool) :
    FragCert [] []
      (.app (.lam .unres .bit (.var .unres 0)) (.bitLit b)) .bit :=
  .appU CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil trivial
    Ty.SemanticFragment.bit fragCert_lamU_id_bit
    (FragCert.closed_bitLit_cert b)

/-- Identity-body linear projection unfolds to unitors (enables closed β). -/
theorem fragCert_varL0_unit_denote :
    FragCert.denote fragCert_varL0_unit =
      Hom.comp (DayTensor.leftUnitor (fragmentModule .unit))
        (DayTensor.map (Hom.id dayTensorUnit)
          (Hom.comp (DayTensor.rightUnitor (fragmentModule .unit))
            (DayTensor.map (Hom.id (fragmentModule .unit))
              (Hom.id dayTensorUnit)))) := by
  simp only [fragCert_varL0_unit, FragCert.denote_varL_eq,
    FragmentContext.combinedLookupLinear,
    FragmentContext.linearOnlySomeAtProject,
    FragmentContext.linearOnlySomeAtProjectLists_singleton]
  rfl

/-- Spine expansion of the closed unit identity redex through FO Day eval. -/
theorem fragment_betaL_id_unit_spine :
    FragCert.denote fragCert_appL_id_unit =
      Hom.comp
        (FragmentContext.evalFragmentFirstOrder Ty.FirstOrder.unit _)
        (Hom.comp
          (DayTensor.map
            (FragmentContext.abstractLinear Ty.FirstOrder.unit
              (FragCert.denote fragCert_varL0_unit))
            (FragCert.denote FragCert.closed_unit_cert))
          (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) :=
  fragment_subst_lin_spine CtxUAllBit.nil CtxLAllSomeFragment.nil
    OSplit.nil fragment_unit_admissible Ty.FirstOrder.unit Ty.SemanticFragment.unit
    CtxLAllSomeFragment.nil fragCert_varL0_unit FragCert.closed_unit_cert

/-- Spine expansion of the closed bit identity redex. -/
theorem fragment_betaL_id_bit_spine (b : Bool) :
    FragCert.denote (fragCert_appL_id_bit b) =
      Hom.comp
        (FragmentContext.evalFragmentFirstOrder Ty.FirstOrder.bit _)
        (Hom.comp
          (DayTensor.map
            (FragmentContext.abstractLinear Ty.FirstOrder.bit
              (FragCert.denote fragCert_varL0_bit))
            (FragCert.denote (FragCert.closed_bitLit_cert b)))
          (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) :=
  fragment_subst_lin_spine CtxUAllBit.nil CtxLAllSomeFragment.nil
    OSplit.nil fragment_bit_admissible Ty.FirstOrder.bit Ty.SemanticFragment.bit
    CtxLAllSomeFragment.nil fragCert_varL0_bit (FragCert.closed_bitLit_cert b)

/-- Spine expansion of the closed unrestricted bit identity redex. -/
theorem fragment_betaU_id_bit_spine (b : Bool) :
    FragCert.denote (fragCert_appU_id_bit b) =
      Hom.comp (FragmentContext.evalUnrestrictedBit _)
        (Hom.comp
          (DayTensor.map
            (FragmentContext.abstractUnrestricted
              (FragCert.denote fragCert_varU0_bit))
            (FragCert.denote (FragCert.closed_bitLit_cert b)))
          (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) :=
  fragment_subst_unres_bit_spine CtxUAllBit.nil
    CtxLAllSomeFragment.nil OSplit.nil fragment_bit_admissible fragment_bit_duplicable trivial
    (.arrowUnresBit Ty.SemanticFragment.bit) Ty.SemanticFragment.bit
    CtxLAllSomeFragment.nil trivial fragCert_varU0_bit
    (FragCert.closed_bitLit_cert b)

/-- Unpair denotation expands through `unpairApply`. -/
theorem fragment_unpair_beta_spine {Γ Δ Δ₁ Δ₂ A B C M K}
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
  FragCert.denote_unpair_eq hΓ hΔ hs hA hB hC cM cK

/-- Identity linear body simplifies to `λ ∘ (id ⊗ ρ)`. -/
theorem fragCert_varL0_unit_denote_simple :
    FragCert.denote fragCert_varL0_unit =
      Hom.comp (DayTensor.leftUnitor (fragmentModule .unit))
        (DayTensor.map (Hom.id dayTensorUnit)
          (DayTensor.rightUnitor (fragmentModule .unit))) := by
  rw [fragCert_varL0_unit_denote, DayTensor.map_id, Hom.comp_id]

theorem fragCert_varL0_bit_denote :
    FragCert.denote fragCert_varL0_bit =
      Hom.comp (DayTensor.leftUnitor (fragmentModule .bit))
        (DayTensor.map (Hom.id dayTensorUnit)
          (Hom.comp (DayTensor.rightUnitor (fragmentModule .bit))
            (DayTensor.map (Hom.id (fragmentModule .bit))
              (Hom.id dayTensorUnit)))) := by
  simp only [fragCert_varL0_bit, FragCert.denote_varL_eq,
    FragmentContext.combinedLookupLinear,
    FragmentContext.linearOnlySomeAtProject,
    FragmentContext.linearOnlySomeAtProjectLists_singleton]
  rfl

theorem fragCert_varL0_bit_denote_simple :
    FragCert.denote fragCert_varL0_bit =
      Hom.comp (DayTensor.leftUnitor (fragmentModule .bit))
        (DayTensor.map (Hom.id dayTensorUnit)
          (DayTensor.rightUnitor (fragmentModule .bit))) := by
  rw [fragCert_varL0_bit_denote, DayTensor.map_id, Hom.comp_id]

/-- Closed identity move/split cancellation against a Day-unit point. -/
theorem closed_identity_move_cancel {A : Module}
    (f : Hom dayTensorUnit A) :
    Hom.comp
      (Hom.comp (DayTensor.leftUnitor A)
        (DayTensor.map (DayTensor.rightUnitor dayTensorUnit) (Hom.id A)))
      (Hom.comp
        (DayTensor.map (Hom.id (FragmentContext.combined [] []))
          (Hom.comp f FragmentContext.combinedClosedCollapse))
        (DayTensor.map FragmentContext.closedLeftUnitorInv
          FragmentContext.closedLeftUnitorInv)) =
    Hom.comp f FragmentContext.combinedClosedCollapse := by
  have hsplit :
      Hom.comp
          (DayTensor.map (Hom.id (FragmentContext.combined [] []))
            (Hom.comp f FragmentContext.combinedClosedCollapse))
          (DayTensor.map FragmentContext.closedLeftUnitorInv
            FragmentContext.closedLeftUnitorInv) =
        DayTensor.map FragmentContext.closedLeftUnitorInv f := by
    have h :=
      (DayTensor.map_comp
        (Hom.id (FragmentContext.combined [] []))
        FragmentContext.closedLeftUnitorInv
        (Hom.comp f FragmentContext.combinedClosedCollapse)
        FragmentContext.closedLeftUnitorInv).symm
    have h' :
        Hom.comp
            (DayTensor.map (Hom.id (FragmentContext.combined [] []))
              (Hom.comp f FragmentContext.combinedClosedCollapse))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv) =
          DayTensor.map FragmentContext.closedLeftUnitorInv
            (Hom.comp (Hom.comp f FragmentContext.combinedClosedCollapse)
              FragmentContext.closedLeftUnitorInv) := by
      simpa only [Hom.id_comp] using h
    refine h'.trans ?_
    have hf :
        Hom.comp (Hom.comp f FragmentContext.combinedClosedCollapse)
            FragmentContext.closedLeftUnitorInv =
          f := by
      rw [← Hom.comp_assoc, FragmentContext.combinedClosedCollapse_leftUnitorInv,
        Hom.comp_id]
    exact congrArg _ hf
  have hcancel :
      Hom.comp (DayTensor.rightUnitor dayTensorUnit)
          FragmentContext.closedLeftUnitorInv =
        Hom.id dayTensorUnit := by
    rw [FragmentContext.closedLeftUnitorInv_eq]
    exact FragmentContext.rightUnitor_comp_leftUnitorInv_unit
  have hcollapse :
      FragmentContext.combinedClosedCollapse =
        DayTensor.leftUnitor dayTensorUnit := by
    change Hom.comp (DayTensor.leftUnitor dayTensorUnit)
        (DayTensor.map (Hom.id dayTensorUnit) (Hom.id dayTensorUnit)) =
      DayTensor.leftUnitor dayTensorUnit
    rw [DayTensor.map_id, Hom.comp_id]
  refine Eq.trans (congrArg _ hsplit) ?_
  refine Eq.trans ((Hom.comp_assoc _ _ _).symm) ?_
  -- Goal: λ ∘ (map ρ id ∘ map λinv f) = f ∘ collapse
  have hmap :
      Hom.comp
          (DayTensor.map (DayTensor.rightUnitor dayTensorUnit) (Hom.id A))
          (DayTensor.map FragmentContext.closedLeftUnitorInv f) =
        DayTensor.map (Hom.id dayTensorUnit) f := by
    have h :=
      (DayTensor.map_comp (DayTensor.rightUnitor dayTensorUnit)
        FragmentContext.closedLeftUnitorInv (Hom.id A) f).symm
    -- map ρ id ∘ map λinv f = map (ρ∘λinv) (id∘f)
    refine h.trans ?_
    rw [hcancel, Hom.id_comp]
  refine Eq.trans (congrArg (Hom.comp (DayTensor.leftUnitor A)) hmap) ?_
  -- Goal: λ ∘ map id f = f ∘ collapse
  refine Eq.trans (leftUnitor_natural f) ?_
  exact congrArg (Hom.comp f) hcollapse.symm

/-- Fragment packaging: identity body ∘ move ∘ map id arg ∘ split. -/
theorem closed_identity_move_cancel_frag {A : Module}
    (f : Hom dayTensorUnit A) :
    Hom.comp
      (Hom.comp
        (Hom.comp (DayTensor.leftUnitor A)
          (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.rightUnitor A)))
        (FragmentContext.moveArgumentIntoLinear dayTensorUnit dayTensorUnit A))
      (Hom.comp
        (DayTensor.map (Hom.id (FragmentContext.combined [] []))
          (FragmentContext.closedPoint f))
        (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) =
    FragmentContext.closedPoint f := by
  rw [FragmentContext.identity_body_move_eq]
  have hO :
      FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil =
        DayTensor.map FragmentContext.closedLeftUnitorInv
          FragmentContext.closedLeftUnitorInv := by
    rw [FragmentContext.combinedOSplit_nil]; rfl
  rw [hO, FragmentContext.closedPoint]
  exact closed_identity_move_cancel f

/-- Helper: FO Day β plus move/split cancellation for a closed identity body. -/
private theorem fragment_betaL_id_closed_aux {A : Ty}
    (hA : Ty.FirstOrder A)
    (body : Hom
      (dayTensor dayTensorUnit
        (dayTensor (fragmentModule A) dayTensorUnit))
      (fragmentModule A))
    (f : Hom dayTensorUnit (fragmentModule A))
    (hbody :
      body =
        Hom.comp (DayTensor.leftUnitor (fragmentModule A))
          (DayTensor.map (Hom.id dayTensorUnit)
            (DayTensor.rightUnitor (fragmentModule A)))) :
    Hom.comp (FragmentContext.evalFragmentFirstOrder hA _)
      (Hom.comp
        (DayTensor.map (FragmentContext.abstractLinear hA body)
          (FragmentContext.closedPoint f))
        (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) =
      FragmentContext.closedPoint f := by
  let Φ : Hom (FragmentContext.combined [] [])
      (internalHomRepresentable A.hilbertDim (fragmentModule A)) :=
    FragmentContext.abstractLinear hA body
  have hΦ : Φ = FragmentContext.abstractLinear hA body := rfl
  have hfactor :
      DayTensor.map Φ (FragmentContext.closedPoint f) =
        Hom.comp (DayTensor.map Φ (Hom.id (fragmentModule A)))
          (DayTensor.map (Hom.id (FragmentContext.combined [] []))
            (FragmentContext.closedPoint f)) := by
    simpa only [Hom.comp_id, Hom.id_comp] using
      DayTensor.map_comp Φ (Hom.id (FragmentContext.combined [] []))
        (Hom.id (fragmentModule A)) (FragmentContext.closedPoint f)
  -- Rewrite the goal to use Φ
  change Hom.comp (FragmentContext.evalFragmentFirstOrder hA _)
      (Hom.comp (DayTensor.map Φ (FragmentContext.closedPoint f))
        (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) =
    FragmentContext.closedPoint f
  rw [hfactor]
  -- eval ∘ ((map Φ id ∘ map id arg) ∘ split)
  have hreassoc :
      Hom.comp (FragmentContext.evalFragmentFirstOrder hA _)
          (Hom.comp
            (Hom.comp (DayTensor.map Φ (Hom.id (fragmentModule A)))
              (DayTensor.map (Hom.id (FragmentContext.combined [] []))
                (FragmentContext.closedPoint f)))
            (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) =
        Hom.comp
          (Hom.comp (FragmentContext.evalFragmentFirstOrder hA _)
            (DayTensor.map Φ (Hom.id (fragmentModule A))))
          (Hom.comp
            (DayTensor.map (Hom.id (FragmentContext.combined [] []))
              (FragmentContext.closedPoint f))
            (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) := by
    rw [Hom.comp_assoc, Hom.comp_assoc, ← Hom.comp_assoc]
  rw [hreassoc]
  -- FO β: eval ∘ map Φ id = body ∘ move, after unfolding Φ
  have hβ :
      Hom.comp (FragmentContext.evalFragmentFirstOrder hA _)
          (DayTensor.map Φ (Hom.id (fragmentModule A))) =
        Hom.comp body
          (FragmentContext.moveArgumentIntoLinear dayTensorUnit dayTensorUnit
            (fragmentModule A)) := by
    rw [hΦ]
    exact FragmentContext.evalFragmentFirstOrder_abstractLinear hA body
  rw [hβ, hbody]
  exact closed_identity_move_cancel_frag f

/-- Closed linear identity β at unit: `app (λx. x) unit = unit`. -/
theorem fragment_betaL_id_unit :
    FragCert.denote fragCert_appL_id_unit =
      FragCert.denote FragCert.closed_unit_cert := by
  have harg :
      FragCert.denote FragCert.closed_unit_cert =
        FragmentContext.closedPoint routeAFragmentModel.unitIntro :=
    fragment_step_denote_sound_unit FragCert.closed_unit_cert
  rw [fragment_betaL_id_unit_spine, harg]
  exact fragment_betaL_id_closed_aux Ty.FirstOrder.unit _
    routeAFragmentModel.unitIntro fragCert_varL0_unit_denote_simple

/-- Closed linear identity β at bit: `app (λx. x) (bitLit b) = bitLit b`. -/
theorem fragment_betaL_id_bit (b : Bool) :
    FragCert.denote (fragCert_appL_id_bit b) =
      FragCert.denote (FragCert.closed_bitLit_cert b) := by
  have harg :
      FragCert.denote (FragCert.closed_bitLit_cert b) =
        FragmentContext.closedPoint (bitLitHom b) :=
    FragCert.closed_bitLit_denote_eq b
  rw [fragment_betaL_id_bit_spine, harg]
  exact fragment_betaL_id_closed_aux Ty.FirstOrder.bit _
    (bitLitHom b) fragCert_varL0_bit_denote_simple


/-- Unrestricted identity body unfolds through structural lookup. -/
theorem fragCert_varU0_bit_denote :
    FragCert.denote fragCert_varU0_bit =
      Hom.comp (DayTensor.rightUnitor (fragmentModule .bit))
        (DayTensor.map
          (Hom.comp (DayTensor.rightUnitor (fragmentModule .bit))
            (DayTensor.map classicalBitInclusion (Hom.id dayTensorUnit)))
          (Hom.id dayTensorUnit)) := by
  simp only [fragCert_varU0_bit, FragCert.denote_varU_eq,
    FragmentContext.combinedLookupUnrestricted,
    FragmentContext.unrestrictedLookup,
    FragmentContext.unrestrictedLookupLists_zero_bit]
  rfl

/-- F4b foothold: substituting a value for linear `var 0` is the value
(definitionally on terms). -/
theorem substLin_varL0 (V : Term) :
    Term.substLin 0 V (.var .lin 0) = V := by
  simp [Term.substLin, Term.shiftLin_zero]

/-- F4b: denotation of the closed linear identity redex equals the argument
(packaged from the identity β theorems). -/
theorem fragment_substLin_id_denote_unit :
    FragCert.denote fragCert_appL_id_unit =
      FragCert.denote FragCert.closed_unit_cert :=
  fragment_betaL_id_unit

theorem fragment_substLin_id_denote_bit (b : Bool) :
    FragCert.denote (fragCert_appL_id_bit b) =
      FragCert.denote (FragCert.closed_bitLit_cert b) :=
  fragment_betaL_id_bit b

/-- F4b: substituting at unrestricted `var 0` returns the value. -/
theorem substUnres_varU0 (V : Term) :
    Term.substUnres 0 V (.var .unres 0) = V := by
  simp [Term.substUnres, shiftUnres_zero]

end QLambda.Linear
