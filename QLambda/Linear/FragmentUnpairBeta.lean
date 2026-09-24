/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentIdentityBeta

/-!
# Closed first-order `unpair` β on `FragCert.denote`

Day coherence lemmas (unit braiding, inverse associator naturality, the
inverse unit triangle) plus cocommutativity/coassociativity of the closed
context split, combined into the named redex=contractum theorem
`fragment_unpair_beta`:

    unpair (pair M N) K  ⟶  app (app K M) N

for closed first-order `M`, `N` and a closed curried continuation `K`.

The same Day-β spine also widens linear and unrestricted application β from
the closed identity instances to arbitrary open contexts
(`fragment_betaL_open_move`, `fragment_betaU_bit_open_move`).
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf

/-! ## Day coherence used by closed `unpair` β -/

/-- The Day braiding on `1 ⊗ 1` is the identity. -/
theorem dayBraiding_unit_unit :
    DayTensor.braiding dayTensorUnit dayTensorUnit =
      Hom.id (dayTensor dayTensorUnit dayTensorUnit) := by
  have hρσ :
      Hom.comp (DayTensor.rightUnitor dayTensorUnit)
          (DayTensor.braiding dayTensorUnit dayTensorUnit) =
        DayTensor.rightUnitor dayTensorUnit := by
    rw [FragmentContext.rightUnitor_comp_braiding,
      leftUnitor_unit_eq_rightUnitor_unit]
  have hinv :
      Hom.comp (DayTensor.rightUnitorInv dayTensorUnit)
          (DayTensor.rightUnitor dayTensorUnit) =
        Hom.id (dayTensor dayTensorUnit dayTensorUnit) :=
    (DayTensor.rightUnitorIso dayTensorUnit).inv_hom
  calc DayTensor.braiding dayTensorUnit dayTensorUnit
      = Hom.comp (DayTensor.rightUnitorInv dayTensorUnit)
          (Hom.comp (DayTensor.rightUnitor dayTensorUnit)
            (DayTensor.braiding dayTensorUnit dayTensorUnit)) := by
        rw [Hom.comp_assoc, hinv, Hom.id_comp]
    _ = Hom.comp (DayTensor.rightUnitorInv dayTensorUnit)
          (DayTensor.rightUnitor dayTensorUnit) := by rw [hρσ]
    _ = Hom.id (dayTensor dayTensorUnit dayTensorUnit) := hinv

/-- Inverse associator naturality (dual of `DayTensor.associator_naturality`). -/
theorem dayAssociatorInv_naturality {M M' N N' P P' : Module}
    (f : Hom M M') (g : Hom N N') (h : Hom P P') :
    Hom.comp (DayTensor.associatorInv M' N' P')
        (DayTensor.map f (DayTensor.map g h)) =
      Hom.comp (DayTensor.map (DayTensor.map f g) h)
        (DayTensor.associatorInv M N P) := by
  have hkey :
      Hom.comp (DayTensor.associatorInv M' N' P')
          (Hom.comp (DayTensor.map f (DayTensor.map g h))
            (DayTensor.associator M N P)) =
        DayTensor.map (DayTensor.map f g) h := by
    rw [← DayTensor.associator_naturality, Hom.comp_assoc,
      DayTensor.associator_inv_hom, Hom.id_comp]
  rw [← hkey]
  show Hom.comp (DayTensor.associatorInv M' N' P')
      (DayTensor.map f (DayTensor.map g h)) =
    Hom.comp (DayTensor.associatorInv M' N' P')
      (Hom.comp (DayTensor.map f (DayTensor.map g h))
        (Hom.comp (DayTensor.associator M N P)
          (DayTensor.associatorInv M N P)))
  rw [DayTensor.associator_hom_inv, Hom.comp_id]

/-- Unit triangle in inverse form: `α⁻¹ ∘ (id ⊗ λ⁻¹) = λ⁻¹ ⊗ id`. -/
theorem dayAssociatorInv_leftUnitorInv (N : Module) :
    Hom.comp (DayTensor.associatorInv dayTensorUnit dayTensorUnit N)
        (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitorInv N)) =
      DayTensor.map (DayTensor.leftUnitorInv dayTensorUnit) (Hom.id N) := by
  have htri :
      Hom.comp
          (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor N))
          (DayTensor.associator dayTensorUnit dayTensorUnit N) =
        DayTensor.map (DayTensor.leftUnitor dayTensorUnit) (Hom.id N) := by
    rw [DayTensor.triangle, leftUnitor_unit_eq_rightUnitor_unit]
  have hcancel :
      Hom.comp (DayTensor.map (DayTensor.leftUnitor dayTensorUnit) (Hom.id N))
          (Hom.comp (DayTensor.associatorInv dayTensorUnit dayTensorUnit N)
            (DayTensor.map (Hom.id dayTensorUnit)
              (DayTensor.leftUnitorInv N))) =
        Hom.id (dayTensor dayTensorUnit N) := by
    rw [← htri]
    show Hom.comp
        (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor N))
        (Hom.comp
          (Hom.comp (DayTensor.associator dayTensorUnit dayTensorUnit N)
            (DayTensor.associatorInv dayTensorUnit dayTensorUnit N))
          (DayTensor.map (Hom.id dayTensorUnit)
            (DayTensor.leftUnitorInv N))) =
      Hom.id (dayTensor dayTensorUnit N)
    rw [DayTensor.associator_hom_inv, Hom.id_comp, ← DayTensor.map_comp,
      DayTensor.leftUnitor_hom_inv, Hom.id_comp, DayTensor.map_id]
  have hmapinv :
      Hom.comp
          (DayTensor.map (DayTensor.leftUnitorInv dayTensorUnit) (Hom.id N))
          (DayTensor.map (DayTensor.leftUnitor dayTensorUnit) (Hom.id N)) =
        Hom.id (dayTensor (dayTensor dayTensorUnit dayTensorUnit) N) := by
    have hlu :
        Hom.comp (DayTensor.leftUnitorInv dayTensorUnit)
            (DayTensor.leftUnitor dayTensorUnit) =
          Hom.id (dayTensor dayTensorUnit dayTensorUnit) :=
      (DayTensor.leftUnitorIso dayTensorUnit).inv_hom
    rw [← DayTensor.map_comp, hlu, Hom.id_comp, DayTensor.map_id]
  calc Hom.comp (DayTensor.associatorInv dayTensorUnit dayTensorUnit N)
          (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitorInv N))
      = Hom.comp
          (DayTensor.map (DayTensor.leftUnitorInv dayTensorUnit) (Hom.id N))
          (Hom.comp
            (DayTensor.map (DayTensor.leftUnitor dayTensorUnit) (Hom.id N))
            (Hom.comp (DayTensor.associatorInv dayTensorUnit dayTensorUnit N)
              (DayTensor.map (Hom.id dayTensorUnit)
                (DayTensor.leftUnitorInv N)))) := by
        rw [Hom.comp_assoc, hmapinv, Hom.id_comp]
    _ = Hom.comp
          (DayTensor.map (DayTensor.leftUnitorInv dayTensorUnit) (Hom.id N))
          (Hom.id (dayTensor dayTensorUnit N)) := by rw [hcancel]
    _ = DayTensor.map (DayTensor.leftUnitorInv dayTensorUnit) (Hom.id N) :=
        Hom.comp_id _

/-- Coassociativity of a unit-generated diagonal on `1 ⊗ 1`. -/
private theorem closedSplit_coassoc_aux
    (u : Hom dayTensorUnit (dayTensor dayTensorUnit dayTensorUnit))
    (htri :
      Hom.comp
          (DayTensor.associatorInv dayTensorUnit dayTensorUnit dayTensorUnit)
          (DayTensor.map (Hom.id dayTensorUnit) u) =
        DayTensor.map u (Hom.id dayTensorUnit)) :
    Hom.comp
        (DayTensor.associatorInv (dayTensor dayTensorUnit dayTensorUnit)
          (dayTensor dayTensorUnit dayTensorUnit)
          (dayTensor dayTensorUnit dayTensorUnit))
        (Hom.comp
          (DayTensor.map (Hom.id (dayTensor dayTensorUnit dayTensorUnit))
            (DayTensor.map u u))
          (DayTensor.map u u)) =
      Hom.comp
        (DayTensor.map (DayTensor.map u u)
          (Hom.id (dayTensor dayTensorUnit dayTensorUnit)))
        (DayTensor.map u u) := by
  have hL :
      Hom.comp
          (DayTensor.map (Hom.id (dayTensor dayTensorUnit dayTensorUnit))
            (DayTensor.map u u))
          (DayTensor.map u u) =
        Hom.comp (DayTensor.map u (DayTensor.map u u))
          (DayTensor.map (Hom.id dayTensorUnit) u) := by
    simp only [← DayTensor.map_comp, Hom.id_comp, Hom.comp_id]
  rw [hL]
  calc Hom.comp
          (DayTensor.associatorInv (dayTensor dayTensorUnit dayTensorUnit)
            (dayTensor dayTensorUnit dayTensorUnit)
            (dayTensor dayTensorUnit dayTensorUnit))
          (Hom.comp (DayTensor.map u (DayTensor.map u u))
            (DayTensor.map (Hom.id dayTensorUnit) u))
      = Hom.comp
          (Hom.comp
            (DayTensor.associatorInv (dayTensor dayTensorUnit dayTensorUnit)
              (dayTensor dayTensorUnit dayTensorUnit)
              (dayTensor dayTensorUnit dayTensorUnit))
            (DayTensor.map u (DayTensor.map u u)))
          (DayTensor.map (Hom.id dayTensorUnit) u) := by
        simp only [Hom.comp_assoc]
    _ = Hom.comp
          (Hom.comp (DayTensor.map (DayTensor.map u u) u)
            (DayTensor.associatorInv dayTensorUnit dayTensorUnit
              dayTensorUnit))
          (DayTensor.map (Hom.id dayTensorUnit) u) := by
        rw [dayAssociatorInv_naturality]
    _ = Hom.comp (DayTensor.map (DayTensor.map u u) u)
          (Hom.comp
            (DayTensor.associatorInv dayTensorUnit dayTensorUnit dayTensorUnit)
            (DayTensor.map (Hom.id dayTensorUnit) u)) := by
        simp only [Hom.comp_assoc]
    _ = Hom.comp (DayTensor.map (DayTensor.map u u) u)
          (DayTensor.map u (Hom.id dayTensorUnit)) := by rw [htri]
    _ = Hom.comp
          (DayTensor.map (DayTensor.map u u)
            (Hom.id (dayTensor dayTensorUnit dayTensorUnit)))
          (DayTensor.map u u) := by
        simp only [← DayTensor.map_comp, Hom.id_comp, Hom.comp_id]

/-- The closed context split is cocommutative. -/
theorem combinedOSplit_nil_braiding :
    Hom.comp
        (DayTensor.braiding (FragmentContext.combined [] [])
          (FragmentContext.combined [] []))
        (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil) =
      FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil := by
  have h :
      Hom.comp
          (DayTensor.braiding (dayTensor dayTensorUnit dayTensorUnit)
            (dayTensor dayTensorUnit dayTensorUnit))
          (DayTensor.map (DayTensor.leftUnitorInv dayTensorUnit)
            (DayTensor.leftUnitorInv dayTensorUnit)) =
        DayTensor.map (DayTensor.leftUnitorInv dayTensorUnit)
          (DayTensor.leftUnitorInv dayTensorUnit) := by
    rw [DayTensor.braiding_naturality, dayBraiding_unit_unit, Hom.comp_id]
  exact h

/-- The closed context split is coassociative. -/
theorem combinedOSplit_nil_coassoc :
    Hom.comp
        (DayTensor.associatorInv (FragmentContext.combined [] [])
          (FragmentContext.combined [] []) (FragmentContext.combined [] []))
        (Hom.comp
          (DayTensor.map (Hom.id (FragmentContext.combined [] []))
            (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil))
          (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) =
      Hom.comp
        (DayTensor.map
          (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)
          (Hom.id (FragmentContext.combined [] [])))
        (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil) :=
  closedSplit_coassoc_aux (DayTensor.leftUnitorInv dayTensorUnit)
    (dayAssociatorInv_leftUnitorInv dayTensorUnit)

/-- First-order pair elimination inverts pair introduction. -/
theorem tensorElim_comp_tensorIntro {A B : Ty}
    (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B) :
    Hom.comp (FragmentContext.tensorElim hA hB)
        (FragmentContext.tensorIntro hA hB) =
      Hom.id (dayTensor (fragmentModule A) (fragmentModule B)) := by
  have hstep1 :
      Hom.comp (FragmentContext.tensorElim hA hB)
          (FragmentContext.tensorIntro hA hB) =
        Hom.comp
          (DayTensor.map (FragmentContext.firstOrderFromRep hA)
            (FragmentContext.firstOrderFromRep hB))
          (Hom.comp
            (Hom.comp (dayTensorRepresentableIso A.hilbertDim B.hilbertDim).inv
              (dayTensorRepresentableIso A.hilbertDim B.hilbertDim).hom)
            (DayTensor.map (FragmentContext.firstOrderToRep hA)
              (FragmentContext.firstOrderToRep hB))) :=
    congrArg
      (fun g =>
        Hom.comp
          (DayTensor.map (FragmentContext.firstOrderFromRep hA)
            (FragmentContext.firstOrderFromRep hB))
          (Hom.comp
            (Hom.comp
              (dayTensorRepresentableIso A.hilbertDim B.hilbertDim).inv
              (Hom.comp g
                (dayTensorRepresentableIso A.hilbertDim B.hilbertDim).hom))
            (DayTensor.map (FragmentContext.firstOrderToRep hA)
              (FragmentContext.firstOrderToRep hB))))
      (FragmentContext.firstOrderToRep_comp_fromRep
        (Ty.FirstOrder.tensor hA hB))
  have hstep2 :
      Hom.comp
          (DayTensor.map (FragmentContext.firstOrderFromRep hA)
            (FragmentContext.firstOrderFromRep hB))
          (Hom.comp
            (Hom.comp (dayTensorRepresentableIso A.hilbertDim B.hilbertDim).inv
              (dayTensorRepresentableIso A.hilbertDim B.hilbertDim).hom)
            (DayTensor.map (FragmentContext.firstOrderToRep hA)
              (FragmentContext.firstOrderToRep hB))) =
        Hom.comp
          (DayTensor.map (FragmentContext.firstOrderFromRep hA)
            (FragmentContext.firstOrderFromRep hB))
          (DayTensor.map (FragmentContext.firstOrderToRep hA)
            (FragmentContext.firstOrderToRep hB)) :=
    congrArg
      (fun g =>
        Hom.comp
          (DayTensor.map (FragmentContext.firstOrderFromRep hA)
            (FragmentContext.firstOrderFromRep hB))
          (Hom.comp g
            (DayTensor.map (FragmentContext.firstOrderToRep hA)
              (FragmentContext.firstOrderToRep hB))))
      (dayTensorRepresentableIso A.hilbertDim B.hilbertDim).inv_hom
  have hstep3 :
      Hom.comp
          (DayTensor.map (FragmentContext.firstOrderFromRep hA)
            (FragmentContext.firstOrderFromRep hB))
          (DayTensor.map (FragmentContext.firstOrderToRep hA)
            (FragmentContext.firstOrderToRep hB)) =
        Hom.id (dayTensor (fragmentModule A) (fragmentModule B)) := by
    rw [← DayTensor.map_comp, FragmentContext.firstOrderFromRep_comp_toRep,
      FragmentContext.firstOrderFromRep_comp_toRep, DayTensor.map_id]
  exact hstep1.trans (hstep2.trans hstep3)

/-! ## F4a: closed first-order `unpair` β on `FragCert.denote` -/

/-- Symmetric-monoidal core of closed `unpair` β: unpacking a first-order pair
and feeding it to a curried continuation agrees with two applications. -/
private theorem unpair_beta_aux
    {U FA FB FAB H HB FC : Module}
    (S : Hom U (dayTensor U U))
    (hSym : Hom.comp (DayTensor.braiding U U) S = S)
    (hAssoc :
      Hom.comp (DayTensor.associatorInv U U U)
          (Hom.comp (DayTensor.map (Hom.id U) S) S) =
        Hom.comp (DayTensor.map S (Hom.id U)) S)
    (TI : Hom (dayTensor FA FB) FAB) (TE : Hom FAB (dayTensor FA FB))
    (hTE : Hom.comp TE TI = Hom.id (dayTensor FA FB))
    (evA : Hom (dayTensor H FA) HB) (evB : Hom (dayTensor HB FB) FC)
    (dM : Hom U FA) (dN : Hom U FB) (dK : Hom U H) :
    Hom.comp
        (Hom.comp evB
          (Hom.comp (DayTensor.map evA (Hom.id FB))
            (Hom.comp (DayTensor.associatorInv H FA FB)
              (Hom.comp (DayTensor.map (Hom.id H) TE)
                (DayTensor.braiding FAB H)))))
        (Hom.comp
          (DayTensor.map
            (Hom.comp TI (Hom.comp (DayTensor.map dM dN) S)) dK)
          S) =
      Hom.comp evB
        (Hom.comp
          (DayTensor.map (Hom.comp evA (Hom.comp (DayTensor.map dK dM) S))
            dN)
          S) := by
  have step1 :
      Hom.comp (DayTensor.braiding FAB H)
          (Hom.comp
            (DayTensor.map
              (Hom.comp TI (Hom.comp (DayTensor.map dM dN) S)) dK)
            S) =
        Hom.comp
          (DayTensor.map dK
            (Hom.comp TI (Hom.comp (DayTensor.map dM dN) S)))
          S := by
    rw [Hom.comp_assoc, DayTensor.braiding_naturality, ← Hom.comp_assoc, hSym]
  have step2 :
      Hom.comp (DayTensor.map (Hom.id H) TE)
          (Hom.comp
            (DayTensor.map dK
              (Hom.comp TI (Hom.comp (DayTensor.map dM dN) S)))
            S) =
        Hom.comp (DayTensor.map dK (Hom.comp (DayTensor.map dM dN) S)) S := by
    rw [Hom.comp_assoc, ← DayTensor.map_comp, Hom.id_comp,
      Hom.comp_assoc TE TI (Hom.comp (DayTensor.map dM dN) S), hTE,
      Hom.id_comp]
  have step3 :
      Hom.comp (DayTensor.associatorInv H FA FB)
          (Hom.comp (DayTensor.map dK (Hom.comp (DayTensor.map dM dN) S)) S) =
        Hom.comp (DayTensor.map (DayTensor.map dK dM) dN)
          (Hom.comp (DayTensor.map S (Hom.id U)) S) := by
    have hfac :
        DayTensor.map dK (Hom.comp (DayTensor.map dM dN) S) =
          Hom.comp (DayTensor.map dK (DayTensor.map dM dN))
            (DayTensor.map (Hom.id U) S) := by
      simp only [← DayTensor.map_comp, Hom.comp_id]
    rw [hfac]
    calc Hom.comp (DayTensor.associatorInv H FA FB)
            (Hom.comp
              (Hom.comp (DayTensor.map dK (DayTensor.map dM dN))
                (DayTensor.map (Hom.id U) S))
              S)
        = Hom.comp
            (Hom.comp (DayTensor.associatorInv H FA FB)
              (DayTensor.map dK (DayTensor.map dM dN)))
            (Hom.comp (DayTensor.map (Hom.id U) S) S) := by
          simp only [Hom.comp_assoc]
      _ = Hom.comp
            (Hom.comp (DayTensor.map (DayTensor.map dK dM) dN)
              (DayTensor.associatorInv U U U))
            (Hom.comp (DayTensor.map (Hom.id U) S) S) := by
          rw [dayAssociatorInv_naturality]
      _ = Hom.comp (DayTensor.map (DayTensor.map dK dM) dN)
            (Hom.comp (DayTensor.associatorInv U U U)
              (Hom.comp (DayTensor.map (Hom.id U) S) S)) := by
          simp only [Hom.comp_assoc]
      _ = Hom.comp (DayTensor.map (DayTensor.map dK dM) dN)
            (Hom.comp (DayTensor.map S (Hom.id U)) S) := by rw [hAssoc]
  have step4 :
      Hom.comp (DayTensor.map evA (Hom.id FB))
          (Hom.comp (DayTensor.map (DayTensor.map dK dM) dN)
            (Hom.comp (DayTensor.map S (Hom.id U)) S)) =
        Hom.comp
          (DayTensor.map (Hom.comp evA (Hom.comp (DayTensor.map dK dM) S))
            dN)
          S := by
    calc Hom.comp (DayTensor.map evA (Hom.id FB))
            (Hom.comp (DayTensor.map (DayTensor.map dK dM) dN)
              (Hom.comp (DayTensor.map S (Hom.id U)) S))
        = Hom.comp
            (Hom.comp
              (Hom.comp (DayTensor.map evA (Hom.id FB))
                (DayTensor.map (DayTensor.map dK dM) dN))
              (DayTensor.map S (Hom.id U)))
            S := by
          simp only [Hom.comp_assoc]
      _ = Hom.comp
            (DayTensor.map
              (Hom.comp (Hom.comp evA (DayTensor.map dK dM)) S)
              (Hom.comp (Hom.comp (Hom.id FB) dN) (Hom.id U))) S := by
          simp only [← DayTensor.map_comp]
      _ = Hom.comp
            (DayTensor.map (Hom.comp evA (Hom.comp (DayTensor.map dK dM) S))
              dN)
            S := by
          simp only [Hom.comp_assoc, Hom.comp_id, Hom.id_comp]
  have hgroup :
      Hom.comp
          (Hom.comp evB
            (Hom.comp (DayTensor.map evA (Hom.id FB))
              (Hom.comp (DayTensor.associatorInv H FA FB)
                (Hom.comp (DayTensor.map (Hom.id H) TE)
                  (DayTensor.braiding FAB H)))))
          (Hom.comp
            (DayTensor.map
              (Hom.comp TI (Hom.comp (DayTensor.map dM dN) S)) dK)
            S) =
        Hom.comp evB
          (Hom.comp (DayTensor.map evA (Hom.id FB))
            (Hom.comp (DayTensor.associatorInv H FA FB)
              (Hom.comp (DayTensor.map (Hom.id H) TE)
                (Hom.comp (DayTensor.braiding FAB H)
                  (Hom.comp
                    (DayTensor.map
                      (Hom.comp TI (Hom.comp (DayTensor.map dM dN) S)) dK)
                    S))))) := by
    simp only [Hom.comp_assoc]
  rw [hgroup, step1, step2, step3, step4]

/-- **F4a closed `unpair` β**: for closed first-order components the redex
`unpair (pair M N) K` and its contractum `app (app K M) N` have equal
`FragCert.denote`. -/
theorem fragment_unpair_beta {A B C : Ty} {M N K : Term}
    (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B) (hC : Ty.SemanticFragment C)
    (cM : FragCert.Closed M A) (cN : FragCert.Closed N B)
    (cK : FragCert.Closed K (.arrow .lin A (.arrow .lin B C))) :
    FragCert.denote
        (.unpair CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil hA hB hC
          (.pair CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil hA hB cM cN)
          cK) =
      FragCert.denote
        (.appL CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil hB hC
          (.appL CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil hA
            (Ty.SemanticFragment.arrowLin hB hC) cK cM)
          cN) :=
  unpair_beta_aux (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)
    combinedOSplit_nil_braiding combinedOSplit_nil_coassoc
    (FragmentContext.tensorIntro hA hB) (FragmentContext.tensorElim hA hB)
    (tensorElim_comp_tensorIntro hA hB)
    (FragmentContext.evalFragmentFirstOrder hA _)
    (FragmentContext.evalFragmentFirstOrder hB _)
    (FragCert.denote cM) (FragCert.denote cN) (FragCert.denote cK)

/-- Closed `unpair` β at `unit ⊗ unit`. -/
theorem fragment_unpair_beta_unit {K : Term}
    (cK : FragCert.Closed K
      (.arrow .lin .unit (.arrow .lin .unit .unit))) :
    FragCert.denote
        (.unpair CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
          Ty.FirstOrder.unit Ty.FirstOrder.unit Ty.SemanticFragment.unit
          (.pair CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
            Ty.FirstOrder.unit Ty.FirstOrder.unit
            FragCert.closed_unit_cert FragCert.closed_unit_cert)
          cK) =
      FragCert.denote
        (.appL CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
          Ty.FirstOrder.unit Ty.SemanticFragment.unit
          (.appL CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
            Ty.FirstOrder.unit
            (Ty.SemanticFragment.arrowLin Ty.FirstOrder.unit
              Ty.SemanticFragment.unit)
            cK FragCert.closed_unit_cert)
          FragCert.closed_unit_cert) :=
  fragment_unpair_beta Ty.FirstOrder.unit Ty.FirstOrder.unit
    Ty.SemanticFragment.unit FragCert.closed_unit_cert
    FragCert.closed_unit_cert cK

/-- Closed `unpair` β at `bit ⊗ bit`. -/
theorem fragment_unpair_beta_bit {K : Term} (b₁ b₂ : Bool)
    (cK : FragCert.Closed K (.arrow .lin .bit (.arrow .lin .bit .bit))) :
    FragCert.denote
        (.unpair CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
          Ty.FirstOrder.bit Ty.FirstOrder.bit Ty.SemanticFragment.bit
          (.pair CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
            Ty.FirstOrder.bit Ty.FirstOrder.bit
            (FragCert.closed_bitLit_cert b₁) (FragCert.closed_bitLit_cert b₂))
          cK) =
      FragCert.denote
        (.appL CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
          Ty.FirstOrder.bit Ty.SemanticFragment.bit
          (.appL CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
            Ty.FirstOrder.bit
            (Ty.SemanticFragment.arrowLin Ty.FirstOrder.bit
              Ty.SemanticFragment.bit)
            cK (FragCert.closed_bitLit_cert b₁))
          (FragCert.closed_bitLit_cert b₂)) :=
  fragment_unpair_beta Ty.FirstOrder.bit Ty.FirstOrder.bit
    Ty.SemanticFragment.bit (FragCert.closed_bitLit_cert b₁)
    (FragCert.closed_bitLit_cert b₂) cK

/-! ## Open-context linear/unrestricted β on `FragCert.denote` -/

/-- Open-context linear β: `app (λx. M) X` denotes as the body precomposed
with the argument move, for arbitrary contexts and certificates. -/
theorem fragment_betaL_open_move {Γ Δ Δ₁ Δ₂ A B M X}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hAd : Ty.Admissible A) (hFO : Ty.FirstOrder A)
    (hB : Ty.SemanticFragment B) (hL₁ : CtxLAllSomeFragment Δ₁)
    (cBody : FragCert Γ (some A :: Δ₁) M B) (cX : FragCert Γ Δ₂ X A) :
    FragCert.denote
        (.appL hΓ hΔ hs hFO hB (.lamL hΓ hL₁ hAd hFO hB cBody) cX) =
      Hom.comp (FragCert.denote cBody)
        (Hom.comp
          (FragmentContext.moveArgumentIntoLinear
            (FragmentContext.unrestricted Γ) (FragmentContext.linear Δ₁)
            (fragmentModule A))
          (Hom.comp
            (DayTensor.map
              (Hom.id
                (dayTensor (FragmentContext.unrestricted Γ)
                  (FragmentContext.linear Δ₁)))
              (FragCert.denote cX))
            (FragmentContext.combinedOSplit hΓ hs))) := by
  have hfactor :
      DayTensor.map
          (FragmentContext.abstractLinear hFO (FragCert.denote cBody))
          (FragCert.denote cX) =
        Hom.comp
          (DayTensor.map
            (FragmentContext.abstractLinear hFO (FragCert.denote cBody))
            (Hom.id (fragmentModule A)))
          (DayTensor.map
            (Hom.id
              (dayTensor (FragmentContext.unrestricted Γ)
                (FragmentContext.linear Δ₁)))
            (FragCert.denote cX)) := by
    simpa only [Hom.comp_id, Hom.id_comp] using
      DayTensor.map_comp
        (FragmentContext.abstractLinear hFO (FragCert.denote cBody))
        (Hom.id
          (dayTensor (FragmentContext.unrestricted Γ)
            (FragmentContext.linear Δ₁)))
        (Hom.id (fragmentModule A)) (FragCert.denote cX)
  have hβ :
      Hom.comp (FragmentContext.evalFragmentFirstOrder hFO (fragmentModule B))
          (DayTensor.map
            (FragmentContext.abstractLinear hFO (FragCert.denote cBody))
            (Hom.id (fragmentModule A))) =
        Hom.comp (FragCert.denote cBody)
          (FragmentContext.moveArgumentIntoLinear
            (FragmentContext.unrestricted Γ) (FragmentContext.linear Δ₁)
            (fragmentModule A)) :=
    FragmentContext.evalFragmentFirstOrder_abstractLinear hFO
      (FragCert.denote cBody)
  refine Eq.trans (fragment_subst_lin_spine hΓ hΔ hs hAd hFO hB hL₁ cBody cX)
    ?_
  refine Eq.trans
    (congrArg
      (fun g =>
        Hom.comp
          (FragmentContext.evalFragmentFirstOrder hFO (fragmentModule B))
          (Hom.comp g (FragmentContext.combinedOSplit hΓ hs)))
      hfactor) ?_
  exact congrArg
    (fun g =>
      Hom.comp g
        (Hom.comp
          (DayTensor.map
            (Hom.id
              (dayTensor (FragmentContext.unrestricted Γ)
                (FragmentContext.linear Δ₁)))
            (FragCert.denote cX))
          (FragmentContext.combinedOSplit hΓ hs)))
    hβ

/-- Open-context unrestricted bit β: `app (λx. M) X` denotes as the body
precomposed with the unrestricted argument move and classicalization. -/
theorem fragment_betaU_bit_open_move {Γ Δ ΔF ΔX B M X}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ ΔF ΔX) (hAd : Ty.Admissible .bit)
    (hDup : Ty.Duplicable .bit) (hN : AllNone ΔX)
    (hArr : Ty.SemanticFragment (.arrow .unres .bit B))
    (hB : Ty.SemanticFragment B)
    (hLF : CtxLAllSomeFragment ΔF) (hΔF : AllNone ΔF)
    (cBody : FragCert (.bit :: Γ) ΔF M B) (cX : FragCert Γ ΔX X .bit) :
    FragCert.denote
        (.appU hΓ hΔ hs hN hB (.lamU hΓ hLF hAd hDup hΔF hArr cBody) cX) =
      Hom.comp (FragCert.denote cBody)
        (Hom.comp
          (Hom.comp
            (FragmentContext.moveArgumentIntoUnrestricted
              (FragmentContext.unrestricted Γ) (FragmentContext.linear ΔF)
              classicalBitModule)
            (DayTensor.map (Hom.id (FragmentContext.combined Γ ΔF))
              bitClassicalize))
          (Hom.comp
            (DayTensor.map
              (Hom.id
                (dayTensor (FragmentContext.unrestricted Γ)
                  (FragmentContext.linear ΔF)))
              (FragCert.denote cX))
            (FragmentContext.combinedOSplit hΓ hs))) := by
  have hfactor :
      DayTensor.map
          (FragmentContext.abstractUnrestricted (FragCert.denote cBody))
          (FragCert.denote cX) =
        Hom.comp
          (DayTensor.map
            (FragmentContext.abstractUnrestricted (FragCert.denote cBody))
            (Hom.id (fragmentModule .bit)))
          (DayTensor.map
            (Hom.id
              (dayTensor (FragmentContext.unrestricted Γ)
                (FragmentContext.linear ΔF)))
            (FragCert.denote cX)) := by
    simpa only [Hom.comp_id, Hom.id_comp] using
      DayTensor.map_comp
        (FragmentContext.abstractUnrestricted (FragCert.denote cBody))
        (Hom.id
          (dayTensor (FragmentContext.unrestricted Γ)
            (FragmentContext.linear ΔF)))
        (Hom.id (fragmentModule .bit)) (FragCert.denote cX)
  have hβ :
      Hom.comp (FragmentContext.evalUnrestrictedBit (fragmentModule B))
          (DayTensor.map
            (FragmentContext.abstractUnrestricted (FragCert.denote cBody))
            (Hom.id (fragmentModule .bit))) =
        Hom.comp (FragCert.denote cBody)
          (Hom.comp
            (FragmentContext.moveArgumentIntoUnrestricted
              (FragmentContext.unrestricted Γ) (FragmentContext.linear ΔF)
              classicalBitModule)
            (DayTensor.map (Hom.id (FragmentContext.combined Γ ΔF))
              bitClassicalize)) :=
    FragmentContext.evalUnrestrictedBit_abstractUnrestricted
      (FragCert.denote cBody)
  refine Eq.trans
    (fragment_subst_unres_bit_spine hΓ hΔ hs hAd hDup hN hArr hB hLF hΔF
      cBody cX) ?_
  refine Eq.trans
    (congrArg
      (fun g =>
        Hom.comp (FragmentContext.evalUnrestrictedBit (fragmentModule B))
          (Hom.comp g (FragmentContext.combinedOSplit hΓ hs)))
      hfactor) ?_
  exact congrArg
    (fun g =>
      Hom.comp g
        (Hom.comp
          (DayTensor.map
            (Hom.id
              (dayTensor (FragmentContext.unrestricted Γ)
                (FragmentContext.linear ΔF)))
            (FragCert.denote cX))
          (FragmentContext.combinedOSplit hΓ hs)))
    hβ

end QLambda.Linear
