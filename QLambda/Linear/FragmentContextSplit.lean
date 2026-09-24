/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentContextDay

/-!
# Fragment context splits and combined maps

Linear `OSplit`, unrestricted contraction, `combinedOSplit`, and
proof-witness independence.
-/

namespace QLambda.Linear
namespace FragmentContext

set_option maxHeartbeats 8000000

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open DayTensor

/-- Existence of the structural Day split induced by a linear `OSplit`. -/
theorem linearOSplit_exists {Δ Δ₁ Δ₂ : List (Option Ty)}
    (hs : OSplit Δ Δ₁ Δ₂) :
    Nonempty (Hom (linear Δ) (dayTensor (linear Δ₁) (linear Δ₂))) := by
  induction hs with
  | nil =>
      exact ⟨leftUnitorInv dayTensorUnit⟩
  | none hs ih =>
      obtain ⟨f⟩ := ih
      exact ⟨Hom.comp
        (map (leftUnitorInv _) (leftUnitorInv _))
        (Hom.comp (leftUnitor _) (map (Hom.id dayTensorUnit) f))⟩
  | left hs ih =>
      obtain ⟨f⟩ := ih
      exact ⟨Hom.comp
        (map (Hom.id _) (leftUnitorInv _))
        (Hom.comp (associatorInv _ _ _) (map (Hom.id _) f))⟩
  | right hs ih =>
      obtain ⟨f⟩ := ih
      exact ⟨Hom.comp
        (map (leftUnitorInv _) (Hom.id _))
        (Hom.comp (associator _ _ _)
          (Hom.comp (map (braiding _ _) (Hom.id _))
            (Hom.comp (associatorInv _ _ _) (map (Hom.id _) f))))⟩

/-- Structural Day split on the underlying lists (computes without eliminating
`OSplit : Prop`). Impossible shapes return `0`. -/
noncomputable def linearOSplitLists :
    ∀ (Δ Δ₁ Δ₂ : List (Option Ty)),
      Hom (linear Δ) (dayTensor (linear Δ₁) (linear Δ₂))
  | [], [], [] => leftUnitorInv dayTensorUnit
  | none :: Δ, none :: Δ₁, none :: Δ₂ =>
      Hom.comp
        (map (leftUnitorInv _) (leftUnitorInv _))
        (Hom.comp (leftUnitor _)
          (map (Hom.id dayTensorUnit) (linearOSplitLists Δ Δ₁ Δ₂)))
  | some A :: Δ, some B :: Δ₁, none :: Δ₂ =>
      if h : A = B then
        h ▸ Hom.comp
          (map (Hom.id _) (leftUnitorInv _))
          (Hom.comp (associatorInv _ _ _)
            (map (Hom.id _) (linearOSplitLists Δ Δ₁ Δ₂)))
      else
        0
  | some A :: Δ, none :: Δ₁, some B :: Δ₂ =>
      if h : A = B then
        h ▸ Hom.comp
          (map (leftUnitorInv _) (Hom.id _))
          (Hom.comp (associator _ _ _)
            (Hom.comp (map (braiding _ _) (Hom.id _))
              (Hom.comp (associatorInv _ _ _)
                (map (Hom.id _) (linearOSplitLists Δ Δ₁ Δ₂)))))
      else
        0
  | _, _, _ => 0

/-- Structural Day split selected by an `OSplit` witness. -/
noncomputable def linearOSplit {Δ Δ₁ Δ₂ : List (Option Ty)}
    (_hs : OSplit Δ Δ₁ Δ₂) :
    Hom (linear Δ) (dayTensor (linear Δ₁) (linear Δ₂)) :=
  linearOSplitLists Δ Δ₁ Δ₂

theorem linearOSplit_nil (hs : OSplit [] [] []) :
    linearOSplit hs = leftUnitorInv dayTensorUnit :=
  rfl

/-- Physical bit copy retained only as a boundary map; unrestricted
contraction below uses `classicalBitContraction`. -/
noncomputable def bitContraction :
    Hom (representable 2) (dayTensorRepresentable 2 2) :=
  bitCopy

/-- Classical-bit contraction into the actual coend Day tensor. -/
noncomputable def bitContractionDay :
    Hom classicalBitModule
      (dayTensor classicalBitModule classicalBitModule) :=
  classicalBitContraction

/-- Bit discard available for classical weakening (Route A, not bang). -/
noncomputable def bitWeakening :
    Hom classicalBitModule dayTensorUnit :=
  classicalBitWeakening

/-- Existence of direct contraction for an all-bit unrestricted context. -/
theorem unrestrictedContraction_exists {Γ : List Ty}
    (hΓ : CtxUAllBit Γ) :
    Nonempty (Hom (unrestricted Γ)
      (dayTensor (unrestricted Γ) (unrestricted Γ))) := by
  induction Γ with
  | nil =>
      exact ⟨leftUnitorInv dayTensorUnit⟩
  | cons A Γ ih =>
      have hA : A = .bit := hΓ (List.Mem.head _)
      have htail : CtxUAllBit Γ := by
        intro B hm
        exact hΓ (List.Mem.tail _ hm)
      subst A
      obtain ⟨f⟩ := ih htail
      exact ⟨Hom.comp
        (tensorInterchange classicalBitModule classicalBitModule
          (unrestricted Γ) (unrestricted Γ))
        (map bitContractionDay f)⟩

/-- Direct contraction for an all-bit unrestricted context. -/
noncomputable def unrestrictedContractionLists :
    ∀ (Γ : List Ty),
      Hom (unrestricted Γ) (dayTensor (unrestricted Γ) (unrestricted Γ))
  | [] => leftUnitorInv dayTensorUnit
  | .bit :: Γ =>
      Hom.comp
        (tensorInterchange classicalBitModule classicalBitModule
          (unrestricted Γ) (unrestricted Γ))
        (map bitContractionDay (unrestrictedContractionLists Γ))
  | _ :: _ => 0

/-- Direct contraction for an all-bit unrestricted context. -/
noncomputable def unrestrictedContraction {Γ : List Ty}
    (_hΓ : CtxUAllBit Γ) :
    Hom (unrestricted Γ)
      (dayTensor (unrestricted Γ) (unrestricted Γ)) :=
  unrestrictedContractionLists Γ

theorem unrestrictedContraction_nil (hΓ : CtxUAllBit []) :
    unrestrictedContraction hΓ = leftUnitorInv dayTensorUnit :=
  rfl

/-- Duplicate the shared unrestricted context and split the linear context.
On empty contexts the middle-four interchange is omitted: the split is
definitionally `λ⁻¹ ⊗ λ⁻¹`, matching the Day-unit packaging used by closed
`ite` Step soundness. -/
noncomputable def combinedOSplitLists :
    ∀ (Γ : List Ty) (Δ Δ₁ Δ₂ : List (Option Ty)),
      Hom (combined Γ Δ)
        (dayTensor (combined Γ Δ₁) (combined Γ Δ₂))
  | [], [], [], [] =>
      map (leftUnitorInv dayTensorUnit) (leftUnitorInv dayTensorUnit)
  | Γ, Δ, Δ₁, Δ₂ =>
      Hom.comp
        (tensorInterchange (unrestricted Γ) (unrestricted Γ)
          (linear Δ₁) (linear Δ₂))
        (map (unrestrictedContractionLists Γ) (linearOSplitLists Δ Δ₁ Δ₂))

/-- Duplicate the shared unrestricted context and split the linear context. -/
noncomputable def combinedOSplit {Γ : List Ty}
    {Δ Δ₁ Δ₂ : List (Option Ty)} (_hΓ : CtxUAllBit Γ)
    (_hs : OSplit Δ Δ₁ Δ₂) :
    Hom (combined Γ Δ)
      (dayTensor (combined Γ Δ₁) (combined Γ Δ₂)) :=
  combinedOSplitLists Γ Δ Δ₁ Δ₂

/-- Empty combined split is the Day-unit pairing `λ⁻¹ ⊗ λ⁻¹`. -/
theorem combinedOSplit_nil (hΓ : CtxUAllBit []) (hs : OSplit [] [] []) :
    combinedOSplit hΓ hs =
      map (leftUnitorInv dayTensorUnit) (leftUnitorInv dayTensorUnit) :=
  rfl

/-- Select an unrestricted bit variable from a combined context. -/
noncomputable def combinedLookupUnrestricted {Γ : List Ty}
    {Δ : List (Option Ty)} {n : Nat} {A : Ty}
    (hΓ : CtxUAllBit Γ) (hl : Lookup Γ n A) (hΔ : AllNone Δ) :
    Hom (combined Γ Δ) (fragmentModule A) :=
  Hom.comp (rightUnitor (fragmentModule A))
    (map (unrestrictedLookup hΓ hl) (linearAllNoneCollapse hΔ))

/-- Select the unique occupied linear variable from a combined context. -/
noncomputable def combinedLookupLinear {Γ : List Ty}
    {Δ : List (Option Ty)} {n : Nat} {A : Ty}
    (hΓ : CtxUAllBit Γ) (hl : Lookup Δ n (some A))
    (ho : OnlySomeAt Δ n) :
    Hom (combined Γ Δ) (fragmentModule A) :=
  Hom.comp (leftUnitor (fragmentModule A))
    (map (unrestrictedAllBitDiscard hΓ)
      (linearOnlySomeAtProject hl ho))

/-- Discard a combined context with an all-bit unrestricted part and no
occupied linear cells. -/
noncomputable def combinedAllDiscard {Γ : List Ty}
    {Δ : List (Option Ty)} (hΓ : CtxUAllBit Γ) (hΔ : AllNone Δ) :
    Hom (combined Γ Δ) dayTensorUnit :=
  Hom.comp (leftUnitor dayTensorUnit)
    (map (unrestrictedAllBitDiscard hΓ) (linearAllNoneCollapse hΔ))

/-- Extend a point at the Day unit to a constant map on a discardable
combined context. -/
noncomputable def combinedPoint {Γ : List Ty}
    {Δ : List (Option Ty)} {A : Module}
    (hΓ : CtxUAllBit Γ) (hΔ : AllNone Δ)
    (f : Hom dayTensorUnit A) :
    Hom (combined Γ Δ) A :=
  Hom.comp f (combinedAllDiscard hΓ hΔ)

/-- Structural context maps do not depend on proof witnesses. -/
theorem linearAllNoneCollapse_proof_independent {Δ : List (Option Ty)}
    (h h' : AllNone Δ) :
    linearAllNoneCollapse h = linearAllNoneCollapse h' := by
  congr

theorem unrestrictedAllBitDiscard_proof_independent {Γ : List Ty}
    (hΓ hΓ' : CtxUAllBit Γ) :
    unrestrictedAllBitDiscard hΓ = unrestrictedAllBitDiscard hΓ' := by
  congr

theorem combinedAllDiscard_proof_independent {Γ : List Ty}
    {Δ : List (Option Ty)} (hΓ hΓ' : CtxUAllBit Γ) (hΔ hΔ' : AllNone Δ) :
    combinedAllDiscard hΓ hΔ = combinedAllDiscard hΓ' hΔ' := by
  congr

theorem linearOnlySomeAtProject_proof_independent
    {Δ : List (Option Ty)} {n : Nat} {A : Ty}
    (hl hl' : Lookup Δ n (some A)) (ho ho' : OnlySomeAt Δ n) :
    linearOnlySomeAtProject hl ho =
      linearOnlySomeAtProject hl' ho' := by
  congr

theorem linearOSplit_proof_independent {Δ Δ₁ Δ₂ : List (Option Ty)}
    (hs hs' : OSplit Δ Δ₁ Δ₂) :
    linearOSplit hs = linearOSplit hs' := by
  congr

theorem unrestrictedLookup_proof_independent
    {Γ : List Ty} {n : Nat} {A : Ty}
    (hΓ hΓ' : CtxUAllBit Γ) (hl hl' : Lookup Γ n A) :
    unrestrictedLookup hΓ hl = unrestrictedLookup hΓ' hl' := by
  congr

theorem combinedOSplit_proof_independent {Γ : List Ty}
    {Δ Δ₁ Δ₂ : List (Option Ty)}
    (hΓ hΓ' : CtxUAllBit Γ) (hs hs' : OSplit Δ Δ₁ Δ₂) :
    combinedOSplit hΓ hs = combinedOSplit hΓ' hs' := by
  congr


end FragmentContext
end QLambda.Linear
