/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentModel
import QLambda.Domain.Presheaf.DayCoend

/-!
# Open fragment context objects (Route A)

Presheaf counterpart of `ContextObject` for the minimum fragment.  Unrestricted
contexts use ordinary Day tensors of `fragmentModule` (classical-bit structural
maps come from `bitCopy`/`bitDiscard`, not `bang 2`).  Linear `none` cells are
tensor units so de Bruijn indices remain aligned under `OSplit`.
-/

namespace QLambda.Linear
namespace FragmentContext

set_option maxHeartbeats 2000000

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open DayTensor

/-- Unrestricted context object: Day tensor of fragment modules. -/
noncomputable def unrestricted : List Ty → Module
  | [] => dayTensorUnit
  | A :: Γ => dayTensor (fragmentModule A) (unrestricted Γ)

/-- Linear context object; absent cells are tensor units. -/
noncomputable def linear : List (Option Ty) → Module
  | [] => dayTensorUnit
  | none :: Δ => dayTensor dayTensorUnit (linear Δ)
  | some A :: Δ => dayTensor (fragmentModule A) (linear Δ)

/-- Combined context `⟦Γ⟧ ⊗ ⟦Δ⟧`. -/
noncomputable def combined (Γ : List Ty) (Δ : List (Option Ty)) : Module :=
  dayTensor (unrestricted Γ) (linear Δ)

@[simp] theorem unrestricted_nil : unrestricted [] = dayTensorUnit := rfl
@[simp] theorem linear_nil : linear [] = dayTensorUnit := rfl

theorem combined_nil_nil :
    combined [] [] = dayTensor dayTensorUnit dayTensorUnit :=
  rfl

/-- Identity on a combined context. -/
noncomputable def combinedId (Γ : List Ty) (Δ : List (Option Ty)) :
    Hom (combined Γ Δ) (combined Γ Δ) :=
  Hom.id _

/-- Bifunctorial action on combined contexts. -/
noncomputable def combinedMap {Γ Γ' : List Ty} {Δ Δ' : List (Option Ty)}
    (f : Hom (unrestricted Γ) (unrestricted Γ'))
    (g : Hom (linear Δ) (linear Δ')) :
    Hom (combined Γ Δ) (combined Γ' Δ') :=
  map f g

/-- Discard an unrestricted context whose entries are all classical bits. -/
noncomputable def unrestrictedAllBitDiscard {Γ : List Ty}
    (hΓ : CtxUAllBit Γ) : Hom (unrestricted Γ) dayTensorUnit := by
  induction Γ with
  | nil =>
      exact Hom.id dayTensorUnit
  | cons A Γ ih =>
      have hA : A = .bit := hΓ (List.Mem.head _)
      have htail : CtxUAllBit Γ := by
        intro B hm
        exact hΓ (List.Mem.tail _ hm)
      subst A
      exact Hom.comp (leftUnitor dayTensorUnit)
        (map bitDiscard (ih htail))

/-- Existence of lookup from a classical-bit unrestricted context. -/
theorem unrestrictedLookup_exists {Γ : List Ty} {n : Nat} {A : Ty}
    (hΓ : CtxUAllBit Γ) (hl : Lookup Γ n A) :
    Nonempty (Hom (unrestricted Γ) (fragmentModule A)) := by
  cases Γ with
  | nil => cases hl
  | cons B Γ =>
      have hhead : B = .bit := hΓ (List.Mem.head _)
      have htail : CtxUAllBit Γ := by
        intro C hm
        exact hΓ (List.Mem.tail _ hm)
      cases n with
      | zero =>
          cases hl
          subst A
          exact ⟨Hom.comp (rightUnitor (fragmentModule .bit))
            (map (Hom.id (fragmentModule .bit))
              (unrestrictedAllBitDiscard htail))⟩
      | succ n =>
          cases hl with
          | succ hl =>
              subst B
              obtain ⟨f⟩ := unrestrictedLookup_exists htail hl
              exact ⟨Hom.comp (leftUnitor (fragmentModule A))
                (map bitDiscard f)⟩
termination_by Γ.length

/-- Select an unrestricted bit variable, weakening every other bit entry. -/
noncomputable def unrestrictedLookup {Γ : List Ty} {n : Nat} {A : Ty}
    (hΓ : CtxUAllBit Γ) (hl : Lookup Γ n A) :
    Hom (unrestricted Γ) (fragmentModule A) :=
  Classical.choice (unrestrictedLookup_exists hΓ hl)

/-- Collapse the empty combined context to the Day unit. -/
noncomputable def combinedClosedCollapse :
    Hom (combined [] []) dayTensorUnit :=
  Hom.comp (leftUnitor dayTensorUnit)
    (map (Hom.id dayTensorUnit) (Hom.id dayTensorUnit))

/-- Closed observation from a Day-unit point. -/
noncomputable def closedPoint {A : Module}
    (f : Hom dayTensorUnit A) : Hom (combined [] []) A :=
  Hom.comp f combinedClosedCollapse

/-- Insert a leading `none` on the linear context. -/
noncomputable def linearConsNone (Δ : List (Option Ty)) :
    Hom (linear Δ) (linear (none :: Δ)) :=
  Hom.comp (map (Hom.id dayTensorUnit) (Hom.id (linear Δ)))
    (leftUnitorInv (linear Δ))

/-- Collapse a linear context known to contain no resources. -/
noncomputable def linearAllNoneCollapse {Δ : List (Option Ty)}
    (h : AllNone Δ) : Hom (linear Δ) dayTensorUnit := by
  induction Δ with
  | nil =>
      exact Hom.id dayTensorUnit
  | cons cell Δ ih =>
      cases cell with
      | none =>
          simp only [AllNone] at h
          exact Hom.comp (leftUnitor dayTensorUnit)
            (map (Hom.id dayTensorUnit) (ih h))
      | some A =>
          simp [AllNone] at h

/-- Existence of the projection from a singleton-used linear context.
`Nonempty` keeps the proof recursion in `Prop`; the concrete map is selected
below. -/
theorem linearOnlySomeAtProject_exists {Δ : List (Option Ty)}
    {n : Nat} {A : Ty} (hl : Lookup Δ n (some A))
    (ho : OnlySomeAt Δ n) :
    Nonempty (Hom (linear Δ) (fragmentModule A)) := by
  cases Δ with
  | nil => cases hl
  | cons cell Δ =>
      cases n with
      | zero =>
          cases cell with
          | none => cases hl
          | some B =>
              cases hl
              simp only [OnlySomeAt] at ho
              exact ⟨Hom.comp (rightUnitor (fragmentModule A))
                (map (Hom.id (fragmentModule A))
                  (linearAllNoneCollapse ho))⟩
      | succ n =>
          cases cell with
          | none =>
              cases hl with
              | succ hl =>
                  simp only [OnlySomeAt] at ho
                  obtain ⟨f⟩ := linearOnlySomeAtProject_exists hl ho
                  exact ⟨Hom.comp (leftUnitor (fragmentModule A))
                    (map (Hom.id dayTensorUnit) f)⟩
          | some B =>
              simp [OnlySomeAt] at ho
termination_by Δ.length

/-- Project the unique occupied linear cell selected by `Lookup` and
`OnlySomeAt`. -/
noncomputable def linearOnlySomeAtProject {Δ : List (Option Ty)}
    {n : Nat} {A : Ty} (hl : Lookup Δ n (some A))
    (ho : OnlySomeAt Δ n) :
    Hom (linear Δ) (fragmentModule A) :=
  Classical.choice (linearOnlySomeAtProject_exists hl ho)

/-- Canonical middle-four interchange
`(M ⊗ N) ⊗ (P ⊗ Q) → (M ⊗ P) ⊗ (N ⊗ Q)`. -/
noncomputable def tensorInterchange (M N P Q : Module) :
    Hom (dayTensor (dayTensor M N) (dayTensor P Q))
      (dayTensor (dayTensor M P) (dayTensor N Q)) :=
  Hom.comp (associatorInv M P (dayTensor N Q))
    (Hom.comp (map (Hom.id M) (associator P N Q))
      (Hom.comp
        (map (Hom.id M) (map (braiding N P) (Hom.id Q)))
        (Hom.comp (map (Hom.id M) (associatorInv N P Q))
          (associator M N (dayTensor P Q)))))

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

/-- Structural Day split selected by an `OSplit` witness. -/
noncomputable def linearOSplit {Δ Δ₁ Δ₂ : List (Option Ty)}
    (hs : OSplit Δ Δ₁ Δ₂) :
    Hom (linear Δ) (dayTensor (linear Δ₁) (linear Δ₂)) :=
  Classical.choice (linearOSplit_exists hs)

/-- Bit copy available for classical contraction (Route A, not bang). -/
noncomputable def bitContraction :
    Hom (representable 2) (dayTensorRepresentable 2 2) :=
  bitCopy

/-- Bit copy transported to the actual coend Day tensor. -/
noncomputable def bitContractionDay :
    Hom (fragmentModule .bit)
      (dayTensor (fragmentModule .bit) (fragmentModule .bit)) :=
  Hom.comp (dayTensorRepresentableIso 2 2).inv bitCopy

/-- Bit discard available for classical weakening (Route A, not bang). -/
noncomputable def bitWeakening :
    Hom (representable 2) dayTensorUnit :=
  bitDiscard

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
        (tensorInterchange (fragmentModule .bit) (fragmentModule .bit)
          (unrestricted Γ) (unrestricted Γ))
        (map bitContractionDay f)⟩

/-- Direct contraction for an all-bit unrestricted context. -/
noncomputable def unrestrictedContraction {Γ : List Ty}
    (hΓ : CtxUAllBit Γ) :
    Hom (unrestricted Γ)
      (dayTensor (unrestricted Γ) (unrestricted Γ)) :=
  Classical.choice (unrestrictedContraction_exists hΓ)

/-- Duplicate the shared unrestricted context and split the linear context. -/
noncomputable def combinedOSplit {Γ : List Ty}
    {Δ Δ₁ Δ₂ : List (Option Ty)} (hΓ : CtxUAllBit Γ)
    (hs : OSplit Δ Δ₁ Δ₂) :
    Hom (combined Γ Δ)
      (dayTensor (combined Γ Δ₁) (combined Γ Δ₂)) :=
  Hom.comp
    (tensorInterchange (unrestricted Γ) (unrestricted Γ)
      (linear Δ₁) (linear Δ₂))
    (map (unrestrictedContraction hΓ) (linearOSplit hs))

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

/-- OSplit preserves linear context lengths (structural coherence premise). -/
theorem oSplit_lengths {Δ Δ₁ Δ₂ : List (Option Ty)}
    (h : OSplit Δ Δ₁ Δ₂) :
    Δ₁.length = Δ.length ∧ Δ₂.length = Δ.length :=
  OSplit.lengths h

/-- Route A fragment contexts exist without a global bang. -/
theorem routeA_fragment_context_acceptance :
    (unrestricted [] = dayTensorUnit) ∧
    (linear [] = dayTensorUnit) ∧
    (∃ γ : Hom (representable 2) (dayTensorRepresentable 2 2), γ = bitCopy) ∧
    (∃ δ : Hom (representable 2) dayTensorUnit, δ = bitDiscard) ∧
    (∀ Γ Δ, combined Γ Δ = dayTensor (unrestricted Γ) (linear Δ)) :=
  ⟨rfl, rfl, ⟨bitCopy, rfl⟩, ⟨bitDiscard, rfl⟩, fun _ _ => rfl⟩

end FragmentContext
end QLambda.Linear
