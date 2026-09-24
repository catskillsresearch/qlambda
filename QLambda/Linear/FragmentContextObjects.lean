/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentModel
import QLambda.Domain.Presheaf.DayCoend
import QLambda.Domain.Presheaf.Comonoid

/-!
# Fragment context objects (Route A)

Unrestricted/linear/combined Day-tensor contexts, lookup, discard,
closed collapse, and middle-four interchange.
-/

namespace QLambda.Linear
namespace FragmentContext

set_option maxHeartbeats 8000000

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open DayTensor

/-- Unrestricted context object.  Route A admits only bit binders here; the
total definition uses the classical-bit carrier for every list cell, and all
public structural maps require `CtxUAllBit`. -/
noncomputable def unrestricted : List Ty → Module
  | [] => dayTensorUnit
  | _ :: Γ => dayTensor classicalBitModule (unrestricted Γ)

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
        (map classicalBitWeakening (ih htail))

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
            (map classicalBitInclusion
              (unrestrictedAllBitDiscard htail))⟩
      | succ n =>
          cases hl with
          | succ hl =>
              subst B
              obtain ⟨f⟩ := unrestrictedLookup_exists htail hl
              exact ⟨Hom.comp (leftUnitor (fragmentModule A))
                (map classicalBitWeakening f)⟩
termination_by Γ.length

/-- Structural discard of an all-bit unrestricted context. -/
noncomputable def unrestrictedAllBitDiscardLists :
    ∀ (Γ : List Ty), Hom (unrestricted Γ) dayTensorUnit
  | [] => Hom.id dayTensorUnit
  | _ :: Γ =>
      Hom.comp (leftUnitor dayTensorUnit)
        (map classicalBitWeakening (unrestrictedAllBitDiscardLists Γ))

theorem unrestrictedAllBitDiscardLists_nil :
    unrestrictedAllBitDiscardLists [] = Hom.id dayTensorUnit :=
  rfl

/-- Structural unrestricted lookup (computes without eliminating `Lookup` /
`CtxUAllBit : Prop`). Impossible shapes return `0`. -/
noncomputable def unrestrictedLookupLists :
    ∀ (Γ : List Ty) (n : Nat) (A : Ty),
      Hom (unrestricted Γ) (fragmentModule A)
  | [], _, _ => 0
  | _ :: Γ, 0, A =>
      if h : A = .bit then by
        subst A
        exact Hom.comp (rightUnitor (fragmentModule .bit))
          (map classicalBitInclusion
            (unrestrictedAllBitDiscardLists Γ))
      else
        0
  | _ :: Γ, n + 1, A =>
      Hom.comp (leftUnitor (fragmentModule A))
        (map classicalBitWeakening (unrestrictedLookupLists Γ n A))

theorem unrestrictedLookupLists_zero_bit (Γ : List Ty) :
    unrestrictedLookupLists (.bit :: Γ) 0 .bit =
      Hom.comp (rightUnitor (fragmentModule .bit))
        (map classicalBitInclusion
          (unrestrictedAllBitDiscardLists Γ)) := by
  simp only [unrestrictedLookupLists, ↓reduceIte]
  rfl

/-- Select an unrestricted bit variable, weakening every other bit entry. -/
noncomputable def unrestrictedLookup {Γ : List Ty} {n : Nat} {A : Ty}
    (_hΓ : CtxUAllBit Γ) (_hl : Lookup Γ n A) :
    Hom (unrestricted Γ) (fragmentModule A) :=
  unrestrictedLookupLists Γ n A

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

/-- Structural all-none collapse on the underlying list (computes without
eliminating `AllNone : Prop`). Impossible shapes return `0`. -/
noncomputable def linearAllNoneCollapseLists :
    ∀ (Δ : List (Option Ty)), Hom (linear Δ) dayTensorUnit
  | [] => Hom.id dayTensorUnit
  | none :: Δ =>
      Hom.comp (leftUnitor dayTensorUnit)
        (map (Hom.id dayTensorUnit) (linearAllNoneCollapseLists Δ))
  | some _ :: _ => 0

/-- Structural projection from a uniquely occupied linear cell (computes
without eliminating `Lookup`/`OnlySomeAt : Prop`). Impossible shapes return
`0`. -/
noncomputable def linearOnlySomeAtProjectLists :
    ∀ (Δ : List (Option Ty)) (n : Nat) (A : Ty),
      Hom (linear Δ) (fragmentModule A)
  | [], _, _ => 0
  | some B :: Δ, 0, A =>
      if h : B = A then by
        subst A
        exact Hom.comp (rightUnitor (fragmentModule B))
          (map (Hom.id (fragmentModule B))
            (linearAllNoneCollapseLists Δ))
      else
        0
  | none :: Δ, n + 1, A =>
      Hom.comp (leftUnitor (fragmentModule A))
        (map (Hom.id dayTensorUnit)
          (linearOnlySomeAtProjectLists Δ n A))
  | some _ :: _, _ + 1, _ => 0
  | none :: _, 0, _ => 0

/-- Project the unique occupied linear cell selected by `Lookup` and
`OnlySomeAt`. -/
noncomputable def linearOnlySomeAtProject {Δ : List (Option Ty)}
    {n : Nat} {A : Ty} (_hl : Lookup Δ n (some A))
    (_ho : OnlySomeAt Δ n) :
    Hom (linear Δ) (fragmentModule A) :=
  linearOnlySomeAtProjectLists Δ n A

/-- Singleton occupied linear cell projects by the right unitor. -/
theorem linearOnlySomeAtProjectLists_singleton (A : Ty) :
    linearOnlySomeAtProjectLists [some A] 0 A =
      Hom.comp (rightUnitor (fragmentModule A))
        (map (Hom.id (fragmentModule A)) (Hom.id dayTensorUnit)) := by
  simp only [linearOnlySomeAtProjectLists, ↓reduceIte]
  rfl

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


end FragmentContext
end QLambda.Linear
