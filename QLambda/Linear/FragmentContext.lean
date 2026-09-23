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

/-- Bit copy available for classical contraction (Route A, not bang). -/
noncomputable def bitContraction :
    Hom (representable 2) (dayTensorRepresentable 2 2) :=
  bitCopy

/-- Bit discard available for classical weakening (Route A, not bang). -/
noncomputable def bitWeakening :
    Hom (representable 2) dayTensorUnit :=
  bitDiscard

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
