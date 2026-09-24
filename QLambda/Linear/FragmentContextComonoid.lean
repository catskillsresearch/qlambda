/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentContextSplit
import QLambda.Linear.FragmentClassicalBitChannels
import QLambda.Linear.FragmentClassicalBitCoassoc.bitCoassocLeft_eq_right
import QLambda.Domain.Presheaf.Comonoid

/-!
# Classical-bit Day comonoid for fragment contexts

Counit/comult laws, Route A context acceptance, and
`classicalBitComonoid`.
-/

namespace QLambda.Linear
namespace FragmentContext

set_option maxHeartbeats 8000000

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open DayTensor

/-- Classical-bit contraction satisfies the left counit law in the genuine
Day tensor. -/
theorem classicalBitContraction_left_counit :
    Hom.comp (leftUnitor classicalBitModule)
        (Hom.comp
          (map classicalBitWeakening (Hom.id classicalBitModule))
          classicalBitContraction) =
      Hom.id classicalBitModule := by
  apply Hom.ext
  intro n x
  rcases x with ⟨x, hx⟩
  change
    (leftUnitor classicalBitModule).app n
      ((map classicalBitWeakening (Hom.id classicalBitModule)).app n
        ((dayTensor classicalBitModule classicalBitModule).act
          ((DayCoend.intro classicalBitModule classicalBitModule).app
            classicalBitGeneric classicalBitGeneric)
          (Superoperator.comp bitCopySuperoperator x))) =
      ⟨x, hx⟩
  rw [(map classicalBitWeakening (Hom.id classicalBitModule)).naturality]
  rw [map_intro, Hom.id_app]
  rw [(leftUnitor classicalBitModule).naturality]
  change
    classicalBitModule.act
      ((leftUnitor classicalBitModule).app (2 * 2)
        ((DayCoend.intro dayTensorUnit classicalBitModule).app
          (Superoperator.comp SigmaMon.ChoiSum.discardTwo
            bitDephaseSuperoperator)
          classicalBitGeneric))
      (Superoperator.comp bitCopySuperoperator x) =
    ⟨x, hx⟩
  rw [leftUnitor_intro]
  apply Subtype.ext
  simp only [classicalBitModule, classicalBitGeneric]
  rw [← Superoperator.comp_assoc]
  rw [Superoperator.comp_assoc
    (Superoperator.comp
      (Superoperator.tensorLeftUnitor 2)
      (Superoperator.tensor
        (Superoperator.comp SigmaMon.ChoiSum.discardTwo
          bitDephaseSuperoperator)
        (Superoperator.identity 2)))
    bitCopySuperoperator x]
  rw [Superoperator.comp_assoc]
  have hc :
      Superoperator.comp bitDephaseSuperoperator
        (Superoperator.comp
          (Superoperator.comp
            (Superoperator.tensorLeftUnitor 2)
            (Superoperator.tensor
              (Superoperator.comp SigmaMon.ChoiSum.discardTwo
                bitDephaseSuperoperator)
              (Superoperator.identity 2)))
          bitCopySuperoperator) =
        bitDephaseSuperoperator := by
    simpa only [Superoperator.comp_assoc] using
      bitClassicalLeftCounitChannel
  rw [hc]
  exact hx

/-- Classical-bit contraction satisfies the right counit law. -/
theorem classicalBitContraction_right_counit :
    Hom.comp (rightUnitor classicalBitModule)
        (Hom.comp
          (map (Hom.id classicalBitModule) classicalBitWeakening)
          classicalBitContraction) =
      Hom.id classicalBitModule := by
  apply Hom.ext
  intro n x
  rcases x with ⟨x, hx⟩
  change
    (rightUnitor classicalBitModule).app n
      ((map (Hom.id classicalBitModule) classicalBitWeakening).app n
        ((dayTensor classicalBitModule classicalBitModule).act
          ((DayCoend.intro classicalBitModule classicalBitModule).app
            classicalBitGeneric classicalBitGeneric)
          (Superoperator.comp bitCopySuperoperator x))) =
      ⟨x, hx⟩
  rw [(map (Hom.id classicalBitModule) classicalBitWeakening).naturality]
  rw [map_intro, Hom.id_app]
  rw [(rightUnitor classicalBitModule).naturality]
  change
    classicalBitModule.act
      ((rightUnitor classicalBitModule).app (2 * 2)
        ((DayCoend.intro classicalBitModule dayTensorUnit).app
          classicalBitGeneric
          (Superoperator.comp SigmaMon.ChoiSum.discardTwo
            bitDephaseSuperoperator)))
      (Superoperator.comp bitCopySuperoperator x) =
    ⟨x, hx⟩
  rw [rightUnitor_intro]
  apply Subtype.ext
  simp only [classicalBitModule, classicalBitGeneric]
  rw [← Superoperator.comp_assoc]
  rw [Superoperator.comp_assoc
    (Superoperator.comp
      (Superoperator.tensorRightUnitor 2)
      (Superoperator.tensor
        (Superoperator.identity 2)
        (Superoperator.comp SigmaMon.ChoiSum.discardTwo
          bitDephaseSuperoperator)))
    bitCopySuperoperator x]
  rw [Superoperator.comp_assoc]
  have hc :
      Superoperator.comp bitDephaseSuperoperator
        (Superoperator.comp
          (Superoperator.comp
            (Superoperator.tensorRightUnitor 2)
            (Superoperator.tensor
              (Superoperator.identity 2)
              (Superoperator.comp SigmaMon.ChoiSum.discardTwo
                bitDephaseSuperoperator)))
          bitCopySuperoperator) =
        bitDephaseSuperoperator := by
    simpa only [Superoperator.comp_assoc] using
      bitClassicalRightCounitChannel
  rw [hc]
  exact hx

/-- Classical-bit contraction is invariant under Day braiding. -/
theorem classicalBitContraction_cocommutative :
    Hom.comp (braiding classicalBitModule classicalBitModule)
        classicalBitContraction =
      classicalBitContraction := by
  apply Hom.ext
  intro n x
  rcases x with ⟨x, hx⟩
  change
    (braiding classicalBitModule classicalBitModule).app n
      ((dayTensor classicalBitModule classicalBitModule).act
        ((DayCoend.intro classicalBitModule classicalBitModule).app
          classicalBitGeneric classicalBitGeneric)
        (Superoperator.comp bitCopySuperoperator x)) =
      (dayTensor classicalBitModule classicalBitModule).act
        ((DayCoend.intro classicalBitModule classicalBitModule).app
          classicalBitGeneric classicalBitGeneric)
        (Superoperator.comp bitCopySuperoperator x)
  rw [(braiding classicalBitModule classicalBitModule).naturality]
  rw [braiding_intro]
  rw [(dayTensor classicalBitModule classicalBitModule).act_comp]
  congr 1
  rw [Superoperator.comp_assoc]
  exact congrArg (fun z => Superoperator.comp z x)
    bitCocommutativityLeft_eq_copy

/-- Classical-bit contraction is coassociative in the genuine Day tensor. -/
theorem classicalBitContraction_coassociative :
    Hom.comp
        (associator classicalBitModule classicalBitModule classicalBitModule)
        (Hom.comp
          (map classicalBitContraction (Hom.id classicalBitModule))
          classicalBitContraction) =
      Hom.comp
        (map (Hom.id classicalBitModule) classicalBitContraction)
        classicalBitContraction := by
  apply Hom.ext
  intro n x
  rcases x with ⟨x, hx⟩
  change
    (associator classicalBitModule classicalBitModule
        classicalBitModule).app n
      ((map classicalBitContraction (Hom.id classicalBitModule)).app n
        ((dayTensor classicalBitModule classicalBitModule).act
          ((DayCoend.intro classicalBitModule classicalBitModule).app
            classicalBitGeneric classicalBitGeneric)
          (Superoperator.comp bitCopySuperoperator x))) =
      (map (Hom.id classicalBitModule) classicalBitContraction).app n
        ((dayTensor classicalBitModule classicalBitModule).act
          ((DayCoend.intro classicalBitModule classicalBitModule).app
            classicalBitGeneric classicalBitGeneric)
          (Superoperator.comp bitCopySuperoperator x))
  rw [(map classicalBitContraction (Hom.id classicalBitModule)).naturality,
    (map (Hom.id classicalBitModule) classicalBitContraction).naturality,
    map_intro, map_intro]
  -- Goal now has `classicalBitContraction.app 2 classicalBitGeneric` on each side.
  change
    (associator classicalBitModule classicalBitModule
        classicalBitModule).app n
      ((dayTensor
            (dayTensor classicalBitModule classicalBitModule)
            classicalBitModule).act
        ((DayCoend.intro
            (dayTensor classicalBitModule classicalBitModule)
            classicalBitModule).app
          ((dayTensor classicalBitModule classicalBitModule).act
            ((DayCoend.intro classicalBitModule classicalBitModule).app
              classicalBitGeneric classicalBitGeneric)
            (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator))
          classicalBitGeneric)
        (Superoperator.comp bitCopySuperoperator x)) =
      (dayTensor classicalBitModule
          (dayTensor classicalBitModule classicalBitModule)).act
        ((DayCoend.intro classicalBitModule
            (dayTensor classicalBitModule classicalBitModule)).app
          classicalBitGeneric
          ((dayTensor classicalBitModule classicalBitModule).act
            ((DayCoend.intro classicalBitModule classicalBitModule).app
              classicalBitGeneric classicalBitGeneric)
            (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator)))
        (Superoperator.comp bitCopySuperoperator x)
  -- Reassociate nested `act`/`intro` via bilinear naturality.
  have hleft_gen :
      (DayCoend.intro
          (dayTensor classicalBitModule classicalBitModule)
          classicalBitModule).app
        ((dayTensor classicalBitModule classicalBitModule).act
          ((DayCoend.intro classicalBitModule classicalBitModule).app
            classicalBitGeneric classicalBitGeneric)
          (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator))
        classicalBitGeneric =
      (dayTensor
          (dayTensor classicalBitModule classicalBitModule)
          classicalBitModule).act
        ((DayCoend.intro
            (dayTensor classicalBitModule classicalBitModule)
            classicalBitModule).app
          ((DayCoend.intro classicalBitModule classicalBitModule).app
            classicalBitGeneric classicalBitGeneric)
          classicalBitGeneric)
        (Superoperator.tensor
          (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator)
          (Superoperator.identity 2)) := by
    have h :=
      (DayCoend.intro
          (dayTensor classicalBitModule classicalBitModule)
          classicalBitModule).naturality
        ((DayCoend.intro classicalBitModule classicalBitModule).app
          classicalBitGeneric classicalBitGeneric)
        classicalBitGeneric
        (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator)
        (Superoperator.identity 2)
    simpa [classicalBitModule.act_id] using h
  have hright_gen :
      (DayCoend.intro classicalBitModule
          (dayTensor classicalBitModule classicalBitModule)).app
        classicalBitGeneric
        ((dayTensor classicalBitModule classicalBitModule).act
          ((DayCoend.intro classicalBitModule classicalBitModule).app
            classicalBitGeneric classicalBitGeneric)
          (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator)) =
      (dayTensor classicalBitModule
          (dayTensor classicalBitModule classicalBitModule)).act
        ((DayCoend.intro classicalBitModule
            (dayTensor classicalBitModule classicalBitModule)).app
          classicalBitGeneric
          ((DayCoend.intro classicalBitModule classicalBitModule).app
            classicalBitGeneric classicalBitGeneric))
        (Superoperator.tensor (Superoperator.identity 2)
          (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator)) := by
    have h :=
      (DayCoend.intro classicalBitModule
          (dayTensor classicalBitModule classicalBitModule)).naturality
        classicalBitGeneric
        ((DayCoend.intro classicalBitModule classicalBitModule).app
          classicalBitGeneric classicalBitGeneric)
        (Superoperator.identity 2)
        (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator)
    simpa [classicalBitModule.act_id] using h
  rw [hleft_gen, hright_gen]
  rw [(dayTensor
      (dayTensor classicalBitModule classicalBitModule)
      classicalBitModule).act_comp,
    (dayTensor classicalBitModule
      (dayTensor classicalBitModule classicalBitModule)).act_comp]
  rw [(associator classicalBitModule classicalBitModule
      classicalBitModule).naturality]
  have happ :=
    associator_intro_intro
      (M := classicalBitModule) (N := classicalBitModule)
      (P := classicalBitModule)
      classicalBitGeneric classicalBitGeneric classicalBitGeneric
  rw [happ]
  rw [(dayTensor classicalBitModule
      (dayTensor classicalBitModule classicalBitModule)).act_comp]
  congr 1
  -- Channels: associator ∘ ((C∘D)⊗id) ∘ C  =  (id⊗(C∘D)) ∘ C
  have hchan :=
    congrArg (fun z : Superoperator 2 8 => Superoperator.comp z x)
      bitCoassocLeft_eq_right
  -- Unfold the named composites and reassociate past `x`.
  simp only [bitCoassocLeft, bitCoassocLeftPre, bitCoassocRight,
    Superoperator.comp_assoc] at hchan ⊢
  exact hchan

/-- OSplit preserves linear context lengths (structural coherence premise). -/
theorem oSplit_lengths {Δ Δ₁ Δ₂ : List (Option Ty)}
    (h : OSplit Δ Δ₁ Δ₂) :
    Δ₁.length = Δ.length ∧ Δ₂.length = Δ.length :=
  OSplit.lengths h

/-- Route A fragment contexts exist without a global bang. -/
theorem routeA_fragment_context_acceptance :
    (unrestricted [] = dayTensorUnit) ∧
    (linear [] = dayTensorUnit) ∧
    (∃ γ : Hom classicalBitModule
        (dayTensor classicalBitModule classicalBitModule),
      γ = classicalBitContraction) ∧
    (∃ δ : Hom classicalBitModule dayTensorUnit,
      δ = classicalBitWeakening) ∧
    (∀ Γ Δ, combined Γ Δ = dayTensor (unrestricted Γ) (linear Δ)) :=
  ⟨rfl, rfl, ⟨classicalBitContraction, rfl⟩,
    ⟨classicalBitWeakening, rfl⟩, fun _ _ => rfl⟩

/-- The dephasing-fixed classical bit is a commutative Day comonoid. -/
noncomputable def classicalBitComonoid :
    Domain.Presheaf.SuperoperatorModule.Comonoid where
  carrier := classicalBitModule
  counit := classicalBitWeakening
  comult := classicalBitContraction
  left_counit := classicalBitContraction_left_counit
  right_counit := classicalBitContraction_right_counit
  coassociative := classicalBitContraction_coassociative
  cocommutative := classicalBitContraction_cocommutative


end FragmentContext
end QLambda.Linear
