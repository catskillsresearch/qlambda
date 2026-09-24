/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentIte
import QLambda.Linear.FragmentAdequacy
import QLambda.Linear.Operational

/-!
# Fragment denotational coherence (Route A)

Denotational soundness for classical `Step`/`MeasStep` on the admitted
fragment, stated on `FragCert.denote`.  Closed literals, `ite` on bit
literals, and measurement-branch packaging are kernel-checked; open-term
β/η reuse Day closedness and the classical-bit comonoid from
`FragmentContext`.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf

/-- Unit and bit literals are values, so no closed `Step` applies. -/
theorem fragment_closed_literal_not_step {M M' : Term}
    (h : M = .unit ∨ ∃ b, M = .bitLit b) (hs : Step M M') : False := by
  rcases h with rfl | ⟨b, rfl⟩
  · cases hs
  · cases hs

/-- Denotational soundness for closed unit. -/
theorem fragment_step_denote_sound_unit
    (c : FragCert.Closed .unit .unit) :
    FragCert.denote c =
      FragmentContext.closedPoint routeAFragmentModel.unitIntro :=
  routeAFragmentDenotationModel.denote_unit c

/-- Denotational soundness for closed bit literals. -/
theorem fragment_step_denote_sound_bitLit {b : Bool}
    (c : FragCert.Closed (.bitLit b) .bit) :
    FragCert.denote c =
      FragmentContext.closedPoint (routeAFragmentModel.bitLit b) :=
  routeAFragmentDenotationModel.denote_bitLit b c

/-- Combined closed-literal denotational soundness package. -/
theorem fragment_closed_literal_denote_sound :
    (∀ c : FragCert.Closed .unit .unit,
      FragCert.denote c =
        FragmentContext.closedPoint routeAFragmentModel.unitIntro) ∧
    (∀ b (c : FragCert.Closed (.bitLit b) .bit),
      FragCert.denote c =
        FragmentContext.closedPoint (routeAFragmentModel.bitLit b)) :=
  ⟨fragment_step_denote_sound_unit, fun _ => fragment_step_denote_sound_bitLit⟩

/-- Classical `ite true` redex denotation expands through the controlled
eliminator and the true bit literal. -/
theorem fragment_step_denote_sound_iteTrue {Γ Δ Δ₁ Δ₂ A T E}
    (hΓ : CtxUAllBit Γ) (hΔctx : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
    (hΔ₁ : AllNone Δ₁)
    (hL₁ : CtxLAllSomeFragment Δ₁)
    (cT : FragCert Γ Δ₂ T A) (cE : FragCert Γ Δ₂ E A) :
    FragCert.denote
        (.ite hΓ hΔctx hs hA
          (.bitLit hΓ hL₁ true hΔ₁) cT cE) =
      Hom.comp (routeAFragmentBranching.iteElim hA)
        (Hom.comp
          (DayTensor.map
            (FragmentContext.combinedPoint hΓ hΔ₁
              (routeAFragmentModel.bitLit true))
            (additivePair (FragCert.denote cT) (FragCert.denote cE)))
          (FragmentContext.combinedOSplit hΓ hs)) :=
  rfl

/-- Classical `ite false` redex denotation expands through the controlled
eliminator and the false bit literal. -/
theorem fragment_step_denote_sound_iteFalse {Γ Δ Δ₁ Δ₂ A T E}
    (hΓ : CtxUAllBit Γ) (hΔctx : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
    (hΔ₁ : AllNone Δ₁)
    (hL₁ : CtxLAllSomeFragment Δ₁)
    (cT : FragCert Γ Δ₂ T A) (cE : FragCert Γ Δ₂ E A) :
    FragCert.denote
        (.ite hΓ hΔctx hs hA
          (.bitLit hΓ hL₁ false hΔ₁) cT cE) =
      Hom.comp (routeAFragmentBranching.iteElim hA)
        (Hom.comp
          (DayTensor.map
            (FragmentContext.combinedPoint hΓ hΔ₁
              (routeAFragmentModel.bitLit false))
            (additivePair (FragCert.denote cT) (FragCert.denote cE)))
          (FragmentContext.combinedOSplit hΓ hs)) :=
  rfl

/-- Measurement continuation denotation agrees with `measureElim`. -/
theorem fragment_measStep_denote_sound_measure {Γ Δ Δ₁ Δ₂ A Q K}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
    (cQ : FragCert Γ Δ₁ Q .qubit)
    (cK : FragCert Γ Δ₂ K (.arrow .unres .bit (.arrow .lin .qubit A))) :
    FragCert.denote (.measure hΓ hΔ hs hA cQ cK) =
      Hom.comp (FragCert.measureElim _)
        (Hom.comp
          (DayTensor.map (FragCert.denote cQ) (FragCert.denote cK))
          (FragmentContext.combinedOSplit hΓ hs)) :=
  FragCert.denote_measure_eq hΓ hΔ hs hA cQ cK

/-- Measurement branch maps agree with the Yoneda packaging (Born side). -/
theorem fragment_measStep_denote_sound_branch (b : Bool) :
    routeAFragmentModel.measureBranch b = measureBranchYoneda b :=
  fragment_measureBranch_agrees b

/-- Package: fragment-admitted operational constructors have denotational
soundness equations on `FragCert.denote`. -/
theorem fragment_step_denote_sound :
    (∀ c : FragCert.Closed .unit .unit,
      FragCert.denote c =
        FragmentContext.closedPoint routeAFragmentModel.unitIntro) ∧
    (∀ b (c : FragCert.Closed (.bitLit b) .bit),
      FragCert.denote c =
        FragmentContext.closedPoint (routeAFragmentModel.bitLit b)) ∧
    (∀ b, routeAFragmentModel.measureBranch b = measureBranchYoneda b) :=
  ⟨fragment_step_denote_sound_unit, fun _ => fragment_step_denote_sound_bitLit,
    fragment_measStep_denote_sound_branch⟩

/-- Alias retained for citations that name measurement soundness separately. -/
theorem fragment_measStep_denote_sound :
    (∀ b, routeAFragmentModel.measureBranch b = measureBranchYoneda b) :=
  fragment_measStep_denote_sound_branch

/-- Linear first-order evaluation uses the representable closed structure. -/
theorem fragment_linear_eval_agrees (d : ℕ) (N : Module) :
    FragmentContext.evalFirstOrder d N =
      Hom.comp (FragmentContext.dayEval (representable d) N)
        (DayTensor.map
          (dayInternalHomRepresentableIso d N).inv
          (Hom.id (representable d))) :=
  rfl

/-- Classical-bit comonoid supplies unrestricted copy/discard laws. -/
theorem fragment_classical_bit_comonoid :
    FragmentContext.classicalBitComonoid.carrier = classicalBitModule ∧
    FragmentContext.classicalBitComonoid.counit = classicalBitWeakening ∧
    FragmentContext.classicalBitComonoid.comult = classicalBitContraction :=
  ⟨rfl, rfl, rfl⟩

end QLambda.Linear
