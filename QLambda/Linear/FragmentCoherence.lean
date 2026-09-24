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
fragment, stated on `FragCert.denote`.  Closed literals, closed first-order
`ite` β, Day closedness triangles, and compositional application spines are
kernel-checked; open-term equality to `subst` remains out of scope.
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

/-- Closed first-order `ite true` reduces denotationally to the then branch. -/
theorem fragment_step_denote_sound_iteTrue_closed {A : Ty}
    (hFO : Ty.FirstOrder A) {T E : Term}
    (cT : FragCert.Closed T A) (cE : FragCert.Closed E A) :
    FragCert.denote
        (.ite CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
          (Ty.SemanticFragment.ofFirstOrder hFO)
          (FragCert.closed_bitLit_cert true) cT cE) =
      FragCert.denote cT :=
  FragCert.denote_ite_true_closed hFO cT cE

/-- Closed first-order `ite false` reduces denotationally to the else branch. -/
theorem fragment_step_denote_sound_iteFalse_closed {A : Ty}
    (hFO : Ty.FirstOrder A) {T E : Term}
    (cT : FragCert.Closed T A) (cE : FragCert.Closed E A) :
    FragCert.denote
        (.ite CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
          (Ty.SemanticFragment.ofFirstOrder hFO)
          (FragCert.closed_bitLit_cert false) cT cE) =
      FragCert.denote cE :=
  FragCert.denote_ite_false_closed hFO cT cE

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

/-- Day β: evaluating a curried Day morphism recovers the original. -/
theorem fragment_day_beta {X A N : Module}
    (f : Hom (dayTensor X A) N) :
    Hom.comp (FragmentContext.dayEval A N)
      (DayTensor.map (FragmentContext.dayCurry f) (Hom.id A)) =
      f :=
  FragmentContext.dayEval_dayCurry f

/-- Day η: currying an evaluated Day morphism recovers the original. -/
theorem fragment_day_eta {X A N : Module}
    (g : Hom X (dayInternalHom A N)) :
    FragmentContext.dayCurry
        (Hom.comp (FragmentContext.dayEval A N)
          (DayTensor.map g (Hom.id A))) =
      g :=
  FragmentContext.dayCurry_dayEval g

/-- Package: fragment-admitted operational constructors have denotational
soundness equations on `FragCert.denote`, including closed FO `ite` β and
Day closedness triangles. -/
theorem fragment_step_denote_sound :
    (∀ c : FragCert.Closed .unit .unit,
      FragCert.denote c =
        FragmentContext.closedPoint routeAFragmentModel.unitIntro) ∧
    (∀ b (c : FragCert.Closed (.bitLit b) .bit),
      FragCert.denote c =
        FragmentContext.closedPoint (routeAFragmentModel.bitLit b)) ∧
    (∀ b, routeAFragmentModel.measureBranch b = measureBranchYoneda b) ∧
    (∀ {A : Ty} (hFO : Ty.FirstOrder A) {T E : Term}
        (cT : FragCert.Closed T A) (cE : FragCert.Closed E A),
      FragCert.denote
          (.ite CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
            (Ty.SemanticFragment.ofFirstOrder hFO)
            (FragCert.closed_bitLit_cert true) cT cE) =
        FragCert.denote cT) ∧
    (∀ {A : Ty} (hFO : Ty.FirstOrder A) {T E : Term}
        (cT : FragCert.Closed T A) (cE : FragCert.Closed E A),
      FragCert.denote
          (.ite CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
            (Ty.SemanticFragment.ofFirstOrder hFO)
            (FragCert.closed_bitLit_cert false) cT cE) =
        FragCert.denote cE) ∧
    (∀ {X A N : Module} (f : Hom (dayTensor X A) N),
      Hom.comp (FragmentContext.dayEval A N)
          (DayTensor.map (FragmentContext.dayCurry f) (Hom.id A)) =
        f) ∧
    (∀ {X A N : Module} (g : Hom X (dayInternalHom A N)),
      FragmentContext.dayCurry
          (Hom.comp (FragmentContext.dayEval A N)
            (DayTensor.map g (Hom.id A))) =
        g) :=
  ⟨fragment_step_denote_sound_unit, fun _ => fragment_step_denote_sound_bitLit,
    fragment_measStep_denote_sound_branch,
    fun {_A} hFO {_T} {_E} cT cE =>
      fragment_step_denote_sound_iteTrue_closed hFO cT cE,
    fun {_A} hFO {_T} {_E} cT cE =>
      fragment_step_denote_sound_iteFalse_closed hFO cT cE,
    fun {_X} {_A} {_N} f => fragment_day_beta f,
    fun {_X} {_A} {_N} g => fragment_day_eta g⟩

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

/-- Semantic substitution spine for linear application: denotation of
`appL (lamL body) arg` expands as `eval ∘ (lam ⊗ arg) ∘ split`. -/
theorem fragment_subst_lin_spine {Γ Δ Δ₁ Δ₂ A B M X}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hAd : Ty.Admissible A) (hFO : Ty.FirstOrder A)
    (hB : Ty.SemanticFragment B)
    (hL₁ : CtxLAllSomeFragment Δ₁)
    (cBody : FragCert Γ (some A :: Δ₁) M B)
    (cX : FragCert Γ Δ₂ X A) :
    FragCert.denote
        (.appL hΓ hΔ hs hFO hB
          (.lamL hΓ hL₁ hAd hFO hB cBody) cX) =
      Hom.comp (FragmentContext.evalFragmentFirstOrder hFO _)
        (Hom.comp
          (DayTensor.map
            (FragmentContext.abstractLinear hFO (FragCert.denote cBody))
            (FragCert.denote cX))
          (FragmentContext.combinedOSplit hΓ hs)) := by
  rw [FragCert.denote_appL_eq, FragCert.denote_lamL_eq]
  rfl

/-- Semantic substitution spine for unrestricted bit application: denotation of
`appU (lamU body) arg` expands as `eval ∘ (lam ⊗ arg) ∘ split`. -/
theorem fragment_subst_unres_bit_spine {Γ Δ ΔF ΔX B M X}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ ΔF ΔX) (hAd : Ty.Admissible .bit)
    (hDup : Ty.Duplicable .bit) (hN : AllNone ΔX)
    (hArr : Ty.SemanticFragment (.arrow .unres .bit B))
    (hB : Ty.SemanticFragment B)
    (hLF : CtxLAllSomeFragment ΔF) (hΔF : AllNone ΔF)
    (cBody : FragCert (.bit :: Γ) ΔF M B)
    (cX : FragCert Γ ΔX X .bit) :
    FragCert.denote
        (.appU hΓ hΔ hs hN hB
          (.lamU hΓ hLF hAd hDup hΔF hArr cBody) cX) =
      Hom.comp (FragmentContext.evalUnrestrictedBit _)
        (Hom.comp
          (DayTensor.map
            (FragmentContext.abstractUnrestricted (FragCert.denote cBody))
            (FragCert.denote cX))
          (FragmentContext.combinedOSplit hΓ hs)) := by
  rw [FragCert.denote_appU_eq, FragCert.denote_lamU_eq]
  rfl

end QLambda.Linear
