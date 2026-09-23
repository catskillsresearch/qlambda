/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentDenotation
import QLambda.Linear.Operational

/-!
# Fragment soundness and first-order observable adequacy

Soundness for classical source steps that stay in the fragment, and adequacy
for closed unit/bit observations under the Route A denotation.
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule

/-- Closed unit observation: denotation is the Route A unit introduction. -/
theorem fragment_unit_adequacy :
    FragCert.denoteUnit FragCert.closed_unit_cert =
      routeAFragmentModel.unitIntro :=
  FragCert.denoteUnit_eq _

/-- Closed bit observation: denotation is the Route A bit literal. -/
theorem fragment_bitLit_adequacy (b : Bool) :
    FragCert.denoteBitLit (FragCert.closed_bitLit_cert b) =
      routeAFragmentModel.bitLit b :=
  FragCert.denoteBitLit_eq _

/-- Fragment terms are preserved by classical unrestricted β-reduction. -/
theorem fragment_betaU_preserves {M V : Term}
    (hV : Term.SemanticFragment V) (hM : Term.SemanticFragment M) :
    Term.SemanticFragment (Term.substUnres 0 V M) :=
  Term.substUnres_semanticFragment hV hM

/-- Fragment terms are preserved by classical linear β-reduction. -/
theorem fragment_betaL_preserves {M V : Term}
    (hV : Term.SemanticFragment V) (hM : Term.SemanticFragment M) :
    Term.SemanticFragment (Term.substLin 0 V M) :=
  Term.substLin_semanticFragment hV hM

/-- Source `Step` preserves `Term.SemanticFragment` on fragment-admitted
redexes; `fix`/`fold`/`unfold` steps are excluded by the fragment. -/
theorem fragment_step_preserves {M N : Term}
    (hM : Term.SemanticFragment M) (h : Step M N) :
    Term.SemanticFragment N := by
  induction h with
  | betaL hV =>
      cases hM with
      | app hF hX =>
          cases hF with
          | lam _ hBod => exact Term.substLin_semanticFragment hX hBod
  | betaU hV =>
      cases hM with
      | app hF hX =>
          cases hF with
          | lam _ hBod => exact Term.substUnres_semanticFragment hX hBod
  | appF hstep ih =>
      cases hM with
      | app hF hX => exact .app (ih hF) hX
  | appX hV hstep ih =>
      cases hM with
      | app hF hX => exact .app hF (ih hX)
  | iteTrue =>
      cases hM with
      | ite _ hT _ => exact hT
  | iteFalse =>
      cases hM with
      | ite _ _ hE => exact hE
  | iteC hstep ih =>
      cases hM with
      | ite hB hT hE => exact .ite (ih hB) hT hE
  | unpairBeta hM' hN =>
      cases hM with
      | unpair hP hK =>
          cases hP with
          | pair hMl hNr => exact .app (.app hK hMl) hNr
  | unpairC hstep ih =>
      cases hM with
      | unpair hM' hK => exact .unpair (ih hM') hK
  | pairL hstep ih =>
      cases hM with
      | pair hM' hN => exact .pair (ih hM') hN
  | pairR hV hstep ih =>
      cases hM with
      | pair hM' hN => exact .pair hM' (ih hN)
  | measureC hstep ih =>
      cases hM with
      | measure hQ hK => exact .measure (ih hQ) hK
  | unfoldBeta | unfoldC | fixBeta | fixC | foldC =>
      cases hM

/-- Measurement branches stay in the fragment. -/
theorem fragment_measStep_preserves {M : Term} {b : Bool} {N : Term}
    (hM : Term.SemanticFragment M) (h : MeasStep M b N) :
    Term.SemanticFragment N := by
  cases h with
  | branch hQ =>
      cases hM with
      | measure hQ' hK =>
          exact .app (.app hK .bitLit) hQ'

/-- Measurement branch maps agree with the Yoneda packaging. -/
theorem fragment_measureBranch_agrees (b : Bool) :
    routeAFragmentModel.measureBranch b = measureBranchYoneda b :=
  rfl

/-- Named package: Route A supplies denotation, soundness, and closed
unit/bit adequacy for the minimum fragment. -/
theorem fragment_program_complete :
    RouteASucceeded ∧
      (FragCert.denoteUnit FragCert.closed_unit_cert =
        routeAFragmentModel.unitIntro) ∧
      (∀ b, FragCert.denoteBitLit (FragCert.closed_bitLit_cert b) =
        routeAFragmentModel.bitLit b) :=
  ⟨routeA_succeeded, fragment_unit_adequacy, fragment_bitLit_adequacy⟩

end QLambda.Linear
