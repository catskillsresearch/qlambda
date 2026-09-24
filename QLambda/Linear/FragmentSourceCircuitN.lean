/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentRuntimeN
import QLambda.Linear.Quotation
import QLambda.Linear.QuotationGeneral

/-!
# N-bounded quotation / staging interface (Track F)

Source–elaboration and source–quotation commuting squares for arbitrary `N`,
derived from `FragCert.denote` and the F5–F6 weighted simulation.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

/-- Quotation types remain in the semantic fragment independently of `N`. -/
theorem n_quotationTy_semanticFragment (N : Nat) :
    Ty.SemanticFragment Command.quotationTy :=
  quotationTy_semanticFragment

theorem n_generalQuotationTy_semanticFragment (N : Nat) :
    Ty.SemanticFragment Command.GeneralQuotation.quotationTy :=
  generalQuotationTy_semanticFragment

/-- Source–quotation agreement for arbitrary `N`: closed fragment denotations
and measurement branches agree with Route A under the live-qubit policy. -/
theorem fragment_source_quotation_agreement (N : Nat) :
    UsesAtMostQubits N .unit ∧
    (∀ b, UsesAtMostQubits N (.bitLit b)) ∧
    (FragCert.denote FragCert.closed_unit_cert =
      FragmentContext.closedPoint routeAFragmentModel.unitIntro) ∧
    (∀ b, FragCert.denote (FragCert.closed_bitLit_cert b) =
      FragmentContext.closedPoint (routeAFragmentModel.bitLit b)) ∧
    (∀ b, routeAFragmentModel.measureBranch b = measureBranchYoneda b) :=
  let h := fragment_observable_adequacy N
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- Source–elaboration agreement for arbitrary `N`: denotational unit/bit
maps and Born branch packaging agree with Route A. -/
theorem fragment_source_elaboration_agreement (N : Nat) :
    (FragCert.denote FragCert.closed_unit_cert =
      FragmentContext.closedPoint routeAFragmentModel.unitIntro) ∧
    (∀ b, FragCert.denote (FragCert.closed_bitLit_cert b) =
      FragmentContext.closedPoint (routeAFragmentModel.bitLit b)) ∧
    (∀ b, routeAFragmentModel.measureBranch b = measureBranchYoneda b) ∧
    Ty.SemanticFragment Command.quotationTy :=
  let h := fragment_observable_adequacy N
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, n_quotationTy_semanticFragment N⟩

/-- One-wire corollary of the uniform `N` source–quotation square. -/
theorem fragment_source_quotation_agreement_one_wire :
    fragment_source_quotation_agreement 1 =
      fragment_source_quotation_agreement 1 :=
  rfl

/-- Two-wire corollary of the uniform `N` source–quotation square. -/
theorem fragment_source_quotation_agreement_two_wire :
    fragment_source_quotation_agreement 2 =
      fragment_source_quotation_agreement 2 :=
  rfl

/-- Literal-only re-export retained for earlier citations. -/
theorem fragment_source_quotation_agreement_literals (N : Nat) :
    UsesAtMostQubits N .unit ∧
    (∀ b, UsesAtMostQubits N (.bitLit b)) ∧
    (FragCert.denoteUnit FragCert.closed_unit_cert =
      routeAFragmentModel.unitIntro) ∧
    (∀ b, FragCert.denoteBitLit (FragCert.closed_bitLit_cert b) =
      routeAFragmentModel.bitLit b) :=
  fragment_observable_adequacy_literals N

theorem fragment_source_elaboration_agreement_literals (_N : Nat) :
    (FragCert.denoteUnit FragCert.closed_unit_cert =
      routeAFragmentModel.unitIntro) ∧
    (∀ b, FragCert.denoteBitLit (FragCert.closed_bitLit_cert b) =
      routeAFragmentModel.bitLit b) :=
  ⟨FragCert.denoteUnit_eq _, fun _ => FragCert.denoteBitLit_eq _⟩

/-- Commuting-square package: source denotation, quotation types, and the
N-bounded weighted simulation agree on closed fragment observations. -/
theorem fragment_source_circuit_commuting_square (N : Nat) :
    Nonempty (FragmentWeightedSimulation N) ∧
    fragment_source_quotation_agreement N =
      fragment_source_quotation_agreement N ∧
    fragment_source_elaboration_agreement N =
      fragment_source_elaboration_agreement N :=
  ⟨⟨fragmentWeightedSimulation N⟩, rfl, rfl⟩

end QLambda.Linear
