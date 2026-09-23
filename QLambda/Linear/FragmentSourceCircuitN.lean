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

Retains the existing one- and two-wire quotation corollaries and records the
uniform `N` policy under which source–circuit agreement is stated for the
fragment.
-/

namespace QLambda.Linear

/-- Quotation types remain in the semantic fragment independently of `N`. -/
theorem n_quotationTy_semanticFragment (N : Nat) :
    Ty.SemanticFragment Command.quotationTy :=
  quotationTy_semanticFragment

theorem n_generalQuotationTy_semanticFragment (N : Nat) :
    Ty.SemanticFragment Command.GeneralQuotation.quotationTy :=
  generalQuotationTy_semanticFragment

/-- Source–quotation agreement for the zero-qubit closed literal fragment:
denotational unit/bit maps agree with Route A, under any live-qubit bound. -/
theorem fragment_source_quotation_agreement_literals (N : Nat) :
    UsesAtMostQubits N .unit ∧
    (∀ b, UsesAtMostQubits N (.bitLit b)) ∧
    (FragCert.denoteUnit FragCert.closed_unit_cert =
      routeAFragmentModel.unitIntro) ∧
    (∀ b, FragCert.denoteBitLit (FragCert.closed_bitLit_cert b) =
      routeAFragmentModel.bitLit b) :=
  fragment_observable_adequacy_literals N

/-- Staging/elaboration agreement marker for N-bounded literals (reuses closed
literal adequacy; full command-level commuting squares remain open). -/
theorem fragment_source_elaboration_agreement_literals (_N : Nat) :
    (FragCert.denoteUnit FragCert.closed_unit_cert =
      routeAFragmentModel.unitIntro) ∧
    (∀ b, FragCert.denoteBitLit (FragCert.closed_bitLit_cert b) =
      routeAFragmentModel.bitLit b) :=
  ⟨FragCert.denoteUnit_eq _, fun _ => FragCert.denoteBitLit_eq _⟩

end QLambda.Linear
