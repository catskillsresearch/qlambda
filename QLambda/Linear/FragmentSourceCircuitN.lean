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

Source–elaboration and source–quotation packages for arbitrary `N`, built from
`FragCert.denote` on closed unit/bit observations, F5–F6 weighted simulation
(Born mass + `measureBranch = measureBranchYoneda`), fragment certificates for
`Command.quote` of `Quotable` commands, and CQ equalities for quotation compile /
reflect / staged elaboration.

**Claimed.** Closed unit/bit `FragCert.denote` matches Route A; quotable commands
have nonempty `FragCert.Closed` certificates; `Quotation.denote_compile` /
`denote_reflect` and `elaborates_compile_agreement` give CQ equalities;
measurement branches and Born sums agree under `q ≤ N`.

**Not claimed.** Equality or isomorphism between `FragCert.denote` (Day/Hom
semantics) and `CQ.Sem` / `Quotation.denote` / `Command.denote` — those live in
different semantic domains.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

open QLambda.CQ

/-- Quotation types remain in the semantic fragment independently of `N`. -/
theorem n_quotationTy_semanticFragment (_N : Nat) :
    Ty.SemanticFragment Command.quotationTy :=
  quotationTy_semanticFragment

theorem n_generalQuotationTy_semanticFragment (_N : Nat) :
    Ty.SemanticFragment Command.GeneralQuotation.quotationTy :=
  generalQuotationTy_semanticFragment

/-- Classical quotation expressions inherit fragment binder discipline from
their current classical slot. -/
theorem quoteCExpr_fragmentBinders (current : Term)
    (hc : FragCert.FragmentBinders current) :
    ∀ e : Composer.CExpr 1, FragCert.FragmentBinders (Command.quoteCExpr current e) := by
  intro e
  induction e with
  | lit _ => trivial
  | bit _ => exact hc
  | not e ih =>
      exact ⟨ih, trivial, trivial⟩
  | and _ _ ih₁ ih₂ =>
      exact ⟨ih₁, ih₂, trivial⟩
  | or _ _ ih₁ ih₂ =>
      exact ⟨ih₁, trivial, ih₂⟩
  | xor _ _ ih₁ ih₂ =>
      exact ⟨ih₁, ⟨ih₂, trivial, trivial⟩, ih₂⟩

/-- Continuations that preserve fragment binders. -/
def ContinuationFragmentBinders (k : Term → Term) : Prop :=
  ∀ t, FragCert.FragmentBinders t → FragCert.FragmentBinders (k t)

/-- CPS quotation bodies stay inside `FragCert.FragmentBinders`. -/
theorem quoteBody_fragmentBinders {C : Command 1 1} (hC : C.Quotable)
    {current : Term} {k : Term → Term}
    (hc : FragCert.FragmentBinders current)
    (hk : ContinuationFragmentBinders k) :
    FragCert.FragmentBinders (Command.quoteBody C current k) := by
  induction hC generalizing current k with
  | skip =>
      exact hk current hc
  | x =>
      refine ⟨⟨Ty.FirstOrder.qubit, hk current hc⟩, ?_⟩
      change True ∧ True
      exact ⟨trivial, trivial⟩
  | h =>
      refine ⟨⟨Ty.FirstOrder.qubit, hk current hc⟩, ?_⟩
      change True ∧ True
      exact ⟨trivial, trivial⟩
  | t =>
      refine ⟨⟨Ty.FirstOrder.qubit, hk current hc⟩, ?_⟩
      change True ∧ True
      exact ⟨trivial, trivial⟩
  | ry =>
      refine ⟨⟨Ty.FirstOrder.qubit, hk current hc⟩, ?_⟩
      change True ∧ True
      exact ⟨trivial, trivial⟩
  | measure =>
      refine ⟨trivial, ⟨rfl, ⟨Ty.FirstOrder.qubit, ?_⟩⟩⟩
      exact hk (.var .unres 0) trivial
  | reset =>
      refine ⟨⟨Ty.FirstOrder.qubit, hk current hc⟩, ?_⟩
      change True ∧ True
      exact ⟨trivial, trivial⟩
  | store =>
      exact hk _ (quoteCExpr_fragmentBinders current hc _)
  | seq _ _ ihA ihB =>
      exact ihA hc (fun t ht => ihB ht hk)
  | branch _ _ ihy ihn =>
      exact ⟨quoteCExpr_fragmentBinders current hc _,
        ihy hc hk, ihn hc hk⟩

/-- Canonical quotations obey fragment binder discipline. -/
theorem quote_fragmentBinders {C : Command 1 1} (hC : C.Quotable) :
    FragCert.FragmentBinders C.quote := by
  unfold Command.quote
  refine ⟨rfl, ⟨Ty.FirstOrder.qubit, ?_⟩⟩
  exact quoteBody_fragmentBinders hC trivial fun t ht => ⟨trivial, ht⟩

/-- Every quotable one-wire command has a closed fragment certificate for its
canonical quotation. -/
theorem fragment_quote_has_fragCert {C : Command 1 1} (hC : C.Quotable) :
    Nonempty (FragCert.Closed C.quote Command.quotationTy) :=
  ⟨FragCert.ofHasType
    (FragCert.fragmentJudgment_of_hasType (Command.quote_typed hC)
      CtxUAllBit.nil CtxLAllSomeFragment.nil
      (quote_fragmentBinders hC) quotationTy_semanticFragment)⟩

theorem fragment_quote_has_fragCert_skip :
    Nonempty (FragCert.Closed Command.skip.quote Command.quotationTy) :=
  fragment_quote_has_fragCert .skip

theorem fragment_quote_has_fragCert_x {w : Fin 1} :
    Nonempty (FragCert.Closed (Command.x w).quote Command.quotationTy) :=
  fragment_quote_has_fragCert .x

theorem fragment_quote_has_fragCert_h {w : Fin 1} :
    Nonempty (FragCert.Closed (Command.h w).quote Command.quotationTy) :=
  fragment_quote_has_fragCert .h

/-- Propositional content of the N-bounded source–quotation package. -/
def FragmentSourceQuotationAgreement (N : Nat) : Prop :=
  UsesAtMostQubits N .unit ∧
  (∀ b, UsesAtMostQubits N (.bitLit b)) ∧
  (FragCert.denote FragCert.closed_unit_cert =
    FragmentContext.closedPoint routeAFragmentModel.unitIntro) ∧
  (∀ b, FragCert.denote (FragCert.closed_bitLit_cert b) =
    FragmentContext.closedPoint (routeAFragmentModel.bitLit b)) ∧
  (∀ b, routeAFragmentModel.measureBranch b = measureBranchYoneda b) ∧
  (∀ (q : Nat) (_hq : q ≤ N) (w : Fin q) (ρ : Runtime.RegisterState q),
    Runtime.RegisterState.measureProbability ρ w false +
      Runtime.RegisterState.measureProbability ρ w true = 1) ∧
  (∀ C (_hC : Command.Quotable C),
    Nonempty (FragCert.Closed C.quote Command.quotationTy)) ∧
  (∀ (model : Composer.Model 1 1) (Q : Command.Quotation),
    CQ.Eq (Q.denote model) (Q.compile.denote model))

/-- Source–quotation agreement for arbitrary `N`: closed fragment denotations
and measurement branches agree with Route A under the live-qubit policy. -/
theorem fragment_source_quotation_agreement (N : Nat) :
    FragmentSourceQuotationAgreement N :=
  let h := fragment_observable_adequacy N
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2,
    fun _ hC => fragment_quote_has_fragCert hC,
    fun model Q => Command.Quotation.denote_compile model Q⟩

/-- Propositional content of the N-bounded source–elaboration package. -/
def FragmentSourceElaborationAgreement (_N : Nat) : Prop :=
  (FragCert.denote FragCert.closed_unit_cert =
    FragmentContext.closedPoint routeAFragmentModel.unitIntro) ∧
  (∀ b, FragCert.denote (FragCert.closed_bitLit_cert b) =
    FragmentContext.closedPoint (routeAFragmentModel.bitLit b)) ∧
  (∀ b, routeAFragmentModel.measureBranch b = measureBranchYoneda b) ∧
  Ty.SemanticFragment Command.quotationTy ∧
  (∀ C (_hC : Command.Quotable C),
    Nonempty (FragCert.Closed C.quote Command.quotationTy)) ∧
  (∀ {q c fuel M} {P : Compilation q c M} (_h : Elaborates fuel M P)
    (model : Composer.Model q c),
    CQ.Eq (Composer.denoteBlock model P.command.compile)
      (P.command.denote model))

/-- Source–elaboration agreement for arbitrary `N`: denotational unit/bit
maps, Born packaging, quotation certificates, and staged CQ compile
agreement. -/
theorem fragment_source_elaboration_agreement (N : Nat) :
    FragmentSourceElaborationAgreement N :=
  let h := fragment_observable_adequacy N
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, n_quotationTy_semanticFragment N,
    fun _ hC => fragment_quote_has_fragCert hC,
    fun {_q _c _fuel _M _P} h model => elaborates_compile_agreement h model⟩

/-- One-wire specialization of the uniform `N` source–quotation package. -/
theorem fragment_source_quotation_agreement_one_wire :
    FragmentSourceQuotationAgreement 1 :=
  fragment_source_quotation_agreement 1

/-- Two-wire specialization of the uniform `N` source–quotation package. -/
theorem fragment_source_quotation_agreement_two_wire :
    FragmentSourceQuotationAgreement 2 :=
  fragment_source_quotation_agreement 2

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

/-- Commuting-square package: weighted simulation, quote certificates, CQ
compile/reflect equalities, and the N-bounded source packages.  Does not
identify `FragCert.denote` with `CQ.Sem`. -/
theorem fragment_source_circuit_commuting_square (N : Nat) :
    Nonempty (FragmentWeightedSimulation N) ∧
    (∀ C (_hC : Command.Quotable C),
      Nonempty (FragCert.Closed C.quote Command.quotationTy)) ∧
    (∀ (model : Composer.Model 1 1) (Q : Command.Quotation),
      CQ.Eq (Q.denote model) (Q.compile.denote model)) ∧
    (∀ (model : Composer.Model 1 1) (C : Command 1 1) (hC : C.Quotable),
      CQ.Eq ((Command.Quotation.reflect C hC).denote model) (C.denote model)) ∧
    FragmentSourceQuotationAgreement N ∧
    FragmentSourceElaborationAgreement N :=
  ⟨⟨fragmentWeightedSimulation N⟩,
    fun _ hC => fragment_quote_has_fragCert hC,
    fun model Q => Command.Quotation.denote_compile model Q,
    fun model C hC => Command.Quotation.denote_reflect model C hC,
    fragment_source_quotation_agreement N,
    fragment_source_elaboration_agreement N⟩

end QLambda.Linear
