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
measurement branches and Born sums agree under `q ≤ N`.  Hom-side foothold:
hand-built `fragCert_skip_quote` denotes as the Day curry / `tensorIntro` /
lookup spine `quoteSkipSpine` (and likewise gate spines for `x`/`h` when
built); `Prim.superoperator .x` agrees definitionally with the canonical
Composer gate after `yonedaMap`.

**Not claimed.** A full interpret functor from quoted `FragCert.denote` into
`CQ.Sem` for arbitrary commands.  Thin CQ-side: `Command.skip.denote = CQ.skip`.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

open QLambda.CQ
open Domain.Presheaf
open Domain.Presheaf.SuperoperatorModule
open DayTensor

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

/-! ## Hom-side bridge foothold (skip / gate spines) -/

private theorem quote_bit_admissible : Ty.Admissible .bit := by
  decide

private theorem quote_qubit_admissible : Ty.Admissible .qubit := by
  decide

private theorem quote_bit_duplicable : Ty.Duplicable .bit := by
  decide

private theorem quote_ctxU_bit : CtxUAllBit [.bit] :=
  CtxUAllBit.cons CtxUAllBit.nil

private theorem quote_ctxL_live0 :
    CtxLAllSomeFragment [some (.qubit : Ty)] :=
  CtxLAllSomeFragment.cons_some Ty.SemanticFragment.qubit
    CtxLAllSomeFragment.nil

private theorem quote_ctxL_none :
    CtxLAllSomeFragment [none] :=
  CtxLAllSomeFragment.cons_none CtxLAllSomeFragment.nil

/-- Linear qubit variable in the skip-quote pair body. -/
noncomputable def fragCert_skip_varL :
    FragCert [.bit] [some .qubit] (.var .lin 0) .qubit :=
  .varL quote_ctxU_bit quote_ctxL_live0 Lookup.zero
    (by simp [OnlySomeAt, AllNone]) Ty.SemanticFragment.qubit

/-- Unrestricted classical slot in the skip-quote pair body. -/
noncomputable def fragCert_skip_varU :
    FragCert [.bit] [none] (.var .unres 0) .bit :=
  .varU quote_ctxU_bit quote_ctxL_none Lookup.zero quote_bit_duplicable
    (by simp [AllNone]) Ty.SemanticFragment.bit

/-- Pair body `(varL 0, varU 0)` of `Command.skip.quote`. -/
noncomputable def fragCert_skip_pair :
    FragCert [.bit] [some .qubit]
      (.pair (.var .lin 0) (.var .unres 0))
      (.tensor .qubit .bit) :=
  .pair quote_ctxU_bit quote_ctxL_live0 (OSplit.left OSplit.nil)
    Ty.FirstOrder.qubit Ty.FirstOrder.bit
    fragCert_skip_varL fragCert_skip_varU

/-- Inner linear abstraction of `Command.skip.quote`. -/
noncomputable def fragCert_skip_lamL :
    FragCert [.bit] []
      (.lam .lin .qubit (.pair (.var .lin 0) (.var .unres 0)))
      (.arrow .lin .qubit (.tensor .qubit .bit)) :=
  .lamL quote_ctxU_bit CtxLAllSomeFragment.nil quote_qubit_admissible
    Ty.FirstOrder.qubit
    (Ty.SemanticFragment.tensor Ty.FirstOrder.qubit Ty.FirstOrder.bit)
    fragCert_skip_pair

/-- Hand-built closed `FragCert` for `Command.skip.quote` (preferred over
`ofHasType`). -/
noncomputable def fragCert_skip_quote :
    FragCert.Closed Command.skip.quote Command.quotationTy :=
  .lamU CtxUAllBit.nil CtxLAllSomeFragment.nil quote_bit_admissible
    quote_bit_duplicable (by simp [AllNone]) quotationTy_semanticFragment
    fragCert_skip_lamL

/-- Day curry / `tensorIntro` / lookup spine matching `Command.skip.quote`. -/
noncomputable def quoteSkipSpine :
    Hom (FragmentContext.combined [] [])
      (fragmentModule Command.quotationTy) :=
  FragCert.denote fragCert_skip_quote

/-- Explicit Day expansion of `quoteSkipSpine` through curry / pair / lookup. -/
theorem quoteSkipSpine_eq :
    quoteSkipSpine =
      FragmentContext.abstractUnrestricted
        (FragmentContext.abstractLinear Ty.FirstOrder.qubit
          (Hom.comp
            (FragmentContext.tensorIntro Ty.FirstOrder.qubit Ty.FirstOrder.bit)
            (Hom.comp
              (DayTensor.map
                (FragCert.denote fragCert_skip_varL)
                (FragCert.denote fragCert_skip_varU))
              (FragmentContext.combinedOSplit quote_ctxU_bit
                (OSplit.left OSplit.nil))))) := by
  have hU :=
    FragCert.denote_lamU_eq CtxUAllBit.nil CtxLAllSomeFragment.nil
      quote_bit_admissible quote_bit_duplicable (by simp [AllNone])
      quotationTy_semanticFragment fragCert_skip_lamL
  have hL :=
    FragCert.denote_lamL_eq quote_ctxU_bit CtxLAllSomeFragment.nil
      quote_qubit_admissible Ty.FirstOrder.qubit
      (Ty.SemanticFragment.tensor Ty.FirstOrder.qubit Ty.FirstOrder.bit)
      fragCert_skip_pair
  have hP :=
    FragCert.denote_pair_eq quote_ctxU_bit quote_ctxL_live0
      (OSplit.left OSplit.nil) Ty.FirstOrder.qubit Ty.FirstOrder.bit
      fragCert_skip_varL fragCert_skip_varU
  simp only [quoteSkipSpine, fragCert_skip_quote, fragCert_skip_lamL,
    fragCert_skip_pair]
  exact hU.trans <| congrArg _ <| hL.trans <| congrArg _ hP

/-- The hand-built skip certificate denotes as `quoteSkipSpine`. -/
theorem fragCert_skip_quote_denote :
    FragCert.denote fragCert_skip_quote = quoteSkipSpine :=
  rfl

/-- Any closed certificate for `Command.skip.quote` denotes as the skip spine
(via the hand-built certificate and proof-witness independence of `denote`). -/
theorem fragCert_skip_quote_denote_independent
    (c : FragCert.Closed Command.skip.quote Command.quotationTy) :
    FragCert.denote c = quoteSkipSpine := by
  refine Eq.trans ?_ fragCert_skip_quote_denote
  -- Match the unique constructor spine of `Command.skip.quote`.
  cases c with
  | lamU hΓ hΔ hAd hDup hN hArr cLam =>
    cases cLam with
    | lamL hΓ' hΔ' hAd' hFO hB cPair =>
      cases cPair with
      | pair hΓp hΔp hs hA hB' cL cR =>
        cases hs with
        | left hs0 =>
          cases hs0
          cases cL with
          | varL hΓL hΔL hl ho hAq =>
            cases cR with
            | varU hΓR hΔR hlU hDupU hNone hAb =>
              simp only [fragCert_skip_quote, fragCert_skip_lamL,
                fragCert_skip_pair, fragCert_skip_varL, fragCert_skip_varU,
                FragCert.denote_lamU_eq, FragCert.denote_lamL_eq,
                FragCert.denote_pair_eq, FragCert.denote_varL_eq,
                FragCert.denote_varU_eq]
              congr
        | right hs0 =>
            cases hs0
            cases cL with
            | varL _ _ hl _ _ => cases hl

/-- Thin CQ-side interpret for skip: compilation is empty, so denotation is
`CQ.skip`. -/
theorem command_skip_denote_eq_CQ_skip {q c : ℕ}
    (model : Composer.Model q c) :
    Command.skip.denote model = CQ.skip :=
  rfl

/-! ### Gate-quote spines (`x` / `h`) -/

private theorem quote_ctxL_live_none :
    CtxLAllSomeFragment [some (.qubit : Ty), none] :=
  CtxLAllSomeFragment.cons_some Ty.SemanticFragment.qubit quote_ctxL_none

private theorem quote_ctxL_none_none :
    CtxLAllSomeFragment [none, none] :=
  CtxLAllSomeFragment.cons_none quote_ctxL_none

/-- Shared pair body of gate quotations after the post-gate linear binder. -/
noncomputable def fragCert_gate_pair_body :
    FragCert [.bit] [some .qubit, none]
      (.pair (.var .lin 0) (.var .unres 0))
      (.tensor .qubit .bit) :=
  .pair quote_ctxU_bit quote_ctxL_live_none
    (OSplit.left (OSplit.none OSplit.nil))
    Ty.FirstOrder.qubit Ty.FirstOrder.bit
    (.varL quote_ctxU_bit quote_ctxL_live_none Lookup.zero
      (by simp [OnlySomeAt, AllNone]) Ty.SemanticFragment.qubit)
    (.varU quote_ctxU_bit quote_ctxL_none_none Lookup.zero quote_bit_duplicable
      (by simp [AllNone]) Ty.SemanticFragment.bit)

/-- Continuation `λq. (q, classical)` used by gate quotations. -/
noncomputable def fragCert_gate_cont :
    FragCert [.bit] [none]
      (.lam .lin .qubit (.pair (.var .lin 0) (.var .unres 0)))
      (.arrow .lin .qubit (.tensor .qubit .bit)) :=
  .lamL quote_ctxU_bit quote_ctxL_none quote_qubit_admissible
    Ty.FirstOrder.qubit
    (Ty.SemanticFragment.tensor Ty.FirstOrder.qubit Ty.FirstOrder.bit)
    fragCert_gate_pair_body

/-- Closed prim certificate transported to the qubit-arrow type. -/
noncomputable def fragCert_gate_prim (p : Prim)
    (hp : primTy p = .arrow .lin .qubit .qubit) :
    FragCert [.bit] [none] (.prim p) (.arrow .lin .qubit .qubit) := by
  have c : FragCert [.bit] [none] (.prim p) (primTy p) :=
    .prim quote_ctxU_bit quote_ctxL_none p (by simp [AllNone])
  exact hp ▸ c

/-- Argument wire `varL 0` for a gate application. -/
noncomputable def fragCert_gate_wire :
    FragCert [.bit] [some .qubit] (.var .lin 0) .qubit :=
  .varL quote_ctxU_bit quote_ctxL_live0 Lookup.zero
    (by simp [OnlySomeAt, AllNone]) Ty.SemanticFragment.qubit

/-- Argument `prim p · varL 0` for a qubit-to-qubit gate primitive. -/
noncomputable def fragCert_gate_arg (p : Prim)
    (hp : primTy p = .arrow .lin .qubit .qubit) :
    FragCert [.bit] [some .qubit]
      (.app (.prim p) (.var .lin 0)) .qubit :=
  .appL quote_ctxU_bit quote_ctxL_live0 (OSplit.right OSplit.nil)
    Ty.FirstOrder.qubit Ty.SemanticFragment.qubit
    (fragCert_gate_prim p hp) fragCert_gate_wire

/-- Gate quotation body `app (λq. (q, c)) (p · wire)`. -/
noncomputable def fragCert_gate_body (p : Prim)
    (hp : primTy p = .arrow .lin .qubit .qubit) :
    FragCert [.bit] [some .qubit]
      (.app (.lam .lin .qubit (.pair (.var .lin 0) (.var .unres 0)))
        (.app (.prim p) (.var .lin 0)))
      (.tensor .qubit .bit) :=
  .appL quote_ctxU_bit quote_ctxL_live0 (OSplit.right OSplit.nil)
    Ty.FirstOrder.qubit
    (Ty.SemanticFragment.tensor Ty.FirstOrder.qubit Ty.FirstOrder.bit)
    fragCert_gate_cont (fragCert_gate_arg p hp)

/-- Inner linear abstraction of a gate quotation. -/
noncomputable def fragCert_gate_lamL (p : Prim)
    (hp : primTy p = .arrow .lin .qubit .qubit) :
    FragCert [.bit] []
      (.lam .lin .qubit
        (.app (.lam .lin .qubit (.pair (.var .lin 0) (.var .unres 0)))
          (.app (.prim p) (.var .lin 0))))
      (.arrow .lin .qubit (.tensor .qubit .bit)) :=
  .lamL quote_ctxU_bit CtxLAllSomeFragment.nil quote_qubit_admissible
    Ty.FirstOrder.qubit
    (Ty.SemanticFragment.tensor Ty.FirstOrder.qubit Ty.FirstOrder.bit)
    (fragCert_gate_body p hp)

/-- Hand-built closed `FragCert` for `(Command.x w).quote`. -/
noncomputable def fragCert_x_quote (w : Fin 1) :
    FragCert.Closed (Command.x w).quote Command.quotationTy :=
  .lamU CtxUAllBit.nil CtxLAllSomeFragment.nil quote_bit_admissible
    quote_bit_duplicable (by simp [AllNone]) quotationTy_semanticFragment
    (fragCert_gate_lamL .x rfl)

/-- Hand-built closed `FragCert` for `(Command.h w).quote`. -/
noncomputable def fragCert_h_quote (w : Fin 1) :
    FragCert.Closed (Command.h w).quote Command.quotationTy :=
  .lamU CtxUAllBit.nil CtxLAllSomeFragment.nil quote_bit_admissible
    quote_bit_duplicable (by simp [AllNone]) quotationTy_semanticFragment
    (fragCert_gate_lamL .h rfl)

/-- Day spine for a qubit gate quotation: outer curry around the gate body
(whose prim leaf is `denotePrimPoint`, hence `yonedaMap (Prim.superoperator p)`
after Route A agreement). -/
noncomputable def quoteGateSpine (p : Prim)
    (hp : primTy p = .arrow .lin .qubit .qubit) :
    Hom (FragmentContext.combined [] [])
      (fragmentModule Command.quotationTy) :=
  FragCert.denote
    (.lamU CtxUAllBit.nil CtxLAllSomeFragment.nil quote_bit_admissible
      quote_bit_duplicable (by simp [AllNone]) quotationTy_semanticFragment
      (fragCert_gate_lamL p hp))

theorem fragCert_x_quote_denote (w : Fin 1) :
    FragCert.denote (fragCert_x_quote w) = quoteGateSpine .x rfl :=
  rfl

theorem fragCert_h_quote_denote (w : Fin 1) :
    FragCert.denote (fragCert_h_quote w) = quoteGateSpine .h rfl :=
  rfl

/-- Gate-body spine expands through FO eval of the continuation against the
`Prim.superoperator` Yoneda point. -/
theorem quoteGateSpine_body_eq (p : Prim)
    (hp : primTy p = .arrow .lin .qubit .qubit) :
    FragCert.denote (fragCert_gate_body p hp) =
      Hom.comp (FragmentContext.evalFragmentFirstOrder Ty.FirstOrder.qubit _)
        (Hom.comp
          (DayTensor.map
            (FragCert.denote fragCert_gate_cont)
            (FragCert.denote (fragCert_gate_arg p hp)))
          (FragmentContext.combinedOSplit quote_ctxU_bit
            (OSplit.right OSplit.nil))) :=
  FragCert.denote_appL_eq quote_ctxU_bit quote_ctxL_live0
    (OSplit.right OSplit.nil) Ty.FirstOrder.qubit
    (Ty.SemanticFragment.tensor Ty.FirstOrder.qubit Ty.FirstOrder.bit)
    fragCert_gate_cont (fragCert_gate_arg p hp)

/-- Explicit outer expansion of `quoteGateSpine`. -/
theorem quoteGateSpine_eq (p : Prim)
    (hp : primTy p = .arrow .lin .qubit .qubit) :
    quoteGateSpine p hp =
      FragmentContext.abstractUnrestricted
        (FragmentContext.abstractLinear Ty.FirstOrder.qubit
          (FragCert.denote (fragCert_gate_body p hp))) := by
  have hU :=
    FragCert.denote_lamU_eq CtxUAllBit.nil CtxLAllSomeFragment.nil
      quote_bit_admissible quote_bit_duplicable (by simp [AllNone])
      quotationTy_semanticFragment (fragCert_gate_lamL p hp)
  have hL :=
    FragCert.denote_lamL_eq quote_ctxU_bit CtxLAllSomeFragment.nil
      quote_qubit_admissible Ty.FirstOrder.qubit
      (Ty.SemanticFragment.tensor Ty.FirstOrder.qubit Ty.FirstOrder.bit)
      (fragCert_gate_body p hp)
  simp only [quoteGateSpine, fragCert_gate_lamL]
  exact hU.trans <| congrArg _ hL

/-- After Yoneda, `Prim.superoperator .x` is the canonical Composer `x` gate. -/
theorem prim_superoperator_x_yoneda_canonicalModel :
    yonedaMap (Prim.superoperator .x) =
      yonedaMap
        (Superoperator.ofQuantumOperation
          ((Composer.canonicalModel 1 1).gate (.x (0 : Fin 1)))) :=
  rfl

theorem routeA_primMap_x_canonicalModel :
    routeAFragmentModel.primMap .x =
      yonedaMap
        (Superoperator.ofQuantumOperation
          ((Composer.canonicalModel 1 1).gate (.x (0 : Fin 1)))) := by
  rw [fragment_prim_superoperator]
  exact prim_superoperator_x_yoneda_canonicalModel

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
compile/reflect equalities, and the N-bounded source packages.  Hom-side
bridge step: `fragCert_skip_quote_denote` / `fragCert_skip_quote_denote_independent`
identify closed skip-quote denotation with `quoteSkipSpine` (gate quotes
likewise via `fragCert_x_quote_denote` / `fragCert_h_quote_denote`); CQ-side
thin interpret is `command_skip_denote_eq_CQ_skip`.  A full
`FragCert.denote`↔`CQ.Sem` interpret functor for arbitrary quoted commands
remains open. -/
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
