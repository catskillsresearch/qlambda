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
soundness equations on `FragCert.denote`, including closed FO `ite` β,
Day closedness triangles, and FO Day β for linear abstraction. -/
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
        g) ∧
    (∀ (d : ℕ) {X N : Module}
        (f : Hom (dayTensor X (representable d)) N),
      Hom.comp (FragmentContext.evalFirstOrder d N)
          (DayTensor.map (FragmentContext.curryFirstOrder d f)
            (Hom.id (representable d))) =
        f) ∧
    (∀ {U L N : Module} {A : Ty} (hA : Ty.FirstOrder A)
        (body : Hom (dayTensor U (dayTensor (fragmentModule A) L)) N),
      Hom.comp (FragmentContext.evalFragmentFirstOrder hA N)
          (DayTensor.map (FragmentContext.abstractLinear hA body)
            (Hom.id (fragmentModule A))) =
        Hom.comp body
          (FragmentContext.moveArgumentIntoLinear U L (fragmentModule A))) :=
  ⟨fragment_step_denote_sound_unit, fun _ => fragment_step_denote_sound_bitLit,
    fragment_measStep_denote_sound_branch,
    fun {_A} hFO {_T} {_E} cT cE =>
      fragment_step_denote_sound_iteTrue_closed hFO cT cE,
    fun {_A} hFO {_T} {_E} cT cE =>
      fragment_step_denote_sound_iteFalse_closed hFO cT cE,
    fun {_X} {_A} {_N} f => fragment_day_beta f,
    fun {_X} {_A} {_N} g => fragment_day_eta g,
    fun d {_X} {_N} f => FragmentContext.evalFirstOrder_curryFirstOrder d f,
    fun {_U} {_L} {_N} {_A} hA body =>
      FragmentContext.evalFragmentFirstOrder_abstractLinear hA body⟩

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

/-! ## Closed identity β certificate constructors

Closed linear identity β (`fragment_betaL_id_unit` / `fragment_betaL_id_bit`)
is proved via FO Day β plus Day unitor/braiding cancellation against
`combinedOSplit_nil` / `closedPoint`.  Unrestricted identity β follows the
same spine once the unrestricted move cancels. -/

private theorem unit_admissible : Ty.Admissible .unit := by
  decide

private theorem bit_admissible : Ty.Admissible .bit := by
  decide

private theorem bit_duplicable : Ty.Duplicable .bit := by
  decide

private theorem ctxU_bit_nil : CtxUAllBit [.bit] := by
  intro A hm
  simp only [List.mem_cons] at hm
  rcases hm with rfl | hm
  · rfl
  · cases hm

/-- Linear identity body `varL 0` in a singleton unit context. -/
noncomputable def fragCert_varL0_unit :
    FragCert [] [some .unit] (.var .lin 0) .unit :=
  .varL CtxUAllBit.nil
    (CtxLAllSomeFragment.cons_some Ty.SemanticFragment.unit
      CtxLAllSomeFragment.nil)
    Lookup.zero trivial Ty.SemanticFragment.unit

/-- Closed linear identity combinator `λx. x` at unit. -/
noncomputable def fragCert_lamL_id_unit :
    FragCert [] [] (.lam .lin .unit (.var .lin 0))
      (.arrow .lin .unit .unit) :=
  .lamL CtxUAllBit.nil CtxLAllSomeFragment.nil unit_admissible
    Ty.FirstOrder.unit Ty.SemanticFragment.unit fragCert_varL0_unit

/-- Closed β-redex `app (λx. x) unit`. -/
noncomputable def fragCert_appL_id_unit :
    FragCert [] []
      (.app (.lam .lin .unit (.var .lin 0)) .unit) .unit :=
  .appL CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
    Ty.FirstOrder.unit Ty.SemanticFragment.unit
    fragCert_lamL_id_unit FragCert.closed_unit_cert

/-- Linear identity body `varL 0` in a singleton bit context. -/
noncomputable def fragCert_varL0_bit :
    FragCert [] [some .bit] (.var .lin 0) .bit :=
  .varL CtxUAllBit.nil
    (CtxLAllSomeFragment.cons_some Ty.SemanticFragment.bit
      CtxLAllSomeFragment.nil)
    Lookup.zero trivial Ty.SemanticFragment.bit

/-- Closed linear identity combinator `λx. x` at bit. -/
noncomputable def fragCert_lamL_id_bit :
    FragCert [] [] (.lam .lin .bit (.var .lin 0))
      (.arrow .lin .bit .bit) :=
  .lamL CtxUAllBit.nil CtxLAllSomeFragment.nil bit_admissible
    Ty.FirstOrder.bit Ty.SemanticFragment.bit fragCert_varL0_bit

/-- Closed β-redex `app (λx. x) (bitLit b)`. -/
noncomputable def fragCert_appL_id_bit (b : Bool) :
    FragCert [] []
      (.app (.lam .lin .bit (.var .lin 0)) (.bitLit b)) .bit :=
  .appL CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
    Ty.FirstOrder.bit Ty.SemanticFragment.bit
    fragCert_lamL_id_bit (FragCert.closed_bitLit_cert b)

/-- Unrestricted identity body `varU 0`. -/
noncomputable def fragCert_varU0_bit :
    FragCert [.bit] [] (.var .unres 0) .bit :=
  .varU ctxU_bit_nil CtxLAllSomeFragment.nil Lookup.zero
    bit_duplicable trivial Ty.SemanticFragment.bit

/-- Closed unrestricted identity combinator `λx. x` at bit. -/
noncomputable def fragCert_lamU_id_bit :
    FragCert [] [] (.lam .unres .bit (.var .unres 0))
      (.arrow .unres .bit .bit) :=
  .lamU CtxUAllBit.nil CtxLAllSomeFragment.nil bit_admissible bit_duplicable
    trivial (.arrowUnresBit Ty.SemanticFragment.bit) fragCert_varU0_bit

/-- Closed β-redex `appU (λx. x) (bitLit b)`. -/
noncomputable def fragCert_appU_id_bit (b : Bool) :
    FragCert [] []
      (.app (.lam .unres .bit (.var .unres 0)) (.bitLit b)) .bit :=
  .appU CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil trivial
    Ty.SemanticFragment.bit fragCert_lamU_id_bit
    (FragCert.closed_bitLit_cert b)

/-- Identity-body linear projection unfolds to unitors (enables closed β). -/
theorem fragCert_varL0_unit_denote :
    FragCert.denote fragCert_varL0_unit =
      Hom.comp (DayTensor.leftUnitor (fragmentModule .unit))
        (DayTensor.map (Hom.id dayTensorUnit)
          (Hom.comp (DayTensor.rightUnitor (fragmentModule .unit))
            (DayTensor.map (Hom.id (fragmentModule .unit))
              (Hom.id dayTensorUnit)))) := by
  simp only [fragCert_varL0_unit, FragCert.denote_varL_eq,
    FragmentContext.combinedLookupLinear,
    FragmentContext.linearOnlySomeAtProject,
    FragmentContext.linearOnlySomeAtProjectLists_singleton]
  rfl

/-- Spine expansion of the closed unit identity redex through FO Day eval. -/
theorem fragment_betaL_id_unit_spine :
    FragCert.denote fragCert_appL_id_unit =
      Hom.comp
        (FragmentContext.evalFragmentFirstOrder Ty.FirstOrder.unit _)
        (Hom.comp
          (DayTensor.map
            (FragmentContext.abstractLinear Ty.FirstOrder.unit
              (FragCert.denote fragCert_varL0_unit))
            (FragCert.denote FragCert.closed_unit_cert))
          (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) :=
  fragment_subst_lin_spine CtxUAllBit.nil CtxLAllSomeFragment.nil
    OSplit.nil unit_admissible Ty.FirstOrder.unit Ty.SemanticFragment.unit
    CtxLAllSomeFragment.nil fragCert_varL0_unit FragCert.closed_unit_cert

/-- Spine expansion of the closed bit identity redex. -/
theorem fragment_betaL_id_bit_spine (b : Bool) :
    FragCert.denote (fragCert_appL_id_bit b) =
      Hom.comp
        (FragmentContext.evalFragmentFirstOrder Ty.FirstOrder.bit _)
        (Hom.comp
          (DayTensor.map
            (FragmentContext.abstractLinear Ty.FirstOrder.bit
              (FragCert.denote fragCert_varL0_bit))
            (FragCert.denote (FragCert.closed_bitLit_cert b)))
          (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) :=
  fragment_subst_lin_spine CtxUAllBit.nil CtxLAllSomeFragment.nil
    OSplit.nil bit_admissible Ty.FirstOrder.bit Ty.SemanticFragment.bit
    CtxLAllSomeFragment.nil fragCert_varL0_bit (FragCert.closed_bitLit_cert b)

/-- Spine expansion of the closed unrestricted bit identity redex. -/
theorem fragment_betaU_id_bit_spine (b : Bool) :
    FragCert.denote (fragCert_appU_id_bit b) =
      Hom.comp (FragmentContext.evalUnrestrictedBit _)
        (Hom.comp
          (DayTensor.map
            (FragmentContext.abstractUnrestricted
              (FragCert.denote fragCert_varU0_bit))
            (FragCert.denote (FragCert.closed_bitLit_cert b)))
          (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) :=
  fragment_subst_unres_bit_spine CtxUAllBit.nil
    CtxLAllSomeFragment.nil OSplit.nil bit_admissible bit_duplicable trivial
    (.arrowUnresBit Ty.SemanticFragment.bit) Ty.SemanticFragment.bit
    CtxLAllSomeFragment.nil trivial fragCert_varU0_bit
    (FragCert.closed_bitLit_cert b)

/-- Unpair denotation expands through `unpairApply`. -/
theorem fragment_unpair_beta_spine {Γ Δ Δ₁ Δ₂ A B C M K}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B)
    (hC : Ty.SemanticFragment C)
    (cM : FragCert Γ Δ₁ M (.tensor A B))
    (cK : FragCert Γ Δ₂ K (.arrow .lin A (.arrow .lin B C))) :
    FragCert.denote (.unpair hΓ hΔ hs hA hB hC cM cK) =
      Hom.comp (FragmentContext.unpairApply hA hB _)
        (Hom.comp
          (DayTensor.map (FragCert.denote cM) (FragCert.denote cK))
          (FragmentContext.combinedOSplit hΓ hs)) :=
  FragCert.denote_unpair_eq hΓ hΔ hs hA hB hC cM cK

/-- Identity linear body simplifies to `λ ∘ (id ⊗ ρ)`. -/
theorem fragCert_varL0_unit_denote_simple :
    FragCert.denote fragCert_varL0_unit =
      Hom.comp (DayTensor.leftUnitor (fragmentModule .unit))
        (DayTensor.map (Hom.id dayTensorUnit)
          (DayTensor.rightUnitor (fragmentModule .unit))) := by
  rw [fragCert_varL0_unit_denote, DayTensor.map_id, Hom.comp_id]

theorem fragCert_varL0_bit_denote :
    FragCert.denote fragCert_varL0_bit =
      Hom.comp (DayTensor.leftUnitor (fragmentModule .bit))
        (DayTensor.map (Hom.id dayTensorUnit)
          (Hom.comp (DayTensor.rightUnitor (fragmentModule .bit))
            (DayTensor.map (Hom.id (fragmentModule .bit))
              (Hom.id dayTensorUnit)))) := by
  simp only [fragCert_varL0_bit, FragCert.denote_varL_eq,
    FragmentContext.combinedLookupLinear,
    FragmentContext.linearOnlySomeAtProject,
    FragmentContext.linearOnlySomeAtProjectLists_singleton]
  rfl

theorem fragCert_varL0_bit_denote_simple :
    FragCert.denote fragCert_varL0_bit =
      Hom.comp (DayTensor.leftUnitor (fragmentModule .bit))
        (DayTensor.map (Hom.id dayTensorUnit)
          (DayTensor.rightUnitor (fragmentModule .bit))) := by
  rw [fragCert_varL0_bit_denote, DayTensor.map_id, Hom.comp_id]

/-- Closed identity move/split cancellation against a Day-unit point. -/
theorem closed_identity_move_cancel {A : Module}
    (f : Hom dayTensorUnit A) :
    Hom.comp
      (Hom.comp (DayTensor.leftUnitor A)
        (DayTensor.map (DayTensor.rightUnitor dayTensorUnit) (Hom.id A)))
      (Hom.comp
        (DayTensor.map (Hom.id (FragmentContext.combined [] []))
          (Hom.comp f FragmentContext.combinedClosedCollapse))
        (DayTensor.map FragmentContext.closedLeftUnitorInv
          FragmentContext.closedLeftUnitorInv)) =
    Hom.comp f FragmentContext.combinedClosedCollapse := by
  have hsplit :
      Hom.comp
          (DayTensor.map (Hom.id (FragmentContext.combined [] []))
            (Hom.comp f FragmentContext.combinedClosedCollapse))
          (DayTensor.map FragmentContext.closedLeftUnitorInv
            FragmentContext.closedLeftUnitorInv) =
        DayTensor.map FragmentContext.closedLeftUnitorInv f := by
    have h :=
      (DayTensor.map_comp
        (Hom.id (FragmentContext.combined [] []))
        FragmentContext.closedLeftUnitorInv
        (Hom.comp f FragmentContext.combinedClosedCollapse)
        FragmentContext.closedLeftUnitorInv).symm
    have h' :
        Hom.comp
            (DayTensor.map (Hom.id (FragmentContext.combined [] []))
              (Hom.comp f FragmentContext.combinedClosedCollapse))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv) =
          DayTensor.map FragmentContext.closedLeftUnitorInv
            (Hom.comp (Hom.comp f FragmentContext.combinedClosedCollapse)
              FragmentContext.closedLeftUnitorInv) := by
      simpa only [Hom.id_comp] using h
    refine h'.trans ?_
    have hf :
        Hom.comp (Hom.comp f FragmentContext.combinedClosedCollapse)
            FragmentContext.closedLeftUnitorInv =
          f := by
      rw [← Hom.comp_assoc, FragmentContext.combinedClosedCollapse_leftUnitorInv,
        Hom.comp_id]
    exact congrArg _ hf
  have hcancel :
      Hom.comp (DayTensor.rightUnitor dayTensorUnit)
          FragmentContext.closedLeftUnitorInv =
        Hom.id dayTensorUnit := by
    rw [FragmentContext.closedLeftUnitorInv_eq]
    exact FragmentContext.rightUnitor_comp_leftUnitorInv_unit
  have hcollapse :
      FragmentContext.combinedClosedCollapse =
        DayTensor.leftUnitor dayTensorUnit := by
    change Hom.comp (DayTensor.leftUnitor dayTensorUnit)
        (DayTensor.map (Hom.id dayTensorUnit) (Hom.id dayTensorUnit)) =
      DayTensor.leftUnitor dayTensorUnit
    rw [DayTensor.map_id, Hom.comp_id]
  refine Eq.trans (congrArg _ hsplit) ?_
  refine Eq.trans ((Hom.comp_assoc _ _ _).symm) ?_
  -- Goal: λ ∘ (map ρ id ∘ map λinv f) = f ∘ collapse
  have hmap :
      Hom.comp
          (DayTensor.map (DayTensor.rightUnitor dayTensorUnit) (Hom.id A))
          (DayTensor.map FragmentContext.closedLeftUnitorInv f) =
        DayTensor.map (Hom.id dayTensorUnit) f := by
    have h :=
      (DayTensor.map_comp (DayTensor.rightUnitor dayTensorUnit)
        FragmentContext.closedLeftUnitorInv (Hom.id A) f).symm
    -- map ρ id ∘ map λinv f = map (ρ∘λinv) (id∘f)
    refine h.trans ?_
    rw [hcancel, Hom.id_comp]
  refine Eq.trans (congrArg (Hom.comp (DayTensor.leftUnitor A)) hmap) ?_
  -- Goal: λ ∘ map id f = f ∘ collapse
  refine Eq.trans (leftUnitor_natural f) ?_
  exact congrArg (Hom.comp f) hcollapse.symm

/-- Fragment packaging: identity body ∘ move ∘ map id arg ∘ split. -/
theorem closed_identity_move_cancel_frag {A : Module}
    (f : Hom dayTensorUnit A) :
    Hom.comp
      (Hom.comp
        (Hom.comp (DayTensor.leftUnitor A)
          (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.rightUnitor A)))
        (FragmentContext.moveArgumentIntoLinear dayTensorUnit dayTensorUnit A))
      (Hom.comp
        (DayTensor.map (Hom.id (FragmentContext.combined [] []))
          (FragmentContext.closedPoint f))
        (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) =
    FragmentContext.closedPoint f := by
  rw [FragmentContext.identity_body_move_eq]
  have hO :
      FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil =
        DayTensor.map FragmentContext.closedLeftUnitorInv
          FragmentContext.closedLeftUnitorInv := by
    rw [FragmentContext.combinedOSplit_nil]; rfl
  rw [hO, FragmentContext.closedPoint]
  exact closed_identity_move_cancel f

/-- Helper: FO Day β plus move/split cancellation for a closed identity body. -/
private theorem fragment_betaL_id_closed_aux {A : Ty}
    (hA : Ty.FirstOrder A)
    (body : Hom
      (dayTensor dayTensorUnit
        (dayTensor (fragmentModule A) dayTensorUnit))
      (fragmentModule A))
    (f : Hom dayTensorUnit (fragmentModule A))
    (hbody :
      body =
        Hom.comp (DayTensor.leftUnitor (fragmentModule A))
          (DayTensor.map (Hom.id dayTensorUnit)
            (DayTensor.rightUnitor (fragmentModule A)))) :
    Hom.comp (FragmentContext.evalFragmentFirstOrder hA _)
      (Hom.comp
        (DayTensor.map (FragmentContext.abstractLinear hA body)
          (FragmentContext.closedPoint f))
        (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) =
      FragmentContext.closedPoint f := by
  let Φ : Hom (FragmentContext.combined [] [])
      (internalHomRepresentable A.hilbertDim (fragmentModule A)) :=
    FragmentContext.abstractLinear hA body
  have hΦ : Φ = FragmentContext.abstractLinear hA body := rfl
  have hfactor :
      DayTensor.map Φ (FragmentContext.closedPoint f) =
        Hom.comp (DayTensor.map Φ (Hom.id (fragmentModule A)))
          (DayTensor.map (Hom.id (FragmentContext.combined [] []))
            (FragmentContext.closedPoint f)) := by
    simpa only [Hom.comp_id, Hom.id_comp] using
      DayTensor.map_comp Φ (Hom.id (FragmentContext.combined [] []))
        (Hom.id (fragmentModule A)) (FragmentContext.closedPoint f)
  -- Rewrite the goal to use Φ
  change Hom.comp (FragmentContext.evalFragmentFirstOrder hA _)
      (Hom.comp (DayTensor.map Φ (FragmentContext.closedPoint f))
        (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) =
    FragmentContext.closedPoint f
  rw [hfactor]
  -- eval ∘ ((map Φ id ∘ map id arg) ∘ split)
  have hreassoc :
      Hom.comp (FragmentContext.evalFragmentFirstOrder hA _)
          (Hom.comp
            (Hom.comp (DayTensor.map Φ (Hom.id (fragmentModule A)))
              (DayTensor.map (Hom.id (FragmentContext.combined [] []))
                (FragmentContext.closedPoint f)))
            (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) =
        Hom.comp
          (Hom.comp (FragmentContext.evalFragmentFirstOrder hA _)
            (DayTensor.map Φ (Hom.id (fragmentModule A))))
          (Hom.comp
            (DayTensor.map (Hom.id (FragmentContext.combined [] []))
              (FragmentContext.closedPoint f))
            (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) := by
    rw [Hom.comp_assoc, Hom.comp_assoc, ← Hom.comp_assoc]
  rw [hreassoc]
  -- FO β: eval ∘ map Φ id = body ∘ move, after unfolding Φ
  have hβ :
      Hom.comp (FragmentContext.evalFragmentFirstOrder hA _)
          (DayTensor.map Φ (Hom.id (fragmentModule A))) =
        Hom.comp body
          (FragmentContext.moveArgumentIntoLinear dayTensorUnit dayTensorUnit
            (fragmentModule A)) := by
    rw [hΦ]
    exact FragmentContext.evalFragmentFirstOrder_abstractLinear hA body
  rw [hβ, hbody]
  exact closed_identity_move_cancel_frag f

/-- Closed linear identity β at unit: `app (λx. x) unit = unit`. -/
theorem fragment_betaL_id_unit :
    FragCert.denote fragCert_appL_id_unit =
      FragCert.denote FragCert.closed_unit_cert := by
  have harg :
      FragCert.denote FragCert.closed_unit_cert =
        FragmentContext.closedPoint routeAFragmentModel.unitIntro :=
    fragment_step_denote_sound_unit FragCert.closed_unit_cert
  rw [fragment_betaL_id_unit_spine, harg]
  exact fragment_betaL_id_closed_aux Ty.FirstOrder.unit _
    routeAFragmentModel.unitIntro fragCert_varL0_unit_denote_simple

/-- Closed linear identity β at bit: `app (λx. x) (bitLit b) = bitLit b`. -/
theorem fragment_betaL_id_bit (b : Bool) :
    FragCert.denote (fragCert_appL_id_bit b) =
      FragCert.denote (FragCert.closed_bitLit_cert b) := by
  have harg :
      FragCert.denote (FragCert.closed_bitLit_cert b) =
        FragmentContext.closedPoint (bitLitHom b) :=
    FragCert.closed_bitLit_denote_eq b
  rw [fragment_betaL_id_bit_spine, harg]
  exact fragment_betaL_id_closed_aux Ty.FirstOrder.bit _
    (bitLitHom b) fragCert_varL0_bit_denote_simple


/-- Unrestricted identity body unfolds through structural lookup. -/
theorem fragCert_varU0_bit_denote :
    FragCert.denote fragCert_varU0_bit =
      Hom.comp (DayTensor.rightUnitor (fragmentModule .bit))
        (DayTensor.map
          (Hom.comp (DayTensor.rightUnitor (fragmentModule .bit))
            (DayTensor.map classicalBitInclusion (Hom.id dayTensorUnit)))
          (Hom.id dayTensorUnit)) := by
  simp only [fragCert_varU0_bit, FragCert.denote_varU_eq,
    FragmentContext.combinedLookupUnrestricted,
    FragmentContext.unrestrictedLookup,
    FragmentContext.unrestrictedLookupLists_zero_bit]
  rfl

/-- F4b foothold: substituting a value for linear `var 0` is the value
(definitionally on terms). -/
theorem substLin_varL0 (V : Term) :
    Term.substLin 0 V (.var .lin 0) = V := by
  simp [Term.substLin, Term.shiftLin_zero]

/-- F4b: denotation of the closed linear identity redex equals the argument
(packaged from the identity β theorems). -/
theorem fragment_substLin_id_denote_unit :
    FragCert.denote fragCert_appL_id_unit =
      FragCert.denote FragCert.closed_unit_cert :=
  fragment_betaL_id_unit

theorem fragment_substLin_id_denote_bit (b : Bool) :
    FragCert.denote (fragCert_appL_id_bit b) =
      FragCert.denote (FragCert.closed_bitLit_cert b) :=
  fragment_betaL_id_bit b

/-- F4b: substituting at unrestricted `var 0` returns the value. -/
theorem substUnres_varU0 (V : Term) :
    Term.substUnres 0 V (.var .unres 0) = V := by
  simp [Term.substUnres, shiftUnres_zero]

/-! ## F4c: denotational congruence for fragment Step constructors -/

theorem fragment_step_congruence_appL_fun {Γ Δ Δ₁ Δ₂ A B F F' X}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hFO : Ty.FirstOrder A)
    (hB : Ty.SemanticFragment B)
    (cF : FragCert Γ Δ₁ F (.arrow .lin A B))
    (cF' : FragCert Γ Δ₁ F' (.arrow .lin A B))
    (cX : FragCert Γ Δ₂ X A)
    (h : FragCert.denote cF = FragCert.denote cF') :
    FragCert.denote (.appL hΓ hΔ hs hFO hB cF cX) =
      FragCert.denote (.appL hΓ hΔ hs hFO hB cF' cX) := by
  simp only [FragCert.denote_appL_eq, h]

theorem fragment_step_congruence_appL_arg {Γ Δ Δ₁ Δ₂ A B F X X'}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hFO : Ty.FirstOrder A)
    (hB : Ty.SemanticFragment B)
    (cF : FragCert Γ Δ₁ F (.arrow .lin A B))
    (cX : FragCert Γ Δ₂ X A) (cX' : FragCert Γ Δ₂ X' A)
    (h : FragCert.denote cX = FragCert.denote cX') :
    FragCert.denote (.appL hΓ hΔ hs hFO hB cF cX) =
      FragCert.denote (.appL hΓ hΔ hs hFO hB cF cX') := by
  simp only [FragCert.denote_appL_eq, h]

theorem fragment_step_congruence_appU_fun {Γ Δ ΔF ΔX B F F' X}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ ΔF ΔX) (hN : AllNone ΔX)
    (hB : Ty.SemanticFragment B)
    (cF : FragCert Γ ΔF F (.arrow .unres .bit B))
    (cF' : FragCert Γ ΔF F' (.arrow .unres .bit B))
    (cX : FragCert Γ ΔX X .bit)
    (h : FragCert.denote cF = FragCert.denote cF') :
    FragCert.denote (.appU hΓ hΔ hs hN hB cF cX) =
      FragCert.denote (.appU hΓ hΔ hs hN hB cF' cX) := by
  simp only [FragCert.denote_appU_eq, h]

theorem fragment_step_congruence_appU_arg {Γ Δ ΔF ΔX B F X X'}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ ΔF ΔX) (hN : AllNone ΔX)
    (hB : Ty.SemanticFragment B)
    (cF : FragCert Γ ΔF F (.arrow .unres .bit B))
    (cX : FragCert Γ ΔX X .bit) (cX' : FragCert Γ ΔX X' .bit)
    (h : FragCert.denote cX = FragCert.denote cX') :
    FragCert.denote (.appU hΓ hΔ hs hN hB cF cX) =
      FragCert.denote (.appU hΓ hΔ hs hN hB cF cX') := by
  simp only [FragCert.denote_appU_eq, h]

theorem fragment_step_congruence_ite_scrutinee {Γ Δ Δ₁ Δ₂ A B B' T E}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
    (cB : FragCert Γ Δ₁ B .bit) (cB' : FragCert Γ Δ₁ B' .bit)
    (cT : FragCert Γ Δ₂ T A) (cE : FragCert Γ Δ₂ E A)
    (h : FragCert.denote cB = FragCert.denote cB') :
    FragCert.denote (.ite hΓ hΔ hs hA cB cT cE) =
      FragCert.denote (.ite hΓ hΔ hs hA cB' cT cE) := by
  simp only [FragCert.denote_ite_eq, h]

theorem fragment_step_congruence_ite_then {Γ Δ Δ₁ Δ₂ A B T T' E}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
    (cB : FragCert Γ Δ₁ B .bit)
    (cT : FragCert Γ Δ₂ T A) (cT' : FragCert Γ Δ₂ T' A)
    (cE : FragCert Γ Δ₂ E A)
    (h : FragCert.denote cT = FragCert.denote cT') :
    FragCert.denote (.ite hΓ hΔ hs hA cB cT cE) =
      FragCert.denote (.ite hΓ hΔ hs hA cB cT' cE) := by
  simp only [FragCert.denote_ite_eq, h]

theorem fragment_step_congruence_ite_else {Γ Δ Δ₁ Δ₂ A B T E E'}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
    (cB : FragCert Γ Δ₁ B .bit) (cT : FragCert Γ Δ₂ T A)
    (cE : FragCert Γ Δ₂ E A) (cE' : FragCert Γ Δ₂ E' A)
    (h : FragCert.denote cE = FragCert.denote cE') :
    FragCert.denote (.ite hΓ hΔ hs hA cB cT cE) =
      FragCert.denote (.ite hΓ hΔ hs hA cB cT cE') := by
  simp only [FragCert.denote_ite_eq, h]

theorem fragment_step_congruence_pair_left {Γ Δ Δ₁ Δ₂ A B M M' N}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B)
    (cM : FragCert Γ Δ₁ M A) (cM' : FragCert Γ Δ₁ M' A)
    (cN : FragCert Γ Δ₂ N B)
    (h : FragCert.denote cM = FragCert.denote cM') :
    FragCert.denote (.pair hΓ hΔ hs hA hB cM cN) =
      FragCert.denote (.pair hΓ hΔ hs hA hB cM' cN) := by
  simp only [FragCert.denote_pair_eq, h]

theorem fragment_step_congruence_pair_right {Γ Δ Δ₁ Δ₂ A B M N N'}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B)
    (cM : FragCert Γ Δ₁ M A)
    (cN : FragCert Γ Δ₂ N B) (cN' : FragCert Γ Δ₂ N' B)
    (h : FragCert.denote cN = FragCert.denote cN') :
    FragCert.denote (.pair hΓ hΔ hs hA hB cM cN) =
      FragCert.denote (.pair hΓ hΔ hs hA hB cM cN') := by
  simp only [FragCert.denote_pair_eq, h]

theorem fragment_step_congruence_unpair_scrutinee {Γ Δ Δ₁ Δ₂ A B C M M' K}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B)
    (hC : Ty.SemanticFragment C)
    (cM : FragCert Γ Δ₁ M (.tensor A B))
    (cM' : FragCert Γ Δ₁ M' (.tensor A B))
    (cK : FragCert Γ Δ₂ K (.arrow .lin A (.arrow .lin B C)))
    (h : FragCert.denote cM = FragCert.denote cM') :
    FragCert.denote (.unpair hΓ hΔ hs hA hB hC cM cK) =
      FragCert.denote (.unpair hΓ hΔ hs hA hB hC cM' cK) := by
  simp only [FragCert.denote_unpair_eq, h]

theorem fragment_step_congruence_unpair_cont {Γ Δ Δ₁ Δ₂ A B C M K K'}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B)
    (hC : Ty.SemanticFragment C)
    (cM : FragCert Γ Δ₁ M (.tensor A B))
    (cK : FragCert Γ Δ₂ K (.arrow .lin A (.arrow .lin B C)))
    (cK' : FragCert Γ Δ₂ K' (.arrow .lin A (.arrow .lin B C)))
    (h : FragCert.denote cK = FragCert.denote cK') :
    FragCert.denote (.unpair hΓ hΔ hs hA hB hC cM cK) =
      FragCert.denote (.unpair hΓ hΔ hs hA hB hC cM cK') := by
  simp only [FragCert.denote_unpair_eq, h]

theorem fragment_step_congruence_measure_qubit {Γ Δ Δ₁ Δ₂ A Q Q' K}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
    (cQ : FragCert Γ Δ₁ Q .qubit) (cQ' : FragCert Γ Δ₁ Q' .qubit)
    (cK : FragCert Γ Δ₂ K (.arrow .unres .bit (.arrow .lin .qubit A)))
    (h : FragCert.denote cQ = FragCert.denote cQ') :
    FragCert.denote (.measure hΓ hΔ hs hA cQ cK) =
      FragCert.denote (.measure hΓ hΔ hs hA cQ' cK) := by
  simp only [FragCert.denote_measure_eq, h]

theorem fragment_step_congruence_measure_cont {Γ Δ Δ₁ Δ₂ A Q K K'}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
    (cQ : FragCert Γ Δ₁ Q .qubit)
    (cK : FragCert Γ Δ₂ K (.arrow .unres .bit (.arrow .lin .qubit A)))
    (cK' : FragCert Γ Δ₂ K' (.arrow .unres .bit (.arrow .lin .qubit A)))
    (h : FragCert.denote cK = FragCert.denote cK') :
    FragCert.denote (.measure hΓ hΔ hs hA cQ cK) =
      FragCert.denote (.measure hΓ hΔ hs hA cQ cK') := by
  simp only [FragCert.denote_measure_eq, h]

/-- MeasStep congruence: equal qubit denotations give equal measure dens. -/
theorem fragment_measStep_congruence_qubit {Γ Δ Δ₁ Δ₂ A Q Q' K}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
    (cQ : FragCert Γ Δ₁ Q .qubit) (cQ' : FragCert Γ Δ₁ Q' .qubit)
    (cK : FragCert Γ Δ₂ K (.arrow .unres .bit (.arrow .lin .qubit A)))
    (h : FragCert.denote cQ = FragCert.denote cQ') :
    FragCert.denote (.measure hΓ hΔ hs hA cQ cK) =
      FragCert.denote (.measure hΓ hΔ hs hA cQ' cK) :=
  fragment_step_congruence_measure_qubit hΓ hΔ hs hA cQ cQ' cK h

/-- Package: denotational congruence for fragment-admitted Step contexts. -/
theorem fragment_step_congruence_sound :
    (∀ {Γ Δ Δ₁ Δ₂ A B F F' X}
        (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
        (hs : OSplit Δ Δ₁ Δ₂) (hFO : Ty.FirstOrder A)
        (hB : Ty.SemanticFragment B)
        (cF : FragCert Γ Δ₁ F (.arrow .lin A B))
        (cF' : FragCert Γ Δ₁ F' (.arrow .lin A B))
        (cX : FragCert Γ Δ₂ X A),
      FragCert.denote cF = FragCert.denote cF' →
      FragCert.denote (.appL hΓ hΔ hs hFO hB cF cX) =
        FragCert.denote (.appL hΓ hΔ hs hFO hB cF' cX)) ∧
    (∀ {Γ Δ Δ₁ Δ₂ A B F X X'}
        (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
        (hs : OSplit Δ Δ₁ Δ₂) (hFO : Ty.FirstOrder A)
        (hB : Ty.SemanticFragment B)
        (cF : FragCert Γ Δ₁ F (.arrow .lin A B))
        (cX : FragCert Γ Δ₂ X A) (cX' : FragCert Γ Δ₂ X' A),
      FragCert.denote cX = FragCert.denote cX' →
      FragCert.denote (.appL hΓ hΔ hs hFO hB cF cX) =
        FragCert.denote (.appL hΓ hΔ hs hFO hB cF cX')) ∧
    (∀ {Γ Δ ΔF ΔX B F F' X}
        (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
        (hs : OSplit Δ ΔF ΔX) (hN : AllNone ΔX)
        (hB : Ty.SemanticFragment B)
        (cF : FragCert Γ ΔF F (.arrow .unres .bit B))
        (cF' : FragCert Γ ΔF F' (.arrow .unres .bit B))
        (cX : FragCert Γ ΔX X .bit),
      FragCert.denote cF = FragCert.denote cF' →
      FragCert.denote (.appU hΓ hΔ hs hN hB cF cX) =
        FragCert.denote (.appU hΓ hΔ hs hN hB cF' cX)) ∧
    (∀ {Γ Δ ΔF ΔX B F X X'}
        (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
        (hs : OSplit Δ ΔF ΔX) (hN : AllNone ΔX)
        (hB : Ty.SemanticFragment B)
        (cF : FragCert Γ ΔF F (.arrow .unres .bit B))
        (cX : FragCert Γ ΔX X .bit) (cX' : FragCert Γ ΔX X' .bit),
      FragCert.denote cX = FragCert.denote cX' →
      FragCert.denote (.appU hΓ hΔ hs hN hB cF cX) =
        FragCert.denote (.appU hΓ hΔ hs hN hB cF cX')) ∧
    (∀ {Γ Δ Δ₁ Δ₂ A Q Q' K}
        (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
        (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
        (cQ : FragCert Γ Δ₁ Q .qubit) (cQ' : FragCert Γ Δ₁ Q' .qubit)
        (cK : FragCert Γ Δ₂ K (.arrow .unres .bit (.arrow .lin .qubit A))),
      FragCert.denote cQ = FragCert.denote cQ' →
      FragCert.denote (.measure hΓ hΔ hs hA cQ cK) =
        FragCert.denote (.measure hΓ hΔ hs hA cQ' cK)) :=
  ⟨fun {_Γ} {_Δ} {_Δ₁} {_Δ₂} {_A} {_B} {_F} {_F'} {_X} hΓ hΔ hs hFO hB cF cF' cX h =>
      fragment_step_congruence_appL_fun hΓ hΔ hs hFO hB cF cF' cX h,
    fun {_Γ} {_Δ} {_Δ₁} {_Δ₂} {_A} {_B} {_F} {_X} {_X'} hΓ hΔ hs hFO hB cF cX cX' h =>
      fragment_step_congruence_appL_arg hΓ hΔ hs hFO hB cF cX cX' h,
    fun {_Γ} {_Δ} {_ΔF} {_ΔX} {_B} {_F} {_F'} {_X} hΓ hΔ hs hN hB cF cF' cX h =>
      fragment_step_congruence_appU_fun hΓ hΔ hs hN hB cF cF' cX h,
    fun {_Γ} {_Δ} {_ΔF} {_ΔX} {_B} {_F} {_X} {_X'} hΓ hΔ hs hN hB cF cX cX' h =>
      fragment_step_congruence_appU_arg hΓ hΔ hs hN hB cF cX cX' h,
    fun {_Γ} {_Δ} {_Δ₁} {_Δ₂} {_A} {_Q} {_Q'} {_K} hΓ hΔ hs hA cQ cQ' cK h =>
      fragment_step_congruence_measure_qubit hΓ hΔ hs hA cQ cQ' cK h⟩

/-- Unrestricted identity body unfolds to `incl ∘ ρ ∘ ρ`. -/
theorem fragCert_varU0_bit_denote_simple :
    FragCert.denote fragCert_varU0_bit =
      Hom.comp classicalBitInclusion
        (Hom.comp (DayTensor.rightUnitor classicalBitModule)
          (DayTensor.rightUnitor
            (dayTensor classicalBitModule dayTensorUnit))) := by
  rw [fragCert_varU0_bit_denote]
  simp only [fragmentModule_bit]
  have h1 :=
    rightUnitor_natural
      (Hom.comp (DayTensor.rightUnitor (representable 2))
        (DayTensor.map classicalBitInclusion (Hom.id dayTensorUnit)))
  change Hom.comp (DayTensor.rightUnitor (representable 2))
      (DayTensor.map
        (Hom.comp (DayTensor.rightUnitor (representable 2))
          (DayTensor.map classicalBitInclusion (Hom.id dayTensorUnit)))
        (Hom.id dayTensorUnit)) =
    Hom.comp classicalBitInclusion
      (Hom.comp (DayTensor.rightUnitor classicalBitModule)
        (DayTensor.rightUnitor
          (dayTensor classicalBitModule dayTensorUnit)))
  rw [h1, rightUnitor_natural classicalBitInclusion]
  rfl

/-- Upgraded soundness package: closed linear identity β (congruence suite is
`fragment_step_congruence_sound`). -/
theorem fragment_step_denote_sound_upgraded :
    (FragCert.denote fragCert_appL_id_unit =
      FragCert.denote FragCert.closed_unit_cert) ∧
    (∀ b, FragCert.denote (fragCert_appL_id_bit b) =
      FragCert.denote (FragCert.closed_bitLit_cert b)) :=
  ⟨fragment_betaL_id_unit, fragment_betaL_id_bit⟩

/-! Unrestricted closed identity β (`fragment_betaU_id_bit`) remains open:
after `fragCert_varU0_bit_denote_simple`, `evalUnrestrictedBit_abstractUnrestricted`,
and `classicalBitInclusion_comp_bitClassicalize_bitLit`, the residual is
cancellation of `moveArgumentIntoUnrestricted` against closed split/unitors
(analogous to `closed_identity_move_cancel`). -/

end QLambda.Linear
