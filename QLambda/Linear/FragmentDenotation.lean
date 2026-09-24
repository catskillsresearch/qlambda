/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentModel
import QLambda.Linear.FragmentContext
import QLambda.Linear.Operational
import QLambda.Domain.Presheaf.Yoneda
import QLambda.Domain.Presheaf.ClassicalCategory

/-!
# Concrete fragment denotation (Route A)

Type-valued typing certificates for the minimum fragment.  `FragCert` is the
canonical fragment judgment; `HasType` is its propositional erasure via
`toHasType`.  Completeness (`ofHasType`) is the inverse for fragment-disciplined
derivations (context fragment, binder discipline, result fragment).
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open Domain.Presheaf.SigmaMon
open DayTensor
open FragmentContext
open scoped ComplexOrder MatrixOrder

/-- Type-valued fragment typing certificate (canonical derivation shape). -/
inductive FragCert : List Ty → List (Option Ty) → Term → Ty → Type where
  | unit {Γ Δ} (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ) :
      AllNone Δ → FragCert Γ Δ .unit .unit
  | bitLit {Γ Δ} (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
      (b : Bool) : AllNone Δ → FragCert Γ Δ (.bitLit b) .bit
  | prim {Γ Δ} (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
      (p : Prim) : AllNone Δ → FragCert Γ Δ (.prim p) (primTy p)
  | varU {Γ Δ n A} (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ) :
      Lookup Γ n A → Ty.Duplicable A → AllNone Δ → Ty.SemanticFragment A →
      FragCert Γ Δ (.var .unres n) A
  | varL {Γ Δ n A} (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ) :
      Lookup Δ n (some A) → OnlySomeAt Δ n → Ty.SemanticFragment A →
      FragCert Γ Δ (.var .lin n) A
  | lamU {Γ Δ A B M} (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ) :
      Ty.Admissible A → Ty.Duplicable A → AllNone Δ →
      Ty.SemanticFragment (.arrow .unres A B) →
      FragCert (A :: Γ) Δ M B →
      FragCert Γ Δ (.lam .unres A M) (.arrow .unres A B)
  | lamL {Γ Δ A B M} (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ) :
      Ty.Admissible A → Ty.FirstOrder A → Ty.SemanticFragment B →
      FragCert Γ (some A :: Δ) M B →
      FragCert Γ Δ (.lam .lin A M) (.arrow .lin A B)
  | appL {Γ Δ Δ₁ Δ₂ A B F X} (hΓ : CtxUAllBit Γ)
      (hΔ : CtxLAllSomeFragment Δ) :
      OSplit Δ Δ₁ Δ₂ → Ty.FirstOrder A → Ty.SemanticFragment B →
      FragCert Γ Δ₁ F (.arrow .lin A B) → FragCert Γ Δ₂ X A →
      FragCert Γ Δ (.app F X) B
  | appU {Γ Δ ΔF ΔX B F X} (hΓ : CtxUAllBit Γ)
      (hΔ : CtxLAllSomeFragment Δ) :
      OSplit Δ ΔF ΔX → AllNone ΔX → Ty.SemanticFragment B →
      FragCert Γ ΔF F (.arrow .unres .bit B) → FragCert Γ ΔX X .bit →
      FragCert Γ Δ (.app F X) B
  | pair {Γ Δ Δ₁ Δ₂ A B M N} (hΓ : CtxUAllBit Γ)
      (hΔ : CtxLAllSomeFragment Δ) :
      OSplit Δ Δ₁ Δ₂ → Ty.FirstOrder A → Ty.FirstOrder B →
      FragCert Γ Δ₁ M A → FragCert Γ Δ₂ N B →
      FragCert Γ Δ (.pair M N) (.tensor A B)
  | unpair {Γ Δ Δ₁ Δ₂ A B C M K} (hΓ : CtxUAllBit Γ)
      (hΔ : CtxLAllSomeFragment Δ) :
      OSplit Δ Δ₁ Δ₂ → Ty.FirstOrder A → Ty.FirstOrder B →
      Ty.SemanticFragment C →
      FragCert Γ Δ₁ M (.tensor A B) →
      FragCert Γ Δ₂ K (.arrow .lin A (.arrow .lin B C)) →
      FragCert Γ Δ (.unpair M K) C
  | ite {Γ Δ Δ₁ Δ₂ A B T E} (hΓ : CtxUAllBit Γ)
      (hΔ : CtxLAllSomeFragment Δ) :
      OSplit Δ Δ₁ Δ₂ → Ty.SemanticFragment A →
      FragCert Γ Δ₁ B .bit → FragCert Γ Δ₂ T A → FragCert Γ Δ₂ E A →
      FragCert Γ Δ (.ite B T E) A
  | measure {Γ Δ Δ₁ Δ₂ A Q K} (hΓ : CtxUAllBit Γ)
      (hΔ : CtxLAllSomeFragment Δ) :
      OSplit Δ Δ₁ Δ₂ → Ty.SemanticFragment A →
      FragCert Γ Δ₁ Q .qubit →
      FragCert Γ Δ₂ K (.arrow .unres .bit (.arrow .lin .qubit A)) →
      FragCert Γ Δ (.measure Q K) A

namespace FragCert

/-- Every certificate implies ordinary `HasType`. -/
theorem toHasType {Γ Δ M A} : FragCert Γ Δ M A → HasType Γ Δ M A
  | .unit _ _ h => .unit h
  | .bitLit _ _ _ h => .bitLit h
  | .prim _ _ _ h => .prim h
  | .varU _ _ hL hD hN _ => .varU hL hD hN
  | .varL _ _ hL hO _ => .varL hL hO
  | .lamU _ _ hAd hDup hN _ c => .lamU hAd hDup hN c.toHasType
  | .lamL _ _ hAd _ _ c => .lamL hAd c.toHasType
  | .appL _ _ hS _ _ cF cX => .appL hS cF.toHasType cX.toHasType
  | .appU _ _ hS hN _ cF cX => .appU hS hN cF.toHasType cX.toHasType
  | .pair _ _ hS _ _ cM cN => .pair hS cM.toHasType cN.toHasType
  | .unpair _ _ hS _ _ _ cM cK => .unpair hS cM.toHasType cK.toHasType
  | .ite _ _ hS _ cB cT cE => .ite hS cB.toHasType cT.toHasType cE.toHasType
  | .measure _ _ hS _ cQ cK => .measure hS cQ.toHasType cK.toHasType

/-- Every certificate result type lies in the semantic fragment. -/
theorem result_fragment {Γ Δ M A} : FragCert Γ Δ M A → Ty.SemanticFragment A
  | .unit _ _ _ => Ty.SemanticFragment.unit
  | .bitLit _ _ _ _ => Ty.SemanticFragment.bit
  | .prim _ _ p _ => Ty.SemanticFragment.primTy_fragment p
  | .varU _ _ _ _ _ h => h
  | .varL _ _ _ _ h => h
  | .lamU _ _ _ _ _ hArr _ => hArr
  | .lamL _ _ _ hA hB _ => .arrowLin hA hB
  | .appL _ _ _ _ hB _ _ => hB
  | .appU _ _ _ _ hB _ _ => hB
  | .pair _ _ _ hA hB _ _ => Ty.SemanticFragment.tensor hA hB
  | .unpair _ _ _ _ _ hC _ _ => hC
  | .ite _ _ _ hA _ _ _ => hA
  | .measure _ _ _ hA _ _ => hA

/-- Every certified term lies in the syntactic semantic fragment. -/
theorem term_fragment {Γ Δ M A} : FragCert Γ Δ M A → Term.SemanticFragment M
  | .unit _ _ _ => .unit
  | .bitLit _ _ _ _ => .bitLit
  | .prim _ _ _ _ => .prim
  | .varU _ _ _ _ _ _ => .var
  | .varL _ _ _ _ _ => .var
  | .lamU _ _ _ _ _ hArr c =>
      (Ty.SemanticFragment.arrow_unres_eq hArr).symm ▸
        Term.SemanticFragment.lam Ty.SemanticFragment.bit c.term_fragment
  | .lamL _ _ _ hFO _ c =>
      .lam (Ty.SemanticFragment.of_firstOrder hFO) c.term_fragment
  | .appL _ _ _ _ _ cF cX => .app cF.term_fragment cX.term_fragment
  | .appU _ _ _ _ _ cF cX => .app cF.term_fragment cX.term_fragment
  | .pair _ _ _ _ _ cM cN => .pair cM.term_fragment cN.term_fragment
  | .unpair _ _ _ _ _ _ cM cK => .unpair cM.term_fragment cK.term_fragment
  | .ite _ _ _ _ cB cT cE =>
      .ite cB.term_fragment cT.term_fragment cE.term_fragment
  | .measure _ _ _ _ cQ cK => .measure cQ.term_fragment cK.term_fragment

/-- Context types in unrestricted and linear scopes lie in the fragment. -/
theorem ctx_fragment {Γ Δ M A} (c : FragCert Γ Δ M A) :
    CtxUAllBit Γ ∧ CtxLAllSomeFragment Δ := by
  induction c with
  | unit hΓ hΔ _ => exact ⟨hΓ, hΔ⟩
  | bitLit hΓ hΔ _ _ => exact ⟨hΓ, hΔ⟩
  | prim hΓ hΔ _ _ => exact ⟨hΓ, hΔ⟩
  | varU hΓ hΔ _ _ _ _ => exact ⟨hΓ, hΔ⟩
  | varL hΓ hΔ _ _ _ => exact ⟨hΓ, hΔ⟩
  | lamU hΓ hΔ _ _ _ _ _ _ => exact ⟨hΓ, hΔ⟩
  | lamL hΓ hΔ _ _ _ _ _ => exact ⟨hΓ, hΔ⟩
  | appL hΓ hΔ _ _ _ _ _ _ _ => exact ⟨hΓ, hΔ⟩
  | appU hΓ hΔ _ _ _ _ _ _ => exact ⟨hΓ, hΔ⟩
  | pair hΓ hΔ _ _ _ _ _ _ => exact ⟨hΓ, hΔ⟩
  | unpair hΓ hΔ _ _ _ _ _ _ _ => exact ⟨hΓ, hΔ⟩
  | ite hΓ hΔ _ _ _ _ _ _ => exact ⟨hΓ, hΔ⟩
  | measure hΓ hΔ _ _ _ _ _ _ => exact ⟨hΓ, hΔ⟩

/-- Fragment binder discipline: linear binders are first-order; unrestricted
binders are classical bits. -/
def FragmentBinders : Term → Prop
  | .app F X => FragmentBinders F ∧ FragmentBinders X
  | .lam .lin dom body => Ty.FirstOrder dom ∧ FragmentBinders body
  | .lam .unres dom body => dom = .bit ∧ FragmentBinders body
  | .pair M N => FragmentBinders M ∧ FragmentBinders N
  | .unpair M K => FragmentBinders M ∧ FragmentBinders K
  | .ite B T E => FragmentBinders B ∧ FragmentBinders T ∧ FragmentBinders E
  | .measure Q K => FragmentBinders Q ∧ FragmentBinders K
  | .fix _ _ | .fold _ _ | .unfold _ => False
  | _ => True

namespace FragmentBinders

theorem app_left {F X : Term} (h : FragmentBinders (.app F X)) : FragmentBinders F := h.1
theorem app_right {F X : Term} (h : FragmentBinders (.app F X)) : FragmentBinders X := h.2
theorem lamLin_firstOrder {dom : Ty} {M : Term}
    (h : FragmentBinders (.lam .lin dom M)) : Ty.FirstOrder dom := h.1
theorem lamLin_body {dom : Ty} {M : Term}
    (h : FragmentBinders (.lam .lin dom M)) : FragmentBinders M := h.2
theorem lamUnres_bit {dom : Ty} {M : Term}
    (h : FragmentBinders (.lam .unres dom M)) : dom = .bit := h.1
theorem lamUnres_body {dom : Ty} {M : Term}
    (h : FragmentBinders (.lam .unres dom M)) : FragmentBinders M := h.2
theorem pair_left {M N : Term} (h : FragmentBinders (.pair M N)) : FragmentBinders M := h.1
theorem pair_right {M N : Term} (h : FragmentBinders (.pair M N)) : FragmentBinders N := h.2
theorem unpair_left {M K : Term} (h : FragmentBinders (.unpair M K)) : FragmentBinders M := h.1
theorem unpair_right {M K : Term} (h : FragmentBinders (.unpair M K)) : FragmentBinders K := h.2
theorem ite_cond {B T E : Term} (h : FragmentBinders (.ite B T E)) : FragmentBinders B := h.1
theorem ite_then {B T E : Term} (h : FragmentBinders (.ite B T E)) : FragmentBinders T := h.2.1
theorem ite_else {B T E : Term} (h : FragmentBinders (.ite B T E)) : FragmentBinders E := h.2.2
theorem measure_qubit {Q K : Term} (h : FragmentBinders (.measure Q K)) : FragmentBinders Q := h.1
theorem measure_cont {Q K : Term} (h : FragmentBinders (.measure Q K)) : FragmentBinders K := h.2

theorem term_fragment :
    ∀ {M : Term}, FragmentBinders M → Term.SemanticFragment M
  | .var _ _, _ => .var
  | .lam .lin A M, h =>
      .lam (Ty.SemanticFragment.of_firstOrder h.1)
        (term_fragment h.2)
  | .lam .unres A M, h => by
      change A = .bit ∧ FragmentBinders M at h
      rw [h.1]
      exact .lam Ty.SemanticFragment.bit (term_fragment h.2)
  | .app F X, h => .app (term_fragment h.1) (term_fragment h.2)
  | .unit, _ => .unit
  | .bitLit _, _ => .bitLit
  | .pair M N, h => .pair (term_fragment h.1) (term_fragment h.2)
  | .unpair M K, h => .unpair (term_fragment h.1) (term_fragment h.2)
  | .ite B T E, h =>
      .ite (term_fragment h.1) (term_fragment h.2.1)
        (term_fragment h.2.2)
  | .prim _, _ => .prim
  | .measure Q K, h => .measure (term_fragment h.1) (term_fragment h.2)
  | .fix _ _, h => False.elim h
  | .fold _ _, h => False.elim h
  | .unfold _, h => False.elim h

end FragmentBinders

/-- Binder-shape information retained through result types.  Unlike
`Ty.SemanticFragment`, this predicate deliberately imposes no condition on
first-order leaves; it records exactly the domain facts needed while
reconstructing certificates for application and unpairing. -/
def FragmentArrowDomains : Ty → Prop
  | .arrow .lin A B => Ty.FirstOrder A ∧ FragmentArrowDomains B
  | .arrow .unres A B => A = .bit ∧ FragmentArrowDomains B
  | _ => True

namespace FragmentArrowDomains

theorem of_semanticFragment {A : Ty} (h : Ty.SemanticFragment A) :
    FragmentArrowDomains A := by
  induction h with
  | ofFirstOrder h =>
      cases h <;> trivial
  | arrowLin hA _ ih => exact ⟨hA, ih⟩
  | arrowUnresBit _ ih => exact ⟨rfl, ih⟩

theorem of_hasType :
    ∀ {Γ Δ M A}, HasType Γ Δ M A →
      CtxUAllBit Γ → CtxLAllSomeFragment Δ →
      FragmentBinders M → FragmentArrowDomains A
  | _, _, _, _, .varU hl _ _, hΓ, _, _ => by
      rw [CtxUAllBit.lookup hΓ hl]
      trivial
  | _, _, _, _, .varL hl _, _, hΔ, _ =>
      of_semanticFragment (CtxLAllSomeFragment.lookup hΔ hl)
  | _, _, _, _, .lamU _ _ _ h, hΓ, hΔ, hb => by
      change _ = Ty.bit ∧ _
      exact ⟨FragmentBinders.lamUnres_bit hb,
        of_hasType h
          (FragmentBinders.lamUnres_bit hb ▸ CtxUAllBit.cons hΓ)
          hΔ (FragmentBinders.lamUnres_body hb)⟩
  | _, _, _, _, .lamL _ h, hΓ, hΔ, hb =>
      ⟨FragmentBinders.lamLin_firstOrder hb,
        of_hasType h hΓ
          (CtxLAllSomeFragment.cons_some
            (Ty.SemanticFragment.of_firstOrder
              (FragmentBinders.lamLin_firstOrder hb)) hΔ)
          (FragmentBinders.lamLin_body hb)⟩
  | _, _, _, _, .appL hs hF _, hΓ, hΔ, hb =>
      (of_hasType hF hΓ (CtxLAllSomeFragment.of_oSplit_left hΔ hs)
        (FragmentBinders.app_left hb)).2
  | _, _, _, _, .appU hs _ hF _, hΓ, hΔ, hb =>
      (of_hasType hF hΓ (CtxLAllSomeFragment.of_oSplit_left hΔ hs)
        (FragmentBinders.app_left hb)).2
  | _, _, _, _, .unit _, _, _, _ => trivial
  | _, _, _, _, .bitLit _, _, _, _ => trivial
  | _, _, _, _, .pair _ _ _, _, _, _ => trivial
  | _, _, _, _, .unpair hs _ hK, hΓ, hΔ, hb =>
      (of_hasType hK hΓ (CtxLAllSomeFragment.of_oSplit_right hΔ hs)
        (FragmentBinders.unpair_right hb)).2.2
  | _, _, _, _, .ite hs _ hT _, hΓ, hΔ, hb =>
      of_hasType hT hΓ (CtxLAllSomeFragment.of_oSplit_right hΔ hs)
        (FragmentBinders.ite_then hb)
  | _, _, _, _, .prim _, _, _, _ =>
      of_semanticFragment (Ty.SemanticFragment.primTy_fragment _)
  | _, _, _, _, .measure hs _ hK, hΓ, hΔ, hb =>
      (of_hasType hK hΓ (CtxLAllSomeFragment.of_oSplit_right hΔ hs)
        (FragmentBinders.measure_cont hb)).2.2
  | _, _, _, _, .fix _ _ _ _, _, _, hb => False.elim hb
  | _, _, _, _, .fold _ _, _, _, hb => False.elim hb
  | _, _, _, _, .unfold _ _, _, _, hb => False.elim hb

end FragmentArrowDomains

/-- Propositional fragment judgment (mirror of `FragCert`). -/
inductive FragmentJudgment : List Ty → List (Option Ty) → Term → Ty → Prop where
  | unit {Γ Δ} (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ) :
      AllNone Δ → FragmentJudgment Γ Δ .unit .unit
  | bitLit {Γ Δ} (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
      (b : Bool) : AllNone Δ → FragmentJudgment Γ Δ (.bitLit b) .bit
  | prim {Γ Δ} (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
      (p : Prim) : AllNone Δ → FragmentJudgment Γ Δ (.prim p) (primTy p)
  | varU {Γ Δ n A} (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ) :
      Lookup Γ n A → Ty.Duplicable A → AllNone Δ → Ty.SemanticFragment A →
      FragmentJudgment Γ Δ (.var .unres n) A
  | varL {Γ Δ n A} (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ) :
      Lookup Δ n (some A) → OnlySomeAt Δ n → Ty.SemanticFragment A →
      FragmentJudgment Γ Δ (.var .lin n) A
  | lamU {Γ Δ A B M} (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ) :
      Ty.Admissible A → Ty.Duplicable A → AllNone Δ →
      Ty.SemanticFragment (.arrow .unres A B) →
      FragmentJudgment (A :: Γ) Δ M B →
      FragmentJudgment Γ Δ (.lam .unres A M) (.arrow .unres A B)
  | lamL {Γ Δ A B M} (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ) :
      Ty.Admissible A → Ty.FirstOrder A → Ty.SemanticFragment B →
      FragmentJudgment Γ (some A :: Δ) M B →
      FragmentJudgment Γ Δ (.lam .lin A M) (.arrow .lin A B)
  | appL {Γ Δ Δ₁ Δ₂ A B F X} (hΓ : CtxUAllBit Γ)
      (hΔ : CtxLAllSomeFragment Δ) :
      OSplit Δ Δ₁ Δ₂ → Ty.FirstOrder A → Ty.SemanticFragment B →
      FragmentJudgment Γ Δ₁ F (.arrow .lin A B) → FragmentJudgment Γ Δ₂ X A →
      FragmentJudgment Γ Δ (.app F X) B
  | appU {Γ Δ ΔF ΔX B F X} (hΓ : CtxUAllBit Γ)
      (hΔ : CtxLAllSomeFragment Δ) :
      OSplit Δ ΔF ΔX → AllNone ΔX → Ty.SemanticFragment B →
      FragmentJudgment Γ ΔF F (.arrow .unres .bit B) →
      FragmentJudgment Γ ΔX X .bit →
      FragmentJudgment Γ Δ (.app F X) B
  | pair {Γ Δ Δ₁ Δ₂ A B M N} (hΓ : CtxUAllBit Γ)
      (hΔ : CtxLAllSomeFragment Δ) :
      OSplit Δ Δ₁ Δ₂ → Ty.FirstOrder A → Ty.FirstOrder B →
      FragmentJudgment Γ Δ₁ M A → FragmentJudgment Γ Δ₂ N B →
      FragmentJudgment Γ Δ (.pair M N) (.tensor A B)
  | unpair {Γ Δ Δ₁ Δ₂ A B C M K} (hΓ : CtxUAllBit Γ)
      (hΔ : CtxLAllSomeFragment Δ) :
      OSplit Δ Δ₁ Δ₂ → Ty.FirstOrder A → Ty.FirstOrder B →
      Ty.SemanticFragment C →
      FragmentJudgment Γ Δ₁ M (.tensor A B) →
      FragmentJudgment Γ Δ₂ K (.arrow .lin A (.arrow .lin B C)) →
      FragmentJudgment Γ Δ (.unpair M K) C
  | ite {Γ Δ Δ₁ Δ₂ A B T E} (hΓ : CtxUAllBit Γ)
      (hΔ : CtxLAllSomeFragment Δ) :
      OSplit Δ Δ₁ Δ₂ → Ty.SemanticFragment A →
      FragmentJudgment Γ Δ₁ B .bit → FragmentJudgment Γ Δ₂ T A →
      FragmentJudgment Γ Δ₂ E A →
      FragmentJudgment Γ Δ (.ite B T E) A
  | measure {Γ Δ Δ₁ Δ₂ A Q K} (hΓ : CtxUAllBit Γ)
      (hΔ : CtxLAllSomeFragment Δ) :
      OSplit Δ Δ₁ Δ₂ → Ty.SemanticFragment A →
      FragmentJudgment Γ Δ₁ Q .qubit →
      FragmentJudgment Γ Δ₂ K (.arrow .unres .bit (.arrow .lin .qubit A)) →
      FragmentJudgment Γ Δ (.measure Q K) A

/-- Reconstruct the canonical fragment judgment from ordinary typing plus the
explicit context, binder, and result-fragment side conditions. -/
theorem fragmentJudgment_of_hasType :
    ∀ {Γ Δ M A}, HasType Γ Δ M A →
      CtxUAllBit Γ → CtxLAllSomeFragment Δ →
      FragmentBinders M → Ty.SemanticFragment A →
      FragmentJudgment Γ Δ M A
  | _, _, _, _, .varU hl hd hn, hΓ, hΔ, _, hA =>
      .varU hΓ hΔ hl hd hn hA
  | _, _, _, _, .varL hl ho, hΓ, hΔ, _, hA =>
      .varL hΓ hΔ hl ho hA
  | _, _, _, _, .lamU had hd hn h, hΓ, hΔ, hb, hA => by
      have hbit := FragmentBinders.lamUnres_bit hb
      subst hbit
      exact .lamU hΓ hΔ had hd hn hA
        (fragmentJudgment_of_hasType h (CtxUAllBit.cons hΓ) hΔ
          (FragmentBinders.lamUnres_body hb)
          (Ty.SemanticFragment.arrow_unres_cod hA))
  | _, _, _, _, .lamL had h, hΓ, hΔ, hb, hA => by
      obtain ⟨hdom, hcod⟩ := Ty.SemanticFragment.arrow_lin_inv hA
      exact .lamL hΓ hΔ had hdom hcod
        (fragmentJudgment_of_hasType h hΓ
          (CtxLAllSomeFragment.cons_some
            (Ty.SemanticFragment.of_firstOrder hdom) hΔ)
          (FragmentBinders.lamLin_body hb) hcod)
  | _, _, _, _, .appL hs hF hX, hΓ, hΔ, hb, hB => by
      have hdomains :=
        FragmentArrowDomains.of_hasType hF hΓ
          (CtxLAllSomeFragment.of_oSplit_left hΔ hs)
          (FragmentBinders.app_left hb)
      exact .appL hΓ hΔ hs hdomains.1 hB
        (fragmentJudgment_of_hasType hF hΓ
          (CtxLAllSomeFragment.of_oSplit_left hΔ hs)
          (FragmentBinders.app_left hb)
          (.arrowLin hdomains.1 hB))
        (fragmentJudgment_of_hasType hX hΓ
          (CtxLAllSomeFragment.of_oSplit_right hΔ hs)
          (FragmentBinders.app_right hb)
          (Ty.SemanticFragment.of_firstOrder hdomains.1))
  | _, _, _, _, .appU hs hn hF hX, hΓ, hΔ, hb, hB => by
      have hdomains :=
        FragmentArrowDomains.of_hasType hF hΓ
          (CtxLAllSomeFragment.of_oSplit_left hΔ hs)
          (FragmentBinders.app_left hb)
      have hbit := hdomains.1
      subst hbit
      exact .appU hΓ hΔ hs hn hB
        (fragmentJudgment_of_hasType hF hΓ
          (CtxLAllSomeFragment.of_oSplit_left hΔ hs)
          (FragmentBinders.app_left hb) (.arrowUnresBit hB))
        (fragmentJudgment_of_hasType hX hΓ
          (CtxLAllSomeFragment.of_oSplit_right hΔ hs)
          (FragmentBinders.app_right hb) Ty.SemanticFragment.bit)
  | _, _, _, _, .unit hn, hΓ, hΔ, _, _ =>
      .unit hΓ hΔ hn
  | _, _, _, _, .bitLit hn, hΓ, hΔ, _, _ =>
      .bitLit hΓ hΔ _ hn
  | _, _, _, _, .pair hs hM hN, hΓ, hΔ, hb, hAB => by
      obtain ⟨hA, hB⟩ := Ty.SemanticFragment.tensor_firstOrder hAB
      exact .pair hΓ hΔ hs hA hB
        (fragmentJudgment_of_hasType hM hΓ
          (CtxLAllSomeFragment.of_oSplit_left hΔ hs)
          (FragmentBinders.pair_left hb)
          (Ty.SemanticFragment.of_firstOrder hA))
        (fragmentJudgment_of_hasType hN hΓ
          (CtxLAllSomeFragment.of_oSplit_right hΔ hs)
          (FragmentBinders.pair_right hb)
          (Ty.SemanticFragment.of_firstOrder hB))
  | _, _, _, _, .unpair hs hM hK, hΓ, hΔ, hb, hC => by
      have hdomains :=
        FragmentArrowDomains.of_hasType hK hΓ
          (CtxLAllSomeFragment.of_oSplit_right hΔ hs)
          (FragmentBinders.unpair_right hb)
      exact .unpair hΓ hΔ hs hdomains.1 hdomains.2.1 hC
        (fragmentJudgment_of_hasType hM hΓ
          (CtxLAllSomeFragment.of_oSplit_left hΔ hs)
          (FragmentBinders.unpair_left hb)
          (Ty.SemanticFragment.tensor hdomains.1 hdomains.2.1))
        (fragmentJudgment_of_hasType hK hΓ
          (CtxLAllSomeFragment.of_oSplit_right hΔ hs)
          (FragmentBinders.unpair_right hb)
          (.arrowLin hdomains.1 (.arrowLin hdomains.2.1 hC)))
  | _, _, _, _, .ite hs hB hT hE, hΓ, hΔ, hb, hA =>
      .ite hΓ hΔ hs hA
        (fragmentJudgment_of_hasType hB hΓ
          (CtxLAllSomeFragment.of_oSplit_left hΔ hs)
          (FragmentBinders.ite_cond hb) Ty.SemanticFragment.bit)
        (fragmentJudgment_of_hasType hT hΓ
          (CtxLAllSomeFragment.of_oSplit_right hΔ hs)
          (FragmentBinders.ite_then hb) hA)
        (fragmentJudgment_of_hasType hE hΓ
          (CtxLAllSomeFragment.of_oSplit_right hΔ hs)
          (FragmentBinders.ite_else hb) hA)
  | _, _, _, _, .prim hn, hΓ, hΔ, _, _ =>
      .prim hΓ hΔ _ hn
  | _, _, _, _, .measure hs hQ hK, hΓ, hΔ, hb, hA =>
      .measure hΓ hΔ hs hA
        (fragmentJudgment_of_hasType hQ hΓ
          (CtxLAllSomeFragment.of_oSplit_left hΔ hs)
          (FragmentBinders.measure_qubit hb) Ty.SemanticFragment.qubit)
        (fragmentJudgment_of_hasType hK hΓ
          (CtxLAllSomeFragment.of_oSplit_right hΔ hs)
          (FragmentBinders.measure_cont hb)
          (.arrowUnresBit (.arrowLin .qubit hA)))
  | _, _, _, _, .fix _ _ _ _, _, _, hb, _ => False.elim hb
  | _, _, _, _, .fold _ _, _, _, hb, _ => False.elim hb
  | _, _, _, _, .unfold _ _, _, _, hb, _ => False.elim hb

/-- Every fragment judgment yields a certificate (Gate 1 completeness). -/
theorem exists_ofFragmentJudgment {Γ Δ M A}
    (j : FragmentJudgment Γ Δ M A) : Nonempty (FragCert Γ Δ M A) := by
  induction j with
  | unit hΓ hΔ h => exact ⟨.unit hΓ hΔ h⟩
  | bitLit hΓ hΔ b h => exact ⟨.bitLit hΓ hΔ b h⟩
  | prim hΓ hΔ p h => exact ⟨.prim hΓ hΔ p h⟩
  | varU hΓ hΔ hL hD hN hA => exact ⟨.varU hΓ hΔ hL hD hN hA⟩
  | varL hΓ hΔ hL hO hA => exact ⟨.varL hΓ hΔ hL hO hA⟩
  | lamU hΓ hΔ hAd hDup hN hArr _ ih =>
      obtain ⟨c⟩ := ih; exact ⟨.lamU hΓ hΔ hAd hDup hN hArr c⟩
  | lamL hΓ hΔ hAd hFO hB _ ih =>
      obtain ⟨c⟩ := ih; exact ⟨.lamL hΓ hΔ hAd hFO hB c⟩
  | appL hΓ hΔ hS hFO hB _ _ ihF ihX =>
      obtain ⟨cF⟩ := ihF; obtain ⟨cX⟩ := ihX
      exact ⟨.appL hΓ hΔ hS hFO hB cF cX⟩
  | appU hΓ hΔ hS hN hB _ _ ihF ihX =>
      obtain ⟨cF⟩ := ihF; obtain ⟨cX⟩ := ihX
      exact ⟨.appU hΓ hΔ hS hN hB cF cX⟩
  | pair hΓ hΔ hS hA hB _ _ ihM ihN =>
      obtain ⟨cM⟩ := ihM; obtain ⟨cN⟩ := ihN
      exact ⟨.pair hΓ hΔ hS hA hB cM cN⟩
  | unpair hΓ hΔ hS hA hB hC _ _ ihM ihK =>
      obtain ⟨cM⟩ := ihM; obtain ⟨cK⟩ := ihK
      exact ⟨.unpair hΓ hΔ hS hA hB hC cM cK⟩
  | ite hΓ hΔ hS hA _ _ _ ihB ihT ihE =>
      obtain ⟨cB⟩ := ihB; obtain ⟨cT⟩ := ihT; obtain ⟨cE⟩ := ihE
      exact ⟨.ite hΓ hΔ hS hA cB cT cE⟩
  | measure hΓ hΔ hS hA _ _ ihQ ihK =>
      obtain ⟨cQ⟩ := ihQ; obtain ⟨cK⟩ := ihK
      exact ⟨.measure hΓ hΔ hS hA cQ cK⟩

/-- Every fragment judgment yields a certificate. -/
noncomputable def ofFragmentJudgment {Γ Δ M A}
    (j : FragmentJudgment Γ Δ M A) : FragCert Γ Δ M A :=
  (exists_ofFragmentJudgment j).some

/-- Erasure of certificates into the propositional fragment judgment. -/
theorem toFragmentJudgment {Γ Δ M A} (c : FragCert Γ Δ M A) :
    FragmentJudgment Γ Δ M A := by
  induction c with
  | unit hΓ hΔ h => exact .unit hΓ hΔ h
  | bitLit hΓ hΔ b h => exact .bitLit hΓ hΔ b h
  | prim hΓ hΔ p h => exact .prim hΓ hΔ p h
  | varU hΓ hΔ hL hD hN hA => exact .varU hΓ hΔ hL hD hN hA
  | varL hΓ hΔ hL hO hA => exact .varL hΓ hΔ hL hO hA
  | lamU hΓ hΔ hAd hDup hN hArr _ ih => exact .lamU hΓ hΔ hAd hDup hN hArr ih
  | lamL hΓ hΔ hAd hFO hB _ ih => exact .lamL hΓ hΔ hAd hFO hB ih
  | appL hΓ hΔ hS hFO hB _ _ ihF ihX => exact .appL hΓ hΔ hS hFO hB ihF ihX
  | appU hΓ hΔ hS hN hB _ _ ihF ihX => exact .appU hΓ hΔ hS hN hB ihF ihX
  | pair hΓ hΔ hS hA hB _ _ ihM ihN => exact .pair hΓ hΔ hS hA hB ihM ihN
  | unpair hΓ hΔ hS hA hB hC _ _ ihM ihK =>
      exact .unpair hΓ hΔ hS hA hB hC ihM ihK
  | ite hΓ hΔ hS hA _ _ _ ihB ihT ihE => exact .ite hΓ hΔ hS hA ihB ihT ihE
  | measure hΓ hΔ hS hA _ _ ihQ ihK => exact .measure hΓ hΔ hS hA ihQ ihK

/-- Round-trip: fragment judgment ↔ certificate (Gate 1). -/
theorem ofHasType_complete {Γ Δ M A} (j : FragmentJudgment Γ Δ M A) :
    Nonempty (FragCert Γ Δ M A) :=
  exists_ofFragmentJudgment j

/-- Build a certificate from the propositional fragment judgment. -/
noncomputable def ofHasType {Γ Δ M A} (j : FragmentJudgment Γ Δ M A) : FragCert Γ Δ M A :=
  ofFragmentJudgment j

/-- Closed fragment certificate: empty contexts. -/
abbrev Closed (M : Term) (A : Ty) := FragCert [] [] M A

/-- Closed unit certificate. -/
def closed_unit_cert : Closed .unit .unit :=
  .unit CtxUAllBit.nil CtxLAllSomeFragment.nil trivial

/-- Closed bit-literal certificate. -/
def closed_bitLit_cert (b : Bool) : Closed (.bitLit b) .bit :=
  .bitLit CtxUAllBit.nil CtxLAllSomeFragment.nil b trivial

/-- Closed primitive certificate. -/
def closed_prim_cert (p : Prim) : Closed (.prim p) (primTy p) :=
  .prim CtxUAllBit.nil CtxLAllSomeFragment.nil p trivial

theorem closed_unit_cert_unique (c : Closed .unit .unit) :
    c = closed_unit_cert := by
  cases c
  rfl

theorem closed_bitLit_cert_unique {b : Bool} (c : Closed (.bitLit b) .bit) :
    c = closed_bitLit_cert b := by
  cases c
  rfl

theorem closed_prim_cert_unique {p : Prim} (c : Closed (.prim p) (primTy p)) :
    c = closed_prim_cert p := by
  cases c
  rfl

/-- Closed unit/bit/prim judgments inhabit `FragmentJudgment`. -/
theorem fragmentJudgment_closed_unit :
    FragmentJudgment [] [] .unit .unit :=
  .unit CtxUAllBit.nil CtxLAllSomeFragment.nil trivial

theorem fragmentJudgment_closed_bitLit (b : Bool) :
    FragmentJudgment [] [] (.bitLit b) .bit :=
  .bitLit CtxUAllBit.nil CtxLAllSomeFragment.nil b trivial

theorem fragmentJudgment_closed_prim (p : Prim) :
    FragmentJudgment [] [] (.prim p) (primTy p) :=
  .prim CtxUAllBit.nil CtxLAllSomeFragment.nil p trivial

/-- Denotation of closed unit certificates. -/
noncomputable def denoteUnit
    (_c : Closed .unit .unit) :
    Hom dayTensorUnit (representable 1) :=
  routeAFragmentModel.unitIntro

/-- Denotation of closed bit-literal certificates. -/
noncomputable def denoteBitLit {b : Bool}
    (_c : Closed (.bitLit b) .bit) :
    Hom dayTensorUnit (representable 2) :=
  routeAFragmentModel.bitLit b

theorem denoteUnit_eq (c : Closed .unit .unit) :
    denoteUnit c = routeAFragmentModel.unitIntro :=
  rfl

theorem denoteBitLit_eq {b : Bool} (c : Closed (.bitLit b) .bit) :
    denoteBitLit c = routeAFragmentModel.bitLit b :=
  rfl

/-- Closed denotation into the combined empty context. -/
noncomputable def denoteClosedUnit (c : Closed .unit .unit) :
    Hom (FragmentContext.combined [] []) (fragmentModule .unit) :=
  FragmentContext.closedPoint (denoteUnit c)

noncomputable def denoteClosedBitLit {b : Bool} (c : Closed (.bitLit b) .bit) :
    Hom (FragmentContext.combined [] []) (fragmentModule .bit) :=
  FragmentContext.closedPoint (denoteBitLit c)

theorem denoteClosedUnit_eq (c : Closed .unit .unit) :
    denoteClosedUnit c =
      FragmentContext.closedPoint routeAFragmentModel.unitIntro := by
  simp [denoteClosedUnit, denoteUnit]

theorem denoteClosedBitLit_eq {b : Bool} (c : Closed (.bitLit b) .bit) :
    denoteClosedBitLit c =
      FragmentContext.closedPoint (routeAFragmentModel.bitLit b) := by
  simp [denoteClosedBitLit, denoteBitLit]

end FragCert

/-- The sole effect not supplied by symmetric monoidal closed structure:
selection between two already-denoted branches.  Keeping this interface
explicit prevents a zero/fallback map from masquerading as `ite` semantics. -/
structure FragmentBranching where
  iteElim :
    ∀ {A : Ty}, Ty.SemanticFragment A →
      Hom
        (dayTensor (fragmentModule .bit)
          (additiveProduct (fragmentModule A) (fragmentModule A)))
        (fragmentModule A)


namespace FragCert

/-- A primitive constant, curried into its source-language linear-arrow
type. -/
noncomputable def denotePrimPoint (p : Prim) :
    Hom dayTensorUnit (fragmentModule (primTy p)) := by
  cases p with
  | new0 =>
      exact FragmentContext.curryFirstOrder 1
        (Hom.comp (routeAFragmentModel.primMap .new0)
          (DayTensor.leftUnitor (representable 1)))
  | x =>
      exact FragmentContext.curryFirstOrder 2
        (Hom.comp (routeAFragmentModel.primMap .x)
          (DayTensor.leftUnitor (representable 2)))
  | h =>
      exact FragmentContext.curryFirstOrder 2
        (Hom.comp (routeAFragmentModel.primMap .h)
          (DayTensor.leftUnitor (representable 2)))
  | t =>
      exact FragmentContext.curryFirstOrder 2
        (Hom.comp (routeAFragmentModel.primMap .t)
          (DayTensor.leftUnitor (representable 2)))
  | ry θ =>
      exact FragmentContext.curryFirstOrder 2
        (Hom.comp (routeAFragmentModel.primMap (.ry θ))
          (DayTensor.leftUnitor (representable 2)))
  | cx =>
      let inner :
          Hom (representable 2)
            (internalHomRepresentable 2 (representable 4)) :=
        FragmentContext.curryFirstOrder 2
          (Hom.comp (routeAFragmentModel.primMap .cx)
            (dayTensorRepresentableIso 2 2).hom)
      exact FragmentContext.curryFirstOrder 2
        (Hom.comp inner (DayTensor.leftUnitor (representable 2)))
  | reset =>
      exact FragmentContext.curryFirstOrder 2
        (Hom.comp (routeAFragmentModel.primMap .reset)
          (DayTensor.leftUnitor (representable 2)))

/-- Retained computational-basis measurement: the first output is the
classical outcome and the second is the post-measurement qubit. -/
noncomputable def retainedMeasurement :
    Hom (representable 2)
      (dayTensor (representable 2) (representable 2)) :=
  Hom.comp (dayTensorRepresentableIso 2 2).inv
    (yonedaMap
      (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator))

/-- Apply a measurement continuation to the retained outcome and qubit.
The outcome crosses the explicit physical-to-classical boundary before
unrestricted evaluation. -/
noncomputable def measureElim (N : Module) :
    Hom
      (dayTensor (fragmentModule .qubit)
        (dayInternalHom classicalBitModule
          (internalHomRepresentable 2 N)))
      N :=
  Hom.comp (FragmentContext.evalFirstOrder 2 N)
    (Hom.comp
      (DayTensor.map
        (FragmentContext.evalUnrestrictedBit
          (internalHomRepresentable 2 N))
        (Hom.id (representable 2)))
      (Hom.comp
        (DayTensor.associatorInv
          (dayInternalHom classicalBitModule
            (internalHomRepresentable 2 N))
          (representable 2) (representable 2))
        (Hom.comp
          (DayTensor.map (Hom.id _) retainedMeasurement)
          (DayTensor.braiding (representable 2)
            (dayInternalHom classicalBitModule
              (internalHomRepresentable 2 N))))))

/-- Full compositional denotation relative only to a genuine `ite`
eliminator.  All other constructors are concrete. -/
noncomputable def denoteWith (branching : FragmentBranching) :
    {Γ : List Ty} → {Δ : List (Option Ty)} → {M : Term} → {A : Ty} →
      FragCert Γ Δ M A →
        Hom (FragmentContext.combined Γ Δ) (fragmentModule A)
  | _, _, _, _, .unit hΓ _ hΔ =>
      FragmentContext.combinedPoint hΓ hΔ routeAFragmentModel.unitIntro
  | _, _, _, _, .bitLit hΓ _ b hΔ =>
      FragmentContext.combinedPoint hΓ hΔ (routeAFragmentModel.bitLit b)
  | _, _, _, _, .prim hΓ _ p hΔ =>
      FragmentContext.combinedPoint hΓ hΔ (denotePrimPoint p)
  | _, _, _, _, .varU hΓ _ hl _ hΔ _ =>
      FragmentContext.combinedLookupUnrestricted hΓ hl hΔ
  | _, _, _, _, .varL hΓ _ hl ho _ =>
      FragmentContext.combinedLookupLinear hΓ hl ho
  | _, _, _, _, .lamU _ _ _ _ _ hArr c => by
      have hdom : _ = Ty.bit := Ty.SemanticFragment.arrow_unres_eq hArr
      subst hdom
      exact FragmentContext.abstractUnrestricted (denoteWith branching c)
  | _, _, _, _, .lamL _ _ _ hA _ c =>
      FragmentContext.abstractLinear hA (denoteWith branching c)
  | _, _, _, _, .appL hΓ _ hs hA _ cF cX =>
      Hom.comp (FragmentContext.evalFragmentFirstOrder hA _)
        (Hom.comp
          (DayTensor.map (denoteWith branching cF)
            (denoteWith branching cX))
          (FragmentContext.combinedOSplit hΓ hs))
  | _, _, _, _, .appU hΓ _ hs _ _ cF cX =>
      Hom.comp (FragmentContext.evalUnrestrictedBit _)
        (Hom.comp
          (DayTensor.map (denoteWith branching cF)
            (denoteWith branching cX))
          (FragmentContext.combinedOSplit hΓ hs))
  | _, _, _, _, .pair hΓ _ hs hA hB cM cN =>
      Hom.comp (FragmentContext.tensorIntro hA hB)
        (Hom.comp
          (DayTensor.map (denoteWith branching cM)
            (denoteWith branching cN))
          (FragmentContext.combinedOSplit hΓ hs))
  | _, _, _, _, .unpair hΓ _ hs hA hB _ cM cK =>
      Hom.comp (FragmentContext.unpairApply hA hB _)
        (Hom.comp
          (DayTensor.map (denoteWith branching cM)
            (denoteWith branching cK))
          (FragmentContext.combinedOSplit hΓ hs))
  | _, _, _, _, .ite hΓ _ hs hA cB cT cE =>
      Hom.comp (branching.iteElim hA)
        (Hom.comp
          (DayTensor.map (denoteWith branching cB)
            (additivePair (denoteWith branching cT)
              (denoteWith branching cE)))
          (FragmentContext.combinedOSplit hΓ hs))
  | _, _, _, _, .measure hΓ _ hs _ cQ cK =>
      Hom.comp (measureElim _)
        (Hom.comp
          (DayTensor.map (denoteWith branching cQ)
            (denoteWith branching cK))
          (FragmentContext.combinedOSplit hΓ hs))

end FragCert

/-- Operations required for full compositional fragment denotation. -/
structure FragmentDenotationModel where
  /-- Open-term denotation on combined contexts. -/
  denote :
    ∀ {Γ Δ M A}, FragCert Γ Δ M A →
      Hom (FragmentContext.combined Γ Δ) (fragmentModule A)
  /-- Closed unit agrees with Route A. -/
  denote_unit :
    ∀ (c : FragCert.Closed .unit .unit),
      denote c =
        FragmentContext.closedPoint routeAFragmentModel.unitIntro
  /-- Closed bit literals agree with Route A. -/
  denote_bitLit :
    ∀ (b : Bool) (c : FragCert.Closed (.bitLit b) .bit),
      denote c =
        FragmentContext.closedPoint (routeAFragmentModel.bitLit b)


/-- Route A supplies closed unit/bit denotation into combined contexts. -/
noncomputable def routeAClosedDenotationCore :
    (∀ (c : FragCert.Closed .unit .unit),
      Hom (FragmentContext.combined [] []) (fragmentModule .unit)) ×
    (∀ (b : Bool) (c : FragCert.Closed (.bitLit b) .bit),
      Hom (FragmentContext.combined [] []) (fragmentModule .bit)) :=
  ⟨FragCert.denoteClosedUnit, fun b c => FragCert.denoteClosedBitLit c⟩

namespace ClosedSemanticFragment

theorem ofFragCert {M : Term} {A : Ty} (c : FragCert [] [] M A) :
    ClosedSemanticFragment M A :=
  ⟨FragCert.toHasType c, FragCert.result_fragment c, FragCert.term_fragment c⟩

end ClosedSemanticFragment

/-- Exact agreement of Route A primitive maps with `Prim.superoperator`. -/
theorem fragment_prim_superoperator (p : Prim) :
    routeAFragmentModel.primMap p = yonedaMap (Prim.superoperator p) :=
  routeAFragmentModel.prim_agrees p

/-- Exact agreement of Route A primitives with Kraus/`CompletedCP` presentations. -/
theorem fragment_prim_completedCP (p : Prim) :
    (Prim.superoperator p).cp = CPMap.ofKraus p.kraus :=
  Prim.cp_superoperator p

end QLambda.Linear
