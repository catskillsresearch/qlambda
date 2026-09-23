/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.Typing
import QLambda.Linear.Substitution
import QLambda.Linear.Quotation
import QLambda.Linear.QuotationGeneral

/-!
# Minimum semantic source fragment

The fragment used by finite runtime, one- and two-wire quotation, and the
Palomar capstone: first-order data, linear arrows with first-order domain,
and unrestricted binders whose domain is classical `bit`.  It excludes
`mu`, `fix`, `fold`/`unfold`, free type variables, and unrestricted arrows
with non-bit domain.

This is strictly larger than `Ty.FirstOrder` (arrows are admitted) and
strictly smaller than the full source language.
-/

namespace QLambda.Linear

namespace Ty

/-- Types admitted by the minimum CP-presheaf source semantics. -/
inductive SemanticFragment : Ty → Prop where
  | ofFirstOrder {A} : FirstOrder A → SemanticFragment A
  | arrowLin {A B} :
      FirstOrder A → SemanticFragment B → SemanticFragment (.arrow .lin A B)
  | arrowUnresBit {B} :
      SemanticFragment B → SemanticFragment (.arrow .unres .bit B)

namespace SemanticFragment

theorem unit : SemanticFragment .unit :=
  .ofFirstOrder .unit

theorem bit : SemanticFragment .bit :=
  .ofFirstOrder .bit

theorem qubit : SemanticFragment .qubit :=
  .ofFirstOrder .qubit

theorem tensor {A B : Ty} (hA : FirstOrder A) (hB : FirstOrder B) :
    SemanticFragment (.tensor A B) :=
  .ofFirstOrder (.tensor hA hB)

/-- Every first-order type is in the semantic fragment. -/
theorem of_firstOrder {A : Ty} (h : FirstOrder A) : SemanticFragment A :=
  .ofFirstOrder h

/-- Executable checker for the minimum fragment. -/
def semanticFragmentB : Ty → Bool
  | .unit | .bit | .qubit => true
  | .tensor A B => A.firstOrderB && B.firstOrderB
  | .arrow .lin A B => A.firstOrderB && semanticFragmentB B
  | .arrow .unres .bit B => semanticFragmentB B
  | _ => false

theorem semanticFragmentB_sound {A : Ty} (h : semanticFragmentB A = true) :
    SemanticFragment A := by
  match A with
  | .unit => exact unit
  | .bit => exact bit
  | .qubit => exact qubit
  | .tensor A B =>
      simp only [semanticFragmentB, Bool.and_eq_true] at h
      exact tensor (firstOrderB_sound h.1) (firstOrderB_sound h.2)
  | .arrow .lin A B =>
      simp only [semanticFragmentB, Bool.and_eq_true] at h
      exact .arrowLin (firstOrderB_sound h.1) (semanticFragmentB_sound h.2)
  | .arrow .unres .bit B =>
      simp only [semanticFragmentB] at h
      exact .arrowUnresBit (semanticFragmentB_sound h)
  | .arrow .unres .unit B | .arrow .unres .qubit B
  | .arrow .unres (.var _) B | .arrow .unres (.tensor _ _) B
  | .arrow .unres (.arrow _ _ _) B | .arrow .unres (.mu _) B =>
      simp [semanticFragmentB] at h
  | .var _ | .mu _ => simp [semanticFragmentB] at h

theorem not_var {n : Nat} : ¬ SemanticFragment (.var n) := by
  intro h; cases h; rename_i hFO; cases hFO

theorem not_mu {A : Ty} : ¬ SemanticFragment (.mu A) := by
  intro h; cases h; rename_i hFO; cases hFO

/-- Primitive types lie in the fragment. -/
theorem primTy_fragment (p : Prim) : SemanticFragment (primTy p) := by
  cases p with
  | new0 => exact .arrowLin .unit qubit
  | x | h | t | reset => exact .arrowLin .qubit qubit
  | ry _ => exact .arrowLin .qubit qubit
  | cx =>
      exact .arrowLin .qubit (.arrowLin .qubit (tensor .qubit .qubit))

end SemanticFragment

end Ty

/-- One-wire quotation type is in the fragment. -/
theorem quotationTy_semanticFragment :
    Ty.SemanticFragment Command.quotationTy := by
  unfold Command.quotationTy
  exact .arrowUnresBit
    (.arrowLin .qubit (Ty.SemanticFragment.tensor .qubit .bit))

/-- Two-wire quotation type is in the fragment. -/
theorem generalQuotationTy_semanticFragment :
    Ty.SemanticFragment Command.GeneralQuotation.quotationTy := by
  unfold Command.GeneralQuotation.quotationTy
    Command.GeneralQuotation.resultTy
    Command.GeneralQuotation.qubitRegisterTy
  exact .arrowUnresBit
    (.arrowLin .qubit
      (.arrowLin .qubit
        (Ty.SemanticFragment.tensor (.tensor .qubit .qubit) .bit)))

namespace Term

/-- Terms whose annotations and constructors stay inside the minimum fragment
(no `fix` / `fold` / `unfold`). -/
inductive SemanticFragment : Term → Prop where
  | var {κ n} : SemanticFragment (.var κ n)
  | lam {κ A M} :
      Ty.SemanticFragment A → SemanticFragment M →
      SemanticFragment (.lam κ A M)
  | app {F X} :
      SemanticFragment F → SemanticFragment X → SemanticFragment (.app F X)
  | unit : SemanticFragment .unit
  | bitLit {b} : SemanticFragment (.bitLit b)
  | pair {M N} :
      SemanticFragment M → SemanticFragment N → SemanticFragment (.pair M N)
  | unpair {M K} :
      SemanticFragment M → SemanticFragment K → SemanticFragment (.unpair M K)
  | ite {B T E} :
      SemanticFragment B → SemanticFragment T → SemanticFragment E →
      SemanticFragment (.ite B T E)
  | prim {p} : SemanticFragment (.prim p)
  | measure {Q K} :
      SemanticFragment Q → SemanticFragment K → SemanticFragment (.measure Q K)

theorem not_fix {A : Ty} {M : Term} : ¬ SemanticFragment (.fix A M) := by
  intro h; cases h

theorem not_fold {A : Ty} {M : Term} : ¬ SemanticFragment (.fold A M) := by
  intro h; cases h

theorem not_unfold {M : Term} : ¬ SemanticFragment (.unfold M) := by
  intro h; cases h

theorem shiftLin_semanticFragment {d cutoff : Nat} :
    ∀ {M : Term}, SemanticFragment M → SemanticFragment (shiftLin d cutoff M)
  | .var .lin n, h => by
      cases h
      change SemanticFragment
        (.var .lin (if n < cutoff then n else n + d))
      split <;> exact .var
  | .var .unres n, h => by cases h; exact .var
  | .lam .lin A M, .lam hA hM =>
      .lam hA (shiftLin_semanticFragment (cutoff := cutoff + 1) hM)
  | .lam .unres A M, .lam hA hM =>
      .lam hA (shiftLin_semanticFragment (cutoff := cutoff) hM)
  | .app F X, .app hF hX =>
      .app (shiftLin_semanticFragment hF) (shiftLin_semanticFragment hX)
  | .unit, .unit => .unit
  | .bitLit b, .bitLit => .bitLit
  | .pair M N, .pair hM hN =>
      .pair (shiftLin_semanticFragment hM) (shiftLin_semanticFragment hN)
  | .unpair M K, .unpair hM hK =>
      .unpair (shiftLin_semanticFragment hM) (shiftLin_semanticFragment hK)
  | .ite B T E, .ite hB hT hE =>
      .ite (shiftLin_semanticFragment hB) (shiftLin_semanticFragment hT)
        (shiftLin_semanticFragment hE)
  | .prim p, .prim => .prim
  | .measure Q K, .measure hQ hK =>
      .measure (shiftLin_semanticFragment hQ) (shiftLin_semanticFragment hK)

theorem shiftUnres_semanticFragment {d cutoff : Nat} :
    ∀ {M : Term}, SemanticFragment M → SemanticFragment (shiftUnres d cutoff M)
  | .var .unres n, h => by
      cases h
      change SemanticFragment
        (.var .unres (if n < cutoff then n else n + d))
      split <;> exact .var
  | .var .lin n, h => by cases h; exact .var
  | .lam .unres A M, .lam hA hM =>
      .lam hA (shiftUnres_semanticFragment (cutoff := cutoff + 1) hM)
  | .lam .lin A M, .lam hA hM =>
      .lam hA (shiftUnres_semanticFragment (cutoff := cutoff) hM)
  | .app F X, .app hF hX =>
      .app (shiftUnres_semanticFragment hF) (shiftUnres_semanticFragment hX)
  | .unit, .unit => .unit
  | .bitLit b, .bitLit => .bitLit
  | .pair M N, .pair hM hN =>
      .pair (shiftUnres_semanticFragment hM) (shiftUnres_semanticFragment hN)
  | .unpair M K, .unpair hM hK =>
      .unpair (shiftUnres_semanticFragment hM) (shiftUnres_semanticFragment hK)
  | .ite B T E, .ite hB hT hE =>
      .ite (shiftUnres_semanticFragment hB) (shiftUnres_semanticFragment hT)
        (shiftUnres_semanticFragment hE)
  | .prim p, .prim => .prim
  | .measure Q K, .measure hQ hK =>
      .measure (shiftUnres_semanticFragment hQ) (shiftUnres_semanticFragment hK)

theorem substLin_semanticFragment {k : Nat} {V : Term} (hV : SemanticFragment V) :
    ∀ {M : Term}, SemanticFragment M → SemanticFragment (substLin k V M)
  | .var .lin n, h => by
      cases h
      simp only [substLin]
      split
      · exact .var
      · split
        · exact shiftLin_semanticFragment (d := k) (cutoff := 0) hV
        · exact .var
  | .var .unres n, h => by cases h; exact .var
  | .lam .lin A M, .lam hA hM =>
      .lam hA (substLin_semanticFragment (k := k + 1) hV hM)
  | .lam .unres A M, .lam hA hM =>
      .lam hA
        (substLin_semanticFragment (k := k)
          (shiftUnres_semanticFragment (d := 1) (cutoff := 0) hV) hM)
  | .app F X, .app hF hX =>
      .app (substLin_semanticFragment hV hF) (substLin_semanticFragment hV hX)
  | .unit, .unit => .unit
  | .bitLit b, .bitLit => .bitLit
  | .pair M N, .pair hM hN =>
      .pair (substLin_semanticFragment hV hM) (substLin_semanticFragment hV hN)
  | .unpair M K, .unpair hM hK =>
      .unpair (substLin_semanticFragment hV hM) (substLin_semanticFragment hV hK)
  | .ite B T E, .ite hB hT hE =>
      .ite (substLin_semanticFragment hV hB) (substLin_semanticFragment hV hT)
        (substLin_semanticFragment hV hE)
  | .prim p, .prim => .prim
  | .measure Q K, .measure hQ hK =>
      .measure (substLin_semanticFragment hV hQ) (substLin_semanticFragment hV hK)

theorem substUnres_semanticFragment {k : Nat} {V : Term} (hV : SemanticFragment V) :
    ∀ {M : Term}, SemanticFragment M → SemanticFragment (substUnres k V M)
  | .var .unres n, h => by
      cases h
      simp only [substUnres]
      split
      · exact .var
      · split
        · exact shiftUnres_semanticFragment (d := k) (cutoff := 0) hV
        · exact .var
  | .var .lin n, h => by cases h; exact .var
  | .lam .unres A M, .lam hA hM =>
      .lam hA (substUnres_semanticFragment (k := k + 1) hV hM)
  | .lam .lin A M, .lam hA hM =>
      .lam hA
        (substUnres_semanticFragment (k := k)
          (shiftLin_semanticFragment (d := 1) (cutoff := 0) hV) hM)
  | .app F X, .app hF hX =>
      .app (substUnres_semanticFragment hV hF) (substUnres_semanticFragment hV hX)
  | .unit, .unit => .unit
  | .bitLit b, .bitLit => .bitLit
  | .pair M N, .pair hM hN =>
      .pair (substUnres_semanticFragment hV hM) (substUnres_semanticFragment hV hN)
  | .unpair M K, .unpair hM hK =>
      .unpair (substUnres_semanticFragment hV hM) (substUnres_semanticFragment hV hK)
  | .ite B T E, .ite hB hT hE =>
      .ite (substUnres_semanticFragment hV hB) (substUnres_semanticFragment hV hT)
        (substUnres_semanticFragment hV hE)
  | .prim p, .prim => .prim
  | .measure Q K, .measure hQ hK =>
      .measure (substUnres_semanticFragment hV hQ) (substUnres_semanticFragment hV hK)

end Term

/-- Closed fragment judgments: empty contexts, fragment result and term. -/
def ClosedSemanticFragment (M : Term) (A : Ty) : Prop :=
  HasType [] [] M A ∧ Ty.SemanticFragment A ∧ Term.SemanticFragment M

end QLambda.Linear
