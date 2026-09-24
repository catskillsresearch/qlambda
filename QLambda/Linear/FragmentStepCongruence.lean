/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentSubstBeta
import QLambda.Linear.FragmentUnpairBeta

/-!
# Fragment Step denotational congruence

Congruence lemmas for fragment-admitted `Step`/`MeasStep` contexts and the
complete fragment-admitted Step soundness package (closed β cases + full
congruence suite).
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf

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

/-- Package: denotational congruence for fragment-admitted Step contexts
(app, ite, pair, unpair, measure). -/
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
    (∀ {Γ Δ Δ₁ Δ₂ A B B' T E}
        (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
        (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
        (cB : FragCert Γ Δ₁ B .bit) (cB' : FragCert Γ Δ₁ B' .bit)
        (cT : FragCert Γ Δ₂ T A) (cE : FragCert Γ Δ₂ E A),
      FragCert.denote cB = FragCert.denote cB' →
      FragCert.denote (.ite hΓ hΔ hs hA cB cT cE) =
        FragCert.denote (.ite hΓ hΔ hs hA cB' cT cE)) ∧
    (∀ {Γ Δ Δ₁ Δ₂ A B T T' E}
        (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
        (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
        (cB : FragCert Γ Δ₁ B .bit)
        (cT : FragCert Γ Δ₂ T A) (cT' : FragCert Γ Δ₂ T' A)
        (cE : FragCert Γ Δ₂ E A),
      FragCert.denote cT = FragCert.denote cT' →
      FragCert.denote (.ite hΓ hΔ hs hA cB cT cE) =
        FragCert.denote (.ite hΓ hΔ hs hA cB cT' cE)) ∧
    (∀ {Γ Δ Δ₁ Δ₂ A B T E E'}
        (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
        (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
        (cB : FragCert Γ Δ₁ B .bit) (cT : FragCert Γ Δ₂ T A)
        (cE : FragCert Γ Δ₂ E A) (cE' : FragCert Γ Δ₂ E' A),
      FragCert.denote cE = FragCert.denote cE' →
      FragCert.denote (.ite hΓ hΔ hs hA cB cT cE) =
        FragCert.denote (.ite hΓ hΔ hs hA cB cT cE')) ∧
    (∀ {Γ Δ Δ₁ Δ₂ A B M M' N}
        (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
        (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B)
        (cM : FragCert Γ Δ₁ M A) (cM' : FragCert Γ Δ₁ M' A)
        (cN : FragCert Γ Δ₂ N B),
      FragCert.denote cM = FragCert.denote cM' →
      FragCert.denote (.pair hΓ hΔ hs hA hB cM cN) =
        FragCert.denote (.pair hΓ hΔ hs hA hB cM' cN)) ∧
    (∀ {Γ Δ Δ₁ Δ₂ A B M N N'}
        (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
        (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B)
        (cM : FragCert Γ Δ₁ M A)
        (cN : FragCert Γ Δ₂ N B) (cN' : FragCert Γ Δ₂ N' B),
      FragCert.denote cN = FragCert.denote cN' →
      FragCert.denote (.pair hΓ hΔ hs hA hB cM cN) =
        FragCert.denote (.pair hΓ hΔ hs hA hB cM cN')) ∧
    (∀ {Γ Δ Δ₁ Δ₂ A B C M M' K}
        (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
        (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B)
        (hC : Ty.SemanticFragment C)
        (cM : FragCert Γ Δ₁ M (.tensor A B))
        (cM' : FragCert Γ Δ₁ M' (.tensor A B))
        (cK : FragCert Γ Δ₂ K (.arrow .lin A (.arrow .lin B C))),
      FragCert.denote cM = FragCert.denote cM' →
      FragCert.denote (.unpair hΓ hΔ hs hA hB hC cM cK) =
        FragCert.denote (.unpair hΓ hΔ hs hA hB hC cM' cK)) ∧
    (∀ {Γ Δ Δ₁ Δ₂ A B C M K K'}
        (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
        (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B)
        (hC : Ty.SemanticFragment C)
        (cM : FragCert Γ Δ₁ M (.tensor A B))
        (cK : FragCert Γ Δ₂ K (.arrow .lin A (.arrow .lin B C)))
        (cK' : FragCert Γ Δ₂ K' (.arrow .lin A (.arrow .lin B C))),
      FragCert.denote cK = FragCert.denote cK' →
      FragCert.denote (.unpair hΓ hΔ hs hA hB hC cM cK) =
        FragCert.denote (.unpair hΓ hΔ hs hA hB hC cM cK')) ∧
    (∀ {Γ Δ Δ₁ Δ₂ A Q Q' K}
        (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
        (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
        (cQ : FragCert Γ Δ₁ Q .qubit) (cQ' : FragCert Γ Δ₁ Q' .qubit)
        (cK : FragCert Γ Δ₂ K (.arrow .unres .bit (.arrow .lin .qubit A))),
      FragCert.denote cQ = FragCert.denote cQ' →
      FragCert.denote (.measure hΓ hΔ hs hA cQ cK) =
        FragCert.denote (.measure hΓ hΔ hs hA cQ' cK)) ∧
    (∀ {Γ Δ Δ₁ Δ₂ A Q K K'}
        (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
        (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
        (cQ : FragCert Γ Δ₁ Q .qubit)
        (cK : FragCert Γ Δ₂ K (.arrow .unres .bit (.arrow .lin .qubit A)))
        (cK' : FragCert Γ Δ₂ K' (.arrow .unres .bit (.arrow .lin .qubit A))),
      FragCert.denote cK = FragCert.denote cK' →
      FragCert.denote (.measure hΓ hΔ hs hA cQ cK) =
        FragCert.denote (.measure hΓ hΔ hs hA cQ cK')) :=
  ⟨fun {_Γ} {_Δ} {_Δ₁} {_Δ₂} {_A} {_B} {_F} {_F'} {_X} hΓ hΔ hs hFO hB cF cF' cX h =>
      fragment_step_congruence_appL_fun hΓ hΔ hs hFO hB cF cF' cX h,
    fun {_Γ} {_Δ} {_Δ₁} {_Δ₂} {_A} {_B} {_F} {_X} {_X'} hΓ hΔ hs hFO hB cF cX cX' h =>
      fragment_step_congruence_appL_arg hΓ hΔ hs hFO hB cF cX cX' h,
    fun {_Γ} {_Δ} {_ΔF} {_ΔX} {_B} {_F} {_F'} {_X} hΓ hΔ hs hN hB cF cF' cX h =>
      fragment_step_congruence_appU_fun hΓ hΔ hs hN hB cF cF' cX h,
    fun {_Γ} {_Δ} {_ΔF} {_ΔX} {_B} {_F} {_X} {_X'} hΓ hΔ hs hN hB cF cX cX' h =>
      fragment_step_congruence_appU_arg hΓ hΔ hs hN hB cF cX cX' h,
    fun {_Γ} {_Δ} {_Δ₁} {_Δ₂} {_A} {_B} {_B'} {_T} {_E} hΓ hΔ hs hA cB cB' cT cE h =>
      fragment_step_congruence_ite_scrutinee hΓ hΔ hs hA cB cB' cT cE h,
    fun {_Γ} {_Δ} {_Δ₁} {_Δ₂} {_A} {_B} {_T} {_T'} {_E} hΓ hΔ hs hA cB cT cT' cE h =>
      fragment_step_congruence_ite_then hΓ hΔ hs hA cB cT cT' cE h,
    fun {_Γ} {_Δ} {_Δ₁} {_Δ₂} {_A} {_B} {_T} {_E} {_E'} hΓ hΔ hs hA cB cT cE cE' h =>
      fragment_step_congruence_ite_else hΓ hΔ hs hA cB cT cE cE' h,
    fun {_Γ} {_Δ} {_Δ₁} {_Δ₂} {_A} {_B} {_M} {_M'} {_N} hΓ hΔ hs hA hB cM cM' cN h =>
      fragment_step_congruence_pair_left hΓ hΔ hs hA hB cM cM' cN h,
    fun {_Γ} {_Δ} {_Δ₁} {_Δ₂} {_A} {_B} {_M} {_N} {_N'} hΓ hΔ hs hA hB cM cN cN' h =>
      fragment_step_congruence_pair_right hΓ hΔ hs hA hB cM cN cN' h,
    fun {_Γ} {_Δ} {_Δ₁} {_Δ₂} {_A} {_B} {_C} {_M} {_M'} {_K} hΓ hΔ hs hA hB hC cM cM' cK h =>
      fragment_step_congruence_unpair_scrutinee hΓ hΔ hs hA hB hC cM cM' cK h,
    fun {_Γ} {_Δ} {_Δ₁} {_Δ₂} {_A} {_B} {_C} {_M} {_K} {_K'} hΓ hΔ hs hA hB hC cM cK cK' h =>
      fragment_step_congruence_unpair_cont hΓ hΔ hs hA hB hC cM cK cK' h,
    fun {_Γ} {_Δ} {_Δ₁} {_Δ₂} {_A} {_Q} {_Q'} {_K} hΓ hΔ hs hA cQ cQ' cK h =>
      fragment_step_congruence_measure_qubit hΓ hΔ hs hA cQ cQ' cK h,
    fun {_Γ} {_Δ} {_Δ₁} {_Δ₂} {_A} {_Q} {_K} {_K'} hΓ hΔ hs hA cQ cK cK' h =>
      fragment_step_congruence_measure_cont hΓ hΔ hs hA cQ cK cK' h⟩

/-- Complete fragment-admitted Step soundness package: closed linear/unres
identity β, constant unrestricted subst β, closed `unpair` β, and the full
congruence suite. Excludes `fix`/`fold`/`unfold` (outside the fragment). -/
theorem fragment_step_denote_sound_complete :
    (FragCert.denote fragCert_appL_id_unit =
      FragCert.denote FragCert.closed_unit_cert) ∧
    (∀ b, FragCert.denote (fragCert_appL_id_bit b) =
      FragCert.denote (FragCert.closed_bitLit_cert b)) ∧
    (∀ b, FragCert.denote (fragCert_appU_id_bit b) =
      FragCert.denote (FragCert.closed_bitLit_cert b)) ∧
    (∀ c b, FragCert.denote (fragCert_appU_const_bit c b) =
      FragCert.denote (FragCert.closed_bitLit_cert c)) ∧
    (∀ b, FragCert.denote (fragCert_appU_const_unit b) =
      FragCert.denote FragCert.closed_unit_cert) ∧
    (∀ {K : Term}
        (cK : FragCert.Closed K
          (.arrow .lin .unit (.arrow .lin .unit .unit))),
      FragCert.denote
          (.unpair CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
            Ty.FirstOrder.unit Ty.FirstOrder.unit Ty.SemanticFragment.unit
            (.pair CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
              Ty.FirstOrder.unit Ty.FirstOrder.unit
              FragCert.closed_unit_cert FragCert.closed_unit_cert)
            cK) =
        FragCert.denote
          (.appL CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
            Ty.FirstOrder.unit Ty.SemanticFragment.unit
            (.appL CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
              Ty.FirstOrder.unit
              (Ty.SemanticFragment.arrowLin Ty.FirstOrder.unit
                Ty.SemanticFragment.unit)
              cK FragCert.closed_unit_cert)
            FragCert.closed_unit_cert)) ∧
    Nonempty
      (∀ {Γ Δ Δ₁ Δ₂ A B F F' X}
          (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
          (hs : OSplit Δ Δ₁ Δ₂) (hFO : Ty.FirstOrder A)
          (hB : Ty.SemanticFragment B)
          (cF : FragCert Γ Δ₁ F (.arrow .lin A B))
          (cF' : FragCert Γ Δ₁ F' (.arrow .lin A B))
          (cX : FragCert Γ Δ₂ X A),
        FragCert.denote cF = FragCert.denote cF' →
          FragCert.denote (.appL hΓ hΔ hs hFO hB cF cX) =
            FragCert.denote (.appL hΓ hΔ hs hFO hB cF' cX)) :=
  ⟨fragment_betaL_id_unit, fragment_betaL_id_bit, fragment_betaU_id_bit,
    fragment_substUnres_const_denote_bit, fragment_substUnres_const_denote_unit,
    fun {_K} cK => fragment_unpair_beta_unit cK,
    ⟨fun {_Γ} {_Δ} {_Δ₁} {_Δ₂} {_A} {_B} {_F} {_F'} {_X}
        hΓ hΔ hs hFO hB cF cF' cX h =>
      fragment_step_congruence_appL_fun hΓ hΔ hs hFO hB cF cF' cX h⟩⟩

/-- Upgraded soundness package: closed linear and unrestricted identity β plus
the full congruence suite `fragment_step_congruence_sound`. -/
theorem fragment_step_denote_sound_upgraded :
    (FragCert.denote fragCert_appL_id_unit =
      FragCert.denote FragCert.closed_unit_cert) ∧
    (∀ b, FragCert.denote (fragCert_appL_id_bit b) =
      FragCert.denote (FragCert.closed_bitLit_cert b)) ∧
    (∀ b, FragCert.denote (fragCert_appU_id_bit b) =
      FragCert.denote (FragCert.closed_bitLit_cert b)) ∧
    Nonempty
      ((∀ {Γ Δ Δ₁ Δ₂ A B F F' X}
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
              FragCert.denote (.appL hΓ hΔ hs hFO hB cF cX'))) :=
  ⟨fragment_betaL_id_unit, fragment_betaL_id_bit, fragment_betaU_id_bit,
    ⟨fragment_step_congruence_sound.1, fragment_step_congruence_sound.2.1⟩⟩

end QLambda.Linear
