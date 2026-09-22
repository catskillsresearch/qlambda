/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.Context

/-!
# Typing

`HasType Γ Δ M A` means `M` has type `A`, uses exactly the occupied cells of
the linear context `Δ`, and may use the unrestricted context `Γ` any number
of times. `infer` is a syntax-directed checker for that judgment.
-/

namespace QLambda.Linear

inductive HasType : List Ty → List (Option Ty) → Term → Ty → Prop where
  | varU {Γ Δ n A} :
      Lookup Γ n A → AllNone Δ → HasType Γ Δ (.var .unres n) A
  | varL {Γ Δ n A} :
      Lookup Δ n (some A) → OnlySomeAt Δ n → HasType Γ Δ (.var .lin n) A
  | lamU {Γ Δ A B M} :
      HasType (A :: Γ) Δ M B →
      HasType Γ Δ (.lam .unres A M) (.arrow .unres A B)
  | lamL {Γ Δ A B M} :
      HasType Γ (some A :: Δ) M B →
      HasType Γ Δ (.lam .lin A M) (.arrow .lin A B)
  | app {Γ Δ Δ₁ Δ₂ κ A B F X} :
      OSplit Δ Δ₁ Δ₂ →
      HasType Γ Δ₁ F (.arrow κ A B) →
      HasType Γ Δ₂ X A →
      HasType Γ Δ (.app F X) B
  | unit {Γ Δ} : AllNone Δ → HasType Γ Δ .unit .unit
  | bitLit {Γ Δ b} : AllNone Δ → HasType Γ Δ (.bitLit b) .bit
  | pair {Γ Δ Δ₁ Δ₂ A B M N} :
      OSplit Δ Δ₁ Δ₂ →
      HasType Γ Δ₁ M A →
      HasType Γ Δ₂ N B →
      HasType Γ Δ (.pair M N) (.tensor A B)
  | unpair {Γ Δ Δ₁ Δ₂ A B C M K} :
      OSplit Δ Δ₁ Δ₂ →
      HasType Γ Δ₁ M (.tensor A B) →
      HasType Γ Δ₂ K (.arrow .lin A (.arrow .lin B C)) →
      HasType Γ Δ (.unpair M K) C
  | ite {Γ Δ Δ₁ Δ₂ A B T E} :
      OSplit Δ Δ₁ Δ₂ →
      HasType Γ Δ₁ B .bit →
      HasType Γ Δ₂ T A →
      HasType Γ Δ₂ E A →
      HasType Γ Δ (.ite B T E) A
  | prim {Γ Δ p} : AllNone Δ → HasType Γ Δ (.prim p) (primTy p)
  | measure {Γ Δ Δ₁ Δ₂ A Q K} :
      OSplit Δ Δ₁ Δ₂ →
      HasType Γ Δ₁ Q .qubit →
      HasType Γ Δ₂ K (.arrow .unres .bit (.arrow .lin .qubit A)) →
      HasType Γ Δ (.measure Q K) A
  | fix {Γ Δ A M} :
      AllNone Δ →
      HasType Γ Δ M (.arrow .unres A A) →
      HasType Γ Δ (.fix A M) A
  | fold {Γ Δ A M} :
      HasType Γ Δ M (Ty.subst 0 (.mu A) A) →
      HasType Γ Δ (.fold A M) (.mu A)
  | unfold {Γ Δ A M} :
      HasType Γ Δ M (.mu A) →
      HasType Γ Δ (.unfold M) (Ty.subst 0 (.mu A) A)

/-- Syntax-directed linear type checker. The Boolean vector marks which variables
of the supplied linear scope are used. -/
def infer (Γ Δ : List Ty) : Term → Option (Ty × List Bool)
  | .var .unres n =>
      match Γ[n]? with
      | some A => some (A, List.replicate Δ.length false)
      | none => none
  | .var .lin n =>
      match Δ[n]? with
      | some A => some (A, mark n Δ)
      | none => none
  | .lam .unres A M =>
      match infer (A :: Γ) Δ M with
      | some (B, u) => some (.arrow .unres A B, u)
      | none => none
  | .lam .lin A M =>
      match infer Γ (A :: Δ) M with
      | some (B, true :: u) => some (.arrow .lin A B, u)
      | _ => none
  | .app F X =>
      match infer Γ Δ F, infer Γ Δ X with
      | some (.arrow _ A B, uF), some (A', uX) =>
          if A = A' then
            match zipOr uF uX with
            | some u => some (B, u)
            | none => none
          else none
      | _, _ => none
  | .unit => some (.unit, List.replicate Δ.length false)
  | .bitLit _ => some (.bit, List.replicate Δ.length false)
  | .pair M N =>
      match infer Γ Δ M, infer Γ Δ N with
      | some (A, uM), some (B, uN) =>
          match zipOr uM uN with
          | some u => some (.tensor A B, u)
          | none => none
      | _, _ => none
  | .unpair M K =>
      match infer Γ Δ M, infer Γ Δ K with
      | some (.tensor A B, uM), some (.arrow .lin A' (.arrow .lin B' C), uK) =>
          if A = A' ∧ B = B' then
            match zipOr uM uK with
            | some u => some (C, u)
            | none => none
          else none
      | _, _ => none
  | .ite B T E =>
      match infer Γ Δ B, infer Γ Δ T, infer Γ Δ E with
      | some (.bit, uB), some (A, uT), some (A', uE) =>
          if A = A' ∧ uT = uE then
            match zipOr uB uT with
            | some u => some (A, u)
            | none => none
          else none
      | _, _, _ => none
  | .prim p => some (primTy p, List.replicate Δ.length false)
  | .measure Q K =>
      match infer Γ Δ Q, infer Γ Δ K with
      | some (.qubit, uQ), some (.arrow .unres .bit (.arrow .lin .qubit A), uK) =>
          match zipOr uQ uK with
          | some u => some (A, u)
          | none => none
      | _, _ => none
  | .fix A M =>
      match infer Γ Δ M with
      | some (.arrow .unres A₁ A₂, u) =>
          if A₁ = A ∧ A₂ = A ∧ allFalse u = true then some (A, u) else none
      | _ => none
  | .fold A M =>
      match infer Γ Δ M with
      | some (B, u) =>
          if B = Ty.subst 0 (.mu A) A then some (.mu A, u) else none
      | none => none
  | .unfold M =>
      match infer Γ Δ M with
      | some (.mu A, u) => some (Ty.subst 0 (.mu A) A, u)
      | _ => none

theorem infer_sound {Γ Δ : List Ty} {M : Term} {A : Ty} {u : List Bool}
    (h : infer Γ Δ M = some (A, u)) :
    HasType Γ (usageCtx Δ u) M A ∧ u.length = Δ.length := by
  induction M generalizing Γ Δ A u with
  | var κ n =>
      cases κ with
      | unres =>
          simp only [infer] at h
          cases hΓ : Γ[n]? with
          | none => simp [hΓ] at h
          | some A' =>
              simp [hΓ] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨HasType.varU (lookup_of_get? hΓ) (allNone_unused Δ),
                by simp [List.length_replicate]⟩
      | lin =>
          simp only [infer] at h
          cases hΔ : Δ[n]? with
          | none => simp [hΔ] at h
          | some A' =>
              simp [hΔ] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨hlook, honly⟩ := varLin_usage hΔ
              exact ⟨HasType.varL hlook honly, mark_length n Δ⟩
  | lam κ B M ih =>
      cases κ with
      | unres =>
          simp only [infer] at h
          cases hM : infer (B :: Γ) Δ M with
          | none => simp [hM] at h
          | some p =>
              obtain ⟨C, uC⟩ := p
              simp [hM] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨hC, hlen⟩ := ih hM
              exact ⟨HasType.lamU hC, hlen⟩
      | lin =>
          simp only [infer] at h
          cases hM : infer Γ (B :: Δ) M with
          | none => simp [hM] at h
          | some p =>
              obtain ⟨C, uC⟩ := p
              cases uC with
              | nil => simp [hM] at h
              | cons head tail =>
                  cases head with
                  | false => simp [hM] at h
                  | true =>
                      simp [hM] at h
                      obtain ⟨rfl, rfl⟩ := h
                      obtain ⟨hC, hlen⟩ := ih hM
                      have hlen' : tail.length = Δ.length := by
                        simpa [List.length_cons] using hlen
                      exact ⟨HasType.lamL hC, hlen'⟩
  | app F X ihF ihX =>
      simp only [infer] at h
      cases hF : infer Γ Δ F with
      | none => simp [hF] at h
      | some pF =>
          obtain ⟨TF, uF⟩ := pF
          cases hX : infer Γ Δ X with
          | none => simp [hF, hX] at h
          | some pX =>
              obtain ⟨TX, uX⟩ := pX
              simp [hF, hX] at h
              cases TF with
              | var _ => simp at h
              | unit => simp at h
              | bit => simp at h
              | qubit => simp at h
              | tensor _ _ => simp at h
              | mu _ => simp at h
              | arrow κ A₀ B₀ =>
                  dsimp at h
                  by_cases hA : A₀ = TX
                  · subst hA
                    rw [if_pos rfl] at h
                    cases hzip : zipOr uF uX with
                    | none => simp [hzip] at h
                    | some u' =>
                        simp [hzip] at h
                        obtain ⟨rfl, rfl⟩ := h
                        obtain ⟨hFty, hFlen⟩ := ihF hF
                        obtain ⟨hXty, hXlen⟩ := ihX hX
                        have hsplit := oSplit_of_zipOr hzip hFlen hXlen
                        obtain ⟨hlen, _⟩ := zipOr_length hzip
                        exact ⟨HasType.app hsplit hFty hXty, hlen.trans hFlen⟩
                  · rw [if_neg hA] at h
                    simp at h
  | unit =>
      simp only [infer] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨HasType.unit (allNone_unused Δ), by simp [List.length_replicate]⟩
  | bitLit b =>
      simp only [infer] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨HasType.bitLit (allNone_unused Δ), by simp [List.length_replicate]⟩
  | pair M N ihM ihN =>
      simp only [infer] at h
      cases hM : infer Γ Δ M with
      | none => simp [hM] at h
      | some pM =>
          obtain ⟨A₀, uM⟩ := pM
          cases hN : infer Γ Δ N with
          | none => simp [hM, hN] at h
          | some pN =>
              obtain ⟨B₀, uN⟩ := pN
              simp [hM, hN] at h
              cases hzip : zipOr uM uN with
              | none => simp [hzip] at h
              | some u' =>
                  simp [hzip] at h
                  obtain ⟨rfl, rfl⟩ := h
                  obtain ⟨hMty, hMlen⟩ := ihM hM
                  obtain ⟨hNty, hNlen⟩ := ihN hN
                  have hsplit := oSplit_of_zipOr hzip hMlen hNlen
                  obtain ⟨hlen, _⟩ := zipOr_length hzip
                  exact ⟨HasType.pair hsplit hMty hNty, hlen.trans hMlen⟩
  | unpair M K ihM ihK =>
      simp only [infer] at h
      cases hM : infer Γ Δ M with
      | none => simp [hM] at h
      | some pM =>
          obtain ⟨TM, uM⟩ := pM
          cases hK : infer Γ Δ K with
          | none => simp [hM, hK] at h
          | some pK =>
              obtain ⟨TK, uK⟩ := pK
              simp [hM, hK] at h
              cases TM with
              | var _ => simp at h
              | unit => simp at h
              | bit => simp at h
              | qubit => simp at h
              | arrow _ _ _ => simp at h
              | mu _ => simp at h
              | tensor A₀ B₀ =>
                  cases TK with
                  | var _ => simp at h
                  | unit => simp at h
                  | bit => simp at h
                  | qubit => simp at h
                  | tensor _ _ => simp at h
                  | mu _ => simp at h
                  | arrow κ A₁ R =>
                      cases κ with
                      | unres => simp at h
                      | lin =>
                          cases R with
                          | var _ => simp at h
                          | unit => simp at h
                          | bit => simp at h
                          | qubit => simp at h
                          | tensor _ _ => simp at h
                          | mu _ => simp at h
                          | arrow κ₂ B₁ C =>
                              cases κ₂ with
                              | unres => simp at h
                              | lin =>
                                  dsimp at h
                                  by_cases hAB : A₀ = A₁ ∧ B₀ = B₁
                                  · rcases hAB with ⟨rfl, rfl⟩
                                    rw [if_pos (And.intro rfl rfl)] at h
                                    cases hzip : zipOr uM uK with
                                    | none => simp [hzip] at h
                                    | some u' =>
                                        simp [hzip] at h
                                        obtain ⟨rfl, rfl⟩ := h
                                        obtain ⟨hMty, hMlen⟩ := ihM hM
                                        obtain ⟨hKty, hKlen⟩ := ihK hK
                                        have hsplit := oSplit_of_zipOr hzip hMlen hKlen
                                        obtain ⟨hlen, _⟩ := zipOr_length hzip
                                        exact ⟨HasType.unpair hsplit hMty hKty,
                                          hlen.trans hMlen⟩
                                  ·
                                    rw [if_neg hAB] at h
                                    simp at h
  | ite B T E ihB ihT ihE =>
      simp only [infer] at h
      cases hB : infer Γ Δ B with
      | none => simp [hB] at h
      | some pB =>
          obtain ⟨TB, uB⟩ := pB
          cases hT : infer Γ Δ T with
          | none => simp [hB, hT] at h
          | some pT =>
              obtain ⟨TT, uT⟩ := pT
              cases hE : infer Γ Δ E with
              | none => simp [hB, hT, hE] at h
              | some pE =>
                  obtain ⟨TE, uE⟩ := pE
                  simp [hB, hT, hE] at h
                  cases TB with
                  | var _ => simp at h
                  | unit => simp at h
                  | qubit => simp at h
                  | tensor _ _ => simp at h
                  | arrow _ _ _ => simp at h
                  | mu _ => simp at h
                  | bit =>
                      dsimp at h
                      by_cases hbr : TT = TE ∧ uT = uE
                      · rcases hbr with ⟨rfl, rfl⟩
                        rw [if_pos (And.intro rfl rfl)] at h
                        cases hzip : zipOr uB uT with
                        | none => simp [hzip] at h
                        | some u' =>
                            simp [hzip] at h
                            obtain ⟨rfl, rfl⟩ := h
                            obtain ⟨hBty, hBlen⟩ := ihB hB
                            obtain ⟨hTty, hTlen⟩ := ihT hT
                            obtain ⟨hEty, _⟩ := ihE hE
                            have hsplit := oSplit_of_zipOr hzip hBlen hTlen
                            obtain ⟨hlen, _⟩ := zipOr_length hzip
                            exact ⟨HasType.ite hsplit hBty hTty hEty, hlen.trans hBlen⟩
                      ·
                        rw [if_neg hbr] at h
                        simp at h
  | prim p =>
      simp only [infer] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨HasType.prim (allNone_unused Δ), by simp [List.length_replicate]⟩
  | measure Q K ihQ ihK =>
      simp only [infer] at h
      cases hQ : infer Γ Δ Q with
      | none => simp [hQ] at h
      | some pQ =>
          obtain ⟨TQ, uQ⟩ := pQ
          cases hK : infer Γ Δ K with
          | none => simp [hQ, hK] at h
          | some pK =>
              obtain ⟨TK, uK⟩ := pK
              simp [hQ, hK] at h
              cases TQ with
              | var _ => simp at h
              | unit => simp at h
              | bit => simp at h
              | tensor _ _ => simp at h
              | arrow _ _ _ => simp at h
              | mu _ => simp at h
              | qubit =>
                  cases TK with
                  | var _ => simp at h
                  | unit => simp at h
                  | bit => simp at h
                  | qubit => simp at h
                  | tensor _ _ => simp at h
                  | mu _ => simp at h
                  | arrow κ TB R =>
                      cases κ with
                      | lin => simp at h
                      | unres =>
                          cases TB with
                          | var _ => simp at h
                          | unit => simp at h
                          | qubit => simp at h
                          | tensor _ _ => simp at h
                          | arrow _ _ _ => simp at h
                          | mu _ => simp at h
                          | bit =>
                              cases R with
                              | var _ => simp at h
                              | unit => simp at h
                              | bit => simp at h
                              | qubit => simp at h
                              | tensor _ _ => simp at h
                              | mu _ => simp at h
                              | arrow κ₂ TQ₂ A₀ =>
                                  cases κ₂ with
                                  | unres => simp at h
                                  | lin =>
                                      cases TQ₂ with
                                      | var _ => simp at h
                                      | unit => simp at h
                                      | bit => simp at h
                                      | tensor _ _ => simp at h
                                      | arrow _ _ _ => simp at h
                                      | mu _ => simp at h
                                      | qubit =>
                                          cases hzip : zipOr uQ uK with
                                          | none => simp [hzip] at h
                                          | some u' =>
                                              simp [hzip] at h
                                              obtain ⟨rfl, rfl⟩ := h
                                              obtain ⟨hQty, hQlen⟩ := ihQ hQ
                                              obtain ⟨hKty, hKlen⟩ := ihK hK
                                              have hsplit := oSplit_of_zipOr hzip hQlen hKlen
                                              obtain ⟨hlen, _⟩ := zipOr_length hzip
                                              exact ⟨HasType.measure hsplit hQty hKty,
                                                hlen.trans hQlen⟩
  | fix A₀ M ih =>
      simp only [infer] at h
      cases hM : infer Γ Δ M with
      | none => simp [hM] at h
      | some p =>
          obtain ⟨TM, uM⟩ := p
          simp [hM] at h
          cases TM with
          | var _ => simp at h
          | unit => simp at h
          | bit => simp at h
          | qubit => simp at h
          | tensor _ _ => simp at h
          | mu _ => simp at h
          | arrow κ A₁ A₂ =>
              cases κ with
              | lin => simp at h
              | unres =>
                  dsimp at h
                  by_cases hfix : A₁ = A₀ ∧ A₂ = A₀ ∧ allFalse uM = true
                  · rcases hfix with ⟨rfl, rfl, hu⟩
                    rw [if_pos (And.intro rfl (And.intro rfl hu))] at h
                    obtain ⟨rfl, rfl⟩ := h
                    obtain ⟨hMty, hlen⟩ := ih hM
                    exact ⟨HasType.fix (allNone_of_allFalse hlen hu) hMty, hlen⟩
                  ·
                    rw [if_neg hfix] at h
                    simp at h
  | fold A₀ M ih =>
      simp only [infer] at h
      cases hM : infer Γ Δ M with
      | none => simp [hM] at h
      | some p =>
          obtain ⟨B, uM⟩ := p
          simp [hM] at h
          rcases h with ⟨hB, rfl, rfl⟩
          subst hB
          obtain ⟨hMty, hlen⟩ := ih hM
          exact ⟨HasType.fold hMty, hlen⟩
  | unfold M ih =>
      simp only [infer] at h
      cases hM : infer Γ Δ M with
      | none => simp [hM] at h
      | some p =>
          obtain ⟨TM, uM⟩ := p
          simp [hM] at h
          cases TM with
          | var _ => simp at h
          | unit => simp at h
          | bit => simp at h
          | qubit => simp at h
          | tensor _ _ => simp at h
          | arrow _ _ _ => simp at h
          | mu A₀ =>
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨hMty, hlen⟩ := ih hM
              exact ⟨HasType.unfold hMty, hlen⟩

end QLambda.Linear
