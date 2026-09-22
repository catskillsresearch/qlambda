/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.Examples
import QLambda.Linear.Metatheory

/-!
# Operational semantics

Classical call-by-value reduction is deterministic. Measurement is a separate
labelled transition: the classical bit is not chosen by a probabilistic term
constructor. Quantum primitive applications are staged as circuit operations,
not reduced by this source relation.
-/

namespace QLambda.Linear

open Term

inductive Step : Term → Term → Prop where
  | betaL {A M V} : Value V → Step (.app (.lam .lin A M) V) (substLin 0 V M)
  | betaU {A M V} : Value V → Step (.app (.lam .unres A M) V) (substUnres 0 V M)
  | appF {F F' X} : Step F F' → Step (.app F X) (.app F' X)
  | appX {V X X'} : Value V → Step X X' → Step (.app V X) (.app V X')
  | iteTrue {T E} : Step (.ite (.bitLit true) T E) T
  | iteFalse {T E} : Step (.ite (.bitLit false) T E) E
  | iteC {B B' T E} : Step B B' → Step (.ite B T E) (.ite B' T E)
  | unpairBeta {M N K} :
      Value M → Value N →
      Step (.unpair (.pair M N) K) (.app (.app K M) N)
  | unpairC {M M' K} : Step M M' → Step (.unpair M K) (.unpair M' K)
  | pairL {M M' N} : Step M M' → Step (.pair M N) (.pair M' N)
  | pairR {V N N'} : Value V → Step N N' → Step (.pair V N) (.pair V N')
  | unfoldBeta {A V} : Value V → Step (.unfold (.fold A V)) V
  | unfoldC {M M'} : Step M M' → Step (.unfold M) (.unfold M')
  | fixBeta {A V} : Value V → Step (.fix A V) (.app V (.fix A V))
  | fixC {A M M'} : Step M M' → Step (.fix A M) (.fix A M')
  | foldC {A M M'} : Step M M' → Step (.fold A M) (.fold A M')
  | measureC {Q Q' K} : Step Q Q' → Step (.measure Q K) (.measure Q' K)

/-- Measurement branches. `Q` is returned with the bit, so the qubit is not discarded. -/
inductive MeasStep : Term → Bool → Term → Prop where
  | branch {Q K b} :
      Value Q →
      MeasStep (.measure Q K) b (.app (.app K (.bitLit b)) Q)

/-- A source evaluation context has reached a quantum primitive.  The staging
or machine layer, rather than classical β-reduction, handles this case. -/
inductive QuantumBlocked : Term → Prop where
  | primApp {p V} : Value V → QuantumBlocked (.app (.prim p) V)
  | measure {Q K} : Value Q → QuantumBlocked (.measure Q K)
  | appF {F X} : QuantumBlocked F → QuantumBlocked (.app F X)
  | appX {V X} : Value V → QuantumBlocked X → QuantumBlocked (.app V X)
  | iteC {B T E} : QuantumBlocked B → QuantumBlocked (.ite B T E)
  | unpairC {M K} : QuantumBlocked M → QuantumBlocked (.unpair M K)
  | pairL {M N} : QuantumBlocked M → QuantumBlocked (.pair M N)
  | pairR {V N} : Value V → QuantumBlocked N → QuantumBlocked (.pair V N)
  | unfoldC {M} : QuantumBlocked M → QuantumBlocked (.unfold M)
  | fixC {A M} : QuantumBlocked M → QuantumBlocked (.fix A M)
  | foldC {A M} : QuantumBlocked M → QuantumBlocked (.fold A M)
  | measureC {Q K} : QuantumBlocked Q → QuantumBlocked (.measure Q K)

def MakesProgress (M : Term) : Prop :=
  Value M ∨ (∃ N, Step M N) ∨ QuantumBlocked M

private theorem oSplit_nil {Δ₁ Δ₂}
    (h : OSplit [] Δ₁ Δ₂) : Δ₁ = [] ∧ Δ₂ = [] := by
  cases h
  exact ⟨rfl, rfl⟩

private theorem value_arrow_shape {Γ Δ V κ A B}
    (hV : Value V) (hT : HasType Γ Δ V (.arrow κ A B)) :
    (∃ C M, V = .lam κ C M) ∨ ∃ p, V = .prim p := by
  cases hV with
  | unit => cases hT
  | bitLit => cases hT
  | lam =>
      cases hT <;> exact Or.inl ⟨_, _, rfl⟩
  | pair _ _ => cases hT
  | prim => exact Or.inr ⟨_, rfl⟩
  | fold _ => cases hT

private theorem value_bit_shape {Γ Δ V}
    (hV : Value V) (hT : HasType Γ Δ V .bit) :
    ∃ b, V = .bitLit b := by
  cases hV with
  | unit => cases hT
  | bitLit => exact ⟨_, rfl⟩
  | lam => cases hT
  | pair _ _ => cases hT
  | prim =>
      cases ‹Prim› <;> cases hT
  | fold _ => cases hT

private theorem value_tensor_shape {Γ Δ V A B}
    (hV : Value V) (hT : HasType Γ Δ V (.tensor A B)) :
    ∃ M N, V = .pair M N ∧ Value M ∧ Value N := by
  cases hV with
  | unit => cases hT
  | bitLit => cases hT
  | lam => cases hT
  | pair hM hN => exact ⟨_, _, rfl, hM, hN⟩
  | prim =>
      cases ‹Prim› <;> cases hT
  | fold _ => cases hT

private theorem value_mu_shape {Γ Δ V A}
    (hV : Value V) (hT : HasType Γ Δ V (.mu A)) :
    ∃ M, V = .fold A M ∧ Value M := by
  cases hV with
  | unit => cases hT
  | bitLit => cases hT
  | lam => cases hT
  | pair _ _ => cases hT
  | prim =>
      cases ‹Prim› <;> cases hT
  | fold hM =>
      cases hT
      exact ⟨_, rfl, hM⟩

theorem value_nostep {V N : Term} (hV : Value V) (hS : Step V N) : False := by
  induction hS with
  | betaL _ => cases hV
  | betaU _ => cases hV
  | appF _ _ => cases hV
  | appX _ _ _ => cases hV
  | iteTrue => cases hV
  | iteFalse => cases hV
  | iteC _ _ => cases hV
  | unpairBeta _ _ => cases hV
  | unpairC _ _ => cases hV
  | pairL _ ih =>
      cases hV with
      | pair hM _ => exact ih hM
  | pairR _ _ ih =>
      cases hV with
      | pair _ hN => exact ih hN
  | unfoldBeta _ => cases hV
  | unfoldC _ _ => cases hV
  | fixBeta _ => cases hV
  | fixC _ _ => cases hV
  | foldC _ ih =>
      cases hV with
      | fold hM => exact ih hM
  | measureC _ _ => cases hV

theorem step_deterministic {M N₁ N₂ : Term} (h₁ : Step M N₁) (h₂ : Step M N₂) : N₁ = N₂ := by
  induction h₁ generalizing N₂ with
  | betaL hV =>
      cases h₂ with
      | betaL _ => rfl
      | appF hF => exact (value_nostep Value.lam hF).elim
      | appX _ hX => exact (value_nostep hV hX).elim
  | betaU hV =>
      cases h₂ with
      | betaU _ => rfl
      | appF hF => exact (value_nostep Value.lam hF).elim
      | appX _ hX => exact (value_nostep hV hX).elim
  | appF hF ih =>
      cases h₂ with
      | betaL _ => exact (value_nostep Value.lam hF).elim
      | betaU _ => exact (value_nostep Value.lam hF).elim
      | appF hF' =>
          have := ih hF'
          simp [this]
      | appX hVF _ => exact (value_nostep hVF hF).elim
  | appX hV hX ih =>
      cases h₂ with
      | betaL hArg => exact (value_nostep hArg hX).elim
      | betaU hArg => exact (value_nostep hArg hX).elim
      | appF hF => exact (value_nostep hV hF).elim
      | appX _ hX' =>
          have := ih hX'
          simp [this]
  | iteTrue =>
      cases h₂ with
      | iteTrue => rfl
      | iteC hB => cases hB
  | iteFalse =>
      cases h₂ with
      | iteFalse => rfl
      | iteC hB => cases hB
  | iteC hB ih =>
      cases h₂ with
      | iteTrue => cases hB
      | iteFalse => cases hB
      | iteC hB' =>
          have := ih hB'
          simp [this]
  | unpairBeta hM hN =>
      cases h₂ with
      | unpairBeta _ _ => rfl
      | unpairC hP =>
          cases hP with
          | pairL hL => exact (value_nostep hM hL).elim
          | pairR _ hR => exact (value_nostep hN hR).elim
  | unpairC hM ih =>
      cases h₂ with
      | unpairBeta hV₁ hV₂ =>
          cases hM with
          | pairL hL => exact (value_nostep hV₁ hL).elim
          | pairR _ hR => exact (value_nostep hV₂ hR).elim
      | unpairC hM' =>
          have := ih hM'
          simp [this]
  | pairL hM ih =>
      cases h₂ with
      | pairL hM' =>
          have := ih hM'
          simp [this]
      | pairR hV _ => exact (value_nostep hV hM).elim
  | pairR hV hN ih =>
      cases h₂ with
      | pairL hM => exact (value_nostep hV hM).elim
      | pairR _ hN' =>
          have := ih hN'
          simp [this]
  | unfoldBeta hV =>
      cases h₂ with
      | unfoldBeta _ => rfl
      | unfoldC hM =>
          cases hM with
          | foldC hF => exact (value_nostep hV hF).elim
  | unfoldC hM ih =>
      cases h₂ with
      | unfoldBeta hV =>
          cases hM with
          | foldC hF => exact (value_nostep hV hF).elim
      | unfoldC hM' =>
          have := ih hM'
          simp [this]
  | fixBeta hV =>
      cases h₂ with
      | fixBeta _ => rfl
      | fixC hM => exact (value_nostep hV hM).elim
  | fixC hM ih =>
      cases h₂ with
      | fixBeta hV => exact (value_nostep hV hM).elim
      | fixC hM' =>
          have := ih hM'
          simp [this]
  | foldC hM ih =>
      cases h₂ with
      | foldC hM' =>
          have := ih hM'
          simp [this]
  | measureC hQ ih =>
      cases h₂ with
      | measureC hQ' =>
          have := ih hQ'
          simp [this]

/-- Closed well-typed terms are values, take a deterministic classical step,
or have reached the explicitly separated quantum staging boundary. -/
theorem progress {M : Term} {A : Ty} (h : HasType [] [] M A) :
    MakesProgress M := by
  have go : ∀ {Γ Δ M A}, HasType Γ Δ M A → Γ = [] → Δ = [] →
      MakesProgress M := by
    intro Γ Δ M A hT hΓ hΔ
    induction hT with
    | varU hlookup _ _ =>
        rw [hΓ] at hlookup
        cases hlookup
    | varL hlookup _ =>
        rw [hΔ] at hlookup
        cases hlookup
    | lamU _ _ _ => exact Or.inl Value.lam
    | lamL _ => exact Or.inl Value.lam
    | appL hsplit hF hX ihF ihX =>
        rw [hΔ] at hsplit
        obtain ⟨rfl, rfl⟩ := oSplit_nil hsplit
        rcases ihF hΓ rfl with hVF | ⟨⟨NF, hSF⟩ | hQF⟩
        · rcases ihX hΓ rfl with hVX | ⟨⟨NX, hSX⟩ | hQX⟩
          · rcases value_arrow_shape hVF hF with hLam | hPrim
            · obtain ⟨C, Body, rfl⟩ := hLam
              exact Or.inr (Or.inl ⟨_, Step.betaL hVX⟩)
            · obtain ⟨p, rfl⟩ := hPrim
              exact Or.inr (Or.inr (QuantumBlocked.primApp hVX))
          · exact Or.inr (Or.inl ⟨_, Step.appX hVF hSX⟩)
          · exact Or.inr (Or.inr (QuantumBlocked.appX hVF hQX))
        · exact Or.inr (Or.inl ⟨_, Step.appF hSF⟩)
        · exact Or.inr (Or.inr (QuantumBlocked.appF hQF))
    | appU _ hF hX ihF ihX =>
        rcases ihF hΓ hΔ with hVF | ⟨⟨NF, hSF⟩ | hQF⟩
        · rcases ihX hΓ hΔ with hVX | ⟨⟨NX, hSX⟩ | hQX⟩
          · rcases value_arrow_shape hVF hF with hLam | hPrim
            · obtain ⟨C, Body, rfl⟩ := hLam
              exact Or.inr (Or.inl ⟨_, Step.betaU hVX⟩)
            · obtain ⟨p, rfl⟩ := hPrim
              exact Or.inr (Or.inr (QuantumBlocked.primApp hVX))
          · exact Or.inr (Or.inl ⟨_, Step.appX hVF hSX⟩)
          · exact Or.inr (Or.inr (QuantumBlocked.appX hVF hQX))
        · exact Or.inr (Or.inl ⟨_, Step.appF hSF⟩)
        · exact Or.inr (Or.inr (QuantumBlocked.appF hQF))
    | unit _ => exact Or.inl Value.unit
    | bitLit _ => exact Or.inl Value.bitLit
    | pair hsplit hM hN ihM ihN =>
        rw [hΔ] at hsplit
        obtain ⟨rfl, rfl⟩ := oSplit_nil hsplit
        rcases ihM hΓ rfl with hVM | ⟨⟨NM, hSM⟩ | hQM⟩
        · rcases ihN hΓ rfl with hVN | ⟨⟨NN, hSN⟩ | hQN⟩
          · exact Or.inl (Value.pair hVM hVN)
          · exact Or.inr (Or.inl ⟨_, Step.pairR hVM hSN⟩)
          · exact Or.inr (Or.inr (QuantumBlocked.pairR hVM hQN))
        · exact Or.inr (Or.inl ⟨_, Step.pairL hSM⟩)
        · exact Or.inr (Or.inr (QuantumBlocked.pairL hQM))
    | unpair hsplit hM _ ihM _ =>
        rw [hΔ] at hsplit
        obtain ⟨rfl, rfl⟩ := oSplit_nil hsplit
        rcases ihM hΓ rfl with hVM | ⟨⟨NM, hSM⟩ | hQM⟩
        · obtain ⟨V, W, rfl, hV, hW⟩ := value_tensor_shape hVM hM
          exact Or.inr (Or.inl ⟨_, Step.unpairBeta hV hW⟩)
        · exact Or.inr (Or.inl ⟨_, Step.unpairC hSM⟩)
        · exact Or.inr (Or.inr (QuantumBlocked.unpairC hQM))
    | ite hsplit hB _ _ ihB _ _ =>
        rw [hΔ] at hsplit
        obtain ⟨rfl, rfl⟩ := oSplit_nil hsplit
        rcases ihB hΓ rfl with hVB | ⟨⟨NB, hSB⟩ | hQB⟩
        · obtain ⟨b, rfl⟩ := value_bit_shape hVB hB
          cases b
          · exact Or.inr (Or.inl ⟨_, Step.iteFalse⟩)
          · exact Or.inr (Or.inl ⟨_, Step.iteTrue⟩)
        · exact Or.inr (Or.inl ⟨_, Step.iteC hSB⟩)
        · exact Or.inr (Or.inr (QuantumBlocked.iteC hQB))
    | prim _ => exact Or.inl Value.prim
    | measure hsplit hQ _ ihQ _ =>
        rw [hΔ] at hsplit
        obtain ⟨rfl, rfl⟩ := oSplit_nil hsplit
        rcases ihQ hΓ rfl with hVQ | ⟨⟨NQ, hSQ⟩ | hBQ⟩
        · exact Or.inr (Or.inr (QuantumBlocked.measure hVQ))
        · exact Or.inr (Or.inl ⟨_, Step.measureC hSQ⟩)
        · exact Or.inr (Or.inr (QuantumBlocked.measureC hBQ))
    | fix _ _ _ ih =>
        rcases ih hΓ hΔ with hV | ⟨⟨N, hS⟩ | hQ⟩
        · exact Or.inr (Or.inl ⟨_, Step.fixBeta hV⟩)
        · exact Or.inr (Or.inl ⟨_, Step.fixC hS⟩)
        · exact Or.inr (Or.inr (QuantumBlocked.fixC hQ))
    | fold _ ih =>
        rcases ih hΓ hΔ with hV | ⟨⟨N, hS⟩ | hQ⟩
        · exact Or.inl (Value.fold hV)
        · exact Or.inr (Or.inl ⟨_, Step.foldC hS⟩)
        · exact Or.inr (Or.inr (QuantumBlocked.foldC hQ))
    | unfold hM ih =>
        rcases ih hΓ hΔ with hV | ⟨⟨N, hS⟩ | hQ⟩
        · obtain ⟨V, rfl, hV'⟩ := value_mu_shape hV hM
          exact Or.inr (Or.inl ⟨_, Step.unfoldBeta hV'⟩)
        · exact Or.inr (Or.inl ⟨_, Step.unfoldC hS⟩)
        · exact Or.inr (Or.inr (QuantumBlocked.unfoldC hQ))
  exact go h rfl rfl

/-- A well-typed identity at gate type reduces on the `H` constant. -/
theorem idGate_apply_h : Step (.app idGate (.prim .h)) (.prim .h) := by
  have hsub : substLin 0 (.prim .h) (.var .lin 0) = .prim .h :=
    substLin_zero_noLin rfl
  simpa [idGate, hsub] using
    (Step.betaL Value.prim :
      Step
        (.app
          (.lam .lin (.arrow .lin .qubit .qubit) (.var .lin 0))
          (.prim .h))
    (substLin 0 (.prim .h) (.var .lin 0)))

theorem idGate_apply_h_typed :
    HasType [] [] (.app idGate (.prim .h)) (.arrow .lin .qubit .qubit) := by
  have h :
      infer [] [] (.app idGate (.prim .h)) =
        some (.arrow .lin .qubit .qubit, []) := by
    rfl
  exact (infer_sound h).1

end QLambda.Linear
