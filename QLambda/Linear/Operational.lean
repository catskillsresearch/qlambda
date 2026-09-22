/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.Examples
import QLambda.Linear.Substitution

/-!
# Operational semantics

Classical call-by-value reduction is deterministic. Measurement is a separate
labelled transition: the classical bit is not chosen by a probabilistic term
constructor. General type preservation for substitution is not claimed here.
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
  | foldC {A M M'} : Step M M' → Step (.fold A M) (.fold A M')
  | measureC {Q Q' K} : Step Q Q' → Step (.measure Q K) (.measure Q' K)

/-- Measurement branches. `Q` is returned with the bit, so the qubit is not discarded. -/
inductive MeasStep : Term → Bool → Term → Prop where
  | branch {Q K b} :
      Value Q →
      MeasStep (.measure Q K) b (.app (.app K (.bitLit b)) Q)

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
  | fixBeta _ =>
      cases h₂ with
      | fixBeta _ => rfl
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

/-- Applying the qubit identity to a gate constant reduces to that constant. -/
theorem idQ_apply_h : Step (.app idQ (.prim .h)) (.prim .h) := by
  have hsub : substLin 0 (.prim .h) (.var .lin 0) = .prim .h :=
    substLin_zero_noLin rfl
  simpa [idQ, hsub] using (Step.betaL Value.prim : Step (.app (.lam .lin .qubit (.var .lin 0)) (.prim .h))
    (substLin 0 (.prim .h) (.var .lin 0)))

end QLambda.Linear
