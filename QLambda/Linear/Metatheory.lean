/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.Substitution
import QLambda.Linear.Typing

/-!
# Structural metatheory

Scoping is a first prerequisite for capture-avoiding substitution and type
preservation.
-/

namespace QLambda.Linear

open Term

theorem typed_scoped {Γ Δ M A} (h : HasType Γ Δ M A) :
    Scoped Δ.length Γ.length M := by
  induction h with
  | varU hlookup _ _ => exact hlookup.lt_length
  | varL hlookup _ => exact hlookup.lt_length
  | lamU _ _ _ _ ih => simpa [Scoped] using ih
  | lamL _ _ ih => simpa [Scoped] using ih
  | appL hsplit _ _ ihF ihX =>
      obtain ⟨hFlen, hXlen⟩ := hsplit.lengths
      exact ⟨hFlen.symm ▸ ihF, hXlen.symm ▸ ihX⟩
  | appU hsplit _ _ _ ihF ihX =>
      obtain ⟨hFlen, hXlen⟩ := hsplit.lengths
      exact ⟨hFlen.symm ▸ ihF, hXlen.symm ▸ ihX⟩
  | unit _ => trivial
  | bitLit _ => trivial
  | pair hsplit _ _ ihM ihN =>
      obtain ⟨hMlen, hNlen⟩ := hsplit.lengths
      exact ⟨hMlen.symm ▸ ihM, hNlen.symm ▸ ihN⟩
  | unpair hsplit _ _ ihM ihK =>
      obtain ⟨hMlen, hKlen⟩ := hsplit.lengths
      exact ⟨hMlen.symm ▸ ihM, hKlen.symm ▸ ihK⟩
  | ite hsplit _ _ _ ihB ihT ihE =>
      obtain ⟨hBlen, hBranchLen⟩ := hsplit.lengths
      exact ⟨hBlen.symm ▸ ihB, hBranchLen.symm ▸ ihT,
        hBranchLen.symm ▸ ihE⟩
  | prim _ => trivial
  | measure hsplit _ _ ihQ ihK =>
      obtain ⟨hQlen, hKlen⟩ := hsplit.lengths
      exact ⟨hQlen.symm ▸ ihQ, hKlen.symm ▸ ihK⟩
  | fix _ _ _ _ ih => exact ih
  | fold _ _ ih => exact ih
  | unfold _ _ ih => exact ih

theorem closed_typed_scoped {M A} (h : HasType [] [] M A) :
    Scoped 0 0 M := by
  simpa using typed_scoped h

theorem shiftLin_closed_typed {d M A} (h : HasType [] [] M A) :
    shiftLin d 0 M = M :=
  shiftLin_eq_of_scoped (closed_typed_scoped h)

theorem shiftUnres_closed_typed {d M A} (h : HasType [] [] M A) :
    shiftUnres d 0 M = M :=
  shiftUnres_eq_of_scoped (closed_typed_scoped h)

/-- Insert an unrestricted assumption at an arbitrary de Bruijn cutoff. -/
theorem shiftUnres_typing {Γ Γ' Δ M A C k}
    (hi : InsertAt C k Γ Γ') (h : HasType Γ Δ M A) :
    HasType Γ' Δ (shiftUnres 1 k M) A := by
  induction h generalizing Γ' k C with
  | varU hlookup hdup hnone =>
      simpa [shiftUnres] using
        HasType.varU (hlookup.insertAt hi) hdup hnone
  | varL hlookup honly =>
      simpa [shiftUnres] using HasType.varL (Γ := Γ') hlookup honly
  | lamU hdup hnone hM ih =>
      simpa [shiftUnres] using
        HasType.lamU hdup hnone (ih (InsertAt.succ hi))
  | lamL hM ih =>
      simpa [shiftUnres] using HasType.lamL (ih hi)
  | appL hs hF hX ihF ihX =>
      simpa [shiftUnres] using HasType.appL hs (ihF hi) (ihX hi)
  | appU hs hnone hF hX ihF ihX =>
      simpa [shiftUnres] using
        HasType.appU hs hnone (ihF hi) (ihX hi)
  | unit hnone => simpa [shiftUnres] using HasType.unit (Γ := Γ') hnone
  | bitLit hnone =>
      simpa [shiftUnres] using HasType.bitLit (Γ := Γ') hnone
  | pair hs hM hN ihM ihN =>
      simpa [shiftUnres] using HasType.pair hs (ihM hi) (ihN hi)
  | unpair hs hM hK ihM ihK =>
      simpa [shiftUnres] using HasType.unpair hs (ihM hi) (ihK hi)
  | ite hs hB hT hE ihB ihT ihE =>
      simpa [shiftUnres] using
        HasType.ite hs (ihB hi) (ihT hi) (ihE hi)
  | prim hnone => simpa [shiftUnres] using HasType.prim (Γ := Γ') hnone
  | measure hs hQ hK ihQ ihK =>
      simpa [shiftUnres] using HasType.measure hs (ihQ hi) (ihK hi)
  | fix hdup hnone hM ih =>
      simpa [shiftUnres] using HasType.fix hdup hnone (ih hi)
  | fold hM ih => simpa [shiftUnres] using HasType.fold (ih hi)
  | unfold hM ih => simpa [shiftUnres] using HasType.unfold (ih hi)

/-- Insert an unused linear cell at an arbitrary de Bruijn cutoff. -/
theorem shiftLin_typing {Γ Δ Δ' M A k}
    (hi : InsertAt (Option.none : Option Ty) k Δ Δ')
    (h : HasType Γ Δ M A) :
    HasType Γ Δ' (shiftLin 1 k M) A := by
  induction h generalizing Δ' k with
  | varU hlookup hdup hnone =>
      simpa [shiftLin] using
        HasType.varU hlookup hdup (AllNone.insertNone hi hnone)
  | varL hlookup honly =>
      simpa [shiftLin] using
        HasType.varL (hlookup.insertAt hi) (honly.insertNone hi)
  | lamU hdup hnone hM ih =>
      simpa [shiftLin] using
        HasType.lamU hdup (AllNone.insertNone hi hnone) (ih hi)
  | lamL hM ih =>
      simpa [shiftLin] using HasType.lamL (ih (InsertAt.succ hi))
  | appL hs hF hX ihF ihX =>
      obtain ⟨Δ₁', Δ₂', hi₁, hi₂, hs'⟩ := hs.insertNone hi
      simpa [shiftLin] using HasType.appL hs' (ihF hi₁) (ihX hi₂)
  | appU hs hnone hF hX ihF ihX =>
      obtain ⟨ΔF', ΔX', hiF, hiX, hs'⟩ := hs.insertNone hi
      simpa [shiftLin] using
        HasType.appU hs' (AllNone.insertNone hiX hnone)
          (ihF hiF) (ihX hiX)
  | unit hnone =>
      simpa [shiftLin] using HasType.unit (AllNone.insertNone hi hnone)
  | bitLit hnone =>
      simpa [shiftLin] using HasType.bitLit (AllNone.insertNone hi hnone)
  | pair hs hM hN ihM ihN =>
      obtain ⟨Δ₁', Δ₂', hi₁, hi₂, hs'⟩ := hs.insertNone hi
      simpa [shiftLin] using HasType.pair hs' (ihM hi₁) (ihN hi₂)
  | unpair hs hM hK ihM ihK =>
      obtain ⟨Δ₁', Δ₂', hi₁, hi₂, hs'⟩ := hs.insertNone hi
      simpa [shiftLin] using HasType.unpair hs' (ihM hi₁) (ihK hi₂)
  | ite hs hB hT hE ihB ihT ihE =>
      obtain ⟨Δ₁', Δ₂', hi₁, hi₂, hs'⟩ := hs.insertNone hi
      simpa [shiftLin] using
        HasType.ite hs' (ihB hi₁) (ihT hi₂) (ihE hi₂)
  | prim hnone =>
      simpa [shiftLin] using HasType.prim (AllNone.insertNone hi hnone)
  | measure hs hQ hK ihQ ihK =>
      obtain ⟨Δ₁', Δ₂', hi₁, hi₂, hs'⟩ := hs.insertNone hi
      simpa [shiftLin] using HasType.measure hs' (ihQ hi₁) (ihK hi₂)
  | fix hdup hnone hM ih =>
      simpa [shiftLin] using
        HasType.fix hdup (AllNone.insertNone hi hnone) (ih hi)
  | fold hM ih => simpa [shiftLin] using HasType.fold (ih hi)
  | unfold hM ih => simpa [shiftLin] using HasType.unfold (ih hi)

theorem weakenUnres {Γ Δ M A C} (h : HasType Γ Δ M A) :
    HasType (C :: Γ) Δ (liftUnres 0 M) A :=
  shiftUnres_typing (InsertAt.zero Γ) h

theorem weakenLinNone {Γ Δ M A} (h : HasType Γ Δ M A) :
    HasType Γ (none :: Δ) (liftLin 0 M) A :=
  shiftLin_typing (InsertAt.zero Δ) h

/-- Typing over an all-unused linear context depends only on its length. -/
theorem allNone_typing_transport {Γ Δ₁ Δ₂ M A}
    (h : HasType Γ Δ₁ M A) (hn₁ : AllNone Δ₁) (hn₂ : AllNone Δ₂)
    (hlen : Δ₁.length = Δ₂.length) :
    HasType Γ Δ₂ M A := by
  have : Δ₁ = Δ₂ := allNone_unique hn₁ hn₂ hlen
  simpa [this] using h

theorem AllNone.noLookupSome {Δ n A} (hn : AllNone Δ) :
    ¬ Lookup Δ n (some A) := by
  intro hl
  induction Δ generalizing n with
  | nil => cases hl
  | cons cell Δ ih =>
      cases cell with
      | some B => simp [AllNone] at hn
      | none =>
          simp only [AllNone] at hn
          cases hl with
          | succ hl => exact ih hn hl

/-- Delete an unused linear cell at a de Bruijn cutoff. -/
inductive DropLin : Nat → List (Option Ty) → List (Option Ty) → Prop where
  | zero (Δ) : DropLin 0 (none :: Δ) Δ
  | succ {k Δ Δ' cell} : DropLin k Δ Δ' →
      DropLin (k + 1) (cell :: Δ) (cell :: Δ')

theorem DropLin.allNone {k Δ Δ'} (hd : DropLin k Δ Δ')
    (hn : AllNone Δ) : AllNone Δ' := by
  induction hd with
  | zero => simpa [AllNone] using hn
  | succ hd ih =>
      cases ‹Option Ty› with
      | none =>
          simp only [AllNone] at hn ⊢
          exact ih hn
      | some A => simp [AllNone] at hn

theorem DropLin.noLookupTarget {k Δ Δ' A}
    (hd : DropLin k Δ Δ') : ¬ Lookup Δ k (some A) := by
  induction hd with
  | zero =>
      intro h
      cases h
  | succ hd ih =>
      intro h
      cases h with
      | succ h => exact ih h

/-- A split drops an absent cell in both children. -/
theorem DropLin.split {k Δ Δ' Δ₁ Δ₂}
    (hd : DropLin k Δ Δ') (hs : OSplit Δ Δ₁ Δ₂) :
    ∃ Δ₁' Δ₂', DropLin k Δ₁ Δ₁' ∧ DropLin k Δ₂ Δ₂' ∧
      OSplit Δ' Δ₁' Δ₂' := by
  induction hd generalizing Δ₁ Δ₂ with
  | zero =>
      cases hs with
      | none hs => exact ⟨_, _, .zero _, .zero _, hs⟩
  | succ hd ih =>
      cases hs with
      | none hs =>
          obtain ⟨Δ₁', Δ₂', h₁, h₂, hs'⟩ := ih hs
          exact ⟨_, _, .succ h₁, .succ h₂, .none hs'⟩
      | left hs =>
          obtain ⟨Δ₁', Δ₂', h₁, h₂, hs'⟩ := ih hs
          exact ⟨_, _, .succ h₁, .succ h₂, .left hs'⟩
      | right hs =>
          obtain ⟨Δ₁', Δ₂', h₁, h₂, hs'⟩ := ih hs
          exact ⟨_, _, .succ h₁, .succ h₂, .right hs'⟩

theorem DropLin.var {k Δ Δ' n A V}
    (hd : DropLin k Δ Δ') (hl : Lookup Δ n (some A))
    (ho : OnlySomeAt Δ n) :
    ∃ n', substLin k V (.var .lin n) = .var .lin n' ∧
      Lookup Δ' n' (some A) ∧ OnlySomeAt Δ' n' := by
  induction hd generalizing n with
  | zero =>
      cases hl with
      | succ hl =>
          exact ⟨_, by simp [substLin], hl, by simpa [OnlySomeAt] using ho⟩
  | @succ k Δ Δ' cell hd ih =>
      cases cell with
      | some C =>
          cases hl with
          | zero =>
              exact ⟨0, by simp [substLin], Lookup.zero,
                hd.allNone (by simpa [OnlySomeAt] using ho)⟩
          | succ hl => simp [OnlySomeAt] at ho
      | none =>
          cases hl with
          | @succ _ _ n _ hl =>
              obtain ⟨n', heq, hl', ho'⟩ :=
                ih hl (by simpa [OnlySomeAt] using ho)
              refine ⟨n' + 1, ?_, Lookup.succ hl', ?_⟩
              · have hne : n ≠ k := by
                  intro h
                  subst h
                  exact hd.noLookupTarget hl
                by_cases hn : n < k
                · simp [substLin, Nat.succ_lt_succ_iff, hn] at heq ⊢
                  simpa [heq]
                · have hnk : k < n :=
                    Nat.lt_of_le_of_ne (Nat.le_of_not_gt hn) (Ne.symm hne)
                  simp [substLin, Nat.succ_lt_succ_iff, hn, hne,
                    Nat.ne_of_gt hnk, Nat.succ_sub_one] at heq ⊢
                  have hpos : 0 < n :=
                    Nat.lt_of_le_of_lt (Nat.zero_le k) hnk
                  calc
                    n = (n - 1) + 1 :=
                      (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
                        (Nat.ne_of_gt hpos))).symm
                    _ = n' + 1 := by rw [heq]
              · simpa [OnlySomeAt] using ho'

/-- Substitution through a cell known to be unused only lowers indices. -/
theorem substLin_unused {Γ Δ Δ' M B V k}
    (hd : DropLin k Δ Δ') (hM : HasType Γ Δ M B) :
    HasType Γ Δ' (substLin k V M) B := by
  induction hM generalizing Δ' k V with
  | varU hlookup hdup hnone =>
      simpa [substLin] using
        HasType.varU hlookup hdup (hd.allNone hnone)
  | varL hlookup honly =>
      obtain ⟨n', heq, hlookup', honly'⟩ := hd.var hlookup honly
      rw [heq]
      exact HasType.varL hlookup' honly'
  | lamU hdup hnone hM ih =>
      simpa [substLin] using
        HasType.lamU hdup (hd.allNone hnone) (ih hd)
  | lamL hM ih =>
      simpa [substLin] using HasType.lamL (ih (DropLin.succ hd))
  | appL hs hF hX ihF ihX =>
      obtain ⟨Δ₁', Δ₂', hd₁, hd₂, hs'⟩ := hd.split hs
      simpa [substLin] using HasType.appL hs' (ihF hd₁) (ihX hd₂)
  | appU hs hnone hF hX ihF ihX =>
      obtain ⟨ΔF', ΔX', hdF, hdX, hs'⟩ := hd.split hs
      simpa [substLin] using
        HasType.appU hs' (hdX.allNone hnone) (ihF hdF) (ihX hdX)
  | unit hnone =>
      simpa [substLin] using HasType.unit (hd.allNone hnone)
  | bitLit hnone =>
      simpa [substLin] using HasType.bitLit (hd.allNone hnone)
  | pair hs hM hN ihM ihN =>
      obtain ⟨Δ₁', Δ₂', hd₁, hd₂, hs'⟩ := hd.split hs
      simpa [substLin] using HasType.pair hs' (ihM hd₁) (ihN hd₂)
  | unpair hs hM hK ihM ihK =>
      obtain ⟨Δ₁', Δ₂', hd₁, hd₂, hs'⟩ := hd.split hs
      simpa [substLin] using HasType.unpair hs' (ihM hd₁) (ihK hd₂)
  | ite hs hB hT hE ihB ihT ihE =>
      obtain ⟨Δ₁', Δ₂', hd₁, hd₂, hs'⟩ := hd.split hs
      simpa [substLin] using
        HasType.ite hs' (ihB hd₁) (ihT hd₂) (ihE hd₂)
  | prim hnone =>
      simpa [substLin] using HasType.prim (hd.allNone hnone)
  | measure hs hQ hK ihQ ihK =>
      obtain ⟨Δ₁', Δ₂', hd₁, hd₂, hs'⟩ := hd.split hs
      simpa [substLin] using HasType.measure hs' (ihQ hd₁) (ihK hd₂)
  | fix hdup hnone hM ih =>
      simpa [substLin] using
        HasType.fix hdup (hd.allNone hnone) (ih hd)
  | fold hM ih => simpa [substLin] using HasType.fold (ih hd)
  | unfold hM ih => simpa [substLin] using HasType.unfold (ih hd)

/-- Replace one occupied linear cell, merging the replacement resources into
the suffix after the de Bruijn cutoff. -/
inductive LinSubCtx (A : Ty) (Δv : List (Option Ty)) :
    Nat → List (Option Ty) → List (Option Ty) → Prop where
  | zero {Δm Δ} : OSplit Δ Δm Δv →
      LinSubCtx A Δv 0 (some A :: Δm) Δ
  | succ {k Δold Δout cell} : LinSubCtx A Δv k Δold Δout →
      LinSubCtx A Δv (k + 1) (cell :: Δold) (cell :: Δout)

theorem LinSubCtx.lookupTarget {A k Δold Δv Δout}
    (hc : LinSubCtx A Δv k Δold Δout) :
    Lookup Δold k (some A) := by
  induction hc with
  | zero => exact Lookup.zero
  | succ _ ih => exact Lookup.succ ih

/-- Split compatibility for used/unused linear substitution. -/
theorem LinSubCtx.split {A k Δold Δv Δout Δ₁ Δ₂}
    (hc : LinSubCtx A Δv k Δold Δout)
    (hs : OSplit Δold Δ₁ Δ₂) :
    ∃ Δ₁' Δ₂', OSplit Δout Δ₁' Δ₂' ∧
      ((LinSubCtx A Δv k Δ₁ Δ₁' ∧ DropLin k Δ₂ Δ₂') ∨
       (DropLin k Δ₁ Δ₁' ∧ LinSubCtx A Δv k Δ₂ Δ₂')) := by
  induction hc generalizing Δ₁ Δ₂ with
  | zero hv =>
      cases hs with
      | left htail =>
          obtain ⟨Δ₁', hmerge, hout⟩ := hv.rotate htail
          exact ⟨Δ₁', _, hout, Or.inl ⟨.zero hmerge.symm, .zero _⟩⟩
      | right htail =>
          obtain ⟨Δ₂', hmerge, hout⟩ := hv.rotate htail.symm
          exact ⟨_, Δ₂', hout.symm,
            Or.inr ⟨.zero _, .zero hmerge.symm⟩⟩
  | @succ k Δold Δout cell hc ih =>
      cases hs with
      | none hs =>
          obtain ⟨Δ₁', Δ₂', hout, hcases⟩ := ih hs
          rcases hcases with hleft | hright
          · exact ⟨none :: Δ₁', none :: Δ₂', .none hout,
              Or.inl ⟨.succ hleft.1, .succ hleft.2⟩⟩
          · exact ⟨none :: Δ₁', none :: Δ₂', .none hout,
              Or.inr ⟨.succ hright.1, .succ hright.2⟩⟩
      | left hs =>
          obtain ⟨Δ₁', Δ₂', hout, hcases⟩ := ih hs
          rcases hcases with hleft | hright
          · exact ⟨some _ :: Δ₁', none :: Δ₂', .left hout,
              Or.inl ⟨.succ hleft.1, .succ hleft.2⟩⟩
          · exact ⟨some _ :: Δ₁', none :: Δ₂', .left hout,
              Or.inr ⟨.succ hright.1, .succ hright.2⟩⟩
      | right hs =>
          obtain ⟨Δ₁', Δ₂', hout, hcases⟩ := ih hs
          rcases hcases with hleft | hright
          · exact ⟨none :: Δ₁', some _ :: Δ₂', .right hout,
              Or.inl ⟨.succ hleft.1, .succ hleft.2⟩⟩
          · exact ⟨none :: Δ₁', some _ :: Δ₂', .right hout,
              Or.inr ⟨.succ hright.1, .succ hright.2⟩⟩

theorem shiftLin_one_after {k cutoff M} :
    shiftLin 1 cutoff (shiftLin k cutoff M) =
      shiftLin (k + 1) cutoff M := by
  induction M generalizing cutoff with
  | var κ i =>
      cases κ with
      | unres => rfl
      | lin =>
          by_cases hi : i < cutoff
          · simp [shiftLin, hi]
          · have hi' : ¬i + k < cutoff :=
              not_lt.mpr (Nat.le_trans (Nat.le_of_not_gt hi)
                (Nat.le_add_right i k))
            have hki : cutoff ≤ k + i :=
              Nat.le_trans (Nat.le_of_not_gt hi) (Nat.le_add_left i k)
            simp [shiftLin, hi, hi', not_lt.mpr hki,
              Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm]
  | lam κ A M ih =>
      cases κ <;> simp [shiftLin, ih]
  | app F X ihF ihX => simp [shiftLin, ihF, ihX]
  | unit => rfl
  | bitLit _ => rfl
  | pair M N ihM ihN => simp [shiftLin, ihM, ihN]
  | unpair M K ihM ihK => simp [shiftLin, ihM, ihK]
  | ite B T E ihB ihT ihE => simp [shiftLin, ihB, ihT, ihE]
  | prim _ => rfl
  | measure Q K ihQ ihK => simp [shiftLin, ihQ, ihK]
  | fix A M ih => simp [shiftLin, ih]
  | fold A M ih => simp [shiftLin, ih]
  | unfold M ih => simp [shiftLin, ih]

theorem shiftLin_substLin_var (k n : Nat) (V : Term) :
    shiftLin 1 0 (substLin k V (.var .lin n)) =
      substLin (k + 1) V (.var .lin (n + 1)) := by
  by_cases hn : n < k
  · simp [substLin, shiftLin, hn, Nat.succ_lt_succ_iff]
  · by_cases heq : n = k
    · subst heq
      simp [substLin, shiftLin, shiftLin_one_after]
    · have hkn : k < n :=
        Nat.lt_of_le_of_ne (Nat.le_of_not_gt hn) (Ne.symm heq)
      have hnpos : 0 < n :=
        Nat.lt_of_le_of_lt (Nat.zero_le k) hkn
      simp [substLin, shiftLin, hn, heq, Nat.succ_lt_succ_iff,
        Nat.ne_of_gt hkn, Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hnpos))]

theorem LinSubCtx.var {Γ A B k Δold Δv Δout V n}
    (hc : LinSubCtx A Δv k Δold Δout)
    (hV : HasType Γ Δv V A)
    (hl : Lookup Δold n (some B)) (ho : OnlySomeAt Δold n) :
    HasType Γ Δout (substLin k V (.var .lin n)) B := by
  induction hc generalizing n Γ V with
  | zero hs =>
      cases hl with
      | zero =>
          rw [hs.eq_right_of_allNone_left
            (by simpa [OnlySomeAt] using ho)]
          simpa [substLin, shiftLin_zero] using hV
      | succ hl => simp [OnlySomeAt] at ho
  | @succ k Δold Δout cell hc ih =>
      cases cell with
      | some C =>
          cases hl with
          | zero =>
              have hnone : AllNone Δold := by simpa [OnlySomeAt] using ho
              exact (hnone.noLookupSome hc.lookupTarget).elim
          | succ hl => simp [OnlySomeAt] at ho
      | none =>
          cases hl with
          | @succ _ _ n _ hl =>
              have hrec := ih hV hl (by simpa [OnlySomeAt] using ho)
              have hweak := weakenLinNone hrec
              simpa [liftLin, shiftLin_substLin_var] using hweak

/-- The used half of linear substitution; together with `substLin_unused` this
follows the unique side of every split containing the substituted variable. -/
theorem substLin_preserves {Γ Δold Δv Δout M A B V k}
    (hc : LinSubCtx A Δv k Δold Δout)
    (hM : HasType Γ Δold M B) (hV : HasType Γ Δv V A) :
    HasType Γ Δout (substLin k V M) B := by
  induction hM generalizing Δv Δout k V with
  | varU hlookup hdup hnone =>
      exact (hnone.noLookupSome hc.lookupTarget).elim
  | varL hlookup honly => exact hc.var hV hlookup honly
  | lamU hdup hnone hM ih =>
      exact (hnone.noLookupSome hc.lookupTarget).elim
  | lamL hM ih =>
      simpa [substLin] using HasType.lamL (ih (.succ hc) hV)
  | appL hs hF hX ihF ihX =>
      obtain ⟨ΔF', ΔX', hs', hcases⟩ := hc.split hs
      rcases hcases with hleft | hright
      · simpa [substLin] using
          HasType.appL hs' (ihF hleft.1 hV)
            (substLin_unused hleft.2 hX)
      · simpa [substLin] using
          HasType.appL hs' (substLin_unused hright.1 hF)
            (ihX hright.2 hV)
  | appU hs hnone hF hX ihF ihX =>
      obtain ⟨ΔF', ΔX', hs', hcases⟩ := hc.split hs
      rcases hcases with hleft | hright
      · simpa [substLin] using
          HasType.appU hs' (hleft.2.allNone hnone)
            (ihF hleft.1 hV) (substLin_unused hleft.2 hX)
      · exact (hnone.noLookupSome hright.2.lookupTarget).elim
  | unit hnone =>
      exact (hnone.noLookupSome hc.lookupTarget).elim
  | bitLit hnone =>
      exact (hnone.noLookupSome hc.lookupTarget).elim
  | pair hs hM hN ihM ihN =>
      obtain ⟨ΔM', ΔN', hs', hcases⟩ := hc.split hs
      rcases hcases with hleft | hright
      · simpa [substLin] using
          HasType.pair hs' (ihM hleft.1 hV)
            (substLin_unused hleft.2 hN)
      · simpa [substLin] using
          HasType.pair hs' (substLin_unused hright.1 hM)
            (ihN hright.2 hV)
  | unpair hs hM hK ihM ihK =>
      obtain ⟨ΔM', ΔK', hs', hcases⟩ := hc.split hs
      rcases hcases with hleft | hright
      · simpa [substLin] using
          HasType.unpair hs' (ihM hleft.1 hV)
            (substLin_unused hleft.2 hK)
      · simpa [substLin] using
          HasType.unpair hs' (substLin_unused hright.1 hM)
            (ihK hright.2 hV)
  | ite hs hB hT hE ihB ihT ihE =>
      obtain ⟨ΔB', ΔR', hs', hcases⟩ := hc.split hs
      rcases hcases with hleft | hright
      · simpa [substLin] using
          HasType.ite hs' (ihB hleft.1 hV)
            (substLin_unused hleft.2 hT)
            (substLin_unused hleft.2 hE)
      · simpa [substLin] using
          HasType.ite hs' (substLin_unused hright.1 hB)
            (ihT hright.2 hV) (ihE hright.2 hV)
  | prim hnone =>
      exact (hnone.noLookupSome hc.lookupTarget).elim
  | measure hs hQ hK ihQ ihK =>
      obtain ⟨ΔQ', ΔK', hs', hcases⟩ := hc.split hs
      rcases hcases with hleft | hright
      · simpa [substLin] using
          HasType.measure hs' (ihQ hleft.1 hV)
            (substLin_unused hleft.2 hK)
      · simpa [substLin] using
          HasType.measure hs' (substLin_unused hright.1 hQ)
            (ihK hright.2 hV)
  | fix hdup hnone hM ih =>
      exact (hnone.noLookupSome hc.lookupTarget).elim
  | fold hM ih =>
      simpa [substLin] using HasType.fold (ih hc hV)
  | unfold hM ih =>
      simpa [substLin] using HasType.unfold (ih hc hV)

theorem substLin_zero_preserves {Γ Δ Δm Δv M V A B}
    (hs : OSplit Δ Δm Δv)
    (hM : HasType Γ (some A :: Δm) M B)
    (hV : HasType Γ Δv V A) :
    HasType Γ Δ (substLin 0 V M) B :=
  substLin_preserves (.zero hs) hM hV

/-- Remove the unrestricted assumption selected by a de Bruijn cutoff. The
tail context is a parameter so replacement terms remain outside every crossed
binder. -/
inductive UnresSubCtx (A : Ty) (Γ : List Ty) :
    Nat → List Ty → List Ty → Prop where
  | zero : UnresSubCtx A Γ 0 (A :: Γ) Γ
  | succ {k Γold Γout C} : UnresSubCtx A Γ k Γold Γout →
      UnresSubCtx A Γ (k + 1) (C :: Γold) (C :: Γout)

theorem shiftUnres_one_after {k cutoff M} :
    shiftUnres 1 cutoff (shiftUnres k cutoff M) =
      shiftUnres (k + 1) cutoff M := by
  induction M generalizing cutoff with
  | var κ i =>
      cases κ with
      | lin => rfl
      | unres =>
          by_cases hi : i < cutoff
          · simp [shiftUnres, hi]
          · have hi' : ¬i + k < cutoff :=
              not_lt.mpr (Nat.le_trans (Nat.le_of_not_gt hi)
                (Nat.le_add_right i k))
            have hki : cutoff ≤ k + i :=
              Nat.le_trans (Nat.le_of_not_gt hi) (Nat.le_add_left i k)
            simp [shiftUnres, hi, hi', not_lt.mpr hki,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | lam κ A M ih =>
      cases κ <;> simp [shiftUnres, ih]
  | app F X ihF ihX => simp [shiftUnres, ihF, ihX]
  | unit => rfl
  | bitLit _ => rfl
  | pair M N ihM ihN => simp [shiftUnres, ihM, ihN]
  | unpair M K ihM ihK => simp [shiftUnres, ihM, ihK]
  | ite B T E ihB ihT ihE => simp [shiftUnres, ihB, ihT, ihE]
  | prim _ => rfl
  | measure Q K ihQ ihK => simp [shiftUnres, ihQ, ihK]
  | fix A M ih => simp [shiftUnres, ih]
  | fold A M ih => simp [shiftUnres, ih]
  | unfold M ih => simp [shiftUnres, ih]

theorem shiftUnres_zero (cutoff : Nat) (M : Term) :
    shiftUnres 0 cutoff M = M := by
  induction M generalizing cutoff with
  | var κ i => cases κ <;> simp [shiftUnres]
  | lam κ A M ih => cases κ <;> simp [shiftUnres, ih]
  | app F X ihF ihX => simp [shiftUnres, ihF, ihX]
  | unit => rfl
  | bitLit _ => rfl
  | pair M N ihM ihN => simp [shiftUnres, ihM, ihN]
  | unpair M K ihM ihK => simp [shiftUnres, ihM, ihK]
  | ite B T E ihB ihT ihE => simp [shiftUnres, ihB, ihT, ihE]
  | prim _ => rfl
  | measure Q K ihQ ihK => simp [shiftUnres, ihQ, ihK]
  | fix A M ih => simp [shiftUnres, ih]
  | fold A M ih => simp [shiftUnres, ih]
  | unfold M ih => simp [shiftUnres, ih]

theorem shiftUnres_substUnres_var (k n : Nat) (V : Term) :
    shiftUnres 1 0 (substUnres k V (.var .unres n)) =
      substUnres (k + 1) V (.var .unres (n + 1)) := by
  by_cases hn : n < k
  · simp [substUnres, shiftUnres, hn, Nat.succ_lt_succ_iff]
  · by_cases heq : n = k
    · subst heq
      simp [substUnres, shiftUnres, shiftUnres_one_after]
    · have hkn : k < n :=
        Nat.lt_of_le_of_ne (Nat.le_of_not_gt hn) (Ne.symm heq)
      have hnpos : 0 < n :=
        Nat.lt_of_le_of_lt (Nat.zero_le k) hkn
      simp [substUnres, shiftUnres, hn, heq, Nat.succ_lt_succ_iff,
        Nat.ne_of_gt hkn, Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hnpos))]

theorem UnresSubCtx.var {A B Γ Γold Γout Δ Δv V k n}
    (hc : UnresSubCtx A Γ k Γold Γout)
    (hV : HasType Γ Δv V A) (hnV : AllNone Δv)
    (hlen : Δv.length = Δ.length)
    (hl : Lookup Γold n B) (hdup : Ty.duplicable B = true)
    (hn : AllNone Δ) :
    HasType Γout Δ (substUnres k V (.var .unres n)) B := by
  induction hc generalizing n Δ Δv V with
  | zero =>
      cases hl with
      | zero =>
          have hV' := allNone_typing_transport hV hnV hn hlen
          simpa [substUnres, shiftUnres_zero] using hV'
      | succ hl =>
          simpa [substUnres] using HasType.varU hl hdup hn
  | @succ k' Γold' Γout' C hc ih =>
      cases hl with
      | zero =>
          simpa [substUnres] using
            HasType.varU Lookup.zero hdup hn
      | @succ _ _ n _ hl =>
          have hrec := ih hV hnV hlen hl hn
          have hweak := weakenUnres (C := C) hrec
          simpa [liftUnres, shiftUnres_substUnres_var] using hweak

/-- Capture-avoiding unrestricted substitution. The replacement has empty
linear support, as required by unrestricted application. -/
theorem substUnres_preserves {A B Γ Γold Γout Δ Δv M V k}
    (hc : UnresSubCtx A Γ k Γold Γout)
    (hM : HasType Γold Δ M B)
    (hV : HasType Γ Δv V A) (hnV : AllNone Δv)
    (hlen : Δv.length = Δ.length) :
    HasType Γout Δ (substUnres k V M) B := by
  induction hM generalizing Γout Δv V k with
  | varU hlookup hdup hnone =>
      exact hc.var hV hnV hlen hlookup hdup hnone
  | varL hlookup honly =>
      simpa [substUnres] using
        HasType.varL (Γ := Γout) hlookup honly
  | lamU hdup hnone hM ih =>
      simpa [substUnres] using
        HasType.lamU hdup hnone (ih (.succ hc) hV hnV hlen)
  | @lamL Γ₀ Δ₀ A₀ B₀ M₀ hM ih =>
      have hV' := weakenLinNone hV
      have hnV' : AllNone (none :: Δv) := by simpa [AllNone] using hnV
      have hlen' :
          (none :: Δv).length = (some A₀ :: Δ₀).length := by
        simp [hlen]
      simpa [substUnres] using
        HasType.lamL (ih hc hV' hnV' hlen')
  | appL hs hF hX ihF ihX =>
      obtain ⟨hFlen, hXlen⟩ := hs.lengths
      simpa [substUnres] using
        HasType.appL hs (ihF hc hV hnV (hlen.trans hFlen.symm))
          (ihX hc hV hnV (hlen.trans hXlen.symm))
  | appU hs hnone hF hX ihF ihX =>
      obtain ⟨hFlen, hXlen⟩ := hs.lengths
      simpa [substUnres] using
        HasType.appU hs hnone
          (ihF hc hV hnV (hlen.trans hFlen.symm))
          (ihX hc hV hnV (hlen.trans hXlen.symm))
  | unit hnone =>
      simpa [substUnres] using HasType.unit (Γ := Γout) hnone
  | bitLit hnone =>
      simpa [substUnres] using HasType.bitLit (Γ := Γout) hnone
  | pair hs hM hN ihM ihN =>
      obtain ⟨hMlen, hNlen⟩ := hs.lengths
      simpa [substUnres] using
        HasType.pair hs (ihM hc hV hnV (hlen.trans hMlen.symm))
          (ihN hc hV hnV (hlen.trans hNlen.symm))
  | unpair hs hM hK ihM ihK =>
      obtain ⟨hMlen, hKlen⟩ := hs.lengths
      simpa [substUnres] using
        HasType.unpair hs (ihM hc hV hnV (hlen.trans hMlen.symm))
          (ihK hc hV hnV (hlen.trans hKlen.symm))
  | ite hs hB hT hE ihB ihT ihE =>
      obtain ⟨hBlen, hRlen⟩ := hs.lengths
      simpa [substUnres] using
        HasType.ite hs (ihB hc hV hnV (hlen.trans hBlen.symm))
          (ihT hc hV hnV (hlen.trans hRlen.symm))
          (ihE hc hV hnV (hlen.trans hRlen.symm))
  | prim hnone =>
      simpa [substUnres] using HasType.prim (Γ := Γout) hnone
  | measure hs hQ hK ihQ ihK =>
      obtain ⟨hQlen, hKlen⟩ := hs.lengths
      simpa [substUnres] using
        HasType.measure hs (ihQ hc hV hnV (hlen.trans hQlen.symm))
          (ihK hc hV hnV (hlen.trans hKlen.symm))
  | fix hdup hnone hM ih =>
      simpa [substUnres] using
        HasType.fix hdup hnone (ih hc hV hnV hlen)
  | fold hM ih =>
      simpa [substUnres] using HasType.fold (ih hc hV hnV hlen)
  | unfold hM ih =>
      simpa [substUnres] using HasType.unfold (ih hc hV hnV hlen)

theorem substUnres_zero_preserves {A B Γ Δ Δv M V}
    (hM : HasType (A :: Γ) Δ M B)
    (hV : HasType Γ Δv V A) (hnV : AllNone Δv)
    (hlen : Δv.length = Δ.length) :
    HasType Γ Δ (substUnres 0 V M) B :=
  substUnres_preserves .zero hM hV hnV hlen

end QLambda.Linear
