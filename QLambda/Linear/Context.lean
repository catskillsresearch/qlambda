/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.Syntax

/-!
# Linear contexts

The linear context of a judgment records exactly the variables used by a term.
`OSplit` shuffles one context into the two sides of an application, tensor, or
measurement. Unrestricted contexts are ordinary lists and are not split.
-/

namespace QLambda.Linear

inductive Lookup {α : Type} : List α → Nat → α → Prop where
  | zero {a xs} : Lookup (a :: xs) 0 a
  | succ {b xs n a} : Lookup xs n a → Lookup (b :: xs) (n + 1) a

/-- Every cell is absent, so the term uses no linear variable. -/
def AllNone : List (Option Ty) → Prop
  | [] => True
  | none :: Δ => AllNone Δ
  | some _ :: _ => False

/-- The only occupied cell of a linear context is index `n`. -/
def OnlySomeAt : List (Option Ty) → Nat → Prop
  | [], _ => True
  | some _ :: Δ, 0 => AllNone Δ
  | none :: _, 0 => False
  | some _ :: _, _ + 1 => False
  | none :: Δ, n + 1 => OnlySomeAt Δ n

/-- A use-respecting partition of a linear context. -/
inductive OSplit :
    List (Option Ty) → List (Option Ty) → List (Option Ty) → Prop where
  | nil : OSplit [] [] []
  | none {Δ Δ₁ Δ₂} :
      OSplit Δ Δ₁ Δ₂ → OSplit (none :: Δ) (none :: Δ₁) (none :: Δ₂)
  | left {A Δ Δ₁ Δ₂} :
      OSplit Δ Δ₁ Δ₂ → OSplit (some A :: Δ) (some A :: Δ₁) (none :: Δ₂)
  | right {A Δ Δ₁ Δ₂} :
      OSplit Δ Δ₁ Δ₂ → OSplit (some A :: Δ) (none :: Δ₁) (some A :: Δ₂)

theorem Lookup.lt_length {α : Type} {xs : List α} {n : Nat} {a : α}
    (h : Lookup xs n a) : n < xs.length := by
  induction h with
  | zero => simp
  | succ _ ih => simpa using Nat.succ_lt_succ ih

theorem OSplit.lengths {Δ Δ₁ Δ₂ : List (Option Ty)}
    (h : OSplit Δ Δ₁ Δ₂) :
    Δ₁.length = Δ.length ∧ Δ₂.length = Δ.length := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | none _ ih | left _ ih | right _ ih =>
      exact ⟨by simp [ih.1], by simp [ih.2]⟩

/-- Mark index `n` and leave every other in-scope variable unused. -/
def mark : Nat → List Ty → List Bool
  | _, [] => []
  | 0, _ :: xs => true :: List.replicate xs.length false
  | n + 1, _ :: xs => false :: mark n xs

/-- Combine two disjoint usage vectors. Fails if any index is used twice. -/
def zipOr : List Bool → List Bool → Option (List Bool)
  | [], [] => some []
  | false :: as, false :: bs =>
      match zipOr as bs with
      | some cs => some (false :: cs)
      | none => none
  | false :: as, true :: bs =>
      match zipOr as bs with
      | some cs => some (true :: cs)
      | none => none
  | true :: as, false :: bs =>
      match zipOr as bs with
      | some cs => some (true :: cs)
      | none => none
  | true :: _, true :: _ => none
  | _, _ => none

/-- Turn a scope and a usage vector into the linear context of a judgment. -/
def usageCtx : List Ty → List Bool → List (Option Ty)
  | A :: As, true :: bs => some A :: usageCtx As bs
  | _ :: As, false :: bs => none :: usageCtx As bs
  | _, _ => []

/-- No linear index is marked. -/
def allFalse : List Bool → Bool
  | [] => true
  | false :: xs => allFalse xs
  | true :: _ => false

theorem lookup_of_get? {α : Type} {xs : List α} {n : Nat} {a : α}
    (h : xs[n]? = some a) : Lookup xs n a := by
  induction xs generalizing n with
  | nil => simp at h
  | cons x xs ih =>
      cases n with
      | zero =>
          simp at h
          subst h
          exact Lookup.zero
      | succ n =>
          simp at h
          exact Lookup.succ (ih h)

theorem allNone_unused (Δ : List Ty) :
    AllNone (usageCtx Δ (List.replicate Δ.length false)) := by
  induction Δ with
  | nil => simp [usageCtx, AllNone]
  | cons A Δ ih =>
      simp [List.replicate_succ, usageCtx, AllNone, ih]

theorem mark_length (n : Nat) (Δ : List Ty) : (mark n Δ).length = Δ.length := by
  induction Δ generalizing n with
  | nil => simp [mark]
  | cons A Δ ih =>
      cases n with
      | zero => simp [mark, List.length_replicate]
      | succ n => simp [mark, ih]

theorem varLin_usage {n : Nat} {Δ : List Ty} {A : Ty} (h : Δ[n]? = some A) :
    Lookup (usageCtx Δ (mark n Δ)) n (some A) ∧
      OnlySomeAt (usageCtx Δ (mark n Δ)) n := by
  induction n generalizing Δ with
  | zero =>
      cases Δ with
      | nil => simp at h
      | cons B Δ =>
          simp at h
          subst h
          exact ⟨Lookup.zero, allNone_unused Δ⟩
  | succ n ih =>
      cases Δ with
      | nil => simp at h
      | cons B Δ =>
          simp at h
          obtain ⟨hlook, honly⟩ := ih h
          exact ⟨Lookup.succ hlook, honly⟩

theorem eq_replicate_false_of_allFalse {u : List Bool} (h : allFalse u = true) :
    u = List.replicate u.length false := by
  induction u with
  | nil => rfl
  | cons a u ih =>
      cases a with
      | true => simp [allFalse] at h
      | false =>
          simp [allFalse] at h
          rw [ih h]
          simp [List.length_cons, List.replicate_succ]

theorem allNone_of_allFalse {Δ : List Ty} {u : List Bool}
    (hlen : u.length = Δ.length) (h : allFalse u = true) :
    AllNone (usageCtx Δ u) := by
  have hu : u = List.replicate Δ.length false := by
    rw [← hlen]
    exact eq_replicate_false_of_allFalse h
  rw [hu]
  exact allNone_unused Δ

theorem zipOr_length {u1 u2 u : List Bool} (h : zipOr u1 u2 = some u) :
    u.length = u1.length ∧ u.length = u2.length := by
  induction u1 generalizing u2 u with
  | nil =>
      cases u2 with
      | nil =>
          simp [zipOr] at h
          subst h
          simp
      | cons _ _ => simp [zipOr] at h
  | cons a u1 ih =>
      cases u2 with
      | nil => simp [zipOr] at h
      | cons b u2 =>
          cases a <;> cases b <;> simp only [zipOr] at h
          · cases htail : zipOr u1 u2 with
            | none => simp [htail] at h
            | some u' =>
                simp [htail] at h
                subst h
                obtain ⟨h1, h2⟩ := ih htail
                exact ⟨by simp [h1], by simp [h2]⟩
          · cases htail : zipOr u1 u2 with
            | none => simp [htail] at h
            | some u' =>
                simp [htail] at h
                subst h
                obtain ⟨h1, h2⟩ := ih htail
                exact ⟨by simp [h1], by simp [h2]⟩
          · cases htail : zipOr u1 u2 with
            | none => simp [htail] at h
            | some u' =>
                simp [htail] at h
                subst h
                obtain ⟨h1, h2⟩ := ih htail
                exact ⟨by simp [h1], by simp [h2]⟩
          · simp at h

theorem oSplit_of_zipOr {Δ : List Ty} {u1 u2 u : List Bool}
    (hzip : zipOr u1 u2 = some u) (h1 : u1.length = Δ.length)
    (h2 : u2.length = Δ.length) :
    OSplit (usageCtx Δ u) (usageCtx Δ u1) (usageCtx Δ u2) := by
  induction Δ generalizing u1 u2 u with
  | nil =>
      cases u1 with
      | nil =>
          cases u2 with
          | nil =>
              simp [zipOr] at hzip
              subst hzip
              exact OSplit.nil
          | cons _ _ => simp at h2
      | cons _ _ => simp at h1
  | cons A Δ ih =>
      cases u1 with
      | nil => simp at h1
      | cons a u1 =>
          cases u2 with
          | nil => simp at h2
          | cons b u2 =>
              simp [List.length_cons] at h1 h2
              cases a <;> cases b <;> simp only [zipOr] at hzip
              · cases htail : zipOr u1 u2 with
                | none => simp [htail] at hzip
                | some u' =>
                    simp [htail] at hzip
                    subst hzip
                    exact OSplit.none (ih htail h1 h2)
              · cases htail : zipOr u1 u2 with
                | none => simp [htail] at hzip
                | some u' =>
                    simp [htail] at hzip
                    subst hzip
                    exact OSplit.right (ih htail h1 h2)
              · cases htail : zipOr u1 u2 with
                | none => simp [htail] at hzip
                | some u' =>
                    simp [htail] at hzip
                    subst hzip
                    exact OSplit.left (ih htail h1 h2)
              · simp at hzip

end QLambda.Linear
