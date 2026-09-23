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

theorem Lookup.mem {α : Type} {xs : List α} {n : Nat} {a : α}
    (h : Lookup xs n a) : a ∈ xs := by
  induction h with
  | zero => exact List.Mem.head _
  | succ _ ih => exact List.Mem.tail _ ih

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

theorem OSplit.symm {Δ Δ₁ Δ₂ : List (Option Ty)}
    (h : OSplit Δ Δ₁ Δ₂) : OSplit Δ Δ₂ Δ₁ := by
  induction h with
  | nil => exact .nil
  | none _ ih => exact .none ih
  | left _ ih => exact .right ih
  | right _ ih => exact .left ih

theorem allNone_eq_replicate (Δ : List (Option Ty)) (h : AllNone Δ) :
    Δ = List.replicate Δ.length none := by
  induction Δ with
  | nil => rfl
  | cons cell Δ ih =>
      cases cell with
      | none =>
          simp only [AllNone] at h
          change none :: Δ = none :: List.replicate Δ.length none
          rw [ih h]
          simp
      | some _ => simp [AllNone] at h

theorem allNone_unique {Δ₁ Δ₂ : List (Option Ty)}
    (h₁ : AllNone Δ₁) (h₂ : AllNone Δ₂)
    (hlen : Δ₁.length = Δ₂.length) : Δ₁ = Δ₂ := by
  rw [allNone_eq_replicate Δ₁ h₁, allNone_eq_replicate Δ₂ h₂, hlen]

theorem OSplit.eq_right_of_allNone_left {Δ Δ₁ Δ₂ : List (Option Ty)}
    (hs : OSplit Δ Δ₁ Δ₂) (h₁ : AllNone Δ₁) :
    Δ = Δ₂ := by
  induction hs with
  | nil => rfl
  | none _ ih =>
      simp only [AllNone] at h₁
      simp [ih h₁]
  | left _ _ => simp [AllNone] at h₁
  | right _ ih =>
      simp only [AllNone] at h₁
      simp [ih h₁]

theorem OSplit.eq_left_of_allNone_right {Δ Δ₁ Δ₂ : List (Option Ty)}
    (hs : OSplit Δ Δ₁ Δ₂) (h₂ : AllNone Δ₂) :
    Δ = Δ₁ :=
  hs.symm.eq_right_of_allNone_left h₂

theorem OSplit.withNoneRight (Δ : List (Option Ty)) :
    OSplit Δ Δ (List.replicate Δ.length (Option.none : Option Ty)) := by
  induction Δ with
  | nil => exact .nil
  | cons cell Δ ih =>
      cases cell with
      | none => simpa [List.replicate_succ] using OSplit.none ih
      | some A => simpa [List.replicate_succ] using OSplit.left ih

theorem allNone_replicate_none (n : Nat) :
    AllNone (List.replicate n (Option.none : Option Ty)) := by
  induction n with
  | zero => trivial
  | succ n ih => simpa [List.replicate_succ, AllNone]

theorem OSplit.mem_left {Δ Δ₁ Δ₂ : List (Option Ty)} (h : OSplit Δ Δ₁ Δ₂)
    {A : Ty} (hm : some A ∈ Δ₁) : some A ∈ Δ := by
  induction h with
  | nil => cases hm
  | none _ ih =>
      cases hm with
      | tail _ hm => exact List.Mem.tail _ (ih hm)
  | left _ ih =>
      cases hm with
      | head => exact List.Mem.head _
      | tail _ hm => exact List.Mem.tail _ (ih hm)
  | right h ih =>
      cases hm with
      | tail _ hm => exact List.Mem.tail _ (ih hm)

theorem OSplit.mem_right {Δ Δ₁ Δ₂ : List (Option Ty)} (h : OSplit Δ Δ₁ Δ₂)
    {A : Ty} (hm : some A ∈ Δ₂) : some A ∈ Δ := by
  induction h with
  | nil => cases hm
  | none _ ih =>
      cases hm with
      | tail _ hm => exact List.Mem.tail _ (ih hm)
  | left h ih =>
      cases hm with
      | tail _ hm => exact List.Mem.tail _ (ih hm)
  | right _ ih =>
      cases hm with
      | head => exact List.Mem.head _
      | tail _ hm => exact List.Mem.tail _ (ih hm)

theorem OSplit.self_of_allNone {Δ : List (Option Ty)} (hn : AllNone Δ) :
    OSplit Δ Δ Δ := by
  induction Δ with
  | nil => exact .nil
  | cons cell Δ ih =>
      cases cell with
      | none =>
          simp only [AllNone] at hn
          exact .none (ih hn)
      | some A => simp [AllNone] at hn

/-- Reassociate a three-way split, moving the outside right part before the
first inside part. -/
theorem OSplit.rotate {Δ Δmn Δk Δm Δn : List (Option Ty)}
    (h : OSplit Δ Δmn Δk) (hmn : OSplit Δmn Δm Δn) :
    ∃ Δkm, OSplit Δkm Δk Δm ∧ OSplit Δ Δkm Δn := by
  induction h generalizing Δm Δn with
  | nil =>
      cases hmn
      exact ⟨[], .nil, .nil⟩
  | none h ih =>
      cases hmn with
      | none hmn =>
          obtain ⟨Δkm, hkm, hout⟩ := ih hmn
          exact ⟨Option.none :: Δkm, .none hkm, .none hout⟩
  | left h ih =>
      cases hmn with
      | left hmn =>
          obtain ⟨Δkm, hkm, hout⟩ := ih hmn
          exact ⟨some _ :: Δkm, .right hkm, .left hout⟩
      | right hmn =>
          obtain ⟨Δkm, hkm, hout⟩ := ih hmn
          exact ⟨Option.none :: Δkm, .none hkm, .right hout⟩
  | right h ih =>
      cases hmn with
      | none hmn =>
          obtain ⟨Δkm, hkm, hout⟩ := ih hmn
          exact ⟨some _ :: Δkm, .left hkm, .left hout⟩

/-- Insert one element at a de Bruijn cutoff. -/
inductive InsertAt {α : Type} (a : α) : Nat → List α → List α → Prop where
  | zero (xs : List α) : InsertAt a 0 xs (a :: xs)
  | succ {n xs ys b} : InsertAt a n xs ys →
      InsertAt a (n + 1) (b :: xs) (b :: ys)

theorem InsertAt.length {α : Type} {a : α} {n : Nat} {xs ys : List α}
    (h : InsertAt a n xs ys) : ys.length = xs.length + 1 := by
  induction h with
  | zero => simp
  | succ _ ih => simp [ih, Nat.add_assoc]

theorem InsertAt.le_length {α : Type} {a : α} {n : Nat} {xs ys : List α}
    (h : InsertAt a n xs ys) : n ≤ xs.length := by
  induction h with
  | zero => exact Nat.zero_le _
  | succ _ ih => simpa using Nat.succ_le_succ ih

theorem Lookup.insertAt {α : Type} {a b : α} {k n : Nat} {xs ys : List α}
    (hi : InsertAt b k xs ys) (hl : Lookup xs n a) :
    Lookup ys (if n < k then n else n + 1) a := by
  induction hi generalizing n with
  | zero =>
      simp
      exact Lookup.succ hl
  | @succ k xs ys b hi ih =>
      cases hl with
      | zero =>
          rw [if_pos (Nat.zero_lt_succ k)]
          exact Lookup.zero
      | @succ _ _ n _ hl =>
          have h := ih hl
          simp only [Nat.succ_lt_succ_iff]
          by_cases hn : n < k
          · rw [if_pos hn]
            rw [if_pos hn] at h
            exact Lookup.succ h
          · rw [if_neg hn]
            rw [if_neg hn] at h
            exact Lookup.succ h

theorem AllNone.insertNone {Δ Δ' : List (Option Ty)} {k : Nat}
    (hi : InsertAt (Option.none : Option Ty) k Δ Δ') (h : AllNone Δ) :
    AllNone Δ' := by
  induction hi with
  | zero => simpa [AllNone]
  | succ hi ih =>
      cases ‹Option Ty› with
      | none =>
          simp only [AllNone] at h ⊢
          exact ih h
      | some A => simp [AllNone] at h

theorem OnlySomeAt.insertNone {Δ Δ' : List (Option Ty)} {k n : Nat}
    (hi : InsertAt (Option.none : Option Ty) k Δ Δ') (ho : OnlySomeAt Δ n) :
    OnlySomeAt Δ' (if n < k then n else n + 1) := by
  induction hi generalizing n with
  | zero =>
      simp only [Nat.not_lt_zero, if_false]
      simpa [OnlySomeAt] using ho
  | @succ k Δ Δ' cell hi ih =>
      cases n with
      | zero =>
          rw [if_pos (Nat.zero_lt_succ k)]
          cases cell with
          | none => simp [OnlySomeAt] at ho
          | some A =>
              change AllNone Δ'
              exact AllNone.insertNone hi ho
      | succ n =>
          cases cell with
          | some A => simp [OnlySomeAt] at ho
          | none =>
              simp only [OnlySomeAt] at ho
              have h := ih ho
              simp only [Nat.succ_lt_succ_iff]
              by_cases hn : n < k
              · rw [if_pos hn]
                rw [if_pos hn] at h
                exact h
              · rw [if_neg hn]
                rw [if_neg hn] at h
                exact h

/-- Inserting an unused cell into a split inserts it in both children. -/
theorem OSplit.insertNone {Δ Δ₁ Δ₂ Δ' : List (Option Ty)} {k : Nat}
    (hs : OSplit Δ Δ₁ Δ₂)
    (hi : InsertAt (Option.none : Option Ty) k Δ Δ') :
    ∃ Δ₁' Δ₂',
      InsertAt (Option.none : Option Ty) k Δ₁ Δ₁' ∧
      InsertAt (Option.none : Option Ty) k Δ₂ Δ₂' ∧
      OSplit Δ' Δ₁' Δ₂' := by
  induction hi generalizing Δ₁ Δ₂ with
  | zero =>
      exact ⟨Option.none :: Δ₁, Option.none :: Δ₂, .zero _, .zero _, .none hs⟩
  | @succ k Δ Δ' cell hi ih =>
      cases hs with
      | none hs =>
          obtain ⟨Δ₁', Δ₂', h₁, h₂, hs'⟩ := ih hs
          exact ⟨Option.none :: Δ₁', Option.none :: Δ₂',
            .succ h₁, .succ h₂, .none hs'⟩
      | left hs =>
          obtain ⟨Δ₁', Δ₂', h₁, h₂, hs'⟩ := ih hs
          exact ⟨some _ :: Δ₁', Option.none :: Δ₂',
            .succ h₁, .succ h₂, .left hs'⟩
      | right hs =>
          obtain ⟨Δ₁', Δ₂', h₁, h₂, hs'⟩ := ih hs
          exact ⟨Option.none :: Δ₁', some _ :: Δ₂',
            .succ h₁, .succ h₂, .right hs'⟩

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
