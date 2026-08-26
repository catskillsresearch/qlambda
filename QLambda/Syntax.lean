/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.String.Lemmas

/-!
# Syntax of untyped quantum λ-calculus (`qλ`)

Paper §2. Terms with the three choice operators:

$$M, N ::= x \mid \lambda x.\, M \mid M\, N
  \mid M \oplus_p N \mid M \sqcap N \mid M \mathbin{\Box} N$$
-/

namespace QLambda

/-- A variable name. -/
abbrev Name : Type := String

/-- Weight of a probabilistic choice. The reduction theory will
restrict to `0 ≤ p ∧ p ≤ 1`. -/
abbrev Prob : Type := ℝ

/-- Untyped `qλ` terms, parameterized by a signature of closed quantum
primitives.  The default empty signature recovers the pure core language. -/
inductive Term (Prim : Type := PEmpty) where
  | var : Name → Term Prim
  | lam : Name → Term Prim → Term Prim
  | app : Term Prim → Term Prim → Term Prim
  /-- A closed primitive computation supplied by the semantic model. -/
  | prim : Prim → Term Prim
  /-- A recursive function value `let rec self arg = body`. -/
  | recLam : Name → Name → Term Prim → Term Prim
  /-- Probabilistic choice `M ⊕_p N`. -/
  | prob : Prob → Term Prim → Term Prim → Term Prim
  /-- Internal (demonic) choice `M ⊓ N`. -/
  | intern : Term Prim → Term Prim → Term Prim
  /-- External / interactive choice `M □ N`. -/
  | extern : Term Prim → Term Prim → Term Prim

open Term

/-- Names occurring free. -/
def free {Prim : Type} : Term Prim → List Name
  | .var x => [x]
  | .lam x M => (free M).filter (· ≠ x)
  | .app M N => free M ++ free N
  | .prim _ => []
  | .recLam self arg M =>
      ((free M).filter (· ≠ self)).filter (· ≠ arg)
  | .prob _ M N => free M ++ free N
  | .intern M N => free M ++ free N
  | .extern M N => free M ++ free N

/-- A term is syntactically closed when it has no free names. -/
def Closed {Prim : Type} (M : Term Prim) : Prop :=
  free M = []

theorem closed_iff_forall_not_mem {Prim : Type} {M : Term Prim} :
    Closed M ↔ ∀ x, x ∉ free M := by
  simp [Closed, List.eq_nil_iff_forall_not_mem]

/-- All names, free or bound (used only to pick a fresh rename). -/
def names {Prim : Type} : Term Prim → List Name
  | .var x => [x]
  | .lam x M => x :: names M
  | .app M N => names M ++ names N
  | .prim _ => []
  | .recLam self arg M => self :: arg :: names M
  | .prob _ M N => names M ++ names N
  | .intern M N => names M ++ names N
  | .extern M N => names M ++ names N

/-- Every free name occurs among all names of the term. -/
theorem mem_names_of_mem_free {Prim : Type} :
    ∀ {M : Term Prim} {x : Name}, x ∈ free M → x ∈ names M
  | .var _, _, h => by simpa [free, names] using h
  | .lam y M, x, h => by
      simp only [free, List.mem_filter] at h
      simp [names, mem_names_of_mem_free h.1]
  | .app M N, x, h => by
      simp only [free, List.mem_append] at h
      rcases h with h | h
      · simp [names, mem_names_of_mem_free h]
      · simp [names, mem_names_of_mem_free h]
  | .prim _, _, h => by simp [free] at h
  | .recLam self arg M, x, h => by
      simp only [free, List.mem_filter] at h
      simp [names, mem_names_of_mem_free h.1.1]
  | .prob _ M N, x, h => by
      simp only [free, List.mem_append] at h
      rcases h with h | h
      · simp [names, mem_names_of_mem_free h]
      · simp [names, mem_names_of_mem_free h]
  | .intern M N, x, h => by
      simp only [free, List.mem_append] at h
      rcases h with h | h
      · simp [names, mem_names_of_mem_free h]
      · simp [names, mem_names_of_mem_free h]
  | .extern M N, x, h => by
      simp only [free, List.mem_append] at h
      rcases h with h | h
      · simp [names, mem_names_of_mem_free h]
      · simp [names, mem_names_of_mem_free h]

/-- A name longer than the total length of all names in `avoid`. -/
def fresh (avoid : List Name) : Name :=
  String.replicate ((avoid.map String.length).sum + 1) 'x'

private theorem length_le_sum_lengths_of_mem {s : Name} :
    ∀ {xs : List Name}, s ∈ xs → s.length ≤ (xs.map String.length).sum
  | [], h => by simp at h
  | a :: xs, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · have ih := length_le_sum_lengths_of_mem h
        simp only [List.map_cons, List.sum_cons]
        omega

/-- The generated name is absent from the finite avoidance list. -/
@[simp]
theorem fresh_not_mem (avoid : List Name) : fresh avoid ∉ avoid := by
  intro h
  have hle := length_le_sum_lengths_of_mem h
  simp [fresh] at hle

/-- A generated fresh name differs from every member of its avoidance
list. -/
theorem fresh_ne_of_mem {avoid : List Name} {x : Name}
    (hx : x ∈ avoid) : fresh avoid ≠ x := by
  intro h
  apply fresh_not_mem avoid
  rw [h]
  exact hx

/-- Freshness transfers from an avoidance list to any list whose members
occur in it. -/
theorem fresh_not_mem_of_subset {avoid xs : List Name}
    (h : ∀ x, x ∈ xs → x ∈ avoid) : fresh avoid ∉ xs := by
  intro hx
  exact fresh_not_mem avoid (h _ hx)

/-- Rename free occurrences of `x` to `y`. -/
def rename {Prim : Type} (x y : Name) : Term Prim → Term Prim
  | .var z => if z = x then .var y else .var z
  | .lam z M => if z = x then .lam z M else .lam z (rename x y M)
  | .app M N => .app (rename x y M) (rename x y N)
  | .prim p => .prim p
  | .recLam self arg M =>
      if self = x ∨ arg = x then .recLam self arg M
      else .recLam self arg (rename x y M)
  | .prob p M N => .prob p (rename x y M) (rename x y N)
  | .intern M N => .intern (rename x y M) (rename x y N)
  | .extern M N => .extern (rename x y M) (rename x y N)

/-- Constructor count (names ignored), so renaming is size-invariant. -/
def termSize {Prim : Type} : Term Prim → ℕ
  | .var _ => 1
  | .lam _ M => termSize M + 1
  | .app M N => termSize M + termSize N + 1
  | .prim _ => 1
  | .recLam _ _ M => termSize M + 1
  | .prob _ M N => termSize M + termSize N + 1
  | .intern M N => termSize M + termSize N + 1
  | .extern M N => termSize M + termSize N + 1

@[simp] theorem rename_termSize {Prim : Type} (x y : Name) :
    ∀ M : Term Prim, termSize (rename x y M) = termSize M
  | .var z => by simp [rename, termSize]; split <;> simp [termSize]
  | .lam z M => by simp [rename, termSize]; split <;> simp [termSize, rename_termSize]
  | .app M N => by simp [rename, termSize, rename_termSize]
  | .prim p => by simp [rename, termSize]
  | .recLam self arg M => by
      simp [rename, termSize]
      split <;> simp [termSize, rename_termSize]
  | .prob p M N => by simp [rename, termSize, rename_termSize]
  | .intern M N => by simp [rename, termSize, rename_termSize]
  | .extern M N => by simp [rename, termSize, rename_termSize]

/-- The body produced by the two-stage recursive-binder renaming in
`subst` has the same constructor count as the original body. -/
theorem recLam_subst_body_termSize {Prim : Type}
    (self arg x : Name) (s M : Term Prim) :
    let avoid := self :: arg :: x :: free s ++ free M ++ names s ++ names M
    let self' := if self ∈ free s then fresh avoid else self
    let M' := if self' = self then M else rename self self' M
    let avoid' := self' :: avoid ++ names M'
    let arg' := if arg ∈ free s then fresh avoid' else arg
    let M'' := if arg' = arg then M' else rename arg arg' M'
    termSize M'' = termSize M := by
  let avoid := self :: arg :: x :: free s ++ free M ++ names s ++ names M
  let self' := if self ∈ free s then fresh avoid else self
  let M' := if self' = self then M else rename self self' M
  let avoid' := self' :: avoid ++ names M'
  let arg' := if arg ∈ free s then fresh avoid' else arg
  let M'' := if arg' = arg then M' else rename arg arg' M'
  change termSize M'' = termSize M
  have hM' : termSize M' = termSize M := by
    dsimp [M']
    split <;> simp
  dsimp [M'']
  split
  · exact hM'
  · rw [rename_termSize, hM']

/-- Capture-avoiding substitution. -/
def subst {Prim : Type} (x : Name) (s : Term Prim) : Term Prim → Term Prim
  | .var y => if y = x then s else .var y
  | .lam y M =>
    if y = x then .lam y M
    else if y ∈ free s then
      let y' := fresh (y :: x :: free s ++ free M ++ names s ++ names M)
      .lam y' (subst x s (rename y y' M))
    else
      .lam y (subst x s M)
  | .app M N => .app (subst x s M) (subst x s N)
  | .prim p => .prim p
  | .recLam self arg M =>
    if self = x ∨ arg = x then
      .recLam self arg M
    else if self = arg then
      if self ∈ free s then
        let z := fresh
          (self :: x :: free s ++ free M ++ names s ++ names M)
        .recLam z z (subst x s (rename self z M))
      else
        .recLam self arg (subst x s M)
    else
      let avoid := self :: arg :: x :: free s ++ free M ++ names s ++ names M
      let self' := if self ∈ free s then fresh avoid else self
      let M' := if self' = self then M else rename self self' M
      let avoid' := self' :: avoid ++ names M'
      let arg' := if arg ∈ free s then fresh avoid' else arg
      let M'' := if arg' = arg then M' else rename arg arg' M'
      have hM' : termSize M' = termSize M := by
        dsimp [M']
        split <;> simp
      have hM'' : termSize M'' = termSize M := by
        dsimp [M'']
        split
        · exact hM'
        · rw [rename_termSize, hM']
      .recLam self' arg' (subst x s M'')
  | .prob p M N => .prob p (subst x s M) (subst x s N)
  | .intern M N => .intern (subst x s M) (subst x s N)
  | .extern M N => .extern (subst x s M) (subst x s N)
termination_by t => termSize t
decreasing_by
  all_goals
    first
    | omega
    | (change termSize M'' < termSize M + 1; omega)
    | (simp [termSize, rename_termSize] <;> omega)

end QLambda
