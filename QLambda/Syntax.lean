/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Data.Real.Basic

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

/-- A name not in `avoid`. Pigeonhole on `x0, …, x_{length}` against a finite list. -/
def fresh (avoid : List Name) : Name :=
  let rec go (n fuel : ℕ) : Name :=
    match fuel with
    | 0 => s!"x{n}"
    | fuel + 1 =>
      let cand : Name := s!"x{n}"
      if cand ∈ avoid then go (n + 1) fuel else cand
  go 0 (avoid.length + 1)

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
