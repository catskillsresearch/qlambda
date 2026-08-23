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

/-- Untyped `qλ` terms. -/
inductive Term where
  | var : Name → Term
  | lam : Name → Term → Term
  | app : Term → Term → Term
  /-- Probabilistic choice `M ⊕_p N`. -/
  | prob : Prob → Term → Term → Term
  /-- Internal (demonic) choice `M ⊓ N`. -/
  | intern : Term → Term → Term
  /-- External / interactive choice `M □ N`. -/
  | extern : Term → Term → Term

open Term

/-- Names occurring free. -/
def free : Term → List Name
  | .var x => [x]
  | .lam x M => (free M).filter (· ≠ x)
  | .app M N => free M ++ free N
  | .prob _ M N => free M ++ free N
  | .intern M N => free M ++ free N
  | .extern M N => free M ++ free N

/-- All names, free or bound (used only to pick a fresh rename). -/
def names : Term → List Name
  | .var x => [x]
  | .lam x M => x :: names M
  | .app M N => names M ++ names N
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
def rename (x y : Name) : Term → Term
  | .var z => if z = x then .var y else .var z
  | .lam z M => if z = x then .lam z M else .lam z (rename x y M)
  | .app M N => .app (rename x y M) (rename x y N)
  | .prob p M N => .prob p (rename x y M) (rename x y N)
  | .intern M N => .intern (rename x y M) (rename x y N)
  | .extern M N => .extern (rename x y M) (rename x y N)

/-- Constructor count (names ignored), so renaming is size-invariant. -/
def termSize : Term → ℕ
  | .var _ => 1
  | .lam _ M => termSize M + 1
  | .app M N => termSize M + termSize N + 1
  | .prob _ M N => termSize M + termSize N + 1
  | .intern M N => termSize M + termSize N + 1
  | .extern M N => termSize M + termSize N + 1

@[simp] theorem rename_termSize (x y : Name) : ∀ M, termSize (rename x y M) = termSize M
  | .var z => by simp [rename, termSize]; split <;> simp [termSize]
  | .lam z M => by simp [rename, termSize]; split <;> simp [termSize, rename_termSize]
  | .app M N => by simp [rename, termSize, rename_termSize]
  | .prob p M N => by simp [rename, termSize, rename_termSize]
  | .intern M N => by simp [rename, termSize, rename_termSize]
  | .extern M N => by simp [rename, termSize, rename_termSize]

/-- Capture-avoiding substitution. -/
def subst (x : Name) (s : Term) : Term → Term
  | .var y => if y = x then s else .var y
  | .lam y M =>
    if y = x then .lam y M
    else if y ∈ free s then
      let y' := fresh (y :: x :: free s ++ free M ++ names s ++ names M)
      .lam y' (subst x s (rename y y' M))
    else
      .lam y (subst x s M)
  | .app M N => .app (subst x s M) (subst x s N)
  | .prob p M N => .prob p (subst x s M) (subst x s N)
  | .intern M N => .intern (subst x s M) (subst x s N)
  | .extern M N => .extern (subst x s M) (subst x s N)
termination_by t => termSize t
decreasing_by
  all_goals (simp [termSize, rename_termSize]; try omega)

end QLambda
