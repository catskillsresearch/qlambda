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

/-- Capture-avoiding substitution. -/
def subst (_x : Name) (_s : Term) : Term → Term := by
  sorry

end QLambda
