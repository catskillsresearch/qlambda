/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Data.Rat.Defs

/-!
# Typed linear quantum λ-calculus

Church-style linear/nonlinear λ-calculus. Lambda is the only binder.
There is no `emit`, sequencing operator, probabilistic choice, internal
choice, or external choice.

* `lam lin A M` is `λ¹(x : A). M`, binding de Bruijn index `0` in the linear context.
* `lam unres A M` is `λω(x : A). M`, binding de Bruijn index `0` in the unrestricted context.
* A tensor is eliminated by a curried linear continuation.
* Measurement consumes a qubit and passes its classical bit unrestricted and its
  post-measurement qubit linear to a continuation.
* Probability is not a term constructor. It arises only when measurement is interpreted.
-/

namespace QLambda.Linear

/-- `lin` is exactly-once use. `unres` is ordinary λ-calculus use. -/
inductive Mode where
  | lin
  | unres
  deriving DecidableEq, Repr

/-- Types. `mu A` binds de Bruijn type variable `0` in `A`. -/
inductive Ty where
  | var : Nat → Ty
  | unit
  | bit
  | qubit
  | tensor : Ty → Ty → Ty
  | arrow : Mode → Ty → Ty → Ty
  | mu : Ty → Ty
  deriving DecidableEq, Repr

namespace Ty

/-- Lift free type variables at or above `n`. -/
def lift (n : Nat) : Ty → Ty
  | .var i => .var (if i < n then i else i + 1)
  | .unit => .unit
  | .bit => .bit
  | .qubit => .qubit
  | .tensor A B => .tensor (lift n A) (lift n B)
  | .arrow κ A B => .arrow κ (lift n A) (lift n B)
  | .mu A => .mu (lift (n + 1) A)

/-- Substitute `σ` for type variable `n`, lowering variables above it. -/
def subst (n : Nat) (σ : Ty) : Ty → Ty
  | .var i =>
      if i < n then .var i
      else if i = n then lift n σ
      else .var (i - 1)
  | .unit => .unit
  | .bit => .bit
  | .qubit => .qubit
  | .tensor A B => .tensor (subst n σ A) (subst n σ B)
  | .arrow κ A B => .arrow κ (subst n σ A) (subst n σ B)
  | .mu A => .mu (subst (n + 1) σ A)

/-- Unfold `μα. A` once: `A[μα. A / α]`. -/
def unfoldMu (A : Ty) : Ty :=
  subst 0 (.mu A) A

/-- Types whose values may be copied and discarded.

An unrestricted function is duplicable because its typing rule forbids a
linear capture. A linear function is not duplicable in general. -/
def duplicable : Ty → Bool
  | .var _ => true
  | .unit => true
  | .bit => true
  | .qubit => false
  | .tensor A B => duplicable A && duplicable B
  | .arrow .lin _ _ => false
  | .arrow .unres _ _ => true
  | .mu A => duplicable A

end Ty

/-- Gate and allocation constants. Measurement is its own elimination form. -/
inductive Prim where
  | new0
  | x
  | h
  | t
  | ry : ℚ → Prim
  | cx
  | reset
  deriving DecidableEq, Repr

/-- Type of a primitive as a linear function. -/
def primTy : Prim → Ty
  | .new0 => .arrow .lin .unit .qubit
  | .x => .arrow .lin .qubit .qubit
  | .h => .arrow .lin .qubit .qubit
  | .t => .arrow .lin .qubit .qubit
  | .ry _ => .arrow .lin .qubit .qubit
  | .cx => .arrow .lin .qubit (.arrow .lin .qubit (.tensor .qubit .qubit))
  | .reset => .arrow .lin .qubit .qubit

/-- Annotated terms. Variable indices are de Bruijn indices in the context of their mode. -/
inductive Term where
  | var : Mode → Nat → Term
  | lam : Mode → Ty → Term → Term
  | app : Term → Term → Term
  | unit
  | bitLit : Bool → Term
  | pair : Term → Term → Term
  | unpair : Term → Term → Term
  | ite : Term → Term → Term → Term
  | prim : Prim → Term
  | measure : Term → Term → Term
  | fix : Ty → Term → Term
  | fold : Ty → Term → Term
  | unfold : Term → Term
  deriving DecidableEq, Repr

namespace Term

/-- Source values for call-by-value. Qubits are not closed values; they are wires. -/
inductive Value : Term → Prop where
  | unit : Value .unit
  | bitLit {b} : Value (.bitLit b)
  | lam {κ A M} : Value (.lam κ A M)
  | pair {M N} : Value M → Value N → Value (.pair M N)
  | prim {p} : Value (.prim p)
  | fold {A M} : Value M → Value (.fold A M)

end Term

end QLambda.Linear
