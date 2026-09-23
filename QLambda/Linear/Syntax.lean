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

/-- Shift free type variables by `d` at or above `cutoff`. -/
def shift (d cutoff : Nat) : Ty → Ty
  | .var i => .var (if i < cutoff then i else i + d)
  | .unit => .unit
  | .bit => .bit
  | .qubit => .qubit
  | .tensor A B => .tensor (shift d cutoff A) (shift d cutoff B)
  | .arrow κ A B => .arrow κ (shift d cutoff A) (shift d cutoff B)
  | .mu A => .mu (shift d (cutoff + 1) A)

/-- Lift free type variables at or above `n` by one. -/
abbrev lift (n : Nat) : Ty → Ty :=
  shift 1 n

/-- Substitute `σ` for type variable `n`, lowering variables above it. -/
def subst (n : Nat) (σ : Ty) : Ty → Ty
  | .var i =>
      if i < n then .var i
      else if i = n then shift n 0 σ
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

theorem subst_avoids_capture :
    subst 0 (.var 0) (.mu (.var 1)) = .mu (.var 1) := by
  rfl

/-- Duplicability relative to recursive type variables. Free variables are
conservatively nonduplicable; `mu` assumes its own recursive occurrence is
duplicable and rejects any quantum component in the body. -/
def duplicableAt (κ : List Bool) : Ty → Bool
  | .var i => κ[i]?.getD false
  | .unit => true
  | .bit => true
  | .qubit => false
  | .tensor A B => duplicableAt κ A && duplicableAt κ B
  | .arrow .lin _ _ => false
  | .arrow .unres _ _ => true
  | .mu A => duplicableAt (true :: κ) A

/-- Closed types whose values may be copied and discarded.

An unrestricted function is duplicable because its typing rule forbids a
linear capture. A linear function is not duplicable in general. -/
def duplicable : Ty → Bool :=
  duplicableAt []

/-- Types which may cross the staging boundary into a first-order circuit
and which currently have representable presheaf objects. -/
inductive FirstOrder : Ty → Prop where
  | unit : FirstOrder .unit
  | bit : FirstOrder .bit
  | qubit : FirstOrder .qubit
  | tensor {A B} : FirstOrder A → FirstOrder B → FirstOrder (.tensor A B)

def firstOrderB : Ty → Bool
  | .unit | .bit | .qubit => true
  | .tensor A B => firstOrderB A && firstOrderB B
  | _ => false

theorem firstOrderB_eq {A : Ty} (h : FirstOrder A) : A.firstOrderB = true := by
  induction h with
  | unit => rfl
  | bit => rfl
  | qubit => rfl
  | tensor hA hB ihA ihB => simp [firstOrderB, ihA, ihB]

theorem firstOrderB_sound {A : Ty} (h : A.firstOrderB = true) :
    FirstOrder A := by
  induction A with
  | unit => exact .unit
  | bit => exact .bit
  | qubit => exact .qubit
  | tensor A B ihA ihB =>
      simp only [firstOrderB, Bool.and_eq_true] at h
      exact .tensor (ihA h.1) (ihB h.2)
  | var n => simp [firstOrderB] at h
  | arrow κ A B => simp [firstOrderB] at h
  | mu A => simp [firstOrderB] at h

/-- Hilbert dimension of a first-order type.  Arrows and recursive types are
mapped to `0` and are not used as objects.  Bits and qubits are both
two-dimensional; their later additive versus linear distinction is not
recorded here. -/
def hilbertDim : Ty → ℕ
  | .unit => 1
  | .bit | .qubit => 2
  | .tensor A B => A.hilbertDim * B.hilbertDim
  | _ => 0

def FirstOrder.dimension {A : Ty} (_h : FirstOrder A) : ℕ :=
  A.hilbertDim

@[simp]
theorem FirstOrder.dimension_unit : FirstOrder.dimension .unit = 1 :=
  rfl

@[simp]
theorem FirstOrder.dimension_bit : FirstOrder.dimension .bit = 2 :=
  rfl

@[simp]
theorem FirstOrder.dimension_qubit : FirstOrder.dimension .qubit = 2 :=
  rfl

@[simp]
theorem FirstOrder.dimension_tensor {A B : Ty}
    (hA : FirstOrder A) (hB : FirstOrder B) :
    FirstOrder.dimension (.tensor hA hB) =
      hA.dimension * hB.dimension :=
  rfl

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
