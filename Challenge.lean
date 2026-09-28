/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import Mathlib.Basic.Real.Basic

@[expose] public section

/-!
# Palomar statement surface for the typed linear quantum λ-calculus

This file depends only on Mathlib. It restates the source syntax, typing
judgment, call-by-value reduction, the finite circuit normal form, and the
canonical two-wire quotation exactly as they are defined in the `QLambda`
development, and states the compared theorems as holes. The runtime,
relation, presheaf, staging, and OpenQASM carriers are definition holes.
`Solution.lean` proves the same statements from the development.

* `source_type_safety`: a closed well-typed term is a value, takes a
  classical step, or is blocked at a quantum primitive; classical steps are
  deterministic, and classical and measurement steps preserve its type.
* `quotation_capstone`: every `Quotable` command in the supported two-qubit,
  one-bit fragment has a canonical source term of `quotationTy` whose
  compilation is that command.
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

namespace QLambda.Linear.Ty

/-- Proof-level scoping judgment for type variables. -/
def WellScopedAt : Nat → Ty → Prop
  | n, .var i => i < n
  | _, .unit => True
  | _, .bit => True
  | _, .qubit => True
  | n, .tensor A B => WellScopedAt n A ∧ WellScopedAt n B
  | n, .arrow _ A B => WellScopedAt n A ∧ WellScopedAt n B
  | n, .mu A => WellScopedAt (n + 1) A

/-- The type variable selected by `target` does not occur in the type. -/
def DoesNotContainAt : Nat → Ty → Prop
  | target, .var i => i ≠ target
  | _, .unit => True
  | _, .bit => True
  | _, .qubit => True
  | target, .tensor A B =>
      DoesNotContainAt target A ∧ DoesNotContainAt target B
  | target, .arrow _ A B =>
      DoesNotContainAt target A ∧ DoesNotContainAt target B
  | target, .mu A => DoesNotContainAt (target + 1) A

/-- Strict positivity of the selected recursive variable: it may occur in
products and function codomains, but not in function domains. -/
def StrictlyPositiveAt : Nat → Ty → Prop
  | _, .var _ => True
  | _, .unit => True
  | _, .bit => True
  | _, .qubit => True
  | target, .tensor A B =>
      StrictlyPositiveAt target A ∧ StrictlyPositiveAt target B
  | target, .arrow _ A B =>
      DoesNotContainAt target A ∧ StrictlyPositiveAt target B
  | target, .mu A => StrictlyPositiveAt (target + 1) A

/-- Every recursive body in a type is strictly positive in its own binder. -/
def PositiveRec : Ty → Prop
  | .mu A => StrictlyPositiveAt 0 A ∧ PositiveRec A
  | .var _ => True
  | .unit => True
  | .bit => True
  | .qubit => True
  | .tensor A B => PositiveRec A ∧ PositiveRec B
  | .arrow _ A B => PositiveRec A ∧ PositiveRec B

/-- A type is admissible at depth `n` when it is scoped there and every
recursive body in it is strictly positive. -/
def AdmissibleAt (n : Nat) (A : Ty) : Prop :=
  WellScopedAt n A ∧ PositiveRec A

/-- Closed, admissible types. -/
abbrev Admissible (A : Ty) : Prop :=
  AdmissibleAt 0 A

/-- Duplicability relative to recursive type variables: qubits and linear
functions are not duplicable; free variables are duplicable only when marked. -/
def DuplicableAt : List Bool → Ty → Prop
  | κ, .var i => κ[i]? = some true
  | _, .unit => True
  | _, .bit => True
  | _, .qubit => False
  | κ, .tensor A B => DuplicableAt κ A ∧ DuplicableAt κ B
  | _, .arrow .lin _ _ => False
  | _, .arrow .unres _ _ => True
  | κ, .mu A => DuplicableAt (true :: κ) A

/-- Closed types whose values may be copied and discarded. -/
abbrev Duplicable (A : Ty) : Prop :=
  DuplicableAt [] A

end QLambda.Linear.Ty

namespace QLambda.Linear

/-- Positional lookup in a context. -/
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

/-- `HasType Γ Δ M A`: `M` has type `A`, uses exactly the occupied cells of
the linear context `Δ`, and may use the unrestricted context `Γ` freely. -/
inductive HasType : List Ty → List (Option Ty) → Term → Ty → Prop where
  | varU {Γ Δ n A} :
      Lookup Γ n A → Ty.Duplicable A → AllNone Δ →
      HasType Γ Δ (.var .unres n) A
  | varL {Γ Δ n A} :
      Lookup Δ n (some A) → OnlySomeAt Δ n → HasType Γ Δ (.var .lin n) A
  | lamU {Γ Δ A B M} :
      Ty.Admissible A →
      Ty.Duplicable A →
      AllNone Δ →
      HasType (A :: Γ) Δ M B →
      HasType Γ Δ (.lam .unres A M) (.arrow .unres A B)
  | lamL {Γ Δ A B M} :
      Ty.Admissible A →
      HasType Γ (some A :: Δ) M B →
      HasType Γ Δ (.lam .lin A M) (.arrow .lin A B)
  | appL {Γ Δ Δ₁ Δ₂ A B F X} :
      OSplit Δ Δ₁ Δ₂ →
      HasType Γ Δ₁ F (.arrow .lin A B) →
      HasType Γ Δ₂ X A →
      HasType Γ Δ (.app F X) B
  | appU {Γ Δ ΔF ΔX A B F X} :
      OSplit Δ ΔF ΔX →
      AllNone ΔX →
      HasType Γ ΔF F (.arrow .unres A B) →
      HasType Γ ΔX X A →
      HasType Γ Δ (.app F X) B
  | unit {Γ Δ} : AllNone Δ → HasType Γ Δ .unit .unit
  | bitLit {Γ Δ b} : AllNone Δ → HasType Γ Δ (.bitLit b) .bit
  | pair {Γ Δ Δ₁ Δ₂ A B M N} :
      OSplit Δ Δ₁ Δ₂ →
      HasType Γ Δ₁ M A →
      HasType Γ Δ₂ N B →
      HasType Γ Δ (.pair M N) (.tensor A B)
  | unpair {Γ Δ Δ₁ Δ₂ A B C M K} :
      OSplit Δ Δ₁ Δ₂ →
      HasType Γ Δ₁ M (.tensor A B) →
      HasType Γ Δ₂ K (.arrow .lin A (.arrow .lin B C)) →
      HasType Γ Δ (.unpair M K) C
  | ite {Γ Δ Δ₁ Δ₂ A B T E} :
      OSplit Δ Δ₁ Δ₂ →
      HasType Γ Δ₁ B .bit →
      HasType Γ Δ₂ T A →
      HasType Γ Δ₂ E A →
      HasType Γ Δ (.ite B T E) A
  | prim {Γ Δ p} : AllNone Δ → HasType Γ Δ (.prim p) (primTy p)
  | measure {Γ Δ Δ₁ Δ₂ A Q K} :
      OSplit Δ Δ₁ Δ₂ →
      HasType Γ Δ₁ Q .qubit →
      HasType Γ Δ₂ K (.arrow .unres .bit (.arrow .lin .qubit A)) →
      HasType Γ Δ (.measure Q K) A
  | fix {Γ Δ A M} :
      Ty.Admissible A →
      Ty.Duplicable A →
      AllNone Δ →
      HasType Γ Δ M (.arrow .unres A A) →
      HasType Γ Δ (.fix A M) A
  | fold {Γ Δ A M} :
      Ty.Admissible (.mu A) →
      HasType Γ Δ M (Ty.subst 0 (.mu A) A) →
      HasType Γ Δ (.fold A M) (.mu A)
  | unfold {Γ Δ A M} :
      Ty.Admissible (.mu A) →
      HasType Γ Δ M (.mu A) →
      HasType Γ Δ (.unfold M) (Ty.subst 0 (.mu A) A)

namespace Term

/-- Both de Bruijn namespaces are locally scoped. -/
def Scoped (linearDepth unresDepth : Nat) : Term → Prop
  | .var .lin i => i < linearDepth
  | .var .unres i => i < unresDepth
  | .lam .lin _ M => Scoped (linearDepth + 1) unresDepth M
  | .lam .unres _ M => Scoped linearDepth (unresDepth + 1) M
  | .app F X => Scoped linearDepth unresDepth F ∧ Scoped linearDepth unresDepth X
  | .unit => True
  | .bitLit _ => True
  | .pair M N => Scoped linearDepth unresDepth M ∧ Scoped linearDepth unresDepth N
  | .unpair M K => Scoped linearDepth unresDepth M ∧ Scoped linearDepth unresDepth K
  | .ite B T E =>
      Scoped linearDepth unresDepth B ∧
      Scoped linearDepth unresDepth T ∧ Scoped linearDepth unresDepth E
  | .prim _ => True
  | .measure Q K => Scoped linearDepth unresDepth Q ∧ Scoped linearDepth unresDepth K
  | .fix _ M => Scoped linearDepth unresDepth M
  | .fold _ M => Scoped linearDepth unresDepth M
  | .unfold M => Scoped linearDepth unresDepth M

/-- Shift linear de Bruijn indices at or above `cutoff` by `d`. -/
def shiftLin (d cutoff : Nat) : Term → Term
  | .var .lin i => .var .lin (if i < cutoff then i else i + d)
  | .var .unres i => .var .unres i
  | .lam .lin A M => .lam .lin A (shiftLin d (cutoff + 1) M)
  | .lam .unres A M => .lam .unres A (shiftLin d cutoff M)
  | .app F X => .app (shiftLin d cutoff F) (shiftLin d cutoff X)
  | .unit => .unit
  | .bitLit b => .bitLit b
  | .pair M N => .pair (shiftLin d cutoff M) (shiftLin d cutoff N)
  | .unpair M K => .unpair (shiftLin d cutoff M) (shiftLin d cutoff K)
  | .ite B T E =>
      .ite (shiftLin d cutoff B) (shiftLin d cutoff T) (shiftLin d cutoff E)
  | .prim p => .prim p
  | .measure Q K => .measure (shiftLin d cutoff Q) (shiftLin d cutoff K)
  | .fix A M => .fix A (shiftLin d cutoff M)
  | .fold A M => .fold A (shiftLin d cutoff M)
  | .unfold M => .unfold (shiftLin d cutoff M)

/-- Shift unrestricted de Bruijn indices at or above `cutoff` by `d`. -/
def shiftUnres (d cutoff : Nat) : Term → Term
  | .var .unres i => .var .unres (if i < cutoff then i else i + d)
  | .var .lin i => .var .lin i
  | .lam .unres A M => .lam .unres A (shiftUnres d (cutoff + 1) M)
  | .lam .lin A M => .lam .lin A (shiftUnres d cutoff M)
  | .app F X => .app (shiftUnres d cutoff F) (shiftUnres d cutoff X)
  | .unit => .unit
  | .bitLit b => .bitLit b
  | .pair M N => .pair (shiftUnres d cutoff M) (shiftUnres d cutoff N)
  | .unpair M K => .unpair (shiftUnres d cutoff M) (shiftUnres d cutoff K)
  | .ite B T E =>
      .ite (shiftUnres d cutoff B) (shiftUnres d cutoff T) (shiftUnres d cutoff E)
  | .prim p => .prim p
  | .measure Q K => .measure (shiftUnres d cutoff Q) (shiftUnres d cutoff K)
  | .fix A M => .fix A (shiftUnres d cutoff M)
  | .fold A M => .fold A (shiftUnres d cutoff M)
  | .unfold M => .unfold (shiftUnres d cutoff M)

/-- Replace linear de Bruijn index `k`. Indices above `k` decrease. -/
def substLin (k : Nat) (v : Term) : Term → Term
  | .var .lin i =>
      if i < k then .var .lin i
      else if i = k then shiftLin k 0 v
      else .var .lin (i - 1)
  | .var .unres i => .var .unres i
  | .lam .lin A M => .lam .lin A (substLin (k + 1) v M)
  | .lam .unres A M =>
      .lam .unres A (substLin k (shiftUnres 1 0 v) M)
  | .app F X => .app (substLin k v F) (substLin k v X)
  | .unit => .unit
  | .bitLit b => .bitLit b
  | .pair M N => .pair (substLin k v M) (substLin k v N)
  | .unpair M K => .unpair (substLin k v M) (substLin k v K)
  | .ite B T E => .ite (substLin k v B) (substLin k v T) (substLin k v E)
  | .prim p => .prim p
  | .measure Q K => .measure (substLin k v Q) (substLin k v K)
  | .fix A M => .fix A (substLin k v M)
  | .fold A M => .fold A (substLin k v M)
  | .unfold M => .unfold (substLin k v M)

/-- Replace unrestricted de Bruijn index `k`. -/
def substUnres (k : Nat) (v : Term) : Term → Term
  | .var .unres i =>
      if i < k then .var .unres i
      else if i = k then shiftUnres k 0 v
      else .var .unres (i - 1)
  | .var .lin i => .var .lin i
  | .lam .unres A M => .lam .unres A (substUnres (k + 1) v M)
  | .lam .lin A M =>
      .lam .lin A (substUnres k (shiftLin 1 0 v) M)
  | .app F X => .app (substUnres k v F) (substUnres k v X)
  | .unit => .unit
  | .bitLit b => .bitLit b
  | .pair M N => .pair (substUnres k v M) (substUnres k v N)
  | .unpair M K => .unpair (substUnres k v M) (substUnres k v K)
  | .ite B T E => .ite (substUnres k v B) (substUnres k v T) (substUnres k v E)
  | .prim p => .prim p
  | .measure Q K => .measure (substUnres k v Q) (substUnres k v K)
  | .fix A M => .fix A (substUnres k v M)
  | .fold A M => .fold A (substUnres k v M)
  | .unfold M => .unfold (substUnres k v M)

end Term

open Term

/-- Classical call-by-value reduction. Quantum primitive applications are not
reduced by this relation; they are staged as circuit operations. -/
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
  | fixC {A M M'} : Step M M' → Step (.fix A M) (.fix A M')
  | foldC {A M M'} : Step M M' → Step (.fold A M) (.fold A M')
  | measureC {Q Q' K} : Step Q Q' → Step (.measure Q K) (.measure Q' K)

/-- Measurement branches. `Q` is returned with the bit, so the qubit is not discarded. -/
inductive MeasStep : Term → Bool → Term → Prop where
  | branch {Q K b} :
      Value Q →
      MeasStep (.measure Q K) b (.app (.app K (.bitLit b)) Q)

/-- A source evaluation context has reached a quantum primitive.  The staging
or machine layer, rather than classical β-reduction, handles this case. -/
inductive QuantumBlocked : Term → Prop where
  | primApp {p V} : Value V → QuantumBlocked (.app (.prim p) V)
  | measure {Q K} : Value Q → QuantumBlocked (.measure Q K)
  | appF {F X} : QuantumBlocked F → QuantumBlocked (.app F X)
  | appX {V X} : Value V → QuantumBlocked X → QuantumBlocked (.app V X)
  | iteC {B T E} : QuantumBlocked B → QuantumBlocked (.ite B T E)
  | unpairC {M K} : QuantumBlocked M → QuantumBlocked (.unpair M K)
  | pairL {M N} : QuantumBlocked M → QuantumBlocked (.pair M N)
  | pairR {V N} : Value V → QuantumBlocked N → QuantumBlocked (.pair V N)
  | unfoldC {M} : QuantumBlocked M → QuantumBlocked (.unfold M)
  | fixC {A M} : QuantumBlocked M → QuantumBlocked (.fix A M)
  | foldC {A M} : QuantumBlocked M → QuantumBlocked (.fold A M)
  | measureC {Q K} : QuantumBlocked Q → QuantumBlocked (.measure Q K)

/-- A term is a value, takes a classical step, or is quantum-blocked. -/
def MakesProgress (M : Term) : Prop :=
  Value M ∨ (∃ N, Step M N) ∨ QuantumBlocked M

end QLambda.Linear

namespace QLambda

namespace Composer

/-- Classical Boolean expressions over the fixed classical register. -/
inductive CExpr (c : ℕ) where
  | lit : Bool → CExpr c
  | bit : Fin c → CExpr c
  | not : CExpr c → CExpr c
  | and : CExpr c → CExpr c → CExpr c
  | or : CExpr c → CExpr c → CExpr c
  | xor : CExpr c → CExpr c → CExpr c

/-- Exactly serializable probability used by the physical compiler. -/
structure Probability where
  val : ℚ
  nonneg : 0 ≤ val
  le_one : val ≤ 1

/-- Typed angle expressions admitted by the normalized circuit target. -/
inductive AngleExpr where
  | rational : ℚ → AngleExpr
  /-- `2 * acos (sqrt p)`, so RY followed by Z measurement returns zero
  with probability `p`. -/
  | coin : Probability → AngleExpr

end Composer

end QLambda

namespace QLambda.Linear

/-- First-order circuit normal form on `q` qubits and `c` classical bits. -/
inductive Command (q c : ℕ) where
  | skip
  | x : Fin q → Command q c
  | h : Fin q → Command q c
  | t : Fin q → Command q c
  | ry : Composer.AngleExpr → Fin q → Command q c
  | cx : Fin q → Fin q → Command q c
  | measure : Fin q → Fin c → Command q c
  | reset : Fin q → Command q c
  | store : Fin c → Composer.CExpr c → Command q c
  | seq : Command q c → Command q c → Command q c
  | branch : Composer.CExpr c → Command q c → Command q c → Command q c

namespace Command

namespace GeneralQuotation

/-- The declared finite register sizes of this quotation. -/
abbrev quantumSize : Nat := 2
abbrev classicalSize : Nat := 1

/-- The two-qubit register type. -/
def qubitRegisterTy : Ty :=
  .tensor .qubit .qubit

/-- The register together with the classical bit. -/
def resultTy : Ty :=
  .tensor qubitRegisterTy .bit

/-- Curried source type for the fixed `2 × 1` register:
`Bit →ω Qubit →¹ Qubit →¹ ((Qubit ⊗ Qubit) ⊗ Bit)`. -/
def quotationTy : Ty :=
  .arrow .unres .bit <|
    .arrow .lin .qubit <|
      .arrow .lin .qubit resultTy

/-- Exactly the target angles represented by source `Prim.ry`. -/
inductive AngleQuotable : Composer.AngleExpr → Prop where
  | rational (r : ℚ) : AngleQuotable (.rational r)

/-- Exact `Command 2 1` fragment represented by the quotation. -/
inductive Quotable : Command quantumSize classicalSize → Prop where
  | skip : Quotable .skip
  | x {w} : Quotable (.x w)
  | h {w} : Quotable (.h w)
  | t {w} : Quotable (.t w)
  | ry {θ w} : AngleQuotable θ → Quotable (.ry θ w)
  | cx {control target} :
      control ≠ target → Quotable (.cx control target)
  | measure {qbit cbit} : Quotable (.measure qbit cbit)
  | reset {qbit} : Quotable (.reset qbit)
  | store {cbit e} : Quotable (.store cbit e)
  | seq {A B} : Quotable A → Quotable B → Quotable (.seq A B)
  | branch {guard yes no} :
      Quotable yes → Quotable no → Quotable (.branch guard yes no)

/-- Interpret the sole classical register cell as a pure source bit term. -/
def quoteCExpr (current : Term) : Composer.CExpr classicalSize → Term
  | .lit b => .bitLit b
  | .bit _ => current
  | .not e => .ite (quoteCExpr current e) (.bitLit false) (.bitLit true)
  | .and e₁ e₂ =>
      .ite (quoteCExpr current e₁) (quoteCExpr current e₂) (.bitLit false)
  | .or e₁ e₂ =>
      .ite (quoteCExpr current e₁) (.bitLit true) (quoteCExpr current e₂)
  | .xor e₁ e₂ =>
      .ite (quoteCExpr current e₁)
        (.ite (quoteCExpr current e₂) (.bitLit false) (.bitLit true))
        (quoteCExpr current e₂)

/-- Apply a unary source primitive to one component of a two-qubit tensor. -/
def unaryRegister (p : Prim) (w : Fin quantumSize) : Term :=
  .lam .lin qubitRegisterTy <|
    .unpair (.var .lin 0) <|
      .lam .lin .qubit <|
        .lam .lin .qubit <|
          if w = 0 then
            .pair (.app (.prim p) (.var .lin 1)) (.var .lin 0)
          else
            .pair (.var .lin 1) (.app (.prim p) (.var .lin 0))

/-- Apply `cx`, restoring canonical register order in the reverse orientation. -/
def cxRegister (control target : Fin quantumSize) : Term :=
  .lam .lin qubitRegisterTy <|
    .unpair (.var .lin 0) <|
      .lam .lin .qubit <|
        .lam .lin .qubit <|
          if control = target then
            .pair (.var .lin 1) (.var .lin 0)
          else if control = 0 then
            .app (.app (.prim .cx) (.var .lin 1)) (.var .lin 0)
          else
            .unpair
              (.app (.app (.prim .cx) (.var .lin 0)) (.var .lin 1))
              (.lam .lin .qubit <|
                .lam .lin .qubit <|
                  .pair (.var .lin 0) (.var .lin 1))

/-- Bind the transformed register as the new linear register variable. -/
def bindRegister (next body : Term) : Term :=
  .app (.lam .lin qubitRegisterTy body) next

/-- Continue with the current classical value and a rebuilt register. -/
def continueWith (k : Term → Term) (current register : Term) : Term :=
  bindRegister register (k current)

/-- Measurement of either wire.  The measurement continuation is linearly
closed and returns a function waiting for the untouched wire. -/
def measureRegister (qbit : Fin quantumSize)
    (k : Term → Term) : Term :=
  .unpair (.var .lin 0) <|
    .lam .lin .qubit <|
      .lam .lin .qubit <|
        if qbit = 0 then
          .app
            (.measure (.var .lin 1) <|
              .lam .unres .bit <|
                .lam .lin .qubit <|
                  .lam .lin .qubit <|
                    continueWith k (.var .unres 0)
                      (.pair (.var .lin 1) (.var .lin 0)))
            (.var .lin 0)
        else
          .app
            (.measure (.var .lin 0) <|
              .lam .unres .bit <|
                .lam .lin .qubit <|
                  .lam .lin .qubit <|
                    continueWith k (.var .unres 0)
                      (.pair (.var .lin 0) (.var .lin 1)))
            (.var .lin 1)

/-- Continuation-passing quotation of a command body. -/
def quoteBody
    (C : Command quantumSize classicalSize)
    (current : Term) (k : Term → Term) : Term :=
  match C with
  | .skip => k current
  | .x w =>
      bindRegister
        (.app (unaryRegister .x w) (.var .lin 0)) (k current)
  | .h w =>
      bindRegister
        (.app (unaryRegister .h w) (.var .lin 0)) (k current)
  | .t w =>
      bindRegister
        (.app (unaryRegister .t w) (.var .lin 0)) (k current)
  | .ry θ w =>
      let r := match θ with
        | .rational r => r
        | .coin p => p.val
      bindRegister
        (.app (unaryRegister (.ry r) w) (.var .lin 0)) (k current)
  | .cx control target =>
      bindRegister
        (.app (cxRegister control target) (.var .lin 0)) (k current)
  | .measure qbit _ => measureRegister qbit k
  | .reset qbit =>
      bindRegister
        (.app (unaryRegister .reset qbit) (.var .lin 0)) (k current)
  | .store _ e => k (quoteCExpr current e)
  | .seq A B =>
      quoteBody A current (fun next => quoteBody B next k)
  | .branch guard yes no =>
      .ite (quoteCExpr current guard)
        (quoteBody yes current k) (quoteBody no current k)

/-- Canonical lambda quotation with one unrestricted classical binder and two
curried linear qubit binders. -/
def quote (C : Command quantumSize classicalSize) : Term :=
  .lam .unres .bit <|
    .lam .lin .qubit <|
      .lam .lin .qubit <|
        bindRegister
          (.pair (.var .lin 1) (.var .lin 0))
          (quoteBody C (.var .unres 0)
            (fun current => .pair (.var .lin 0) current))

/-- A certified canonical source quotation of a `Command 2 1`. -/
structure Quotation where
  command : Command quantumSize classicalSize
  quotable : Quotable command

namespace Quotation

def term (Q : Quotation) : Term :=
  quote Q.command

/-- Exact extraction of the represented finite-register command. -/
def compile (Q : Quotation) : Command quantumSize classicalSize :=
  Q.command

/-- Exact command-to-canonical-source reflection. -/
def reflect (C : Command quantumSize classicalSize)
    (hC : Quotable C) : Quotation :=
  ⟨C, hC⟩

end Quotation

end GeneralQuotation

end Command

end QLambda.Linear

namespace QLambda.Palomar

open QLambda.Linear
open QLambda.Linear.Command.GeneralQuotation

/-- Type safety of the typed linear quantum λ-calculus for closed programs.
A closed well-typed term is a value, takes a classical call-by-value step, or
has reached a quantum primitive; classical reduction is deterministic; and
both classical and measurement transitions preserve the type. -/
theorem source_type_safety {M : Term} {A : Ty} (h : HasType [] [] M A) :
    MakesProgress M ∧
      (∀ N, Step M N → HasType [] [] N A) ∧
      (∀ b N, MeasStep M b N → HasType [] [] N A) ∧
      (∀ N₁ N₂, Step M N₁ → Step M N₂ → N₁ = N₂) := by
  sorry

/-- Two-wire quotation capstone (typing + exact compile): every `Quotable`
command has a well-typed canonical lambda representative whose compilation is
the original command. Ideal CQ agreement is proved in-tree as
`Command.GeneralQuotation.Quotation.quotation_capstone` and staged for a later
comparator expansion that can expose `Composer.Model` without a structure hole. -/
theorem quotation_capstone
    (C : Command quantumSize classicalSize) (hC : Quotable C) :
    HasType [] [] (Quotation.reflect C hC).term quotationTy ∧
    (Quotation.reflect C hC).compile = C := by
  sorry

/-! ## Section 3: finite runtime -/

noncomputable def RuntimeRegister (q : Nat) : Type := sorry
noncomputable def runtimeMeasureProbability {q : Nat}
    (ρ : RuntimeRegister q) (w : Fin q) (b : Bool) : Real := sorry
noncomputable def RuntimeConfig (q : Nat) : Type := sorry
def runtimeWellTyped {q : Nat} (s : RuntimeConfig q) (A : Ty) : Prop := sorry
def runtimeInternalStep {q : Nat} (s s' : RuntimeConfig q) : Prop := sorry
def runtimeMeasurementStep {q : Nat} (s : RuntimeConfig q) (weight : Real)
    (outcome : Bool) (s' : RuntimeConfig q) : Prop := sorry
def runtimeNormal {q : Nat} (s : RuntimeConfig q) : Prop := sorry
def runtimeOutOfWires {q : Nat} (s : RuntimeConfig q) : Prop := sorry

/-- `RegisterState.measureProbability_false_add_true`. -/
theorem runtime_born_normalizes {q : Nat} (ρ : RuntimeRegister q) (w : Fin q) :
    runtimeMeasureProbability ρ w false + runtimeMeasureProbability ρ w true = 1 := by
  sorry

/-- `Runtime.internal_preservation`. -/
theorem runtime_internal_preservation {q : Nat} {s s' : RuntimeConfig q} {A : Ty}
    (ht : runtimeWellTyped s A) (hs : runtimeInternalStep s s') :
    runtimeWellTyped s' A := by
  sorry

/-- `Runtime.measurement_preservation`. -/
theorem runtime_measurement_preservation {q : Nat} {s s' : RuntimeConfig q}
    {weight : Real} {outcome : Bool} {A : Ty}
    (ht : runtimeWellTyped s A)
    (hs : runtimeMeasurementStep s weight outcome s') :
    runtimeWellTyped s' A := by
  sorry

/-- `Runtime.progress`. -/
theorem runtime_progress {q : Nat} {s : RuntimeConfig q} {A : Ty}
    (ht : runtimeWellTyped s A) :
    runtimeNormal s ∨ runtimeOutOfWires s ∨
      (∃ s', runtimeInternalStep s s') ∨
      (∃ weight outcome s', runtimeMeasurementStep s weight outcome s') := by
  sorry

/-! ## Section 4: quantum relations, qCPOs, `Set ⊣ qRel` -/

noncomputable def QuantumSet : Type 1 := sorry
noncomputable def QuantumRel (X Y : QuantumSet) : Type := sorry
noncomputable def relComp {X Y Z : QuantumSet}
    (S : QuantumRel Y Z) (R : QuantumRel X Y) : QuantumRel X Z := sorry
noncomputable def relDagger {X Y : QuantumSet}
    (R : QuantumRel X Y) : QuantumRel Y X := sorry
noncomputable def relISup {X Y : QuantumSet}
    (S : Nat → QuantumRel X Y) : QuantumRel X Y := sorry
def quantumDecEq (X : QuantumSet) : Type := sorry
noncomputable def relId (X : QuantumSet) (_h : quantumDecEq X) : QuantumRel X X := sorry
noncomputable def QuantumPoset : Type 1 := sorry
noncomputable def qubitPoset : QuantumPoset := sorry
def isQuantumCPO (P : QuantumPoset) : Prop := sorry
noncomputable def modelLinearObjects : Type 1 := sorry
noncomputable def qRelObjects : Type 1 := sorry
noncomputable def qCPOCategoryObjects : Type 1 := sorry
noncomputable def quantumCPOCarrier : Type 1 := sorry

/-- `(T ∘ S) ∘ R = T ∘ (S ∘ R)`. -/
theorem quantumRel_assoc {X Y Z W : QuantumSet}
    (T : QuantumRel Z W) (S : QuantumRel Y Z) (R : QuantumRel X Y) :
    relComp (relComp T S) R = relComp T (relComp S R) := by
  sorry

/-- `(S ∘ R)† = R† ∘ S†`. -/
theorem quantumRel_dagger_comp {X Y Z : QuantumSet}
    (S : QuantumRel Y Z) (R : QuantumRel X Y) :
    relDagger (relComp S R) = relComp (relDagger R) (relDagger S) := by
  sorry

/-- `(⨆ S) ∘ R = ⨆ (S ∘ R)`. -/
theorem quantumRel_comp_iSup_left {X Y Z : QuantumSet}
    (S : Nat → QuantumRel Y Z) (R : QuantumRel X Y) :
    relComp (relISup S) R = relISup (fun n => relComp (S n) R) := by
  sorry

/-- `S ∘ (⨆ R) = ⨆ (S ∘ R)`. -/
theorem quantumRel_comp_iSup_right {X Y Z : QuantumSet}
    (S : QuantumRel Y Z) (R : Nat → QuantumRel X Y) :
    relComp S (relISup R) = relISup (fun n => relComp S (R n)) := by
  sorry

/-- `1 ∘ R = R`, when the codomain atoms are decidable. -/
theorem quantumRel_id_comp {X Y : QuantumSet} (hY : quantumDecEq Y)
    (R : QuantumRel X Y) :
    relComp (relId Y hY) R = R := by
  sorry

/-- `R ∘ 1 = R`, when the domain atoms are decidable. -/
theorem quantumRel_comp_id {X Y : QuantumSet} (hX : quantumDecEq X)
    (R : QuantumRel X Y) :
    relComp R (relId X hX) = R := by
  sorry

/-- The discrete qubit is a quantum CPO. -/
theorem qubit_isQuantumCPO : isQuantumCPO qubitPoset := by
  sorry

/-- `quantumLNL.linear` is `qRelCategory`. -/
theorem set_qRel_linear_objects : modelLinearObjects = qRelObjects := by
  sorry

/-- Objects of `qCPOCategory` are quantum CPOs. -/
theorem qCPO_category_objects : qCPOCategoryObjects = quantumCPOCarrier := by
  sorry

/-! ## Section 5: presheaf denotation and recursive-type shift -/

noncomputable def ProjChain : Type 1 := sorry
noncomputable def ChainPoint (C : ProjChain) : Type := sorry
noncomputable def TailPoint (C : ProjChain) : Type := sorry
noncomputable def shiftForward {C : ProjChain} (x : ChainPoint C) : TailPoint C := sorry
noncomputable def shiftBackward {C : ProjChain} (x : TailPoint C) : ChainPoint C := sorry
def PrimCP (p : Prim) : Type := sorry
noncomputable def primSuperoperator (p : Prim) : PrimCP p := sorry
noncomputable def primCompletedCP (p : Prim) : PrimCP p := sorry
def FragmentHom : Type := sorry
def MeasureBranchHom : Type := sorry
noncomputable def denoteClosedMeasureNew0 : FragmentHom := sorry
noncomputable def measureElimClosedNew0 : FragmentHom := sorry

/-- `shiftForward ∘ shiftBackward = id` on every projection chain. -/
theorem shift_forward_backward {C : ProjChain} (x : TailPoint C) :
    shiftForward (shiftBackward x) = x := by
  sorry

/-- `shiftBackward ∘ shiftForward = id` on every projection chain. -/
theorem shift_backward_forward {C : ProjChain} (x : ChainPoint C) :
    shiftBackward (shiftForward x) = x := by
  sorry

/-- Every primitive, including `cx`, has the same completed CP map as its superoperator. -/
theorem prim_cp_agreement (p : Prim) :
    primSuperoperator p = primCompletedCP p := by
  sorry

/-- `cx` agrees with its completed CP map. -/
theorem cx_cp_agreement : primSuperoperator .cx = primCompletedCP .cx := by
  sorry

/-- `FragCert.denote` of closed measure-`new0` equals the `measureElim` spine. -/
theorem measure_elim_denotation :
    denoteClosedMeasureNew0 = measureElimClosedNew0 := by
  sorry

/-! ## Section 6: staging -/

def StagingResult (q c : Nat) (M : Term) : Type := sorry
def StagingSucceeds (fuel : Nat) {q c : Nat} {M : Term}
    (P : StagingResult q c M) : Prop := sorry
def stagingWellFormed {q c : Nat} {M : Term}
    (P : StagingResult q c M) : Prop := sorry
def CircuitModel (q c : Nat) : Type := sorry
def CircuitSem (q c : Nat) : Type 1 := sorry
noncomputable def stagedDenotation {q c : Nat} {M : Term}
    (P : StagingResult q c M) (model : CircuitModel q c) : CircuitSem q c := sorry
noncomputable def compiledDenotation {q c : Nat} {M : Term}
    (P : StagingResult q c M) (model : CircuitModel q c) : CircuitSem q c := sorry
def circuitAgrees {q c : Nat} (a b : CircuitSem q c) : Prop := sorry

/-- `elaborates_deterministic`. -/
theorem staging_deterministic {q c fuel : Nat} {M : Term}
    {P Q : StagingResult q c M}
    (hP : StagingSucceeds fuel P) (hQ : StagingSucceeds fuel Q) : P = Q := by
  sorry

/-- `elaborates_command_wellFormed`. -/
theorem staging_well_formed {q c fuel : Nat} {M : Term}
    {P : StagingResult q c M} (h : StagingSucceeds fuel P) :
    stagingWellFormed P := by
  sorry

/-- `elaborates_compile_agreement`: staged command and compiled block agree. -/
theorem staging_compile_agreement {q c fuel : Nat} {M : Term}
    {P : StagingResult q c M} (h : StagingSucceeds fuel P)
    (model : CircuitModel q c) :
    circuitAgrees (stagedDenotation P model) (compiledDenotation P model) := by
  sorry

/-! ## Section 8: OpenQASM -/

def OpenQASMProgram (q c : Nat) : Type := sorry
def parseOpenQASM (q c : Nat) (text : String) : Option (OpenQASMProgram q c) := sorry
def renderOpenQASM {q c : Nat} (P : OpenQASMProgram q c) : String := sorry
def openQASMWellFormed {q c : Nat} (P : OpenQASMProgram q c) : Prop := sorry
def exportOpenQASM {q c : Nat} (P : OpenQASMProgram q c)
    (h : openQASMWellFormed P) : String := sorry

/-- Successful parse renders back to the same text. -/
theorem openqasm_render_roundTrip {q c : Nat} {text : String}
    {P : OpenQASMProgram q c} (h : parseOpenQASM q c text = some P) :
    renderOpenQASM P = text := by
  sorry

/-- Successful parse exports through `toOpenQASM` to the same text. -/
theorem openqasm_export_roundTrip {q c : Nat} {text : String}
    {P : OpenQASMProgram q c} (hP : openQASMWellFormed P)
    (h : parseOpenQASM q c text = some P) :
    exportOpenQASM P hP = text := by
  sorry

/-! ## Section 9: fragment adequacy -/

noncomputable def ketZeroRegister : RuntimeRegister 1 := sorry
def measuredNew0Within (N : Nat) : Prop := sorry
noncomputable def fragmentMeasureBranch (b : Bool) : MeasureBranchHom := sorry
noncomputable def yonedaMeasureBranch (b : Bool) : MeasureBranchHom := sorry

/-- Measured `new0` in `|0⟩` has Born weight 1 on false and 0 on true. -/
theorem measured_new0_born_false :
    runtimeMeasureProbability ketZeroRegister (0 : Fin 1) false = 1 := by
  sorry

theorem measured_new0_born_true :
    runtimeMeasureProbability ketZeroRegister (0 : Fin 1) true = 0 := by
  sorry

/-- The measured `new0` program uses at most `N` qubits for every `N ≥ 1`. -/
theorem measured_new0_within_bound (N : Nat) (hN : 1 ≤ N) :
    measuredNew0Within N := by
  sorry

/-- Fragment measurement branches are the Yoneda branches. -/
theorem measure_branch_agrees (b : Bool) :
    fragmentMeasureBranch b = yonedaMeasureBranch b := by
  sorry

end QLambda.Palomar
