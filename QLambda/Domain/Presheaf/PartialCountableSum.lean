/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Superoperator
import QLambda.Domain.Presheaf.SuperoperatorInstrument

/-!
# Relational partial countable-sum algebras
-/

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder

namespace QLambda.Domain.Presheaf

namespace SigmaMon

universe u

/-- A genuine relational partial countable-sum algebra.  The associativity
field is an `Iff`, corresponding to Kleene equality of the nested and
flattened partial expressions. -/
structure PartialCountableSum (α : Type u) [Zero α] where
  HasSum : {ι : Type} → [Countable ι] → (ι → α) → α → Prop
  unique : ∀ {ι : Type} [Countable ι] {f : ι → α} {a b : α},
    HasSum f a → HasSum f b → a = b
  empty : HasSum (fun i : Empty => nomatch i) 0
  singleton : ∀ (a : α), HasSum (fun _ : PUnit => a) a
  remove_zero : ∀ {ι : Type} [Countable ι] (f : ι → α)
    (s : Set ι) (a : α), (∀ i, i ∉ s → f i = 0) →
      (HasSum (fun i : s => f i) a ↔ HasSum f a)
  reindex : ∀ {ι κ : Type} [Countable ι] [Countable κ]
    (e : κ ≃ ι) (f : ι → α) (a : α),
      HasSum (f ∘ e) a ↔ HasSum f a
  flatten : ∀ {ι : Type} [Countable ι] {κ : ι → Type}
    [∀ i, Countable (κ i)] (f : (i : ι) → κ i → α) (a : α),
      (HasSum (fun p : Σ i, κ i => f p.1 p.2) a ↔
        ∃ g : ι → α, (∀ i, HasSum (f i) (g i)) ∧ HasSum g a)

end SigmaMon

end QLambda.Domain.Presheaf
