/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Order.UpperLower.CompleteLattice
import QLambda.Syntax
import Scott1972.ContinuousLattice.FunctionSpaces

/-!
# Effect powerdomains besides `Q`

Paper §1–2. Internal choice `⊓` is interpreted by a nondeterministic
powerdomain `𝒫`. Here `𝒫(D)` is the complete lattice of upper sets
(a Smyth-style carrier; Scott-closed convex Plotkin is not yet built).
External choice `□` needs an environment / synchrony structure and is
only a class, with no global instance.
-/

namespace QLambda

open Scott1972.ContinuousLattice

universe u

/-- Upper-set powerdomain of `D` (Smyth carrier, inclusion order). -/
abbrev NondetPower (D : Type u) [Preorder D] : Type u :=
  UpperSet D

noncomputable instance instCompleteLatticeNondetPower (D : Type u)
    [CompleteLattice D] : CompleteLattice (NondetPower D) :=
  inferInstance

/-- Algebra of internal choice on a domain. -/
class HasInternalChoice (D : Type u) [CompleteLattice D] where
  intern : D → D → D

/-- Algebra of external / interactive choice. -/
class HasExternalChoice (D : Type u) [CompleteLattice D] where
  extern : D → D → D

/-- Scott-continuous choice operations consumed by the computation-valued
interpreter.  This interface keeps classical probabilistic, internal, and
external choice distinct; concrete models may realize them differently. -/
class HasComputationChoice (C : Type u) [CompleteLattice C] where
  prob : Prob → ScottMap (C × C) C
  intern : ScottMap (C × C) C
  extern : ScottMap (C × C) C
  left_le_intern : ∀ a b, a ≤ intern (a, b)
  right_le_intern : ∀ a b, b ≤ intern (a, b)

/-- An external observer resolves an external choice.  Selection is a
Bool-indexed family of Scott-continuous maps on computations; it is not a
lattice comparison and does not identify external with internal choice.

The laws here concern only a top-level `extern`.  Closure under application
contexts is a separate property of a model's sequencing operation. -/
class HasExternalSelection (C : Type u) [CompleteLattice C]
    [HasComputationChoice C] where
  select : Bool → ScottMap C C
  select_false : ∀ a b,
    select false (HasComputationChoice.extern (a, b)) = a
  select_true : ∀ a b,
    select true (HasComputationChoice.extern (a, b)) = b

/-- Denotational meaning of a weighted branch transition.  The relation keeps
the transition weight explicit rather than erasing it into lattice order.

These are deliberately only the two top-level probabilistic-choice laws.
Soundness of `WeightedStep.app_left` and `WeightedStep.app_right` additionally
requires closure of `weightedBranch` under the corresponding semantic
application contexts (equivalently, suitable laws for Kleisli sequencing);
that closure is not implied by this interface. -/
class HasWeightedBranchSemantics (C : Type u) [CompleteLattice C]
    [HasComputationChoice C] where
  weightedBranch : C → Prob → C → Prop
  prob_left : ∀ (p : Prob) (a b : C), 0 ≤ p → p ≤ 1 →
    weightedBranch (HasComputationChoice.prob p (a, b)) p a
  prob_right : ∀ (p : Prob) (a b : C), 0 ≤ p → p ≤ 1 →
    weightedBranch (HasComputationChoice.prob p (a, b)) (1 - p) b

/-- Internal choice on `𝒫(D)` is the join of upper sets. -/
instance instHasInternalChoiceNondet (D : Type u)
    [CompleteLattice D] : HasInternalChoice (NondetPower D) where
  intern := (· ⊔ ·)

end QLambda
