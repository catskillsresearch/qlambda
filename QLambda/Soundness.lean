/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Interp

/-!
# Soundness of operational reduction

Every unweighted internal reduction refines the denotation of its source.
Top-level external reduction is exact after applying the selected Boolean
environment action.  Weighted reduction is sound under an explicit abstract
closure specification for semantic application.
-/

namespace QLambda

open Scott1972.ContinuousLattice

universe u

section

variable (Q : (D : Type u) → [CompleteLattice D] → Type u)
variable [IsQuantumMonad Q]
variable (D₀ : QDomain.{u})
variable (j₀ : IsContinuousLatticeProjection D₀.carrier
  (QuantumFunctor (QModel Q) D₀.carrier))
variable [HasComputationChoice (SemanticComp Q D₀ j₀)]

/-- The additional, model-specific laws needed to lift weighted branches
through call-by-value semantic application.

This specification is deliberately specialized to the fixed recursive-domain
solution `Q,D₀,j₀`.  Its fields say exactly that, for arbitrary
environment-indexed Scott maps and every environment, `weightedBranch` is
preserved when either the function computation or the argument computation is
replaced by one of its weighted branches.  No concrete powerdomain, TT
relation, or global instance is asserted here. -/
class HasWeightedApplicationClosure
    [HasWeightedBranchSemantics (SemanticComp Q D₀ j₀)] : Prop where
  app_left :
    ∀ (mf mf' ma : ScottMap (Env (SemanticValue Q D₀ j₀))
        (SemanticComp Q D₀ j₀)) (p : Prob)
        (ρ : Env (SemanticValue Q D₀ j₀)),
      HasWeightedBranchSemantics.weightedBranch (mf ρ) p (mf' ρ) →
        HasWeightedBranchSemantics.weightedBranch
          (applyComp (Q := Q) (D₀ := D₀) (j₀ := j₀) mf ma ρ) p
          (applyComp (Q := Q) (D₀ := D₀) (j₀ := j₀) mf' ma ρ)
  app_right :
    ∀ (mf ma ma' : ScottMap (Env (SemanticValue Q D₀ j₀))
        (SemanticComp Q D₀ j₀)) (p : Prob)
        (ρ : Env (SemanticValue Q D₀ j₀)),
      HasWeightedBranchSemantics.weightedBranch (ma ρ) p (ma' ρ) →
        HasWeightedBranchSemantics.weightedBranch
          (applyComp (Q := Q) (D₀ := D₀) (j₀ := j₀) mf ma ρ) p
          (applyComp (Q := Q) (D₀ := D₀) (j₀ := j₀) mf ma' ρ)

/-- One internal operational step refines the source denotation. -/
theorem interp_step_le {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    {M N : Term Prim} (h : Step M N)
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive N ρ ≤
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M ρ := by
  induction h generalizing ρ with
  | beta x M V hV =>
      exact le_of_eq (interp_beta
        (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive x M V hV ρ).symm
  | rec_beta self arg M V hne hV =>
      exact le_of_eq (interp_rec_beta
        (Q := Q) (D₀ := D₀) (j₀ := j₀)
        primitive self arg M V hne hV ρ).symm
  | intern_left M N =>
      exact interp_le_intern_left
        (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M N ρ
  | intern_right M N =>
      exact interp_le_intern_right
        (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M N ρ
  | app_left hstep ih =>
      rw [interp_app_apply, interp_app_apply]
      exact ScottMap.le_def.mp
        (applyComp_mono_left
          (Q := Q) (D₀ := D₀) (j₀ := j₀)
          (ScottMap.le_def.mpr fun σ => ih σ)) ρ
  | app_right hM hstep ih =>
      rw [interp_app_apply, interp_app_apply]
      exact ScottMap.le_def.mp
        (applyComp_mono_right
          (Q := Q) (D₀ := D₀) (j₀ := j₀)
          (ScottMap.le_def.mpr fun σ => ih σ)) ρ

/-- Reflexive-transitive internal reduction refines the initial denotation. -/
theorem interp_reduces_le {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    {M N : Term Prim} (h : Reduces M N)
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive N ρ ≤
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M ρ := by
  induction h generalizing ρ with
  | refl => exact le_rfl
  | tail hred hstep ih =>
      exact (interp_step_le
        (Q := Q) (D₀ := D₀) (j₀ := j₀)
        primitive hstep ρ).trans (ih ρ)

/-- A top-level external step preserves its Boolean label and is denotational
equality after the corresponding external selection.  `ExternalStep` has no
application-context constructors, so the top-level selection laws suffice. -/
theorem interp_external_step_select
    [HasExternalSelection (SemanticComp Q D₀ j₀)]
    {Prim : Type} (primitive : Prim → SemanticComp Q D₀ j₀)
    {selected : Bool} {M N : Term Prim}
    (h : ExternalStep selected M N)
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    HasExternalSelection.select selected
        (interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M ρ) =
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive N ρ := by
  cases h with
  | left M N =>
      rw [interp_extern_apply]
      exact HasExternalSelection.select_false _ _
  | right M N =>
      rw [interp_extern_apply]
      exact HasExternalSelection.select_true _ _

/-- The left branch of a top-level probabilistic choice carries its declared
weight in the model's weighted-branch relation.  Application-context closure
is intentionally not claimed by this theorem. -/
theorem interp_prob_left_weighted
    [HasWeightedBranchSemantics (SemanticComp Q D₀ j₀)]
    {Prim : Type} (primitive : Prim → SemanticComp Q D₀ j₀)
    (p : Prob) (M N : Term Prim) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    HasWeightedBranchSemantics.weightedBranch
        (interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
          (.prob p M N) ρ)
        p
        (interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M ρ) := by
  rw [interp_prob_apply]
  exact HasWeightedBranchSemantics.prob_left p _ _ hp₀ hp₁

/-- The right branch of a top-level probabilistic choice carries weight
`1 - p`.  A full `WeightedStep` theorem additionally needs closure of
`weightedBranch` under application. -/
theorem interp_prob_right_weighted
    [HasWeightedBranchSemantics (SemanticComp Q D₀ j₀)]
    {Prim : Type} (primitive : Prim → SemanticComp Q D₀ j₀)
    (p : Prob) (M N : Term Prim) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    HasWeightedBranchSemantics.weightedBranch
        (interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
          (.prob p M N) ρ)
        (1 - p)
        (interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive N ρ) := by
  rw [interp_prob_apply]
  exact HasWeightedBranchSemantics.prob_right p _ _ hp₀ hp₁

/-- Every weighted operational step preserves its transition probability in
the model's weighted-branch relation.  The theorem is abstract in the two
application-closure laws above; in particular, it does not claim that any
specific TT construction satisfies them. -/
theorem interp_weighted_step
    [HasWeightedBranchSemantics (SemanticComp Q D₀ j₀)]
    [HasWeightedApplicationClosure Q D₀ j₀]
    {Prim : Type} (primitive : Prim → SemanticComp Q D₀ j₀)
    {M N : Term Prim} {p : Prob} (h : WeightedStep M p N)
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    HasWeightedBranchSemantics.weightedBranch
      (interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M ρ) p
      (interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive N ρ) := by
  induction h generalizing ρ with
  | prob_left p M N hp₀ hp₁ =>
      exact interp_prob_left_weighted
        (Q := Q) (D₀ := D₀) (j₀ := j₀)
        primitive p M N hp₀ hp₁ ρ
  | prob_right p M N hp₀ hp₁ =>
      exact interp_prob_right_weighted
        (Q := Q) (D₀ := D₀) (j₀ := j₀)
        primitive p M N hp₀ hp₁ ρ
  | app_left hstep ih =>
      rw [interp_app_apply, interp_app_apply]
      exact HasWeightedApplicationClosure.app_left
        (interp primitive _) (interp primitive _) (interp primitive _)
        _ ρ (ih ρ)
  | app_right hM hstep ih =>
      rw [interp_app_apply, interp_app_apply]
      exact HasWeightedApplicationClosure.app_right
        (interp primitive _) (interp primitive _) (interp primitive _)
        _ ρ (ih ρ)

end

end QLambda
