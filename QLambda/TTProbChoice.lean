/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.TTWeightedAggregation

/-!
# Probabilistic choice for TT continuations

For a valid probability, probabilistic choice is the pointwise lifting of the
physical weighted aggregation of TT results.  Since `Prob` is currently an
abbreviation for all real numbers, invalid weights are sent to bottom rather
than silently clamped or supplied with fabricated bounds.

This file deliberately does not register `HasComputationChoice`: a distinct
external choice operation is still required for that combined interface.
-/

open Set

namespace QLambda

open Scott1972.ContinuousLattice

universe u

namespace TTContinuation

variable {n : ℕ}
variable {D E : Type u}
variable [CompleteLattice D] [CompleteLattice E]

/-- Apply a binary result operation pointwise to a fixed pair of TT
continuations. -/
private noncomputable def pointwiseBinaryAt
    (f : ScottMap (TTResult n × TTResult n) (TTResult n)) :
    (TTContinuationPower n D × TTContinuationPower n D) →
      TTContinuationPower n D :=
  fun qr =>
  ⟨fun k => f (qr.1 k, qr.2 k),
    continuous_of_preservesDirectedSup fun S hS hdir => by
      let T : Set (TTResult n × TTResult n) :=
        (fun k : ScottMap D (TTResult n) => (qr.1 k, qr.2 k)) '' S
      have hT : T.Nonempty := hS.image _
      have hTdir : DirectedOn (· ≤ ·) T := by
        rintro _ ⟨k, hkS, rfl⟩ _ ⟨l, hlS, rfl⟩
        obtain ⟨m, hmS, hkm, hlm⟩ := hdir k hkS l hlS
        exact ⟨(qr.1 m, qr.2 m), ⟨m, hmS, rfl⟩,
          ⟨qr.1.monotone hkm, qr.2.monotone hkm⟩,
          ⟨qr.1.monotone hlm, qr.2.monotone hlm⟩⟩
      have hf := f.preservesDirectedSup_coe T hT hTdir
      change f (qr.1 (sSup S), qr.2 (sSup S)) =
        sSup ((fun k : ScottMap D (TTResult n) =>
          f (qr.1 k, qr.2 k)) '' S)
      rw [qr.1.preservesDirectedSup_coe S hS hdir,
        qr.2.preservesDirectedSup_coe S hS hdir]
      have hpair :
          (sSup T : TTResult n × TTResult n) =
            (sSup (qr.1 '' S), sSup (qr.2 '' S)) := by
        apply Prod.ext
        · rw [Prod.fst_sSup]
          simp only [T, image_image]
        · rw [Prod.snd_sSup]
          simp only [T, image_image]
      rw [← hpair, hf]
      simp only [T, image_image]⟩

@[simp]
private theorem pointwiseBinaryAt_apply
    (f : ScottMap (TTResult n × TTResult n) (TTResult n))
    (qr : TTContinuationPower n D × TTContinuationPower n D)
    (k : ScottMap D (TTResult n)) :
    pointwiseBinaryAt f qr k = f (qr.1 k, qr.2 k) :=
  rfl

/-- Pointwise lifting of a binary Scott-continuous result operation to TT
continuations. -/
private noncomputable def pointwiseBinary
    (f : ScottMap (TTResult n × TTResult n) (TTResult n)) :
    ScottMap
      (TTContinuationPower n D × TTContinuationPower n D)
      (TTContinuationPower n D) :=
  ⟨pointwiseBinaryAt f,
  continuous_of_preservesDirectedSup fun S hS hdir => by
    apply ScottMap.ext
    intro k
    let T : Set (TTResult n × TTResult n) :=
      (fun qr : TTContinuationPower n D × TTContinuationPower n D =>
        (qr.1 k, qr.2 k)) '' S
    have hT : T.Nonempty := hS.image _
    have hTdir : DirectedOn (· ≤ ·) T := by
      rintro _ ⟨q, hqS, rfl⟩ _ ⟨r, hrS, rfl⟩
      obtain ⟨s, hsS, hqs, hrs⟩ := hdir q hqS r hrS
      exact ⟨(s.1 k, s.2 k), ⟨s, hsS, rfl⟩,
        ⟨hqs.1 k, hqs.2 k⟩, ⟨hrs.1 k, hrs.2 k⟩⟩
    have hf := f.preservesDirectedSup_coe T hT hTdir
    change f ((sSup S).1 k, (sSup S).2 k) = _
    rw [ScottMap.sSup_apply]
    have himage :
        (fun g : TTContinuationPower n D => g k) ''
            (pointwiseBinaryAt f '' S) =
          (fun qr :
              TTContinuationPower n D × TTContinuationPower n D =>
            f (qr.1 k, qr.2 k)) '' S := by
      ext y
      constructor
      · rintro ⟨_, ⟨qr, hqrS, rfl⟩, rfl⟩
        exact ⟨qr, hqrS, rfl⟩
      · rintro ⟨qr, hqrS, rfl⟩
        exact ⟨pointwiseBinaryAt f qr, ⟨qr, hqrS, rfl⟩, rfl⟩
    rw [himage]
    rw [Prod.fst_sSup, Prod.snd_sSup, ScottMap.sSup_apply,
      ScottMap.sSup_apply]
    have hpair :
        (sSup T : TTResult n × TTResult n) =
          (sSup ((fun q : TTContinuationPower n D => q k) ''
            (Prod.fst '' S)),
           sSup ((fun q : TTContinuationPower n D => q k) ''
            (Prod.snd '' S))) := by
      apply Prod.ext
      · rw [Prod.fst_sSup]
        simp only [T, image_image]
      · rw [Prod.snd_sSup]
        simp only [T, image_image]
    rw [← hpair, hf]
    simp only [T, image_image]⟩

@[simp]
private theorem pointwiseBinary_apply
    (f : ScottMap (TTResult n × TTResult n) (TTResult n))
    (q r : TTContinuationPower n D) (k : ScottMap D (TTResult n)) :
    pointwiseBinary f (q, r) k = f (q k, r k) :=
  rfl

/-- The total real-indexed probabilistic operation on TT continuations.

Valid probabilities use physical weighted aggregation pointwise.  Reals
outside `[0,1]` denote no probabilistic computation and therefore map every
pair to bottom. -/
noncomputable def probChoice (p : Prob) :
    ScottMap
      (TTContinuationPower n D × TTContinuationPower n D)
      (TTContinuationPower n D) :=
  if hp : 0 ≤ p ∧ p ≤ 1 then
    pointwiseBinary (TTWeightedAggregation.weightedResultScott p hp.1 hp.2)
  else
    ⊥

/-- The defining pointwise equation, including the honest out-of-range case. -/
theorem probChoice_apply
    (p : Prob) (q r : TTContinuationPower n D)
    (k : ScottMap D (TTResult n)) :
    probChoice p (q, r) k =
      if hp : 0 ≤ p ∧ p ≤ 1 then
        TTWeightedAggregation.weightedResultScott p hp.1 hp.2 (q k, r k)
      else
        ⊥ := by
  split_ifs with hp
  · simp [probChoice, hp]
  · simp [probChoice, hp, ScottMap.bot_apply]

@[simp]
theorem probChoice_zero (q r : TTContinuationPower n D) :
    probChoice 0 (q, r) = r := by
  apply ScottMap.ext
  intro k
  rw [probChoice_apply]
  simp

@[simp]
theorem probChoice_one (q r : TTContinuationPower n D) :
    probChoice 1 (q, r) = q := by
  apply ScottMap.ext
  intro k
  rw [probChoice_apply]
  simp

@[simp]
theorem probChoice_of_invalid (p : Prob) (hp : ¬ (0 ≤ p ∧ p ≤ 1)) :
    probChoice (n := n) (D := D) p = ⊥ := by
  simp [probChoice, hp]

/-- Scott continuity of probabilistic choice in both computations is carried
by the `ScottMap` construction itself. -/
theorem probChoice_preservesDirectedSup (p : Prob)
    (S : Set (TTContinuationPower n D × TTContinuationPower n D))
    (hS : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S) :
    probChoice p (sSup S) =
      sSup ((fun qr => probChoice p qr) '' S) :=
  (probChoice p).preservesDirectedSup_coe S hS hdir

/-- Kleisli extension distributes over probabilistic choice. -/
theorem bind_probChoice (h : ScottMap D (TTContinuationPower n E))
    (p : Prob) (q r : TTContinuationPower n D) :
    bind h (probChoice p (q, r)) =
      probChoice p (bind h q, bind h r) := by
  apply ScottMap.ext
  intro k
  simp only [bind_apply, probChoice_apply]

/-- A concrete weighted branch of a TT probabilistic choice.  The relation
retains both the coin parameter and the selected branch's operational
weight. -/
def weightedBranch
    (source : TTContinuationPower n D) (weight : Prob)
    (branch : TTContinuationPower n D) : Prop :=
  ∃ (p : Prob) (_hp₀ : 0 ≤ p) (_hp₁ : p ≤ 1)
      (q r : TTContinuationPower n D),
    source = probChoice p (q, r) ∧
      ((weight = p ∧ branch = q) ∨
        (weight = 1 - p ∧ branch = r))

theorem weightedBranch_prob_left
    (p : Prob) (q r : TTContinuationPower n D)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    weightedBranch (probChoice p (q, r)) p q :=
  ⟨p, hp₀, hp₁, q, r, rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem weightedBranch_prob_right
    (p : Prob) (q r : TTContinuationPower n D)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    weightedBranch (probChoice p (q, r)) (1 - p) r :=
  ⟨p, hp₀, hp₁, q, r, rfl, Or.inr ⟨rfl, rfl⟩⟩

/-- Weighted branches are closed under a fixed Kleisli continuation.  This is
the application-left closure law needed when the function computation takes a
weighted step. -/
theorem weightedBranch_bind
    {source branch : TTContinuationPower n D} {weight : Prob}
    (hsb : weightedBranch source weight branch)
    (h : ScottMap D (TTContinuationPower n E)) :
    weightedBranch (bind h source) weight (bind h branch) := by
  obtain ⟨p, hp₀, hp₁, q, r, rfl, hbranch⟩ := hsb
  rw [bind_probChoice]
  refine ⟨p, hp₀, hp₁, TTContinuation.bind h q,
    TTContinuation.bind h r, rfl, ?_⟩
  rcases hbranch with hleft | hright
  · exact Or.inl
      ⟨hleft.1, congrArg (TTContinuation.bind h) hleft.2⟩
  · exact Or.inr
      ⟨hright.1, congrArg (TTContinuation.bind h) hright.2⟩

/-- Package the concrete relation as the abstract weighted-branch interface
once a later computation-choice implementation identifies its probabilistic
operation with `probChoice`.  This is a constructor, not a global instance. -/
@[instance_reducible] noncomputable def weightedBranchSemantics
    [HasComputationChoice (TTContinuationPower n D)]
    (hprob : ∀ p,
      (HasComputationChoice.prob p :
        ScottMap
          (TTContinuationPower n D × TTContinuationPower n D)
          (TTContinuationPower n D)) = probChoice p) :
    HasWeightedBranchSemantics (TTContinuationPower n D) where
  weightedBranch := weightedBranch
  prob_left := by
    intro p q r hp₀ hp₁
    rw [hprob p]
    exact weightedBranch_prob_left p q r hp₀ hp₁
  prob_right := by
    intro p q r hp₀ hp₁
    rw [hprob p]
    exact weightedBranch_prob_right p q r hp₀ hp₁

end TTContinuation

end QLambda
