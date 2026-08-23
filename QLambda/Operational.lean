/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Syntax

/-!
# Operational semantics of `qλ`

Paper §2. Call-by-value small-step interfaces for the three choices:

* `⊕_p` — a weighted transition with probabilities `p` and `1-p`;
* `⊓` — internal scheduler, either branch;
* `□` — a separately labelled environment-triggered transition.

Keeping weighted and externally triggered steps separate prevents
either effect from being silently identified with nondeterminism.
-/

namespace QLambda

/-- Call-by-value results. The language currently has no primitive
quantum-data constructor; those arrive with the instrument interface. -/
inductive Value : Term → Prop where
  | lam (x : Name) (M : Term) : Value (.lam x M)

/-- Unweighted internal one-step reduction. -/
inductive Step : Term → Term → Prop where
  | beta (x : Name) (M N : Term) (_hN : Value N) :
      Step (Term.app (Term.lam x M) N) (subst x N M)
  | intern_left (M N : Term) :
      Step (Term.intern M N) M
  | intern_right (M N : Term) :
      Step (Term.intern M N) N
  | app_left {M M' N : Term} :
      Step M M' → Step (Term.app M N) (Term.app M' N)
  | app_right {M N N' : Term} (_hM : Value M) :
      Step N N' → Step (Term.app M N) (Term.app M N')

/-- A probabilistic transition, including its branch weight. -/
inductive WeightedStep : Term → Prob → Term → Prop where
  | prob_left (p : Prob) (M N : Term) (_hp₀ : 0 ≤ p) (_hp₁ : p ≤ 1) :
      WeightedStep (.prob p M N) p M
  | prob_right (p : Prob) (M N : Term) (_hp₀ : 0 ≤ p) (_hp₁ : p ≤ 1) :
      WeightedStep (.prob p M N) (1 - p) N
  | app_left {M M' N : Term} {p : Prob} :
      WeightedStep M p M' → WeightedStep (.app M N) p (.app M' N)
  | app_right {M N N' : Term} {p : Prob} (_hM : Value M) :
      WeightedStep N p N' → WeightedStep (.app M N) p (.app M N')

/-- The environment selects a branch of external choice. -/
inductive ExternalStep : Bool → Term → Term → Prop where
  | left (M N : Term) : ExternalStep false (.extern M N) M
  | right (M N : Term) : ExternalStep true (.extern M N) N

/-- Reflexive-transitive closure of `Step`. -/
inductive Reduces : Term → Term → Prop where
  | refl (M : Term) : Reduces M M
  | tail {M N P : Term} : Reduces M N → Step N P → Reduces M P

end QLambda
