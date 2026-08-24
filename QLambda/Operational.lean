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

/-- Call-by-value results. Primitive quantum operations remain computations;
ordinary and recursive abstractions are values. -/
inductive Value {Prim : Type} : Term Prim → Prop where
  | lam (x : Name) (M : Term Prim) : Value (.lam x M)
  | recLam (self arg : Name) (M : Term Prim) : Value (.recLam self arg M)

/-- Unweighted internal one-step reduction. -/
inductive Step {Prim : Type} : Term Prim → Term Prim → Prop where
  | beta (x : Name) (M N : Term Prim) (_hN : Value N) :
      Step (Term.app (Term.lam x M) N) (subst x N M)
  | rec_beta (self arg : Name) (M N : Term Prim)
      (_hne : self ≠ arg) (_hN : Value N) :
      Step (Term.app (Term.recLam self arg M) N)
        (subst arg N (subst self (Term.recLam self arg M) M))
  | intern_left (M N : Term Prim) :
      Step (Term.intern M N) M
  | intern_right (M N : Term Prim) :
      Step (Term.intern M N) N
  | app_left {M M' N : Term Prim} :
      Step M M' → Step (Term.app M N) (Term.app M' N)
  | app_right {M N N' : Term Prim} (_hM : Value M) :
      Step N N' → Step (Term.app M N) (Term.app M N')

/-- A probabilistic transition, including its branch weight. -/
inductive WeightedStep {Prim : Type} : Term Prim → Prob → Term Prim → Prop where
  | prob_left (p : Prob) (M N : Term Prim) (_hp₀ : 0 ≤ p) (_hp₁ : p ≤ 1) :
      WeightedStep (.prob p M N) p M
  | prob_right (p : Prob) (M N : Term Prim) (_hp₀ : 0 ≤ p) (_hp₁ : p ≤ 1) :
      WeightedStep (.prob p M N) (1 - p) N
  | app_left {M M' N : Term Prim} {p : Prob} :
      WeightedStep M p M' → WeightedStep (.app M N) p (.app M' N)
  | app_right {M N N' : Term Prim} {p : Prob} (_hM : Value M) :
      WeightedStep N p N' → WeightedStep (.app M N) p (.app M N')

/-- The environment selects a branch of external choice. -/
inductive ExternalStep {Prim : Type} : Bool → Term Prim → Term Prim → Prop where
  | left (M N : Term Prim) : ExternalStep false (.extern M N) M
  | right (M N : Term Prim) : ExternalStep true (.extern M N) N

/-- Reflexive-transitive closure of `Step`. -/
inductive Reduces {Prim : Type} : Term Prim → Term Prim → Prop where
  | refl (M : Term Prim) : Reduces M M
  | tail {M N P : Term Prim} : Reduces M N → Step N P → Reduces M P

end QLambda
