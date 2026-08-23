/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Syntax

/-!
# Operational semantics of `qλ`

Paper §2. Small-step reduction for the three choices:

* `⊕_p` — coin of weight `p` (here a nondeterministic envelope of the
  two outcomes; a probabilistic transition system is not yet stated);
* `⊓` — internal scheduler, either branch;
* `□` — external / environment trigger (contextual, not yet stated).
-/

namespace QLambda

/-- One-step reduction. -/
inductive Step : Term → Term → Prop where
  | beta (x : Name) (M N : Term) :
      Step (Term.app (Term.lam x M) N) (subst x N M)
  | prob_left (p : Prob) (M N : Term) :
      Step (Term.prob p M N) M
  | prob_right (p : Prob) (M N : Term) :
      Step (Term.prob p M N) N
  | intern_left (M N : Term) :
      Step (Term.intern M N) M
  | intern_right (M N : Term) :
      Step (Term.intern M N) N
  | app_left {M M' N : Term} :
      Step M M' → Step (Term.app M N) (Term.app M' N)
  | app_right {M N N' : Term} :
      Step N N' → Step (Term.app M N) (Term.app M N')

/-- Reflexive-transitive closure of `Step`. -/
inductive Reduces : Term → Term → Prop where
  | refl (M : Term) : Reduces M M
  | tail {M N P : Term} : Reduces M N → Step N P → Reduces M P

end QLambda
