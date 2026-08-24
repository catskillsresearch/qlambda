/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.TTResultOperations

namespace QLambda

universe u

namespace TTPhysicalEmbedding

variable {n : ℕ} {D : Type u} [CompleteLattice D]

/-- Embed a finite physical instrument into the continuation model by
aggregating finite branch-local result observations. -/
noncomputable def embed (μ : FiniteInstrumentComp n D) :
    TTContinuation.TTContinuationPower n D :=
  TTTokenTheory.bindResultScott μ

@[simp]
theorem embed_apply (μ : FiniteInstrumentComp n D)
    (k : Scott1972.ContinuousLattice.ScottMap D
      (TTContinuation.TTResult n)) :
    embed μ k = TTTokenTheory.aggregateResult μ k :=
  rfl

/-- On a continuation represented by finite result instruments at every
returned value of `μ`, the embedding computes physical finite bind exactly. -/
theorem embed_satisfied
    (μ : FiniteInstrumentComp n D)
    (ν : D → FiniteInstrumentComp n PUnit.{1})
    (k : Scott1972.ContinuousLattice.ScottMap D
      (TTContinuation.TTResult n))
    (hk : ∀ o : μ.Outcome,
      k (μ.value o) =
        (ν (μ.value o)).satisfiedTTTheory TTContinuation.resultCode) :
    embed μ k =
      (μ.bind ν).satisfiedTTTheory TTContinuation.resultCode :=
  TTTokenTheory.bindResultScott_satisfied μ ν k hk

end TTPhysicalEmbedding

end QLambda
