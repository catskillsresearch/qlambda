/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.QuantumDomainEquation
import QLambda.TTContinuationMonad

/-!
# The canonical quantum domain equation for TT continuations

This module specializes the canonical-base capstone to the concrete
fixed-register Scott-continuation quantum power model.
-/

namespace QLambda.TTContinuation

open Scott1972.ContinuousLattice

universe u

/-- The canonical one-point tower for the concrete `TTContinuation.model n`
has an `ωQVA` inverse limit solving the recursive quantum domain equation. -/
theorem canonical_omegaQVA_quantum_domain_equation_solved (n : ℕ) :
    Nonempty
        (IsOmegaQVA
          (QDInf (model n) canonicalQDomain
            (canonicalQDomainProjection (model n)))) ∧
    (qProjInfInf (model n) canonicalQDomain
        (canonicalQDomainProjection (model n))).comp
        (qEmbInfInf (model n) canonicalQDomain
          (canonicalQDomainProjection (model n))) =
      ScottMap.idMap ∧
    (qEmbInfInf (model n) canonicalQDomain
        (canonicalQDomainProjection (model n))).comp
        (qProjInfInf (model n) canonicalQDomain
          (canonicalQDomainProjection (model n))) =
      ScottMap.idMap ∧
    Nonempty
        (QDInf (model n) canonicalQDomain
            (canonicalQDomainProjection (model n)) ≃o
          ScottMap
            (QDInf (model n) canonicalQDomain
              (canonicalQDomainProjection (model n)))
            (QuantumPower (model n)
              (QDInf (model n) canonicalQDomain
                (canonicalQDomainProjection (model n))))) ∧
    (ScottMap.idMap :
        ScottMap
          (QDInf (model n) canonicalQDomain
            (canonicalQDomainProjection (model n)))
          (QDInf (model n) canonicalQDomain
            (canonicalQDomainProjection (model n)))) =
      ⨆ k,
        (embInf
          (qTowerType (model n) ⟨canonicalQDomain.carrier⟩)
          (qTowerProj (model n) ⟨canonicalQDomain.carrier⟩
            (canonicalQDomainProjection (model n))) k).comp
          (projInf
            (qTowerType (model n) ⟨canonicalQDomain.carrier⟩)
            (qTowerProj (model n) ⟨canonicalQDomain.carrier⟩
              (canonicalQDomainProjection (model n))) k) :=
  Scott1972.ContinuousLattice.canonical_omegaQVA_quantum_domain_equation_solved
    (model n)

end QLambda.TTContinuation
