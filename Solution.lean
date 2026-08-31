/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.QuantumDomainEquation
import QLambda.Saturation
import QLambda.TTContinuationDomainEquation
import QLambda.TTContinuationMonad

/-!
# Solutions to the Challenge

Importing the QLambda proof modules supplies the compared canonical-base
capstone `canonical_omegaQVA_quantum_domain_equation_solved`, quantified by a
bundled `QuantumPowerModel`, with the same name and type as in
`Challenge.lean`. The general `(M, D₀, j₀)` theorem, the concrete
`TTContinuation.model` specialization, `qDInf_isOmegaQVA`, and
`finitelySeparated_wayBelow` remain available as unselected library results.
`QLambda.TTPhysicalEmbedding` supplies the finite physical embedding and its
compatibility results; language interpretation and operational adequacy remain
separate from the compared theorem.
-/
