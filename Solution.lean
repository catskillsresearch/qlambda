/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.QuantumDomainEquation
import QLambda.Saturation
import QLambda.TTContinuationMonad

/-!
# Solutions to the Challenge

Importing the QLambda proof modules supplies the compared capstone
`omegaQVA_quantum_domain_equation_solved` (parameterized by a bundled
`QuantumPowerModel`), `qDInf_isOmegaQVA`, and
`finitelySeparated_wayBelow`, with the same names and types as in
`Challenge.lean`. `QLambda.TTContinuation.model` now supplies a concrete
Scott-continuation instance. `QLambda.TTPhysicalEmbedding` supplies the
finite physical embedding and its stated compatibility results; language
interpretation and operational adequacy remain separate from the compared
theorem.
-/
