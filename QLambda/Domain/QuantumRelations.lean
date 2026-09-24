/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumRel
import QLambda.Domain.QuantumRelComp
import QLambda.Domain.QuantumRelDagger
import QLambda.Domain.QuantumRelFunction
import QLambda.Domain.QuantumRelAtoms
import QLambda.Domain.QuantumRelChains
import QLambda.Domain.QuantumRelExamples
import QLambda.Domain.Finite

/-!
# Quantum relations

Barrel re-exporting the Weaver–Kornell quantum-relation API.

A quantum binary relation from `X` to `Y` is a matrix of operator
subspaces `R(x,y) ⊆ L(X_x, Y_y)`.  Composition is the subspace generated
by operator products, summed over intermediate atoms.

See arXiv:2109.02196, §2, and Weaver, *Quantum relations*.
-/

namespace QLambda.Domain

end QLambda.Domain
