/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Domain.QuantumRelInstances
public import QLambda.Domain.QuantumRelComp
public import QLambda.Domain.QuantumRelDagger
public import QLambda.Domain.QuantumRelFunction
public import QLambda.Domain.QuantumRelAtoms
public import QLambda.Domain.QuantumRelChains
public import QLambda.Domain.QuantumRelExamples
public import QLambda.Domain.FiniteInstances

@[expose] public section

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
