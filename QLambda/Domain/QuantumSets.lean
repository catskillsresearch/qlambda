/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumSet
import QLambda.Domain.Finite

/-!
# Quantum sets

Barrel re-exporting `QuantumSet` and `QuantumSet.Finite`.

This is the published Kornell presentation used by Lindenhovius–Mislove–
Kornell quantum CPOs: a quantum set is a collection of finite-dimensional
Hilbert spaces (its atoms).  The Cartesian product tensors atoms; the
classical embedding `liftSet` replaces each ordinary point by a
one-dimensional atom.

See arXiv:2109.02196, §2.
-/

namespace QLambda.Domain

end QLambda.Domain
