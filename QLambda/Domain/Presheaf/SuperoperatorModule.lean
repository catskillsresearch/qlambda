/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Domain.Presheaf.ModuleChoiSum
public import QLambda.Domain.Presheaf.FiberInstances
public import QLambda.Domain.Presheaf.Module
public import QLambda.Domain.Presheaf.HasActSumFromDimInstances
public import QLambda.Domain.Presheaf.HomInstances
public import QLambda.Domain.Presheaf.ModuleIso

@[expose] public section

/-!
# Specialized modules over finite-dimensional superoperators

Barrel re-exporting `Fiber`, `Module`, `HasActSumFromDim`, `Hom`, and `Iso`
(with supporting Choi/CPMap sum lemmas).
-/

namespace QLambda.Domain.Presheaf

end QLambda.Domain.Presheaf
