/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Domain.Presheaf.Basis
public import QLambda.Domain.Presheaf.BasisGenerated

@[expose] public section

/-!
# Basis-generated superoperator modules

Barrel re-exporting `Basis` and `BasisGenerated`.

`ClosedGenerated.lean` adds an actual generated coefficient restriction.
Neither class is the paper's classical subcategory: double-dual reflexivity is
an additional requirement.
-/

namespace QLambda.Domain.Presheaf

end QLambda.Domain.Presheaf
