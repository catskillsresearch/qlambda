/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Domain.OmegaObject

@[expose] public section

/-!
# Instance `instCoeSortOmegaObject`
-/

namespace QLambda.Domain
namespace OmegaObject

instance instCoeSortOmegaObject : CoeSort OmegaObject (Type u) :=
  ⟨OmegaObject.Carrier⟩

end OmegaObject
end QLambda.Domain
