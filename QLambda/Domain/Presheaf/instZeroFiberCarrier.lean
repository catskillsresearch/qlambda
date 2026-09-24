/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.Fiber

/-!
# Instance `instZeroFiberCarrier`
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

instance instZeroFiberCarrier (X : Fiber) : Zero X.Carrier := ⟨X.zero⟩

end SuperoperatorModule
end QLambda.Domain.Presheaf
