/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.Syntax
import QLambda.Domain.Presheaf.ClosedGenerated

/-!
# First-order type objects

Unit, bits, qubits, and their tensors are interpreted as representable
superoperator modules.  This is not an interpretation of arrows,
unrestricted exponentials, or recursive types.  Those remain semantic
objectives.
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule

namespace Ty.FirstOrder

/-- Representable module of a first-order type. -/
noncomputable def object {A : Ty} (h : FirstOrder A) : ClosedGenerated :=
  closedRepresentable h.dimension

@[simp]
theorem object_module {A : Ty} (h : FirstOrder A) :
    (object h).module = representable h.dimension :=
  rfl

/-- Tensor of first-order types is the Day tensor of their representables. -/
theorem object_tensor {A B : Ty}
    (hA : FirstOrder A) (hB : FirstOrder B) :
    (object (.tensor hA hB)).module =
      dayTensorRepresentable hA.dimension hB.dimension :=
  rfl

end Ty.FirstOrder

end QLambda.Linear
