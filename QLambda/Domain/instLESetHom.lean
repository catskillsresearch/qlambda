/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.SetHom
import QLambda.Domain.instCoeFunSetHom

/-!
# Instance `instLESetHom`
-/

namespace QLambda.Domain
namespace SetHom

universe u

instance instLESetHom {A B : Type u} : LE (SetHom A B) :=
  ⟨fun f g => f = g⟩

end SetHom
end QLambda.Domain
