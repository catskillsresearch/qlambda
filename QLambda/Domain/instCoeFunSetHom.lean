/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.SetHom

/-!
# Instance `instCoeFunSetHom`
-/

namespace QLambda.Domain
namespace SetHom

universe u

instance instCoeFunSetHom {A B : Type u} : CoeFun (SetHom A B) (fun _ => A → B) :=
  ⟨SetHom.toFun⟩

end SetHom
end QLambda.Domain
