/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.SetHom
import QLambda.Domain.instCoeFunSetHom
import QLambda.Domain.instLESetHom
import QLambda.Domain.instPartialOrderSetHom
import QLambda.Domain.instOmegaCompleteSetHom

/-!
# Instances from `SetHom`
-/

namespace QLambda.Domain
namespace SetHom

universe u

@[ext]
theorem ext {A B : Type u} {f g : SetHom A B}
    (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  congr
  exact funext h


def id (A : Type u) : SetHom A A :=
  ⟨fun x => x⟩

def comp {A B C : Type u} (g : SetHom B C) (f : SetHom A B) :
    SetHom A C :=
  ⟨fun x => g (f x)⟩


end SetHom
end QLambda.Domain
