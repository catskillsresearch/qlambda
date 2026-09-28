/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Domain.SetHom
public import QLambda.Domain.instCoeFunSetHom
public import QLambda.Domain.instLESetHom
public import QLambda.Domain.instPartialOrderSetHom

@[expose] public section

/-!
# Instance `instOmegaCompleteSetHom`
-/

namespace QLambda.Domain
namespace SetHom

universe u

noncomputable instance instOmegaCompleteSetHom {A B : Type u} : OmegaComplete (SetHom A B) where
  ωSup c _ := c 0
  le_ωSup c hc n := chain_eq_zero c hc n
  ωSup_le _ _ _ hx := hx 0

end SetHom
end QLambda.Domain
