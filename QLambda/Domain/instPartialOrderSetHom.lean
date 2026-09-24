/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.SetHom
import QLambda.Domain.instCoeFunSetHom
import QLambda.Domain.instLESetHom

/-!
# Instance `instPartialOrderSetHom`
-/

namespace QLambda.Domain
namespace SetHom

universe u

instance instPartialOrderSetHom {A B : Type u} : PartialOrder (SetHom A B) where
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ hfg _ := hfg

/-- An increasing chain in a discrete order is constant. -/
theorem chain_eq_zero {A B : Type u} (c : ℕ → SetHom A B)
    (hc : Monotone c) (n : ℕ) : c n = c 0 :=
  (hc (Nat.zero_le n)).symm

end SetHom
end QLambda.Domain
