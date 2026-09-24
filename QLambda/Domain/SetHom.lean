/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Enriched

/-!
# Discrete-order set homs
-/

namespace QLambda.Domain

universe u

/-- An ordinary function equipped with the discrete equality order. -/
structure SetHom (A B : Type u) where
  toFun : A → B

namespace SetHom

instance instCoeFunSetHom {A B : Type u} : CoeFun (SetHom A B) (fun _ => A → B) :=
  ⟨SetHom.toFun⟩

@[ext]
theorem ext {A B : Type u} {f g : SetHom A B}
    (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  congr
  exact funext h

instance instLESetHom {A B : Type u} : LE (SetHom A B) :=
  ⟨fun f g => f = g⟩

instance instPartialOrderSetHom {A B : Type u} : PartialOrder (SetHom A B) where
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h

/-- An increasing chain in a discrete order is constant. -/
theorem chain_eq_zero {A B : Type u} (c : ℕ → SetHom A B)
    (hc : Monotone c) (n : ℕ) : c n = c 0 :=
  (hc (Nat.zero_le n)).symm

noncomputable instance instOmegaCompleteSetHom {A B : Type u} : OmegaComplete (SetHom A B) where
  ωSup c _ := c 0
  le_ωSup c hc n := chain_eq_zero c hc n
  ωSup_le _ _ _ hx := hx 0

def id (A : Type u) : SetHom A A :=
  ⟨fun x => x⟩

def comp {A B C : Type u} (g : SetHom B C) (f : SetHom A B) :
    SetHom A C :=
  ⟨fun x => g (f x)⟩

end SetHom

end QLambda.Domain
