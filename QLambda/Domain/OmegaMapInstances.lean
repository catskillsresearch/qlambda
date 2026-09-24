/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.OmegaMap
import QLambda.Domain.instCoeFunOmegaMap
import QLambda.Domain.instLEOmegaMap
import QLambda.Domain.instOrderBotOmegaMap
import QLambda.Domain.instPartialOrderOmegaMap

/-!
# Instances from `OmegaMap`

Barrel re-exporting `QLambda.Domain.OmegaMap` and its typeclass instances,
plus the Scott-map API that depends on those instances.
-/

namespace QLambda.Domain

namespace OmegaMap

universe u v w

variable
  {D : Type u} {E : Type v} {F : Type w} {G : Type u}
  [PartialOrder D] [OmegaComplete D]
  [PartialOrder E] [OmegaComplete E]
  [PartialOrder F] [OmegaComplete F]
  [PartialOrder G] [OmegaComplete G]


def id : OmegaMap D D where
  toFun x := x
  monotone := monotone_id
  map_ωSup _ _ := rfl

def comp (f : OmegaMap E F) (g : OmegaMap D E) : OmegaMap D F where
  toFun x := f (g x)
  monotone := f.monotone.comp g.monotone
  map_ωSup c hc := by
    rw [g.map_ωSup c hc, f.map_ωSup]

@[simp] theorem id_apply (x : D) : id x = x := rfl
@[simp] theorem comp_apply (f : OmegaMap E F) (g : OmegaMap D E) (x : D) :
    f.comp g x = f (g x) := rfl

@[simp] theorem id_comp (f : OmegaMap D E) : id.comp f = f := by
  ext
  rfl

@[simp] theorem comp_id (f : OmegaMap D E) : f.comp id = f := by
  ext
  rfl

theorem comp_assoc (h : OmegaMap F G) (g : OmegaMap E F) (f : OmegaMap D E) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext
  rfl

section Pointed

variable [OrderBot D]

/-- Finite iterates from bottom. -/
def iterateBot (f : OmegaMap D D) : ℕ → D
  | 0 => ⊥
  | n + 1 => f (iterateBot f n)

theorem iterateBot_mono (f : OmegaMap D D) : Monotone (iterateBot f) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih => exact f.monotone ih

/-- Least fixed point of an ω-continuous endomap. -/
noncomputable def fix (f : OmegaMap D D) : D :=
  OmegaComplete.ωSup (iterateBot f) (iterateBot_mono f)

theorem fix_eq (f : OmegaMap D D) : f (fix f) = fix f := by
  unfold fix
  rw [f.map_ωSup]
  apply le_antisymm
  · apply OmegaComplete.ωSup_le
    intro n
    exact OmegaComplete.le_ωSup (iterateBot f) (iterateBot_mono f) (n + 1)
  · apply OmegaComplete.ωSup_le
    intro n
    cases n with
    | zero => exact bot_le
    | succ n =>
        exact OmegaComplete.le_ωSup
          (fun k => f (iterateBot f k))
          (f.monotone.comp (iterateBot_mono f)) n

theorem fix_le_of_prefixed (f : OmegaMap D D) {x : D} (hx : f x ≤ x) :
    fix f ≤ x := by
  apply OmegaComplete.ωSup_le
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih => exact (f.monotone ih).trans hx

/-- Least fixed points are monotone in their defining functional. -/
theorem fix_mono {f g : OmegaMap D D} (hfg : f ≤ g) :
    fix f ≤ fix g := by
  apply fix_le_of_prefixed
  calc
    f (fix g) ≤ g (fix g) := hfg _
    _ = fix g := fix_eq g

/-- A parameter-indexed family of least fixed points. -/
noncomputable def paramFix
    {P : Type w} [PartialOrder P] [OmegaComplete P]
    (f : P → OmegaMap D D) (p : P) : D :=
  fix (f p)

theorem paramFix_mono
    {P : Type w} [PartialOrder P] [OmegaComplete P]
    {f : P → OmegaMap D D} (hf : Monotone f) :
    Monotone (paramFix f) := by
  intro p q hpq
  exact fix_mono (hf hpq)

end Pointed

end OmegaMap

end QLambda.Domain
