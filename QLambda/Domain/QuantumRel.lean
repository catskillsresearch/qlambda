/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.CompleteLattice.Basic
import QLambda.Domain.QuantumSet

/-!
# Quantum relations (definition and lattice order)
-/

open Matrix

namespace QLambda.Domain

/-- Operator space from atom `x` of `X` to atom `y` of `Y`. -/
abbrev OpSpace (X Y : QuantumSet) (x : X.Atom) (y : Y.Atom) : Type :=
  Submodule ℂ (QuantumSet.Op X Y x y)

/-- A quantum binary relation: one operator subspace per pair of atoms. -/
structure QuantumRel (X Y : QuantumSet) where
  component : ∀ (x : X.Atom) (y : Y.Atom), OpSpace X Y x y

namespace QuantumRel

variable {X Y Z W : QuantumSet}

/-- Pointwise inclusion of quantum relations. -/
instance : LE (QuantumRel X Y) where
  le R S := ∀ x y, R.component x y ≤ S.component x y

instance : PartialOrder (QuantumRel X Y) where
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ hRS hST x y := (hRS x y).trans (hST x y)
  le_antisymm R S hRS hSR := by
    cases R
    cases S
    congr 1
    funext x y
    exact le_antisymm (hRS x y) (hSR x y)

/-- The zero relation. -/
def bot : QuantumRel X Y where
  component := fun _ _ => ⊥

/-- The top relation: every operator is allowed. -/
def top : QuantumRel X Y where
  component := fun _ _ => ⊤

instance : Bot (QuantumRel X Y) := ⟨bot⟩
instance : Top (QuantumRel X Y) := ⟨top⟩

instance : InfSet (QuantumRel X Y) where
  sInf s := ⟨fun x y => ⨅ R : s, R.1.component x y⟩

instance : SupSet (QuantumRel X Y) where
  sSup s := ⟨fun x y => ⨆ R : s, R.1.component x y⟩

instance : SemilatticeInf (QuantumRel X Y) where
  inf R S := ⟨fun x y => R.component x y ⊓ S.component x y⟩
  inf_le_left := fun _ _ _ _ => inf_le_left
  inf_le_right := fun _ _ _ _ => inf_le_right
  le_inf := fun _ _ _ hR hS x y => le_inf (hR x y) (hS x y)

instance : SemilatticeSup (QuantumRel X Y) where
  sup R S := ⟨fun x y => R.component x y ⊔ S.component x y⟩
  le_sup_left := fun _ _ _ _ => le_sup_left
  le_sup_right := fun _ _ _ _ => le_sup_right
  sup_le := fun _ _ _ hR hS x y => sup_le (hR x y) (hS x y)

instance : Lattice (QuantumRel X Y) where

instance : BoundedOrder (QuantumRel X Y) where
  le_top := fun _ _ _ => le_top
  bot_le := fun _ _ _ => bot_le

theorem isLUB_sSup (s : Set (QuantumRel X Y)) :
    IsLUB s (sSup s) := by
  constructor
  · intro R hR x y
    exact le_iSup_of_le ⟨R, hR⟩ le_rfl
  · intro R hR x y
    apply iSup_le
    intro S
    exact (hR S.property) x y

theorem isGLB_sInf (s : Set (QuantumRel X Y)) :
    IsGLB s (sInf s) := by
  constructor
  · intro R hR x y
    exact iInf_le_of_le ⟨R, hR⟩ le_rfl
  · intro R hR x y
    apply le_iInf
    intro S
    exact (hR S.property) x y

noncomputable instance : CompleteLattice (QuantumRel X Y) where
  isLUB_sSup := isLUB_sSup
  isGLB_sInf := isGLB_sInf


end QuantumRel

end QLambda.Domain
