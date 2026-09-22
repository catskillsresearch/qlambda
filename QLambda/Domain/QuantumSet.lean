/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import QLambda.QuantumInstrument

/-!
# Quantum sets

This is the published Kornell presentation used by Lindenhovius–Mislove–
Kornell quantum CPOs: a quantum set is a collection of finite-dimensional
Hilbert spaces (its atoms).  The Cartesian product tensors atoms; the
classical embedding `liftSet` replaces each ordinary point by a
one-dimensional atom.

See arXiv:2109.02196, §2.
-/

set_option warn.classDefReducibility false

open Matrix

namespace QLambda.Domain

/-- A quantum set is a family of finite-dimensional Hilbert spaces. -/
structure QuantumSet where
  Atom : Type
  dim : Atom → ℕ

namespace QuantumSet

variable {X Y : QuantumSet} {α : Type} {n : ℕ}

/-- The Hilbert space of one atom, identified with `ℂ^n`. -/
abbrev Hilbert (X : QuantumSet) (x : X.Atom) : Type :=
  Fin (X.dim x) → ℂ

/-- Operators from the atom `x` of `X` to the atom `y` of `Y`. -/
abbrev Op (X Y : QuantumSet) (x : X.Atom) (y : Y.Atom) : Type :=
  KrausOperator (X.dim x) (Y.dim y)

/-- The empty quantum set. -/
def empty : QuantumSet where
  Atom := Empty
  dim := Empty.elim

/-- The monoidal unit: a single one-dimensional atom. -/
def unit : QuantumSet where
  Atom := PUnit
  dim := fun _ => 1

/-- An atomic quantum set whose only atom is `n`-dimensional. -/
def atomic (n : ℕ) : QuantumSet where
  Atom := PUnit
  dim := fun _ => n

/-- The qubit: one two-dimensional atom. -/
def qubit : QuantumSet :=
  atomic 2

/-- Lift an ordinary set to a classical quantum set of one-dimensional
atoms. -/
def liftSet (α : Type) : QuantumSet where
  Atom := α
  dim := fun _ => 1

/-- The classical bit. -/
def bit : QuantumSet :=
  liftSet Bool

/-- Tensor product of quantum sets: atoms are pairs of Hilbert spaces. -/
def tensor (X Y : QuantumSet) : QuantumSet where
  Atom := X.Atom × Y.Atom
  dim := fun p => X.dim p.1 * Y.dim p.2

/-- Coproduct / disjoint union of quantum sets. -/
def sum (X Y : QuantumSet) : QuantumSet where
  Atom := X.Atom ⊕ Y.Atom
  dim := fun
    | .inl x => X.dim x
    | .inr y => Y.dim y

/-- Dual quantum set.  Dimensions are unchanged; duality lives in the
operator spaces of relations. -/
def dual (X : QuantumSet) : QuantumSet where
  Atom := X.Atom
  dim := X.dim

/-- A quantum set is finite when it has finitely many atoms. -/
class Finite (X : QuantumSet) where
  fintype : Fintype X.Atom
  decidable : DecidableEq X.Atom

attribute [instance, instance_reducible] Finite.fintype Finite.decidable

instance : Inhabited unit.Atom := ⟨PUnit.unit⟩
instance : Inhabited qubit.Atom := ⟨PUnit.unit⟩
instance : Inhabited (atomic n).Atom := ⟨PUnit.unit⟩
instance : Unique unit.Atom := inferInstanceAs (Unique PUnit)
instance : Unique qubit.Atom := inferInstanceAs (Unique PUnit)
instance : Unique (atomic n).Atom := inferInstanceAs (Unique PUnit)

instance : Finite empty where
  fintype := inferInstanceAs (Fintype Empty)
  decidable := inferInstanceAs (DecidableEq Empty)

instance : Finite unit where
  fintype := inferInstanceAs (Fintype PUnit)
  decidable := inferInstanceAs (DecidableEq PUnit)

instance : Finite qubit where
  fintype := inferInstanceAs (Fintype PUnit)
  decidable := inferInstanceAs (DecidableEq PUnit)

instance : Finite bit where
  fintype := inferInstanceAs (Fintype Bool)
  decidable := inferInstanceAs (DecidableEq Bool)

instance : Finite (atomic n) where
  fintype := inferInstanceAs (Fintype PUnit)
  decidable := inferInstanceAs (DecidableEq PUnit)

instance [Finite X] [Finite Y] : Finite (tensor X Y) where
  fintype := inferInstanceAs (Fintype (X.Atom × Y.Atom))
  decidable := inferInstanceAs (DecidableEq (X.Atom × Y.Atom))

instance [Finite X] [Finite Y] : Finite (sum X Y) where
  fintype := inferInstanceAs (Fintype (X.Atom ⊕ Y.Atom))
  decidable := inferInstanceAs (DecidableEq (X.Atom ⊕ Y.Atom))

instance [Fintype α] [DecidableEq α] : Finite (liftSet α) where
  fintype := inferInstanceAs (Fintype α)
  decidable := inferInstanceAs (DecidableEq α)

instance [DecidableEq α] : DecidableEq (liftSet α).Atom :=
  show DecidableEq α from inferInstance

instance [Fintype α] : Fintype (liftSet α).Atom :=
  show Fintype α from inferInstance

instance [LE α] : LE (liftSet α).Atom :=
  show LE α from inferInstance

instance [Preorder α] : Preorder (liftSet α).Atom :=
  show Preorder α from inferInstance

instance [PartialOrder α] : PartialOrder (liftSet α).Atom :=
  show PartialOrder α from inferInstance

instance [DecidableEq X.Atom] [DecidableEq Y.Atom] :
    DecidableEq (tensor X Y).Atom :=
  show DecidableEq (X.Atom × Y.Atom) from inferInstance

instance [DecidableEq X.Atom] [DecidableEq Y.Atom] :
    DecidableEq (sum X Y).Atom :=
  show DecidableEq (X.Atom ⊕ Y.Atom) from inferInstance

@[simp] theorem dim_unit (x : unit.Atom) : unit.dim x = 1 :=
  rfl

@[simp] theorem dim_qubit (x : qubit.Atom) : qubit.dim x = 2 :=
  rfl

@[simp] theorem dim_bit (x : bit.Atom) : bit.dim x = 1 :=
  rfl

@[simp] theorem dim_liftSet {α} (a : α) : (liftSet α).dim a = 1 :=
  rfl

@[simp] theorem dim_atomic (n : ℕ) (x : (atomic n).Atom) :
    (atomic n).dim x = n :=
  rfl

end QuantumSet

end QLambda.Domain
