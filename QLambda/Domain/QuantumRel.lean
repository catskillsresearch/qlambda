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

/-- The zero relation. -/
def bot : QuantumRel X Y where
  component := fun _ _ => ⊥

/-- The top relation: every operator is allowed. -/
def top : QuantumRel X Y where
  component := fun _ _ => ⊤

end QuantumRel

end QLambda.Domain
