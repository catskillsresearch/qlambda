/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Quantum.OmegaQVA
import Scott1972.ContinuousLattice.FunctionSpaces

/-!
# The quantum state powerdomain `Q(D)`

The intended object is the continuous quantum-valuation powerdomain of a
complete lattice `D`: Scott-continuous assignments of subnormalized
states on finite-dimensional `C*`-algebras to Scott-opens of `D`,
completed to a continuous lattice (the non-commutative analogue of
`𝒱_{≤1}(D)`).

The carrier and its lattice / `ωQVA` structure are not yet constructed.
The names and types below are the API the capstone is written against.
-/

namespace Scott1972.ContinuousLattice

universe u

variable {D E F : Type u} [CompleteLattice D] [CompleteLattice E] [CompleteLattice F]

/-- Quantum state powerdomain `Q(D)`. -/
noncomputable def QuantumPower (D : Type u) [CompleteLattice D] : Type u := by
  sorry

noncomputable instance instCompleteLatticeQuantumPower (D : Type u) [CompleteLattice D] :
    CompleteLattice (QuantumPower D) := by
  sorry

/-- Functoriality of `Q` on Scott maps. -/
noncomputable def QuantumPower.map (f : ScottMap D E) :
    ScottMap (QuantumPower D) (QuantumPower E) := by
  sorry

theorem QuantumPower.map_id :
    QuantumPower.map (ScottMap.idMap : ScottMap D D) = ScottMap.idMap := by
  sorry

theorem QuantumPower.map_comp (f : ScottMap E F) (g : ScottMap D E) :
    QuantumPower.map (f.comp g) = (QuantumPower.map f).comp (QuantumPower.map g) := by
  sorry

/-- `[D → Q(D)]`. -/
abbrev QuantumFunctor (D : Type u) [CompleteLattice D] : Type u :=
  ScottMap D (QuantumPower D)

/-- `ωQVA` is closed under the quantum powerdomain. -/
noncomputable def omegaQVA_closed_under_quantumPower (h : IsOmegaQVA D) :
    IsOmegaQVA (QuantumPower D) := by
  sorry

/-- `ωQVA` is Cartesian closed. -/
noncomputable def omegaQVA_closed_under_functionSpace (hD : IsOmegaQVA D) (hE : IsOmegaQVA E) :
    IsOmegaQVA (ScottMap D E) := by
  sorry

end Scott1972.ContinuousLattice
