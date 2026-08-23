/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Quantum.OmegaQVA
import Scott1972.ContinuousLattice.FunctionSpaces

/-!
# The quantum state powerdomain `Q(D)`

`IsQuantumPowerModel Q` is the spec of a quantum powerdomain: `Q`
sends complete lattices to complete lattices, is a Scott functor, and
preserves `ωQVA`. Both unweakened carriers are instances (arxiv.md, §5):

* **(V)** `QuantumValuationPower` — Jones–Plotkin-style quantum
  valuations: monotone maps from Scott-opens of `D` to a finite
  `DensityVec`.
* **(S)** `QuantumSaturationPower` — compatible families of finite
  densities along an `ωQVA` approximate identity, extended to all
  complete lattices.

A `QuantumPowerModel` is a bundled `Q` with its instance. The capstone
is parameterized by that bundle and applied to both instances.
-/

namespace Scott1972.ContinuousLattice

universe u

variable {D E F : Type u} [CompleteLattice D] [CompleteLattice E] [CompleteLattice F]

open DensityVec

/-- The empty set is Scott-open. -/
theorem scottOpen_empty : ScottOpen (∅ : Set D) :=
  ⟨isUpperSet_empty, fun _ _ _ hmem => False.elim hmem⟩

/-- Scott-opens of `D`, ordered by inclusion. -/
abbrev ScottOpens (D : Type*) [CompleteLattice D] := { U : Set D // ScottOpen U }

/-- **(V)** A quantum valuation on `D` valued in a fixed finite
`DensityVec dims` (the size parameter: one algebra, or a finite
direct sum). Directed-union continuity is the remaining axiom. -/
structure QuantumValuation (D : Type*) [CompleteLattice D] (dims : List ℕ) where
  val : ScottOpens D → DensityVec dims
  monotone : Monotone val
  map_empty : val ⟨∅, scottOpen_empty⟩ = ⊥

/-- **(V)** Quantum valuations with a varying finite algebra. -/
def QuantumValuationPower (D : Type u) [CompleteLattice D] : Type u :=
  Σ dims : List ℕ, QuantumValuation D dims

/-- Bonding of finite densities along the `ωQVA` approximate identity.
The maps between `DensityVec` stages are not yet constructed. -/
def QuantumSaturationCompatible [IsOmegaQVA D]
    (_ρ : ∀ n, DensityVec (IsOmegaQVA.qfactorable (D := D) n).dims) : Prop := by
  sorry

/-- Compatible families of finite densities, on `ωQVA` objects. -/
def QuantumSaturationFamily [IsOmegaQVA D] :=
  { ρ : ∀ n, DensityVec (IsOmegaQVA.qfactorable (D := D) n).dims //
    QuantumSaturationCompatible ρ }

/-- **(S)** The saturation carrier, as an endofunctor on complete
lattices. On `ωQVA` objects this is `QuantumSaturationFamily`; the
extension off `ωQVA` is not yet constructed. -/
noncomputable def QuantumSaturationPower (D : Type u) [CompleteLattice D] : Type u := by
  sorry

/-- Spec of a quantum powerdomain model. Both (V) and (S) are instances. -/
class IsQuantumPowerModel (Q : (D : Type u) → [CompleteLattice D] → Type u) where
  str : ∀ (D : Type u) [CompleteLattice D], CompleteLattice (Q D)
  map : ∀ {D E : Type u} [CompleteLattice D] [CompleteLattice E],
    ScottMap D E →
      letI := str D
      letI := str E
      ScottMap (Q D) (Q E)
  map_id : ∀ {D : Type u} [CompleteLattice D],
    letI := str D
    map (ScottMap.idMap : ScottMap D D) = ScottMap.idMap
  map_comp : ∀ {D E F : Type u} [CompleteLattice D] [CompleteLattice E] [CompleteLattice F]
      (f : ScottMap E F) (g : ScottMap D E),
    letI := str D
    letI := str E
    letI := str F
    map (f.comp g) = (map f).comp (map g)
  closed : ∀ {D : Type u} [CompleteLattice D] (h : IsOmegaQVA D),
    letI := str D
    IsOmegaQVA (Q D)

attribute [instance] IsQuantumPowerModel.str

noncomputable instance instIsQuantumPowerModelValuation :
    IsQuantumPowerModel QuantumValuationPower := by
  sorry

noncomputable instance instIsQuantumPowerModelSaturation :
    IsQuantumPowerModel QuantumSaturationPower := by
  sorry

/-- A bundled quantum powerdomain: a `Q` that satisfies the spec. -/
structure QuantumPowerModel where
  Power : (D : Type u) → [CompleteLattice D] → Type u
  [spec : IsQuantumPowerModel Power]

attribute [instance] QuantumPowerModel.spec

section ModelAPI

variable (M : QuantumPowerModel)

/-- Carrier of the model at `D`. -/
abbrev QuantumPower (D : Type u) [CompleteLattice D] : Type u :=
  M.Power D

/-- `[D → Q(D)]` for the chosen model. -/
abbrev QuantumFunctor (D : Type u) [CompleteLattice D] : Type u :=
  ScottMap D (M.Power D)

/-- `ωQVA` is closed under the model's powerdomain. -/
abbrev omegaQVA_closed_under_quantumPower {D : Type u} [CompleteLattice D]
    (h : IsOmegaQVA D) : IsOmegaQVA (M.Power D) :=
  IsQuantumPowerModel.closed (Q := M.Power) h

end ModelAPI

/-- `ωQVA` is Cartesian closed (not a field of the spec). -/
noncomputable def omegaQVA_closed_under_functionSpace (hD : IsOmegaQVA D) (hE : IsOmegaQVA E) :
    IsOmegaQVA (ScottMap D E) := by
  sorry

/-- **(V)** bundled as a quantum model. -/
noncomputable def valuationModel : QuantumPowerModel :=
  ⟨QuantumValuationPower⟩

/-- **(S)** bundled as a quantum model. -/
noncomputable def saturationModel : QuantumPowerModel :=
  ⟨QuantumSaturationPower⟩

end Scott1972.ContinuousLattice
