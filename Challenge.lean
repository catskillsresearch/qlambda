/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Quantum.QDomain
import Scott1972.ContinuousLattice.FunctionSpaceTower

/-!
# Palomar statement of record (ωQVA quantum domain equation)

Challenge restates the compared capstone. It may use `sorry`.
Sorry-free proofs live in `Quantum/` and are exposed through `Solution.lean`.
-/

namespace Scott1972.ContinuousLattice

universe u

/-- Compared capstone: the quantum inverse limit is in `ωQVA` and solves
`D_∞ ≅ [D_∞ → Q(D_∞)]`. -/
theorem omegaQVA_quantum_domain_equation_solved
    (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor D₀.carrier)) :
    Nonempty (IsOmegaQVA (QDInf D₀ j₀)) ∧
    (projInfInf ⟨D₀.carrier⟩ j₀).comp (embInfInf ⟨D₀.carrier⟩ j₀) = ScottMap.idMap ∧
    (embInfInf ⟨D₀.carrier⟩ j₀).comp (projInfInf ⟨D₀.carrier⟩ j₀) = ScottMap.idMap ∧
    Nonempty (QDInf D₀ j₀ ≃o ScottMap (QDInf D₀ j₀) (QDInf D₀ j₀)) ∧
    (ScottMap.idMap : ScottMap (QDInf D₀ j₀) (QDInf D₀ j₀)) =
      ⨆ n, (embInf (towerType ⟨D₀.carrier⟩) (towerProj ⟨D₀.carrier⟩ j₀) n).comp
            (projInf (towerType ⟨D₀.carrier⟩) (towerProj ⟨D₀.carrier⟩ j₀) n) := by
  sorry

@[reducible] noncomputable def qDInf_isOmegaQVA
    (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor D₀.carrier)) :
    IsOmegaQVA (QDInf D₀ j₀) := by
  sorry

end Scott1972.ContinuousLattice
