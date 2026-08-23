/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Quantum.QDomain
import Scott1972.ContinuousLattice.FunctionSpaceTower
import Scott1972.ContinuousLattice.InverseLimits

/-!
# The recursive quantum domain equation in `ωQVA`

The inverse limit of the quantum tower is a Scott-continuous retract of
the countable product of its stages. Each stage is in `ωQVA` by the
`QDomain` functor-closure hypothesis, the product is in `ωQVA` by
`omegaQVA_pi`, and retracts stay in `ωQVA`. The remaining conjuncts are
Scott 1972, Theorem 4.4.
-/

namespace Scott1972.ContinuousLattice

universe u

/-- `ωQVA` structure on the inverse limit: it is a retract of a countable
product of `ωQVA` stages. -/
@[reducible] noncomputable def qDInf_isOmegaQVA (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor D₀.carrier)) :
    IsOmegaQVA (QDInf D₀ j₀) :=
  letI : ∀ n, IsOmegaQVA (towerType ⟨D₀.carrier⟩ n) := omegaOnTower D₀
  letI : IsOmegaQVA (∀ n, towerType ⟨D₀.carrier⟩ n) := omegaQVA_pi
  omegaQVA_of_retract
    (inverseLimitRetraction (towerType ⟨D₀.carrier⟩) (towerProj ⟨D₀.carrier⟩ j₀))

/-- **Capstone.** The quantum inverse limit solves
`D_∞ ≅ [D_∞ → Q(D_∞)]` inside `ωQVA`. -/
theorem omegaQVA_quantum_domain_equation_solved
    (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor D₀.carrier)) :
    Nonempty (IsOmegaQVA (QDInf D₀ j₀)) ∧
    (projInfInf ⟨D₀.carrier⟩ j₀).comp (embInfInf ⟨D₀.carrier⟩ j₀) = ScottMap.idMap ∧
    (embInfInf ⟨D₀.carrier⟩ j₀).comp (projInfInf ⟨D₀.carrier⟩ j₀) = ScottMap.idMap ∧
    Nonempty (QDInf D₀ j₀ ≃o ScottMap (QDInf D₀ j₀) (QDInf D₀ j₀)) ∧
    (ScottMap.idMap : ScottMap (QDInf D₀ j₀) (QDInf D₀ j₀)) =
      ⨆ n, (embInf (towerType ⟨D₀.carrier⟩) (towerProj ⟨D₀.carrier⟩ j₀) n).comp
            (projInf (towerType ⟨D₀.carrier⟩) (towerProj ⟨D₀.carrier⟩ j₀) n) :=
  ⟨⟨qDInf_isOmegaQVA D₀ j₀⟩,
    projInfInf_comp_embInfInf ⟨D₀.carrier⟩ j₀,
    embInfInf_comp_projInfInf ⟨D₀.carrier⟩ j₀,
    ⟨theorem_4_4_orderIso ⟨D₀.carrier⟩ j₀⟩,
    idInf_eq_iSup (towerType ⟨D₀.carrier⟩) (towerProj ⟨D₀.carrier⟩ j₀)⟩

end Scott1972.ContinuousLattice
