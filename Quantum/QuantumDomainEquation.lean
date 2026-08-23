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

Parameterized theorem: for any `QuantumPowerModel`, the inverse limit
of `D_{n+1} = [D_n → Q(D_n)]` lies in `ωQVA` and solves
`D_∞ ≅ [D_∞ → Q(D_∞)]`. The two applications are (V) and (S).
-/

namespace Scott1972.ContinuousLattice

universe u

/-- `ωQVA` structure on the inverse limit: retract of a countable
product of `ωQVA` stages. Requires `qTowerProj`. -/
@[reducible] noncomputable def qDInf_isOmegaQVA (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    IsOmegaQVA (QDInf M D₀ j₀) :=
  letI : ∀ n, IsOmegaQVA (qTowerType M ⟨D₀.carrier⟩ n) := omegaOnQTower M D₀
  letI : IsOmegaQVA (∀ n, qTowerType M ⟨D₀.carrier⟩ n) := omegaQVA_pi
  omegaQVA_of_retract
    (inverseLimitRetraction (qTowerType M ⟨D₀.carrier⟩) (qTowerProj M ⟨D₀.carrier⟩ j₀))

/-- Embedding `i_∞ : D_∞ → [D_∞ → Q(D_∞)]`. -/
noncomputable def qEmbInfInf (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    ScottMap (QDInf M D₀ j₀) (QuantumFunctor M (QDInf M D₀ j₀)) := by
  sorry

/-- Projection `j_∞ : [D_∞ → Q(D_∞)] → D_∞`. -/
noncomputable def qProjInfInf (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    ScottMap (QuantumFunctor M (QDInf M D₀ j₀)) (QDInf M D₀ j₀) := by
  sorry

theorem qProjInfInf_comp_qEmbInfInf (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    (qProjInfInf M D₀ j₀).comp (qEmbInfInf M D₀ j₀) = ScottMap.idMap := by
  sorry

theorem qEmbInfInf_comp_qProjInfInf (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    (qEmbInfInf M D₀ j₀).comp (qProjInfInf M D₀ j₀) = ScottMap.idMap := by
  sorry

/-- Order isomorphism `D_∞ ≃o [D_∞ → Q(D_∞)]`. -/
noncomputable def qDInf_orderIso (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    QDInf M D₀ j₀ ≃o ScottMap (QDInf M D₀ j₀) (QuantumPower M (QDInf M D₀ j₀)) := by
  sorry

/-- **Capstone (parameterized).** The inverse limit of
`D_{n+1} = [D_n → Q(D_n)]` is in `ωQVA` and solves
`D_∞ ≅ [D_∞ → Q(D_∞)]`. -/
theorem omegaQVA_quantum_domain_equation_solved
    (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    Nonempty (IsOmegaQVA (QDInf M D₀ j₀)) ∧
    (qProjInfInf M D₀ j₀).comp (qEmbInfInf M D₀ j₀) = ScottMap.idMap ∧
    (qEmbInfInf M D₀ j₀).comp (qProjInfInf M D₀ j₀) = ScottMap.idMap ∧
    Nonempty (QDInf M D₀ j₀ ≃o ScottMap (QDInf M D₀ j₀) (QuantumPower M (QDInf M D₀ j₀))) ∧
    (ScottMap.idMap : ScottMap (QDInf M D₀ j₀) (QDInf M D₀ j₀)) =
      ⨆ n, (embInf (qTowerType M ⟨D₀.carrier⟩) (qTowerProj M ⟨D₀.carrier⟩ j₀) n).comp
            (projInf (qTowerType M ⟨D₀.carrier⟩) (qTowerProj M ⟨D₀.carrier⟩ j₀) n) :=
  ⟨⟨qDInf_isOmegaQVA M D₀ j₀⟩,
    qProjInfInf_comp_qEmbInfInf M D₀ j₀,
    qEmbInfInf_comp_qProjInfInf M D₀ j₀,
    ⟨qDInf_orderIso M D₀ j₀⟩,
    idInf_eq_iSup (qTowerType M ⟨D₀.carrier⟩) (qTowerProj M ⟨D₀.carrier⟩ j₀)⟩

/-- **Corollary (V).** The capstone at the quantum-valuation model. -/
theorem omegaQVA_quantum_domain_equation_solved_valuation
    (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor valuationModel D₀.carrier)) :
    Nonempty (IsOmegaQVA (QDInf valuationModel D₀ j₀)) ∧
    (qProjInfInf valuationModel D₀ j₀).comp (qEmbInfInf valuationModel D₀ j₀) =
      ScottMap.idMap ∧
    (qEmbInfInf valuationModel D₀ j₀).comp (qProjInfInf valuationModel D₀ j₀) =
      ScottMap.idMap ∧
    Nonempty (QDInf valuationModel D₀ j₀ ≃o
      ScottMap (QDInf valuationModel D₀ j₀)
        (QuantumPower valuationModel (QDInf valuationModel D₀ j₀))) ∧
    (ScottMap.idMap : ScottMap (QDInf valuationModel D₀ j₀) (QDInf valuationModel D₀ j₀)) =
      ⨆ n, (embInf (qTowerType valuationModel ⟨D₀.carrier⟩)
              (qTowerProj valuationModel ⟨D₀.carrier⟩ j₀) n).comp
            (projInf (qTowerType valuationModel ⟨D₀.carrier⟩)
              (qTowerProj valuationModel ⟨D₀.carrier⟩ j₀) n) :=
  omegaQVA_quantum_domain_equation_solved valuationModel D₀ j₀

/-- **Corollary (S).** The capstone at the saturation model. -/
theorem omegaQVA_quantum_domain_equation_solved_saturation
    (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor saturationModel D₀.carrier)) :
    Nonempty (IsOmegaQVA (QDInf saturationModel D₀ j₀)) ∧
    (qProjInfInf saturationModel D₀ j₀).comp (qEmbInfInf saturationModel D₀ j₀) =
      ScottMap.idMap ∧
    (qEmbInfInf saturationModel D₀ j₀).comp (qProjInfInf saturationModel D₀ j₀) =
      ScottMap.idMap ∧
    Nonempty (QDInf saturationModel D₀ j₀ ≃o
      ScottMap (QDInf saturationModel D₀ j₀)
        (QuantumPower saturationModel (QDInf saturationModel D₀ j₀))) ∧
    (ScottMap.idMap : ScottMap (QDInf saturationModel D₀ j₀) (QDInf saturationModel D₀ j₀)) =
      ⨆ n, (embInf (qTowerType saturationModel ⟨D₀.carrier⟩)
              (qTowerProj saturationModel ⟨D₀.carrier⟩ j₀) n).comp
            (projInf (qTowerType saturationModel ⟨D₀.carrier⟩)
              (qTowerProj saturationModel ⟨D₀.carrier⟩ j₀) n) :=
  omegaQVA_quantum_domain_equation_solved saturationModel D₀ j₀

end Scott1972.ContinuousLattice
