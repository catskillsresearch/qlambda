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

Intended theorem: the inverse limit of `D_{n+1} = [D_n → Q(D_n)]` lies
in `ωQVA` and solves `D_∞ ≅ [D_∞ → Q(D_∞)]`.

`ωQVA` membership of the limit follows the CKL saturation pattern
(retract of a countable product of `ωQVA` stages) once the bonding maps
`qTowerProj` exist. The iso `[D_∞ → Q(D_∞)]` is not Scott 1972
Theorem 4.4 (that theorem is `[D_∞ → D_∞]`).
-/

namespace Scott1972.ContinuousLattice

universe u

/-- `ωQVA` structure on the inverse limit: retract of a countable
product of `ωQVA` stages. Requires `qTowerProj`. -/
@[reducible] noncomputable def qDInf_isOmegaQVA (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor D₀.carrier)) :
    IsOmegaQVA (QDInf D₀ j₀) :=
  letI : ∀ n, IsOmegaQVA (qTowerType ⟨D₀.carrier⟩ n) := omegaOnQTower D₀
  letI : IsOmegaQVA (∀ n, qTowerType ⟨D₀.carrier⟩ n) := omegaQVA_pi
  omegaQVA_of_retract
    (inverseLimitRetraction (qTowerType ⟨D₀.carrier⟩) (qTowerProj ⟨D₀.carrier⟩ j₀))

/-- Embedding `i_∞ : D_∞ → [D_∞ → Q(D_∞)]`. -/
noncomputable def qEmbInfInf (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor D₀.carrier)) :
    ScottMap (QDInf D₀ j₀) (QuantumFunctor (QDInf D₀ j₀)) := by
  sorry

/-- Projection `j_∞ : [D_∞ → Q(D_∞)] → D_∞`. -/
noncomputable def qProjInfInf (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor D₀.carrier)) :
    ScottMap (QuantumFunctor (QDInf D₀ j₀)) (QDInf D₀ j₀) := by
  sorry

theorem qProjInfInf_comp_qEmbInfInf (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor D₀.carrier)) :
    (qProjInfInf D₀ j₀).comp (qEmbInfInf D₀ j₀) = ScottMap.idMap := by
  sorry

theorem qEmbInfInf_comp_qProjInfInf (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor D₀.carrier)) :
    (qEmbInfInf D₀ j₀).comp (qProjInfInf D₀ j₀) = ScottMap.idMap := by
  sorry

/-- Order isomorphism `D_∞ ≃o [D_∞ → Q(D_∞)]`. -/
noncomputable def qDInf_orderIso (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor D₀.carrier)) :
    QDInf D₀ j₀ ≃o ScottMap (QDInf D₀ j₀) (QuantumPower (QDInf D₀ j₀)) := by
  sorry

/-- **Capstone.** The inverse limit of `D_{n+1} = [D_n → Q(D_n)]` is in
`ωQVA` and solves `D_∞ ≅ [D_∞ → Q(D_∞)]`. -/
theorem omegaQVA_quantum_domain_equation_solved
    (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor D₀.carrier)) :
    Nonempty (IsOmegaQVA (QDInf D₀ j₀)) ∧
    (qProjInfInf D₀ j₀).comp (qEmbInfInf D₀ j₀) = ScottMap.idMap ∧
    (qEmbInfInf D₀ j₀).comp (qProjInfInf D₀ j₀) = ScottMap.idMap ∧
    Nonempty (QDInf D₀ j₀ ≃o ScottMap (QDInf D₀ j₀) (QuantumPower (QDInf D₀ j₀))) ∧
    (ScottMap.idMap : ScottMap (QDInf D₀ j₀) (QDInf D₀ j₀)) =
      ⨆ n, (embInf (qTowerType ⟨D₀.carrier⟩) (qTowerProj ⟨D₀.carrier⟩ j₀) n).comp
            (projInf (qTowerType ⟨D₀.carrier⟩) (qTowerProj ⟨D₀.carrier⟩ j₀) n) :=
  ⟨⟨qDInf_isOmegaQVA D₀ j₀⟩,
    qProjInfInf_comp_qEmbInfInf D₀ j₀,
    qEmbInfInf_comp_qProjInfInf D₀ j₀,
    ⟨qDInf_orderIso D₀ j₀⟩,
    idInf_eq_iSup (qTowerType ⟨D₀.carrier⟩) (qTowerProj ⟨D₀.carrier⟩ j₀)⟩

end Scott1972.ContinuousLattice
