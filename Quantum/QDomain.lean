/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Quantum.QuantumPower
import Scott1972.ContinuousLattice.FunctionSpaceTower
import Scott1972.ContinuousLattice.InverseLimits

/-!
# Quantum domains and the tower `D_{n+1} = [D_n → Q(D_n)]`

A `QDomain` is a pointed object of `ωQVA`. The tower and its inverse
limit are formed for `F(X) = [X → Q(X)]` relative to a bundled
`QuantumPowerModel` (a `Q` that is an instance of
`IsQuantumPowerModel`), not Scott's `X ↦ [X → X]`.
-/

namespace Scott1972.ContinuousLattice

universe u

/-- A pointed object of `ωQVA`. -/
structure QDomain : Type (u + 1) where
  carrier : Type u
  [str : CompleteLattice carrier]
  omega : IsOmegaQVA carrier

attribute [instance] QDomain.str

/-- The quantum tower `D_{n+1} = [D_n → Q(D_n)]` as bundled lattices. -/
noncomputable def qTowerCLat (M : QuantumPowerModel) (D₀ : CLat.{u}) : ℕ → CLat.{u}
  | 0 => D₀
  | n + 1 =>
    ⟨ScottMap (qTowerCLat M D₀ n).carrier (QuantumPower M (qTowerCLat M D₀ n).carrier)⟩

/-- The carrier `Dₙ` of the quantum tower. -/
def qTowerType (M : QuantumPowerModel) (D₀ : CLat.{u}) (n : ℕ) : Type u :=
  (qTowerCLat M D₀ n).carrier

noncomputable instance qTowerCompleteLattice (M : QuantumPowerModel) (D₀ : CLat.{u})
    (n : ℕ) : CompleteLattice (qTowerType M D₀ n) :=
  (qTowerCLat M D₀ n).str

@[simp] theorem qTowerType_zero (M : QuantumPowerModel) (D₀ : CLat.{u}) :
    qTowerType M D₀ 0 = D₀.carrier :=
  rfl

theorem qTowerType_succ (M : QuantumPowerModel) (D₀ : CLat.{u}) (n : ℕ) :
    qTowerType M D₀ (n + 1) =
      ScottMap (qTowerType M D₀ n) (QuantumPower M (qTowerType M D₀ n)) :=
  rfl

/-- The quantum tower as a sequence of `QDomain`s. -/
noncomputable def qTower (M : QuantumPowerModel) (D₀ : QDomain.{u}) : ℕ → QDomain.{u}
  | 0 => D₀
  | n + 1 =>
    { carrier := ScottMap (qTower M D₀ n).carrier (QuantumPower M (qTower M D₀ n).carrier)
      omega :=
        omegaQVA_closed_under_functionSpace (qTower M D₀ n).omega
          (omegaQVA_closed_under_quantumPower M (qTower M D₀ n).omega) }

@[simp] theorem qTower_zero (M : QuantumPowerModel) (D₀ : QDomain.{u}) :
    qTower M D₀ 0 = D₀ :=
  rfl

theorem qTower_carrier_succ (M : QuantumPowerModel) (D₀ : QDomain.{u}) (n : ℕ) :
    (qTower M D₀ (n + 1)).carrier =
      ScottMap (qTower M D₀ n).carrier (QuantumPower M (qTower M D₀ n).carrier) :=
  rfl

/-- Stagewise `ωQVA` instance on the quantum tower. -/
@[reducible] noncomputable def omegaOnQTower (M : QuantumPowerModel) (D₀ : QDomain.{u}) :
    (n : ℕ) → IsOmegaQVA (qTowerType M ⟨D₀.carrier⟩ n)
  | 0 => D₀.omega
  | n + 1 =>
    omegaQVA_closed_under_functionSpace (omegaOnQTower M D₀ n)
      (omegaQVA_closed_under_quantumPower M (omegaOnQTower M D₀ n))

/-- Bonding projections `j_{n+1} = F(j_n)` for `F(X) = [X → Q(X)]`. -/
noncomputable def qTowerProj (M : QuantumPowerModel) (D₀ : CLat.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    ∀ n, IsContinuousLatticeProjection (qTowerType M D₀ n) (qTowerType M D₀ (n + 1)) := by
  sorry

/-- Inverse limit of the quantum tower. -/
abbrev QDInf (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    Type u :=
  InverseLimit (qTowerType M ⟨D₀.carrier⟩) (qTowerProj M ⟨D₀.carrier⟩ j₀)

end Scott1972.ContinuousLattice
