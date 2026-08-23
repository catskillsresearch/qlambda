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

A `QDomain` is a pointed object of `ωQVA`. Closure of `ωQVA` under `Q`
and under `[— → —]` is stated in `QuantumPower.lean` (currently `sorry`).
The tower and its inverse limit are formed for the endofunctor
`F(X) = [X → Q(X)]`, not Scott's `X ↦ [X → X]`.
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
noncomputable def qTowerCLat (D₀ : CLat.{u}) : ℕ → CLat.{u}
  | 0 => D₀
  | n + 1 =>
    ⟨ScottMap (qTowerCLat D₀ n).carrier (QuantumPower (qTowerCLat D₀ n).carrier)⟩

/-- The carrier `Dₙ` of the quantum tower. -/
def qTowerType (D₀ : CLat.{u}) (n : ℕ) : Type u := (qTowerCLat D₀ n).carrier

noncomputable instance qTowerCompleteLattice (D₀ : CLat.{u}) (n : ℕ) :
    CompleteLattice (qTowerType D₀ n) := (qTowerCLat D₀ n).str

@[simp] theorem qTowerType_zero (D₀ : CLat.{u}) : qTowerType D₀ 0 = D₀.carrier := rfl

theorem qTowerType_succ (D₀ : CLat.{u}) (n : ℕ) :
    qTowerType D₀ (n + 1) =
      ScottMap (qTowerType D₀ n) (QuantumPower (qTowerType D₀ n)) :=
  rfl

/-- The quantum tower as a sequence of `QDomain`s. -/
noncomputable def qTower (D₀ : QDomain.{u}) : ℕ → QDomain.{u}
  | 0 => D₀
  | n + 1 =>
    { carrier := ScottMap (qTower D₀ n).carrier (QuantumPower (qTower D₀ n).carrier)
      omega :=
        omegaQVA_closed_under_functionSpace (qTower D₀ n).omega
          (omegaQVA_closed_under_quantumPower (qTower D₀ n).omega) }

@[simp] theorem qTower_zero (D₀ : QDomain.{u}) : qTower D₀ 0 = D₀ := rfl

theorem qTower_carrier_succ (D₀ : QDomain.{u}) (n : ℕ) :
    (qTower D₀ (n + 1)).carrier =
      ScottMap (qTower D₀ n).carrier (QuantumPower (qTower D₀ n).carrier) :=
  rfl

/-- Stagewise `ωQVA` instance on the quantum tower. -/
@[reducible] noncomputable def omegaOnQTower (D₀ : QDomain.{u}) :
    (n : ℕ) → IsOmegaQVA (qTowerType ⟨D₀.carrier⟩ n)
  | 0 => D₀.omega
  | n + 1 =>
    omegaQVA_closed_under_functionSpace (omegaOnQTower D₀ n)
      (omegaQVA_closed_under_quantumPower (omegaOnQTower D₀ n))

/-- Bonding projections `j_{n+1} = F(j_n)` for `F(X) = [X → Q(X)]`. -/
noncomputable def qTowerProj (D₀ : CLat.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor D₀.carrier)) :
    ∀ n, IsContinuousLatticeProjection (qTowerType D₀ n) (qTowerType D₀ (n + 1)) := by
  sorry

/-- Inverse limit of the quantum tower. -/
abbrev QDInf (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor D₀.carrier)) :
    Type u :=
  InverseLimit (qTowerType ⟨D₀.carrier⟩) (qTowerProj ⟨D₀.carrier⟩ j₀)

end Scott1972.ContinuousLattice
