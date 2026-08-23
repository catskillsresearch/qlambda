/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Quantum.OmegaQVA
import Scott1972.ContinuousLattice.FunctionSpaceTower
import Scott1972.ContinuousLattice.InverseLimits

/-!
# Quantum domains and the function-space tower

`QuantumFunctor D` is `[D → D]`, standing for `[D → Q(D)]` at the
carrier level (the quantum powerdomain is interpreted by the same
continuous-lattice function space used in Scott 1972, Theorem 4.4).
-/

namespace Scott1972.ContinuousLattice

universe u

/-- Bundled continuous lattice in `ωQVA`, closed under the quantum
function-space functor. The functor-closure field is the Cartesian
hypothesis needed to keep every tower stage inside `ωQVA`. -/
structure QDomain : Type (u + 1) where
  carrier : Type u
  [str : CompleteLattice carrier]
  omega : IsOmegaQVA carrier
  functionSpace_omega :
    ∀ {E : Type u} [CompleteLattice E],
      IsOmegaQVA E → IsOmegaQVA (ScottMap E E)

attribute [instance] QDomain.str

/-- `[D → Q(D)]` as a Scott function space on the carrier. -/
abbrev QuantumFunctor (D : Type u) [CompleteLattice D] : Type u :=
  ScottMap D D

/-- The quantum tower `D_{n+1} = [D_n → Q(D_n)]`. -/
noncomputable def qTower (D₀ : QDomain.{u}) : ℕ → QDomain.{u}
  | 0 => D₀
  | n + 1 =>
    { carrier := ScottMap (qTower D₀ n).carrier (qTower D₀ n).carrier
      omega := D₀.functionSpace_omega (qTower D₀ n).omega
      functionSpace_omega := D₀.functionSpace_omega }

@[simp] theorem qTower_zero (D₀ : QDomain.{u}) : qTower D₀ 0 = D₀ := rfl

theorem qTower_carrier_succ (D₀ : QDomain.{u}) (n : ℕ) :
    (qTower D₀ (n + 1)).carrier =
      ScottMap (qTower D₀ n).carrier (qTower D₀ n).carrier := rfl

/-- Stagewise `ωQVA` instance on Scott's function-space tower. -/
@[reducible] noncomputable def omegaOnTower (D₀ : QDomain.{u}) :
    (n : ℕ) → IsOmegaQVA (towerType ⟨D₀.carrier⟩ n)
  | 0 => D₀.omega
  | n + 1 => D₀.functionSpace_omega (omegaOnTower D₀ n)

/-- Carriers of the quantum tower agree with Scott's function-space tower
    at `n = 0`; both successor stages are function spaces. -/
theorem qTower_carrier_eq_towerType_zero (D₀ : QDomain.{u}) :
    (qTower D₀ 0).carrier = towerType ⟨D₀.carrier⟩ 0 :=
  rfl

/-- Inverse limit of the quantum tower. -/
abbrev QDInf (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor D₀.carrier)) :
    Type u :=
  InverseLimit (towerType ⟨D₀.carrier⟩) (towerProj ⟨D₀.carrier⟩ j₀)

end Scott1972.ContinuousLattice
