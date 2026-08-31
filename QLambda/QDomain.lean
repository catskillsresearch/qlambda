/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.QuantumPower
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

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A pointed object of `ωQVA`. -/
structure QDomain : Type (u + 1) where
  carrier : Type u
  [str : CompleteLattice carrier]
  omega : IsOmegaQVA carrier

attribute [instance] QDomain.str

/-- The canonical one-point quantum domain, used as the base of the
quantum-domain tower when no additional base data is needed. -/
@[reducible] noncomputable def canonicalQDomain : QDomain.{u} where
  carrier := PUnit.{u + 1}
  omega := omegaQVA_pUnit

/-- The canonical initial projection from the one-point base into
`[PUnit → Q(PUnit)]`.

The inclusion `incl` sends the unique base point to the bottom Scott map.
The retraction `retr` goes in the important reverse direction—from the
quantum function space back to the one-point base—and is necessarily the
unique constant map. -/
noncomputable def canonicalQDomainProjection (M : QuantumPowerModel) :
    IsContinuousLatticeProjection canonicalQDomain.carrier
      (QuantumFunctor M canonicalQDomain.carrier) where
  incl :=
    (⊥ : ScottMap canonicalQDomain.carrier
      (QuantumFunctor M canonicalQDomain.carrier))
  retr :=
    ScottMap.const (D := QuantumFunctor M canonicalQDomain.carrier)
      (⟨⟩ : canonicalQDomain.carrier)
  retr_incl := by
    intro d
    cases d
    rfl
  incl_retr_le := by
    intro f
    rw [ScottMap.le_def]
    intro x
    rw [ScottMap.bot_apply, ScottMap.bot_apply]
    exact bot_le

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

/-- View an element of `D_{n+1}` as the Scott map `[Dₙ → Q(Dₙ)]` it is. -/
def qTowerToMap (M : QuantumPowerModel) (D₀ : CLat.{u}) {n : ℕ}
    (f : qTowerType M D₀ (n + 1)) :
    ScottMap (qTowerType M D₀ n) (QuantumPower M (qTowerType M D₀ n)) :=
  f

instance qTowerCoeFun (M : QuantumPowerModel) (D₀ : CLat.{u}) {n : ℕ} :
    CoeFun (qTowerType M D₀ (n + 1))
      (fun _ => qTowerType M D₀ n → QuantumPower M (qTowerType M D₀ n)) where
  coe f := qTowerToMap M D₀ f

@[simp] theorem qTowerToMap_coe (M : QuantumPowerModel) (D₀ : CLat.{u}) {n : ℕ}
    (f : qTowerType M D₀ (n + 1)) (x : qTowerType M D₀ n) :
    qTowerToMap M D₀ f x = f x :=
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

/-! Mixed conjugation `f ↦ post ∘ f ∘ pre` on `[D → E]`, Scott-continuous
because directed suprema of Scott maps are pointwise. The diagonal case
`[Y → Y]` is vendor `conjMap`; this is the form needed for `[X → Q(X)]`. -/

section ConjHom

open Set

variable {D E F W : Type u} [CompleteLattice D] [CompleteLattice E]
  [CompleteLattice F] [CompleteLattice W]

/-- Conjugation `f ↦ post ∘ f ∘ pre` as a bare function. -/
def conjMapHomFun (post : ScottMap E F) (pre : ScottMap W D) (f : ScottMap D E) :
    ScottMap W F :=
  post.comp (f.comp pre)

theorem conjMapHom_preservesDirectedSup (post : ScottMap E F) (pre : ScottMap W D) :
    PreservesDirectedSup (conjMapHomFun post pre) := by
  intro S hS hSdir
  apply ScottMap.ext
  intro x
  have hdir : DirectedOn (· ≤ ·) ((fun f : ScottMap D E => f (pre x)) '' S) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
    exact ⟨c (pre x), ⟨c, hc, rfl⟩, hac (pre x), hbc (pre x)⟩
  show post ((sSup S : ScottMap D E) (pre x)) =
      (sSup (conjMapHomFun post pre '' S) : ScottMap W F) x
  rw [ScottMap.sSup_apply S (pre x), post.preservesDirectedSup_coe _ (hS.image _) hdir,
    ScottMap.sSup_apply, Set.image_image, Set.image_image]
  rfl

/-- Conjugation `f ↦ post ∘ f ∘ pre` as a Scott map `[D → E] → [W → F]`. -/
noncomputable def conjMapHom (post : ScottMap E F) (pre : ScottMap W D) :
    ScottMap (ScottMap D E) (ScottMap W F) :=
  ⟨conjMapHomFun post pre,
    continuous_of_preservesDirectedSup (conjMapHom_preservesDirectedSup post pre)⟩

@[simp] theorem conjMapHom_apply (post : ScottMap E F) (pre : ScottMap W D)
    (f : ScottMap D E) (x : W) :
    conjMapHom post pre f x = post (f (pre x)) :=
  rfl

end ConjHom

/-- **Proposition 3.7, mixed.** If `A ◃ B` and `QA ◃ QB`, then
`[A → QA] ◃ [B → QB]` via `f ↦ i_Q ∘ f ∘ j` and `g ↦ j_Q ∘ g ∘ i`. -/
noncomputable def IsContinuousLatticeProjection.quantumFunctionSpace
    {A B QA QB : Type u}
    [CompleteLattice A] [CompleteLattice B]
    [CompleteLattice QA] [CompleteLattice QB]
    (P : IsContinuousLatticeProjection A B)
    (PQ : IsContinuousLatticeProjection QA QB) :
    IsContinuousLatticeProjection (ScottMap A QA) (ScottMap B QB) where
  incl := conjMapHom PQ.incl P.retr
  retr := conjMapHom PQ.retr P.incl
  retr_incl f := by
    apply ScottMap.ext
    intro x
    simp only [conjMapHom_apply, P.retr_incl, PQ.retr_incl]
  incl_retr_le g := by
    rw [ScottMap.le_def]
    intro x
    simp only [conjMapHom_apply]
    exact le_trans (PQ.incl_retr_le _) (g.monotone (P.incl_retr_le x))

/-- Bonding projections `j_{n+1} = F(j_n)` for `F(X) = [X → Q(X)]`. -/
noncomputable def qTowerProj (M : QuantumPowerModel) (D₀ : CLat.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    ∀ n, IsContinuousLatticeProjection (qTowerType M D₀ n) (qTowerType M D₀ (n + 1))
  | 0 => j₀
  | n + 1 =>
    (qTowerProj M D₀ j₀ n).quantumFunctionSpace
      (IsQuantumPowerModel.mapProjection (Q := M.Power) (qTowerProj M D₀ j₀ n))

theorem qTowerProj_zero (M : QuantumPowerModel) (D₀ : CLat.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    qTowerProj M D₀ j₀ 0 = j₀ :=
  rfl

theorem qTowerProj_succ (M : QuantumPowerModel) (D₀ : CLat.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) (n : ℕ) :
    qTowerProj M D₀ j₀ (n + 1) =
      (qTowerProj M D₀ j₀ n).quantumFunctionSpace
        (IsQuantumPowerModel.mapProjection (Q := M.Power) (qTowerProj M D₀ j₀ n)) :=
  rfl

theorem qTowerProj_succ_incl_apply (M : QuantumPowerModel) (D₀ : CLat.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier))
    (n : ℕ) (x : qTowerType M D₀ (n + 1)) (y : qTowerType M D₀ (n + 1)) :
    qTowerToMap M D₀ ((qTowerProj M D₀ j₀ (n + 1)).incl x) y =
      IsQuantumPowerModel.map (Q := M.Power) (qTowerProj M D₀ j₀ n).incl
        (qTowerToMap M D₀ x ((qTowerProj M D₀ j₀ n).retr y)) :=
  rfl

theorem qTowerProj_succ_retr_apply (M : QuantumPowerModel) (D₀ : CLat.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier))
    (n : ℕ) (x' : qTowerType M D₀ (n + 2)) (y : qTowerType M D₀ n) :
    qTowerToMap M D₀ ((qTowerProj M D₀ j₀ (n + 1)).retr x') y =
      IsQuantumPowerModel.map (Q := M.Power) (qTowerProj M D₀ j₀ n).retr
        (qTowerToMap M D₀ x' ((qTowerProj M D₀ j₀ n).incl y)) :=
  rfl

/-- Inverse limit of the quantum tower. -/
abbrev QDInf (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    Type u :=
  InverseLimit (qTowerType M ⟨D₀.carrier⟩) (qTowerProj M ⟨D₀.carrier⟩ j₀)

end Scott1972.ContinuousLattice
