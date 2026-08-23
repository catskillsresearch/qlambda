/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.QuantumPower
import QLambda.QDomain
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

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Stage types of the quantum tower at `D₀`. -/
abbrev qD (M : QuantumPowerModel) (D₀ : QDomain.{u}) : ℕ → Type u :=
  qTowerType M ⟨D₀.carrier⟩

/-- Bonding projections of the quantum tower at `D₀`. -/
noncomputable abbrev qP (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    ∀ n, IsContinuousLatticeProjection (qD M D₀ n) (qD M D₀ (n + 1)) :=
  qTowerProj M ⟨D₀.carrier⟩ j₀

/-- `Q` applied to a Scott map. -/
noncomputable abbrev qMap (M : QuantumPowerModel)
    {A B : Type u} [CompleteLattice A] [CompleteLattice B]
    (f : ScottMap A B) : ScottMap (QuantumPower M A) (QuantumPower M B) :=
  IsQuantumPowerModel.map (Q := M.Power) f

/-- `ωQVA` structure on the inverse limit: retract of a countable
product of `ωQVA` stages. Requires `qTowerProj`. -/
@[reducible] noncomputable def qDInf_isOmegaQVA (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    IsOmegaQVA (QDInf M D₀ j₀) :=
  letI : ∀ n, IsOmegaQVA (qTowerType M ⟨D₀.carrier⟩ n) := omegaOnQTower M D₀
  letI : IsOmegaQVA (∀ n, qTowerType M ⟨D₀.carrier⟩ n) := omegaQVA_pi
  omegaQVA_of_retract
    (inverseLimitRetraction (qTowerType M ⟨D₀.carrier⟩) (qTowerProj M ⟨D₀.carrier⟩ j₀))

section LimitMaps

variable (M : QuantumPowerModel) (D₀ : QDomain.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier))

/-- The `n`-th summand of `i_∞`: `x ↦ Q(i_{n∞}) ∘ x_{n+1} ∘ j_{∞n}`. -/
noncomputable def qiInfTerm (n : ℕ) :
    ScottMap (QDInf M D₀ j₀) (QuantumFunctor M (QDInf M D₀ j₀)) :=
  (conjMapHom (qMap M (embInf (qD M D₀) (qP M D₀ j₀) n))
      (projInf (qD M D₀) (qP M D₀ j₀) n)).comp
    (projInf (qD M D₀) (qP M D₀ j₀) (n + 1))

@[simp] theorem qiInfTerm_apply (n : ℕ) (x z : QDInf M D₀ j₀) :
    (qiInfTerm M D₀ j₀ n x) z =
      qMap M (embInf (qD M D₀) (qP M D₀ j₀) n)
        ((x.1 (n + 1)) ((projInf (qD M D₀) (qP M D₀ j₀) n) z)) :=
  rfl

/-- Embedding `i_∞ : D_∞ → [D_∞ → Q(D_∞)]`. -/
noncomputable def qEmbInfInf :
    ScottMap (QDInf M D₀ j₀) (QuantumFunctor M (QDInf M D₀ j₀)) :=
  ⨆ n, qiInfTerm M D₀ j₀ n

theorem qEmbInfInf_apply (x : QDInf M D₀ j₀) :
    qEmbInfInf M D₀ j₀ x = ⨆ n, qiInfTerm M D₀ j₀ n x := by
  show (sSup (Set.range (qiInfTerm M D₀ j₀)) : ScottMap _ _) x = _
  rw [ScottMap.sSup_apply, ← Set.range_comp, sSup_range]
  rfl

/-- The `n`-th summand of `j_∞`: `f ↦ i_{(n+1)∞}(Q(j_{∞n}) ∘ f ∘ i_{n∞})`. -/
noncomputable def qjInfTerm (n : ℕ) :
    ScottMap (QuantumFunctor M (QDInf M D₀ j₀)) (QDInf M D₀ j₀) :=
  (embInf (qD M D₀) (qP M D₀ j₀) (n + 1)).comp
    (conjMapHom (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n))
      (embInf (qD M D₀) (qP M D₀ j₀) n))

@[simp] theorem qjInfTerm_apply (n : ℕ) (f : QuantumFunctor M (QDInf M D₀ j₀)) :
    qjInfTerm M D₀ j₀ n f =
      embInf (qD M D₀) (qP M D₀ j₀) (n + 1)
        (conjMapHom (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n))
          (embInf (qD M D₀) (qP M D₀ j₀) n) f) :=
  rfl

/-- Projection `j_∞ : [D_∞ → Q(D_∞)] → D_∞`. -/
noncomputable def qProjInfInf :
    ScottMap (QuantumFunctor M (QDInf M D₀ j₀)) (QDInf M D₀ j₀) :=
  ⨆ n, qjInfTerm M D₀ j₀ n

theorem qProjInfInf_apply (f : QuantumFunctor M (QDInf M D₀ j₀)) :
    qProjInfInf M D₀ j₀ f = ⨆ n, qjInfTerm M D₀ j₀ n f := by
  show (sSup (Set.range (qjInfTerm M D₀ j₀)) : ScottMap _ _) f = _
  rw [ScottMap.sSup_apply, ← Set.range_comp, sSup_range]
  rfl

theorem conjMapHom_iSup (n : ℕ)
    (post : ScottMap (QuantumPower M (QDInf M D₀ j₀)) (QuantumPower M (qD M D₀ n)))
    (pre : ScottMap (qD M D₀ n) (QDInf M D₀ j₀))
    (f : ℕ → ScottMap (QDInf M D₀ j₀) (QuantumPower M (QDInf M D₀ j₀)))
    (hf : Monotone f) :
    conjMapHom post pre (⨆ m, f m) = ⨆ m, conjMapHom post pre (f m) := by
  have hdir : DirectedOn (· ≤ ·) (Set.range f) :=
    directedOn_range.2 fun a b => ⟨max a b, hf (le_max_left a b), hf (le_max_right a b)⟩
  have hne := Set.range_nonempty f
  rw [show (⨆ m, f m) = sSup (Set.range f) from sSup_range.symm,
    (conjMapHom post pre).preservesDirectedSup_coe (Set.range f) hne hdir, ← Set.range_comp]
  rfl

theorem embInf_succ_iSup_q (n : ℕ) (f : ℕ → qD M D₀ (n + 1)) (hf : Monotone f) :
    embInf (qD M D₀) (qP M D₀ j₀) (n + 1) (⨆ m, f m) =
      ⨆ m, embInf (qD M D₀) (qP M D₀ j₀) (n + 1) (f m) := by
  have hdir : DirectedOn (· ≤ ·) (Set.range f) :=
    directedOn_range.2 fun a b => ⟨max a b, hf (le_max_left a b), hf (le_max_right a b)⟩
  have hne := Set.range_nonempty f
  rw [show (⨆ m, f m) = sSup (Set.range f) from sSup_range.symm,
    (embInf (qD M D₀) (qP M D₀ j₀) (n + 1)).preservesDirectedSup_coe
      (Set.range f) hne hdir, ← Set.range_comp]
  rfl

/-- `Q(j_{∞n}) ∘ Q(i_{n∞}) ∘ x_{n+1} ∘ j_{∞n} ∘ i_{n∞} = x_{n+1}`. -/
theorem conj_qiInfTerm_eq (n : ℕ) (x : QDInf M D₀ j₀) :
    conjMapHom (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n))
        (embInf (qD M D₀) (qP M D₀ j₀) n)
        (qiInfTerm M D₀ j₀ n x) =
      x.1 (n + 1) := by
  apply ScottMap.ext
  intro y
  have hy : (projInf (qD M D₀) (qP M D₀ j₀) n)
      (embInf (qD M D₀) (qP M D₀ j₀) n y) = y :=
    (proposition_4_2 (qD M D₀) (qP M D₀ j₀) n).retr_incl y
  have hcomp := IsQuantumPowerModel.map_comp (Q := M.Power)
    (f := projInf (qD M D₀) (qP M D₀ j₀) n)
    (g := embInf (qD M D₀) (qP M D₀ j₀) n)
  have hid' := IsQuantumPowerModel.map_id (Q := M.Power) (D := qD M D₀ n)
  have hpair : (projInf (qD M D₀) (qP M D₀ j₀) n).comp
      (embInf (qD M D₀) (qP M D₀ j₀) n) = ScottMap.idMap :=
    ScottMap.ext fun z =>
      (proposition_4_2 (qD M D₀) (qP M D₀ j₀) n).retr_incl z
  have hQid : (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n)).comp
      (qMap M (embInf (qD M D₀) (qP M D₀ j₀) n)) = ScottMap.idMap := by
    rw [← hcomp, hpair, hid']
  -- `conjMapHom post pre g y = post (g (pre y))`.
  change qMap M (projInf (qD M D₀) (qP M D₀ j₀) n)
      (qiInfTerm M D₀ j₀ n x (embInf (qD M D₀) (qP M D₀ j₀) n y)) =
    x.1 (n + 1) y
  rw [qiInfTerm_apply, hy]
  exact congrArg (fun g : ScottMap _ _ =>
      (g : _ → _) (qTowerToMap M ⟨D₀.carrier⟩ (x.1 (n + 1)) y)) hQid

theorem q_incl_projInf_le_projInf_succ (n : ℕ) (w : QDInf M D₀ j₀) :
    (qP M D₀ j₀ n).incl (projInf (qD M D₀) (qP M D₀ j₀) n w) ≤
      projInf (qD M D₀) (qP M D₀ j₀) (n + 1) w := by
  have h := (qP M D₀ j₀ n).incl_retr_le
    (projInf (qD M D₀) (qP M D₀ j₀) (n + 1) w)
  rwa [show (qP M D₀ j₀ n).retr (projInf (qD M D₀) (qP M D₀ j₀) (n + 1) w)
      = projInf (qD M D₀) (qP M D₀ j₀) n w from w.2 n] at h

theorem qiInfTerm_le_succ (x : QDInf M D₀ j₀) (m : ℕ) :
    qiInfTerm M D₀ j₀ m x ≤ qiInfTerm M D₀ j₀ (m + 1) x := by
  rw [ScottMap.le_def]
  intro z
  -- `Q(i_{m∞}) = Q(i_{(m+1)∞}) ∘ Q(i_m)` by `embInf_succ` and functoriality.
  have hclimb :
      qMap M (embInf (qD M D₀) (qP M D₀ j₀) m) =
        (qMap M (embInf (qD M D₀) (qP M D₀ j₀) (m + 1))).comp
          (qMap M (qP M D₀ j₀ m).incl) := by
    have hsucc : (embInf (qD M D₀) (qP M D₀ j₀) (m + 1)).comp
        (qP M D₀ j₀ m).incl =
        embInf (qD M D₀) (qP M D₀ j₀) m :=
      ScottMap.ext fun w => embInf_succ (qD M D₀) (qP M D₀ j₀) m w
    have hcomp := IsQuantumPowerModel.map_comp (Q := M.Power)
      (f := embInf (qD M D₀) (qP M D₀ j₀) (m + 1))
      (g := (qP M D₀ j₀ m).incl)
    rw [← hcomp, hsucc]
  have hab : (qP M D₀ j₀ m).incl (projInf (qD M D₀) (qP M D₀ j₀) m z) ≤
      projInf (qD M D₀) (qP M D₀ j₀) (m + 1) z :=
    q_incl_projInf_le_projInf_succ M D₀ j₀ m z
  have hmid :
      qMap M (qP M D₀ j₀ m).incl
          ((x.1 (m + 1)) (projInf (qD M D₀) (qP M D₀ j₀) m z)) ≤
        x.1 (m + 2) (projInf (qD M D₀) (qP M D₀ j₀) (m + 1) z) := by
    have hx : x.1 (m + 1) = (qP M D₀ j₀ (m + 1)).retr (x.1 (m + 2)) := (x.2 (m + 1)).symm
    calc
      qMap M (qP M D₀ j₀ m).incl
          ((x.1 (m + 1)) (projInf (qD M D₀) (qP M D₀ j₀) m z))
        = qMap M (qP M D₀ j₀ m).incl
            (((qP M D₀ j₀ (m + 1)).retr (x.1 (m + 2)))
              (projInf (qD M D₀) (qP M D₀ j₀) m z)) := by rw [hx]
      _ = qMap M (qP M D₀ j₀ m).incl
            (qMap M (qP M D₀ j₀ m).retr
              (x.1 (m + 2) ((qP M D₀ j₀ m).incl
                (projInf (qD M D₀) (qP M D₀ j₀) m z)))) := by
          rw [qTowerProj_succ_retr_apply]
      _ ≤ x.1 (m + 2) ((qP M D₀ j₀ m).incl
            (projInf (qD M D₀) (qP M D₀ j₀) m z)) :=
        (IsQuantumPowerModel.mapProjection (Q := M.Power) (qP M D₀ j₀ m)).incl_retr_le _
      _ ≤ x.1 (m + 2) (projInf (qD M D₀) (qP M D₀ j₀) (m + 1) z) :=
        ScottMap.monotone (x.1 (m + 2)) hab
  have hL :
      qiInfTerm M D₀ j₀ m x z =
        qMap M (embInf (qD M D₀) (qP M D₀ j₀) (m + 1))
          (qMap M (qP M D₀ j₀ m).incl
            ((x.1 (m + 1)) (projInf (qD M D₀) (qP M D₀ j₀) m z))) := by
    rw [qiInfTerm_apply, hclimb]
    rfl
  rw [hL, qiInfTerm_apply]
  exact (qMap M (embInf (qD M D₀) (qP M D₀ j₀) (m + 1))).monotone hmid

theorem qiInfTerm_monotone (x : QDInf M D₀ j₀) :
    Monotone (fun m => qiInfTerm M D₀ j₀ m x) :=
  monotone_nat_of_le_succ (qiInfTerm_le_succ M D₀ j₀ x)

theorem q_iSup₂_monotone_eq_diagonal {α : Type*} [CompleteLattice α] (f : ℕ → ℕ → α)
    (hfm : ∀ n, Monotone (f n)) (hfn : ∀ m, Monotone (fun n => f n m)) :
    ⨆ n, ⨆ m, f n m = ⨆ n, f n n := by
  apply le_antisymm
  · refine iSup_le fun n => iSup_le fun m => ?_
    have hk : n ≤ n ⊔ m := le_sup_left
    have hk' : m ≤ n ⊔ m := le_sup_right
    calc f n m ≤ f (n ⊔ m) m := hfn m hk
      _ ≤ f (n ⊔ m) (n ⊔ m) := hfm (n ⊔ m) hk'
      _ ≤ ⨆ n', f n' n' := le_iSup (fun n' => f n' n') (n ⊔ m)
  · refine iSup_le fun n => le_trans (le_iSup (f n) n) (le_iSup (fun n' => ⨆ m, f n' m) n)

theorem conjMapHom_incl_le_conjMapHom_succ (n : ℕ)
    (f : QuantumFunctor M (QDInf M D₀ j₀)) :
    (qP M D₀ j₀ (n + 1)).incl
        (conjMapHom (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n))
          (embInf (qD M D₀) (qP M D₀ j₀) n) f) ≤
      conjMapHom (qMap M (projInf (qD M D₀) (qP M D₀ j₀) (n + 1)))
        (embInf (qD M D₀) (qP M D₀ j₀) (n + 1)) f := by
  refine ScottMap.le_def.mpr fun y => ?_
  -- `incl_{n+1}(g) y = Q(incl_n) (g (retr_n y))`
  change qMap M (qP M D₀ j₀ n).incl
      (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n)
        (f (embInf (qD M D₀) (qP M D₀ j₀) n ((qP M D₀ j₀ n).retr y)))) ≤
    qMap M (projInf (qD M D₀) (qP M D₀ j₀) (n + 1))
      (f (embInf (qD M D₀) (qP M D₀ j₀) (n + 1) y))
  have hpre : embInf (qD M D₀) (qP M D₀ j₀) n ((qP M D₀ j₀ n).retr y) ≤
      embInf (qD M D₀) (qP M D₀ j₀) (n + 1) y := by
    rw [← embInf_succ (qD M D₀) (qP M D₀ j₀) n ((qP M D₀ j₀ n).retr y)]
    exact embInf_monotone (qD M D₀) (qP M D₀ j₀) (n + 1)
      ((qP M D₀ j₀ n).incl_retr_le y)
  have h1 : qMap M (qP M D₀ j₀ n).incl
      (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n)
        (f (embInf (qD M D₀) (qP M D₀ j₀) n ((qP M D₀ j₀ n).retr y)))) ≤
      qMap M (qP M D₀ j₀ n).incl
        (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n)
          (f (embInf (qD M D₀) (qP M D₀ j₀) (n + 1) y))) :=
    (qMap M (qP M D₀ j₀ n).incl).monotone
      ((qMap M (projInf (qD M D₀) (qP M D₀ j₀) n)).monotone (f.monotone hpre))
  refine le_trans h1 ?_
  -- `Q(i_n) ∘ Q(j_{∞n}) ⊑ Q(j_{∞(n+1)})` at `f (i_{(n+1)∞} y)`.
  have hpair : (qP M D₀ j₀ n).incl.comp
      (projInf (qD M D₀) (qP M D₀ j₀) n) ≤
      projInf (qD M D₀) (qP M D₀ j₀) (n + 1) := by
    intro w
    exact q_incl_projInf_le_projInf_succ M D₀ j₀ n w
  have hQ : qMap M ((qP M D₀ j₀ n).incl.comp
      (projInf (qD M D₀) (qP M D₀ j₀) n)) ≤
      qMap M (projInf (qD M D₀) (qP M D₀ j₀) (n + 1)) :=
    IsQuantumPowerModel.map_mono (Q := M.Power) hpair
  have hcomp := IsQuantumPowerModel.map_comp (Q := M.Power)
    (f := (qP M D₀ j₀ n).incl)
    (g := projInf (qD M D₀) (qP M D₀ j₀) n)
  have : (qMap M (qP M D₀ j₀ n).incl).comp
      (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n)) ≤
      qMap M (projInf (qD M D₀) (qP M D₀ j₀) (n + 1)) := by
    rw [← hcomp]
    exact hQ
  exact this (f (embInf (qD M D₀) (qP M D₀ j₀) (n + 1) y))

theorem qProjInfInf_qEmbInfInf_eq (x : QDInf M D₀ j₀) :
    qProjInfInf M D₀ j₀ (qEmbInfInf M D₀ j₀ x) =
      ⨆ n, embInf (qD M D₀) (qP M D₀ j₀) (n + 1) (x.1 (n + 1)) := by
  rw [qProjInfInf_apply]
  set g := fun n m =>
    embInf (qD M D₀) (qP M D₀ j₀) (n + 1)
      (conjMapHom (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n))
        (embInf (qD M D₀) (qP M D₀ j₀) n)
        (qiInfTerm M D₀ j₀ m x)) with hg
  have hmono (n : ℕ) : Monotone (fun m =>
      conjMapHom (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n))
        (embInf (qD M D₀) (qP M D₀ j₀) n)
        (qiInfTerm M D₀ j₀ m x)) := fun a b hab =>
    (conjMapHom (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n))
      (embInf (qD M D₀) (qP M D₀ j₀) n)).monotone
      (ScottMap.le_def.mpr (qiInfTerm_monotone M D₀ j₀ x hab))
  have hinner (n : ℕ) : qjInfTerm M D₀ j₀ n (qEmbInfInf M D₀ j₀ x) = ⨆ m, g n m :=
    calc qjInfTerm M D₀ j₀ n (qEmbInfInf M D₀ j₀ x)
        = embInf (qD M D₀) (qP M D₀ j₀) (n + 1)
            (⨆ m, conjMapHom (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n))
              (embInf (qD M D₀) (qP M D₀ j₀) n)
              (qiInfTerm M D₀ j₀ m x)) := by
          rw [qjInfTerm_apply, qEmbInfInf_apply,
            conjMapHom_iSup M D₀ j₀ n
              (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n))
              (embInf (qD M D₀) (qP M D₀ j₀) n)
              (fun m => qiInfTerm M D₀ j₀ m x) (qiInfTerm_monotone M D₀ j₀ x)]
          rfl
      _ = ⨆ m, embInf (qD M D₀) (qP M D₀ j₀) (n + 1)
            (conjMapHom (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n))
              (embInf (qD M D₀) (qP M D₀ j₀) n)
              (qiInfTerm M D₀ j₀ m x)) :=
          embInf_succ_iSup_q M D₀ j₀ n _ (hmono n)
      _ = ⨆ m, g n m := by simp only [hg]
  have g_mono_m (n : ℕ) : Monotone (g n) := by
    intro a b hab
    rw [hg]
    exact (embInf (qD M D₀) (qP M D₀ j₀) (n + 1)).monotone
      ((conjMapHom (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n))
        (embInf (qD M D₀) (qP M D₀ j₀) n)).monotone
        (ScottMap.le_def.mpr (qiInfTerm_monotone M D₀ j₀ x hab)))
  have g_mono_n_succ (m n : ℕ) : g n m ≤ g (n + 1) m := by
    rw [hg]
    dsimp only
    rw [← embInf_succ (qD M D₀) (qP M D₀ j₀) (n + 1)
        (conjMapHom (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n))
          (embInf (qD M D₀) (qP M D₀ j₀) n)
          (qiInfTerm M D₀ j₀ m x))]
    exact embInf_monotone (qD M D₀) (qP M D₀ j₀) (n + 2)
      (conjMapHom_incl_le_conjMapHom_succ M D₀ j₀ n (qiInfTerm M D₀ j₀ m x))
  have g_mono_n (m : ℕ) : Monotone (fun n => g n m) :=
    monotone_nat_of_le_succ (g_mono_n_succ m)
  have hin : (⨆ n, qjInfTerm M D₀ j₀ n (qEmbInfInf M D₀ j₀ x)) = ⨆ n, ⨆ m, g n m := by
    congr 1
    funext n
    exact hinner n
  rw [hin, q_iSup₂_monotone_eq_diagonal g g_mono_m g_mono_n]
  congr 1
  funext n
  rw [hg]
  dsimp only
  rw [conj_qiInfTerm_eq M D₀ j₀ n x]

theorem qProjInfInf_comp_qEmbInfInf :
    (qProjInfInf M D₀ j₀).comp (qEmbInfInf M D₀ j₀) = ScottMap.idMap := by
  apply ScottMap.ext
  intro x
  have hmono : Monotone (fun k => embInf (qD M D₀) (qP M D₀ j₀) k (x.1 k)) :=
    monotone_nat_of_le_succ (embInf_le_succ (qD M D₀) (qP M D₀ j₀) x)
  rw [ScottMap.comp_apply, ScottMap.idMap_apply, qProjInfInf_qEmbInfInf_eq M D₀ j₀ x,
    Monotone.iSup_nat_add hmono 1]
  exact (inverseLimit_eq_iSup (qD M D₀) (qP M D₀ j₀) x).symm

theorem qTowerProj_retr_conjMapHom_succ (n : ℕ)
    (f : QuantumFunctor M (QDInf M D₀ j₀)) :
    (qP M D₀ j₀ (n + 1)).retr
        (conjMapHom (qMap M (projInf (qD M D₀) (qP M D₀ j₀) (n + 1)))
          (embInf (qD M D₀) (qP M D₀ j₀) (n + 1)) f) =
      conjMapHom (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n))
        (embInf (qD M D₀) (qP M D₀ j₀) n) f := by
  apply ScottMap.ext
  intro y
  -- `retr_{n+1}(g) y = Q(retr_n) (g (incl_n y))`
  change qMap M (qP M D₀ j₀ n).retr
      (qMap M (projInf (qD M D₀) (qP M D₀ j₀) (n + 1))
        (f (embInf (qD M D₀) (qP M D₀ j₀) (n + 1) ((qP M D₀ j₀ n).incl y)))) =
    qMap M (projInf (qD M D₀) (qP M D₀ j₀) n)
      (f (embInf (qD M D₀) (qP M D₀ j₀) n y))
  -- `i_{(n+1)∞} ∘ i_n = i_{n∞}` and `j_{∞n} = j_n ∘ j_{∞(n+1)}`.
  rw [embInf_succ (qD M D₀) (qP M D₀ j₀) n y]
  -- `j_{∞n} w = retr_n (j_{∞(n+1)} w)`, so
  -- `Q(j_{∞n}) = Q(retr_n) ∘ Q(j_{∞(n+1)})`.
  have hproj : projInf (qD M D₀) (qP M D₀ j₀) n =
      (qP M D₀ j₀ n).retr.comp
        (projInf (qD M D₀) (qP M D₀ j₀) (n + 1)) :=
    ScottMap.ext fun w => (w.2 n).symm ▸ rfl
  -- After `embInf_succ`, the argument of `f` matches, so this is
  -- `Q(retr_n) (Q(j_{∞(n+1)}) (f (i_{n∞} y))) = Q(j_{∞n}) (f (i_{n∞} y))`.
  have hQ : qMap M (qP M D₀ j₀ n).retr ∘
      qMap M (projInf (qD M D₀) (qP M D₀ j₀) (n + 1)) =
      qMap M (projInf (qD M D₀) (qP M D₀ j₀) n) := by
    have hcomp := IsQuantumPowerModel.map_comp (Q := M.Power)
      (f := (qP M D₀ j₀ n).retr)
      (g := projInf (qD M D₀) (qP M D₀ j₀) (n + 1))
    have : (qMap M (qP M D₀ j₀ n).retr).comp
        (qMap M (projInf (qD M D₀) (qP M D₀ j₀) (n + 1))) =
        qMap M (projInf (qD M D₀) (qP M D₀ j₀) n) := by
      rw [← hcomp, ← hproj]
    exact funext fun z => congrArg (fun g : ScottMap _ _ => (g : _ → _) z) this
  exact congrArg (fun g => g (f (embInf (qD M D₀) (qP M D₀ j₀) n y))) hQ

theorem qEmbInfInf_comp_qProjInfInf :
    (qEmbInfInf M D₀ j₀).comp (qProjInfInf M D₀ j₀) = ScottMap.idMap := by
  apply ScottMap.ext
  intro f
  rw [ScottMap.comp_apply, ScottMap.idMap_apply]
  apply ScottMap.ext
  intro z
  set r : ℕ → ScottMap (QDInf M D₀ j₀) (QDInf M D₀ j₀) :=
    fun n => (embInf (qD M D₀) (qP M D₀ j₀) n).comp
              (projInf (qD M D₀) (qP M D₀ j₀) n) with hr
  have hrw : ∀ n (w : QDInf M D₀ j₀), r n w
      = embInf (qD M D₀) (qP M D₀ j₀) n
          (projInf (qD M D₀) (qP M D₀ j₀) n w) := by
    intro n w
    simp only [hr, ScottMap.comp_apply]
  have hr_mono : ∀ (w : QDInf M D₀ j₀), Monotone (fun m => r m w) := by
    intro w
    refine monotone_nat_of_le_succ (fun m => ?_)
    show r m w ≤ r (m + 1) w
    rw [hrw, hrw]
    exact embInf_le_succ (qD M D₀) (qP M D₀ j₀) w m
  have hA : ∀ (w : QDInf M D₀ j₀), w = ⨆ m, r m w := by
    intro w
    have h1 : (⨆ m, r m w)
        = ⨆ m, embInf (qD M D₀) (qP M D₀ j₀) m
                (projInf (qD M D₀) (qP M D₀ j₀) m w) :=
      iSup_congr (fun m => hrw m w)
    rw [h1]
    exact inverseLimit_eq_iSup (qD M D₀) (qP M D₀ j₀) w
  have hsup_apply : ∀ (g : ℕ → ScottMap (QDInf M D₀ j₀) (QuantumPower M (QDInf M D₀ j₀)))
      (w : QDInf M D₀ j₀),
      (⨆ n, g n) w = ⨆ n, g n w := by
    intro g w
    rw [show (⨆ n, g n) = sSup (Set.range g) from sSup_range.symm,
      ScottMap.sSup_apply, ← Set.range_comp, sSup_range]
    rfl
  have hcontD : ∀ (g : ScottMap (QDInf M D₀ j₀) (QDInf M D₀ j₀))
      (a : ℕ → QDInf M D₀ j₀),
      Monotone a → g (⨆ m, a m) = ⨆ m, g (a m) := by
    intro g a ha
    have hdir : DirectedOn (· ≤ ·) (Set.range a) :=
      directedOn_range.2 fun i j => ⟨max i j, ha (le_max_left i j), ha (le_max_right i j)⟩
    rw [show (⨆ m, a m) = sSup (Set.range a) from sSup_range.symm,
      g.preservesDirectedSup_coe (Set.range a) (Set.range_nonempty a) hdir,
      ← Set.range_comp, sSup_range]
    rfl
  have hcontQ : ∀ (g : ScottMap (QDInf M D₀ j₀) (QuantumPower M (QDInf M D₀ j₀)))
      (a : ℕ → QDInf M D₀ j₀),
      Monotone a → g (⨆ m, a m) = ⨆ m, g (a m) := by
    intro g a ha
    have hdir : DirectedOn (· ≤ ·) (Set.range a) :=
      directedOn_range.2 fun i j => ⟨max i j, ha (le_max_left i j), ha (le_max_right i j)⟩
    rw [show (⨆ m, a m) = sSup (Set.range a) from sSup_range.symm,
      g.preservesDirectedSup_coe (Set.range a) (Set.range_nonempty a) hdir,
      ← Set.range_comp, sSup_range]
    rfl
  have hpi : qProjInfInf M D₀ j₀ f
      = ⨆ k, embInf (qD M D₀) (qP M D₀ j₀) (k + 1)
          (conjMapHom (qMap M (projInf (qD M D₀) (qP M D₀ j₀) k))
            (embInf (qD M D₀) (qP M D₀ j₀) k) f) := by
    rw [qProjInfInf_apply]
    exact iSup_congr (fun n => qjInfTerm_apply M D₀ j₀ n f)
  have hcoord : ∀ n, (qProjInfInf M D₀ j₀ f).1 (n + 1)
      = conjMapHom (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n))
          (embInf (qD M D₀) (qP M D₀ j₀) n) f := by
    intro n
    rw [hpi]
    exact lemma_4_5 (qD M D₀) (qP M D₀ j₀)
      (fun k => conjMapHom (qMap M (projInf (qD M D₀) (qP M D₀ j₀) k))
        (embInf (qD M D₀) (qP M D₀ j₀) k) f)
      (fun m => qTowerProj_retr_conjMapHom_succ M D₀ j₀ m f) n
  have hev : qEmbInfInf M D₀ j₀ (qProjInfInf M D₀ j₀ f) z
      = ⨆ n, (qiInfTerm M D₀ j₀ n (qProjInfInf M D₀ j₀ f)) z := by
    rw [qEmbInfInf_apply]
    exact hsup_apply (fun n => qiInfTerm M D₀ j₀ n (qProjInfInf M D₀ j₀ f)) z
  -- Each summand is `Q(r_n) (f (r_n z))`.
  have hterm : ∀ n,
      (qiInfTerm M D₀ j₀ n (qProjInfInf M D₀ j₀ f)) z =
        qMap M (r n) (f (r n z)) := by
    intro n
    rw [qiInfTerm_apply, hcoord n]
    -- `Q(i_{n∞}) ∘ Q(j_{∞n}) = Q(r_n)`
    have hrn : r n = (embInf (qD M D₀) (qP M D₀ j₀) n).comp
        (projInf (qD M D₀) (qP M D₀ j₀) n) := rfl
    have hQ : qMap M (embInf (qD M D₀) (qP M D₀ j₀) n) ∘
        qMap M (projInf (qD M D₀) (qP M D₀ j₀) n) =
        qMap M (r n) := by
      have hcomp := IsQuantumPowerModel.map_comp (Q := M.Power)
        (f := embInf (qD M D₀) (qP M D₀ j₀) n)
        (g := projInf (qD M D₀) (qP M D₀ j₀) n)
      have : (qMap M (embInf (qD M D₀) (qP M D₀ j₀) n)).comp
          (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n)) =
          qMap M (r n) := by
        rw [← hcomp]
      exact funext fun t => congrArg (fun g : ScottMap _ _ => (g : _ → _) t) this
    change qMap M (embInf (qD M D₀) (qP M D₀ j₀) n)
        (qMap M (projInf (qD M D₀) (qP M D₀ j₀) n)
          (f (embInf (qD M D₀) (qP M D₀ j₀) n
            (projInf (qD M D₀) (qP M D₀ j₀) n z)))) =
      qMap M (r n) (f (r n z))
    simpa [hrw] using congrArg (fun g => g (f (r n z))) hQ
  have hmono_frz : Monotone (fun m => f (r m z)) :=
    fun a b hab => f.monotone (hr_mono z hab)
  have hfm : ∀ n, Monotone (fun m => qMap M (r n) (f (r m z))) :=
    fun n _ _ hab => (qMap M (r n)).monotone (f.monotone (hr_mono z hab))
  have hfn : ∀ m, Monotone (fun n => qMap M (r n) (f (r m z))) := by
    intro m a b hab
    -- `r` is monotone in the index, so `Q(r_a) ≤ Q(r_b)`.
    have : r a ≤ r b := by
      rw [ScottMap.le_def]
      intro w
      exact hr_mono w hab
    exact IsQuantumPowerModel.map_mono (Q := M.Power) this (f (r m z))
  have hcontR : ∀ n (a : ℕ → QuantumPower M (QDInf M D₀ j₀)),
      Monotone a → qMap M (r n) (⨆ m, a m) = ⨆ m, qMap M (r n) (a m) := by
    intro n a ha
    have hdir : DirectedOn (· ≤ ·) (Set.range a) :=
      directedOn_range.2 fun i j => ⟨max i j, ha (le_max_left i j), ha (le_max_right i j)⟩
    rw [show (⨆ m, a m) = sSup (Set.range a) from sSup_range.symm,
      (qMap M (r n)).preservesDirectedSup_coe (Set.range a) (Set.range_nonempty a) hdir,
      ← Set.range_comp, sSup_range]
    rfl
  have hmono_r : Monotone r := by
    intro a b hab
    rw [ScottMap.le_def]
    intro w
    exact hr_mono w hab
  have hidQ : (⨆ n, qMap M (r n)) = ScottMap.idMap := by
    have hr : (⨆ n, r n) = ScottMap.idMap :=
      (idInf_eq_iSup (qD M D₀) (qP M D₀ j₀)).symm
    have hpres := IsQuantumPowerModel.map_iSup (Q := M.Power) r hmono_r
    have hid := IsQuantumPowerModel.map_id (Q := M.Power) (D := QDInf M D₀ j₀)
    calc (⨆ n, qMap M (r n)) = qMap M (⨆ n, r n) := hpres.symm
      _ = qMap M (ScottMap.idMap : ScottMap (QDInf M D₀ j₀) (QDInf M D₀ j₀)) := by
            rw [hr]
      _ = ScottMap.idMap := hid
  have hsupQ : ∀ (g : ℕ → ScottMap (QuantumPower M (QDInf M D₀ j₀))
        (QuantumPower M (QDInf M D₀ j₀)))
      (w : QuantumPower M (QDInf M D₀ j₀)),
      (⨆ n, g n) w = ⨆ n, g n w := by
    intro g w
    rw [show (⨆ n, g n) = sSup (Set.range g) from sSup_range.symm,
      ScottMap.sSup_apply, ← Set.range_comp, sSup_range]
    rfl
  have hfz : f z = ⨆ n, qMap M (r n) (f (r n z)) :=
    calc f z = ⨆ k, qMap M (r k) (f z) := by
          have h1 : (⨆ n, qMap M (r n)) (f z) = f z := by
            rw [hidQ, ScottMap.idMap_apply]
          exact h1.symm.trans (hsupQ (fun n => qMap M (r n)) (f z))
      _ = ⨆ k, qMap M (r k) (f (⨆ m, r m z)) := by
            refine iSup_congr fun k => ?_
            rw [← hA z]
      _ = ⨆ k, qMap M (r k) (⨆ m, f (r m z)) := by
            refine iSup_congr fun k => ?_
            rw [hcontQ f (fun m => r m z) (hr_mono z)]
      _ = ⨆ k, ⨆ m, qMap M (r k) (f (r m z)) :=
            iSup_congr fun k => hcontR k (fun m => f (r m z)) hmono_frz
      _ = ⨆ n, qMap M (r n) (f (r n z)) :=
            q_iSup₂_monotone_eq_diagonal (fun n m => qMap M (r n) (f (r m z)))
              hfm hfn
  calc qEmbInfInf M D₀ j₀ (qProjInfInf M D₀ j₀ f) z
      = ⨆ n, (qiInfTerm M D₀ j₀ n (qProjInfInf M D₀ j₀ f)) z := hev
    _ = ⨆ n, qMap M (r n) (f (r n z)) := iSup_congr hterm
    _ = f z := hfz.symm

theorem qProjInfInf_qEmbInfInf (x : QDInf M D₀ j₀) :
    qProjInfInf M D₀ j₀ (qEmbInfInf M D₀ j₀ x) = x := by
  have h := congrArg (fun g => g x) (qProjInfInf_comp_qEmbInfInf M D₀ j₀)
  simpa [ScottMap.comp_apply, ScottMap.idMap_apply] using h

theorem qEmbInfInf_qProjInfInf (f : QuantumFunctor M (QDInf M D₀ j₀)) :
    qEmbInfInf M D₀ j₀ (qProjInfInf M D₀ j₀ f) = f := by
  have h := congrArg (fun g => g f) (qEmbInfInf_comp_qProjInfInf M D₀ j₀)
  simpa [ScottMap.comp_apply, ScottMap.idMap_apply] using h

/-- Order isomorphism `D_∞ ≃o [D_∞ → Q(D_∞)]`. -/
noncomputable def qDInf_orderIso :
    QDInf M D₀ j₀ ≃o ScottMap (QDInf M D₀ j₀) (QuantumPower M (QDInf M D₀ j₀)) :=
  (Equiv.mk (qEmbInfInf M D₀ j₀) (qProjInfInf M D₀ j₀)
      (qProjInfInf_qEmbInfInf M D₀ j₀) (qEmbInfInf_qProjInfInf M D₀ j₀)).toOrderIso
    (qEmbInfInf M D₀ j₀).monotone (qProjInfInf M D₀ j₀).monotone

end LimitMaps

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
