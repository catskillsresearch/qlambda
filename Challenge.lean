/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Directed
import Mathlib.Order.Hom.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Topology.Order.ScottTopology

/-!
# Palomar statement of record (ωQVA quantum domain equation)

This module states the compared capstone and its type surface. It imports
only Mathlib. Challenge is allowed `sorry`. `IsQuantumPowerModel` is the
spec of a quantum powerdomain. Both unweakened carriers of `arxiv.md` §5
are instances. The capstone is parameterized by a bundled
`QuantumPowerModel` and applied to (V) and (S).
-/

open Matrix
open scoped MatrixOrder ComplexOrder

/-- Sub-normalized density operator on `M_n(ℂ)`: positive semidefinite
with real trace at most one. -/
structure SubNormalizedDensity (n : ℕ) where
  mat : Matrix (Fin n) (Fin n) ℂ
  posSemidef : mat.PosSemidef
  trace_le_one : (Matrix.trace mat).re ≤ 1

namespace SubNormalizedDensity

variable {n : ℕ}

instance : PartialOrder (SubNormalizedDensity n) where
  le ρ σ := ρ.mat ≤ σ.mat
  le_refl ρ := le_refl ρ.mat
  le_trans ρ σ τ := le_trans
  le_antisymm ρ σ hρσ hσρ := by
    cases ρ; cases σ; congr
    exact le_antisymm hρσ hσρ

instance : OrderBot (SubNormalizedDensity n) where
  bot := ⟨0, PosSemidef.zero, by simp [Matrix.trace_zero]⟩
  bot_le ρ := by
    change (ρ.mat - 0).PosSemidef
    simpa using ρ.posSemidef

end SubNormalizedDensity

namespace Scott1972.ContinuousLattice

open Set

universe u

section InducedTopology

variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

/-- **Scott 1972, §2, the induced topology.** -/
def ScottOpen (U : Set D) : Prop :=
  IsUpperSet U ∧
    ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → sSup S ∈ U → (S ∩ U).Nonempty

/-- **Scott 1972, §2.** The *way-below* relation. -/
def WayBelow (x y : D) : Prop :=
  ∃ U : Set D, ScottOpen U ∧ y ∈ U ∧ U ⊆ Set.Ici x

@[inherit_doc] scoped infix:50 " ≪ " => WayBelow

def IsContinuousLattice (D : Type*) [CompleteLattice D] : Prop :=
  ∀ y : D, IsLUB {x | x ≪ y} y

/-- Scott's induced topology on a complete lattice, realized as mathlib's Scott topology. -/
@[reducible] noncomputable def scottTopologicalSpace : TopologicalSpace D :=
  Topology.scott D univ

/-- Continuous maps between complete lattices with Scott's induced topologies. -/
def ScottMap (D D' : Type*) [CompleteLattice D] [CompleteLattice D'] : Type _ :=
  { f : D → D' // @Continuous D D' scottTopologicalSpace scottTopologicalSpace f }

namespace ScottMap

instance : CoeFun (ScottMap D D') (fun _ => D → D') where
  coe f := f.1

@[ext]
theorem ext {f g : ScottMap D D'} (h : ∀ x, f x = g x) : f = g :=
  Subtype.ext (funext h)

instance instPartialOrder : PartialOrder (ScottMap D D') where
  le f g := ∀ x, (f : D → D') x ≤ g x
  le_refl _ _ := le_refl _
  le_trans _ _ _ hfg hgh x := le_trans (hfg x) (hgh x)
  le_antisymm _ _ hfg hgf := ScottMap.ext fun x => le_antisymm (hfg x) (hgf x)

noncomputable instance instSupSet : SupSet (ScottMap D D') := by
  sorry

noncomputable instance instCompleteLattice : CompleteLattice (ScottMap D D') := by
  sorry

/-- The identity Scott map. -/
noncomputable def idMap : ScottMap D D := by
  sorry

noncomputable def comp (f : ScottMap D' D'') (g : ScottMap D D') : ScottMap D D'' := by
  sorry

end ScottMap

/-- **Scott 1972, Definition 3.6.** A *retraction* of continuous lattices. -/
structure IsContinuousLatticeRetraction (D D' : Type*) [CompleteLattice D] [CompleteLattice D']
    where
  incl : ScottMap D D'
  retr : ScottMap D' D
  retr_incl : ∀ d, retr (incl d) = d

/-- **Scott 1972, Definition 3.6.** A *projection* of continuous lattices. -/
structure IsContinuousLatticeProjection (D D' : Type*) [CompleteLattice D] [CompleteLattice D']
    extends IsContinuousLatticeRetraction D D' where
  incl_retr_le : ∀ d, incl (retr d) ≤ d

end InducedTopology

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- Compatibility of a sequence: `jₙ(x_{n+1}) = xₙ` for all `n`. -/
def Compatible (x : ∀ n, D n) : Prop :=
  ∀ n, (P n).retr (x (n + 1)) = x n

/-- **Scott 1972, §4.** The inverse limit `D_∞` as the subspace of compatible sequences. -/
abbrev InverseLimit : Type u :=
  {x : ∀ n, D n // Compatible D P x}

noncomputable instance instCompleteLattice : CompleteLattice (InverseLimit D P) := by
  sorry

end InverseLimit

/-- A complete lattice bundled with its instance. -/
structure CLat : Type (u + 1) where
  carrier : Type u
  [str : CompleteLattice carrier]

attribute [instance] CLat.str

/-- The embedding `i_{n∞} : Dₙ → D_∞`, Scott-continuous. -/
noncomputable def embInf (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
    (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1))) (n : ℕ) :
    ScottMap (D n) (InverseLimit D P) := by
  sorry

/-- The projection `j_{∞n} : D_∞ → Dₙ`, Scott-continuous. -/
noncomputable def projInf (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
    (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1))) (n : ℕ) :
    ScottMap (InverseLimit D P) (D n) := by
  sorry

/-- Finite product of Loewner spectrahedra, one block per matrix size. -/
def DensityVec : List ℕ → Type
  | [] => PUnit
  | n :: ns => SubNormalizedDensity n × DensityVec ns

namespace DensityVec

instance instPartialOrder : (ns : List ℕ) → PartialOrder (DensityVec ns)
  | [] => inferInstanceAs (PartialOrder PUnit)
  | _ :: ns =>
    haveI := instPartialOrder ns
    inferInstanceAs (PartialOrder (_ × _))

instance instOrderBot : (ns : List ℕ) → OrderBot (DensityVec ns)
  | [] => { bot := ⟨⟩, bot_le := fun _ => trivial }
  | _ :: ns =>
    haveI := instOrderBot ns
    inferInstanceAs (OrderBot (_ × _))

end DensityVec

variable {D E : Type*} [CompleteLattice D] [CompleteLattice E]

/-- `a` factors through `DensityVec dims` via monotone encoding and reconstruction. -/
structure QFactorable (a : ScottMap D E) where
  dims : List ℕ
  enc : D → DensityVec dims
  recon : DensityVec dims → E
  enc_mono : Monotone enc
  recon_mono : Monotone recon
  factor : ∀ x, (a : D → E) x = recon (enc x)

/-- Jung / CKL finite separator. -/
def FinitelySeparated (f : ScottMap D D) : Prop :=
  ∃ M : Finset D, ∀ x, ∃ m ∈ M, (f : D → D) x ≤ m ∧ m ≤ x

/-- A continuous lattice whose identity is a directed supremum of
Q-factorable, finitely separated approximants. -/
class IsOmegaQVA (D : Type*) [CompleteLattice D] where
  isContinuousLattice : IsContinuousLattice D
  approx : ℕ → ScottMap D D
  qfactorable : ∀ n, QFactorable (approx n)
  separated : ∀ n, FinitelySeparated (approx n)
  monotone_approx : Monotone approx
  iSup_approx : (⨆ n, approx n) = ScottMap.idMap

/-- The empty set is Scott-open. -/
theorem scottOpen_empty : ScottOpen (∅ : Set D) :=
  ⟨isUpperSet_empty, fun _ _ _ hmem => False.elim hmem⟩

/-- Scott-opens of `D`, ordered by inclusion. -/
abbrev ScottOpens (D : Type*) [CompleteLattice D] := { U : Set D // ScottOpen U }

/-- **(V)** A quantum valuation on `D` valued in a fixed finite `DensityVec`. -/
structure QuantumValuation (D : Type*) [CompleteLattice D] (dims : List ℕ) where
  val : ScottOpens D → DensityVec dims
  monotone : Monotone val
  map_empty : val ⟨∅, scottOpen_empty⟩ = ⊥

/-- **(V)** Quantum valuations with a varying finite algebra. -/
def QuantumValuationPower (D : Type u) [CompleteLattice D] : Type u :=
  Σ dims : List ℕ, QuantumValuation D dims

/-- **(S)** The saturation carrier as an endofunctor on complete lattices. -/
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

/-- Carrier of the model at `D`. -/
abbrev QuantumPower (M : QuantumPowerModel) (D : Type u) [CompleteLattice D] : Type u :=
  M.Power D

/-- `[D → Q(D)]` for the chosen model. -/
abbrev QuantumFunctor (M : QuantumPowerModel) (D : Type u) [CompleteLattice D] : Type u :=
  ScottMap D (M.Power D)

/-- `ωQVA` is closed under the model's powerdomain. -/
abbrev omegaQVA_closed_under_quantumPower (M : QuantumPowerModel) {D : Type u}
    [CompleteLattice D] (h : IsOmegaQVA D) : IsOmegaQVA (M.Power D) :=
  IsQuantumPowerModel.closed (Q := M.Power) h

/-- `ωQVA` is Cartesian closed (not a field of the spec). -/
noncomputable def omegaQVA_closed_under_functionSpace {D E : Type u}
    [CompleteLattice D] [CompleteLattice E]
    (hD : IsOmegaQVA D) (hE : IsOmegaQVA E) : IsOmegaQVA (ScottMap D E) := by
  sorry

/-- **(V)** bundled as a quantum model. -/
noncomputable def valuationModel : QuantumPowerModel :=
  ⟨QuantumValuationPower⟩

/-- **(S)** bundled as a quantum model. -/
noncomputable def saturationModel : QuantumPowerModel :=
  ⟨QuantumSaturationPower⟩

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

/-- The quantum tower as a sequence of `QDomain`s. -/
noncomputable def qTower (M : QuantumPowerModel) (D₀ : QDomain.{u}) : ℕ → QDomain.{u}
  | 0 => D₀
  | n + 1 =>
    { carrier := ScottMap (qTower M D₀ n).carrier (QuantumPower M (qTower M D₀ n).carrier)
      omega :=
        omegaQVA_closed_under_functionSpace (qTower M D₀ n).omega
          (omegaQVA_closed_under_quantumPower M (qTower M D₀ n).omega) }

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

/-- Compared capstone, parameterized by a quantum powerdomain model. -/
theorem omegaQVA_quantum_domain_equation_solved
    (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    Nonempty (IsOmegaQVA (QDInf M D₀ j₀)) ∧
    (qProjInfInf M D₀ j₀).comp (qEmbInfInf M D₀ j₀) = ScottMap.idMap ∧
    (qEmbInfInf M D₀ j₀).comp (qProjInfInf M D₀ j₀) = ScottMap.idMap ∧
    Nonempty (QDInf M D₀ j₀ ≃o ScottMap (QDInf M D₀ j₀) (QuantumPower M (QDInf M D₀ j₀))) ∧
    (ScottMap.idMap : ScottMap (QDInf M D₀ j₀) (QDInf M D₀ j₀)) =
      ⨆ n, (embInf (qTowerType M ⟨D₀.carrier⟩) (qTowerProj M ⟨D₀.carrier⟩ j₀) n).comp
            (projInf (qTowerType M ⟨D₀.carrier⟩) (qTowerProj M ⟨D₀.carrier⟩ j₀) n) := by
  sorry

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
              (qTowerProj valuationModel ⟨D₀.carrier⟩ j₀) n) := by
  sorry

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
              (qTowerProj saturationModel ⟨D₀.carrier⟩ j₀) n) := by
  sorry

@[reducible] noncomputable def qDInf_isOmegaQVA (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    IsOmegaQVA (QDInf M D₀ j₀) := by
  sorry

/-- **Chen–Kou–Lyu Lemma 6.8.** A finitely separated Scott map satisfies `f x ≪ x`. -/
theorem finitelySeparated_wayBelow (hD : IsContinuousLattice D) {f : ScottMap D D}
    (hf : FinitelySeparated f) (x : D) : (f : D → D) x ≪ x := by
  sorry

end Scott1972.ContinuousLattice
