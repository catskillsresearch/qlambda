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
only Mathlib. Challenge is allowed `sorry`. The intended claim is
`D_∞ ≅ [D_∞ → Q(D_∞)]` for a quantum powerdomain `Q`, not Scott's
`[D_∞ → D_∞]`.
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

/-- Quantum state powerdomain `Q(D)`. -/
noncomputable def QuantumPower (D : Type u) [CompleteLattice D] : Type u := by
  sorry

noncomputable instance instCompleteLatticeQuantumPower (D : Type u) [CompleteLattice D] :
    CompleteLattice (QuantumPower D) := by
  sorry

/-- `[D → Q(D)]`. -/
abbrev QuantumFunctor (D : Type u) [CompleteLattice D] : Type u :=
  ScottMap D (QuantumPower D)

/-- `ωQVA` is closed under the quantum powerdomain. -/
noncomputable def omegaQVA_closed_under_quantumPower {D : Type u} [CompleteLattice D]
    (h : IsOmegaQVA D) : IsOmegaQVA (QuantumPower D) := by
  sorry

/-- `ωQVA` is Cartesian closed. -/
noncomputable def omegaQVA_closed_under_functionSpace {D E : Type u}
    [CompleteLattice D] [CompleteLattice E]
    (hD : IsOmegaQVA D) (hE : IsOmegaQVA E) : IsOmegaQVA (ScottMap D E) := by
  sorry

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

/-- The quantum tower as a sequence of `QDomain`s. -/
noncomputable def qTower (D₀ : QDomain.{u}) : ℕ → QDomain.{u}
  | 0 => D₀
  | n + 1 =>
    { carrier := ScottMap (qTower D₀ n).carrier (QuantumPower (qTower D₀ n).carrier)
      omega :=
        omegaQVA_closed_under_functionSpace (qTower D₀ n).omega
          (omegaQVA_closed_under_quantumPower (qTower D₀ n).omega) }

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

/-- Compared capstone: `D_∞` is in `ωQVA` and `D_∞ ≅ [D_∞ → Q(D_∞)]`. -/
theorem omegaQVA_quantum_domain_equation_solved
    (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor D₀.carrier)) :
    Nonempty (IsOmegaQVA (QDInf D₀ j₀)) ∧
    (qProjInfInf D₀ j₀).comp (qEmbInfInf D₀ j₀) = ScottMap.idMap ∧
    (qEmbInfInf D₀ j₀).comp (qProjInfInf D₀ j₀) = ScottMap.idMap ∧
    Nonempty (QDInf D₀ j₀ ≃o ScottMap (QDInf D₀ j₀) (QuantumPower (QDInf D₀ j₀))) ∧
    (ScottMap.idMap : ScottMap (QDInf D₀ j₀) (QDInf D₀ j₀)) =
      ⨆ n, (embInf (qTowerType ⟨D₀.carrier⟩) (qTowerProj ⟨D₀.carrier⟩ j₀) n).comp
            (projInf (qTowerType ⟨D₀.carrier⟩) (qTowerProj ⟨D₀.carrier⟩ j₀) n) := by
  sorry

@[reducible] noncomputable def qDInf_isOmegaQVA
    (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor D₀.carrier)) :
    IsOmegaQVA (QDInf D₀ j₀) := by
  sorry

/-- **Chen–Kou–Lyu Lemma 6.8.** A finitely separated Scott map satisfies `f x ≪ x`. -/
theorem finitelySeparated_wayBelow (hD : IsContinuousLattice D) {f : ScottMap D D}
    (hf : FinitelySeparated f) (x : D) : (f : D → D) x ≪ x := by
  sorry

end Scott1972.ContinuousLattice
