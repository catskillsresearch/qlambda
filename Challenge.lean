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

This module states the **single compared Palomar capstone** and the Mathlib
type surface it depends on. Challenge may use `sorry`; Solution supplies the
proofs.

The selected capstone takes only a bundled `QuantumPowerModel` and starts from
a canonical one-point `QDomain`. Its stage-zero embedding–retraction pair maps
the point to the bottom function and has bonding retraction
`[PUnit → Q(PUnit)] ↠ PUnit`.

The theorem proves that the inverse limit `D_∞` of
`D_{n+1} = [D_n → Q(D_n)]` lies in ωQVA, that the constructed limit embedding
and projection between `D_∞` and `[D_∞ → Q(D_∞)]` are mutual inverses, that
`D_∞` is order-isomorphic to its function space, and that Scott's inverse-limit
identity holds on the quantum tower.

Concrete models and the language/hardware development are outside this surface.
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

/-- Pointwise suprema of Scott maps. This is a Comparator definition hole:
Solution supplies the proved Scott-continuous construction. -/
noncomputable instance instSupSet : SupSet (ScottMap D D') := by
  sorry

/-- The pointwise complete-lattice structure on Scott maps. -/
noncomputable instance instCompleteLattice : CompleteLattice (ScottMap D D') := by
  sorry

/-- The identity Scott map `x ↦ x`. -/
noncomputable def idMap : ScottMap D D := by
  sorry

/-- Scott-map composition, with underlying function `x ↦ f (g x)`. -/
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

/-- The inverse-limit complete lattice. Its infima are inherited pointwise
from the product and restricted to compatible sequences. -/
noncomputable instance instCompleteLattice : CompleteLattice (InverseLimit D P) := by
  sorry

end InverseLimit

/-- A complete lattice bundled with its instance. -/
structure CLat : Type (u + 1) where
  carrier : Type u
  [str : CompleteLattice carrier]

attribute [instance] CLat.str

/-- The embedding `i_{n∞} : Dₙ → D_∞`, obtained by climbing with `incl`
above stage `n` and descending with `retr` below it. -/
noncomputable def embInf (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
    (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1))) (n : ℕ) :
    ScottMap (D n) (InverseLimit D P) := by
  sorry

/-- The coordinate projection `j_{∞n} : D_∞ → Dₙ`. -/
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

/-- The one-point lattice is in `ωQVA`: its identity sequence factors through
`DensityVec [] = PUnit` and the unique point is a finite separator. -/
@[reducible] noncomputable def omegaQVA_pUnit : IsOmegaQVA PUnit.{u + 1} := by
  sorry

/-- Conditional specification of a quantum powerdomain model. -/
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
  map_mono : ∀ {D E : Type u} [CompleteLattice D] [CompleteLattice E]
      {f g : ScottMap D E},
    letI := str D
    letI := str E
    f ≤ g → map f ≤ map g
  map_iSup : ∀ {D E : Type u} [CompleteLattice D] [CompleteLattice E]
      (F : ℕ → ScottMap D E) (_hF : Monotone F),
    letI := str D
    letI := str E
    map (⨆ n, F n) = ⨆ n, map (F n)
  closed : ∀ {D : Type u} [CompleteLattice D] (h : IsOmegaQVA D),
    letI := str D
    IsOmegaQVA (Q D)

attribute [instance] IsQuantumPowerModel.str

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

/-- A pointed object of `ωQVA`. -/
structure QDomain : Type (u + 1) where
  carrier : Type u
  [str : CompleteLattice carrier]
  omega : IsOmegaQVA carrier

attribute [instance] QDomain.str

/-- The canonical one-point initial object used by the selected capstone. -/
@[reducible] noncomputable def canonicalQDomain : QDomain.{u} where
  carrier := PUnit.{u + 1}
  omega := omegaQVA_pUnit

/-- The canonical stage-zero embedding–projection pair. Its inclusion sends
the unique point to the bottom element of `[PUnit → Q(PUnit)]`; its retraction
is the unique map `[PUnit → Q(PUnit)] → PUnit`. -/
noncomputable def canonicalQDomainProjection (M : QuantumPowerModel) :
    IsContinuousLatticeProjection canonicalQDomain.carrier
      (QuantumFunctor M canonicalQDomain.carrier) := by
  sorry

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

/-- Bonding embedding–projection pairs, recursively lifted by
`F(X) = [X → Q(X)]`; stage zero is the supplied pair `j₀`. Compatibility uses
the retraction `(qTowerProj M D₀ j₀ n).retr : D_{n+1} → D_n`. -/
noncomputable def qTowerProj (M : QuantumPowerModel) (D₀ : CLat.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    ∀ n, IsContinuousLatticeProjection (qTowerType M D₀ n) (qTowerType M D₀ (n + 1)) := by
  sorry

/-- Inverse limit of the quantum tower. -/
abbrev QDInf (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    Type u :=
  InverseLimit (qTowerType M ⟨D₀.carrier⟩) (qTowerProj M ⟨D₀.carrier⟩ j₀)

/-- Limit embedding `i_∞ : D_∞ → [D_∞ → Q(D_∞)]`, the supremum of its
finite-stage conjugation terms. -/
noncomputable def qEmbInfInf (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    ScottMap (QDInf M D₀ j₀) (QuantumFunctor M (QDInf M D₀ j₀)) := by
  sorry

/-- Limit projection `j_∞ : [D_∞ → Q(D_∞)] → D_∞`, the supremum of its
finite-stage conjugation terms. -/
noncomputable def qProjInfInf (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    ScottMap (QuantumFunctor M (QDInf M D₀ j₀)) (QDInf M D₀ j₀) := by
  sorry

/-- **Compared Palomar capstone.** For every bundled quantum power model, use
the canonical one-point domain and projection pair. The resulting inverse
limit satisfies five claims: (1) it lies in `ωQVA`; (2) limit projection after
embedding is the identity; (3) limit embedding after projection is the
identity; (4) it is order-isomorphic to `[D_∞ → Q(D_∞)]`; and (5) Scott's
bilimit identity `id = ⨆ n, embInf n ∘ projInf n` holds. -/
theorem canonical_omegaQVA_quantum_domain_equation_solved
    (M : QuantumPowerModel) :
    let D₀ := canonicalQDomain
    let j₀ := canonicalQDomainProjection M
    let Dinf := QDInf M D₀ j₀
    Nonempty (IsOmegaQVA Dinf) ∧
    (qProjInfInf M D₀ j₀).comp (qEmbInfInf M D₀ j₀) = ScottMap.idMap ∧
    (qEmbInfInf M D₀ j₀).comp (qProjInfInf M D₀ j₀) = ScottMap.idMap ∧
    Nonempty (Dinf ≃o ScottMap Dinf (QuantumPower M Dinf)) ∧
    (ScottMap.idMap : ScottMap Dinf Dinf) =
      ⨆ n, (embInf (qTowerType M ⟨D₀.carrier⟩)
          (qTowerProj M ⟨D₀.carrier⟩ j₀) n).comp
        (projInf (qTowerType M ⟨D₀.carrier⟩)
          (qTowerProj M ⟨D₀.carrier⟩ j₀) n) := by
  sorry

end Scott1972.ContinuousLattice
