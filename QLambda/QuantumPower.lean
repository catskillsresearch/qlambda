/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.OmegaQVA
import Scott1972.ContinuousLattice.FunctionSpaces

/-!
# The quantum state powerdomain `Q(D)`

`IsQuantumPowerModel Q` is the spec of a quantum powerdomain: `Q`
sends complete lattices to complete lattices, is a Scott functor
(including monotonicity and local continuity on monotone `ℕ`-families),
and preserves `ωQVA`. Both unweakened carriers are instances
(arxiv.md, §5):

* **(V)** `QuantumValuationPower` — Jones–Plotkin-style quantum
  valuations: monotone maps from Scott-opens of `D` to a finite
  `DensityVec`.
* **(S)** `QuantumSaturationPower` — compatible families of finite
  densities along an `ωQVA` approximate identity, extended to all
  complete lattices.

A `QuantumPowerModel` is a bundled `Q` with its instance. The capstone
is parameterized by that bundle and applied to both instances.
-/

namespace Scott1972.ContinuousLattice

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open DensityVec

section Carriers

variable {D E F : Type u} [CompleteLattice D] [CompleteLattice E] [CompleteLattice F]

/-- The empty set is Scott-open. -/
theorem scottOpen_empty : ScottOpen (∅ : Set D) :=
  ⟨isUpperSet_empty, fun _ _ _ hmem => False.elim hmem⟩

/-- Scott-opens of `D`, ordered by inclusion. -/
abbrev ScottOpens (D : Type*) [CompleteLattice D] := { U : Set D // ScottOpen U }

/-- **(V)** A quantum valuation on `D` valued in a fixed finite
`DensityVec dims` (the size parameter: one algebra, or a finite
direct sum). Directed-union continuity is the remaining axiom. -/
structure QuantumValuation (D : Type*) [CompleteLattice D] (dims : List ℕ) where
  val : ScottOpens D → DensityVec dims
  monotone : Monotone val
  map_empty : val ⟨∅, scottOpen_empty⟩ = ⊥

/-- **(V)** Quantum valuations with a varying finite algebra. -/
def QuantumValuationPower (D : Type u) [CompleteLattice D] : Type u :=
  Σ dims : List ℕ, QuantumValuation D dims

/-- Bonding of finite densities along the `ωQVA` approximate identity:
the reconstructed points satisfy `recon_n(ρ_n) = a_n(recon_{n+1}(ρ_{n+1}))`. -/
def QuantumSaturationCompatible [IsOmegaQVA D]
    (ρ : ∀ n, DensityVec (IsOmegaQVA.qfactorable (D := D) n).dims) : Prop :=
  ∀ n,
    (IsOmegaQVA.qfactorable (D := D) n).recon (ρ n) =
      (IsOmegaQVA.approx n : D → D)
        ((IsOmegaQVA.qfactorable (D := D) (n + 1)).recon (ρ (n + 1)))

/-- Compatible families of finite densities, on `ωQVA` objects. -/
def QuantumSaturationFamily [IsOmegaQVA D] :=
  { ρ : ∀ n, DensityVec (IsOmegaQVA.qfactorable (D := D) n).dims //
    QuantumSaturationCompatible ρ }

/-- **(S)** The saturation carrier, as an endofunctor on complete
lattices. On `ωQVA` objects this is `QuantumSaturationFamily`; the
extension off `ωQVA` is not yet constructed. -/
noncomputable def QuantumSaturationPower (D : Type u) [CompleteLattice D] : Type u := by
  sorry

end Carriers

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
  /-- Order-enriched: `Q` is monotone on Scott maps. Needed so that a
  projection `A ◃ B` lifts to `Q(A) ◃ Q(B)` (`mapProjection`). -/
  map_mono : ∀ {D E : Type u} [CompleteLattice D] [CompleteLattice E]
      {f g : ScottMap D E},
    letI := str D
    letI := str E
    f ≤ g → map f ≤ map g
  /-- Local continuity on monotone `ℕ`-families: `Q(⨆ F n) = ⨆ Q(F n)`.
  This is the fragment of local continuity used to collapse
  `i_∞ ∘ j_∞ = id` on `[D_∞ → Q(D_∞)]`. -/
  map_iSup : ∀ {D E : Type u} [CompleteLattice D] [CompleteLattice E]
      (F : ℕ → ScottMap D E) (_hF : Monotone F),
    letI := str D
    letI := str E
    map (⨆ n, F n) = ⨆ n, map (F n)
  closed : ∀ {D : Type u} [CompleteLattice D] (_h : IsOmegaQVA D),
    letI := str D
    IsOmegaQVA (Q D)

attribute [instance] IsQuantumPowerModel.str

/-- `j ∘ i = id` as Scott maps. -/
theorem IsContinuousLatticeProjection.retr_incl_comp {A B : Type u}
    [CompleteLattice A] [CompleteLattice B]
    (P : IsContinuousLatticeProjection A B) :
    P.retr.comp P.incl = ScottMap.idMap :=
  ScottMap.ext fun x => P.retr_incl x

/-- `i ∘ j ⊑ id` as Scott maps. -/
theorem IsContinuousLatticeProjection.incl_retr_le_comp {A B : Type u}
    [CompleteLattice A] [CompleteLattice B]
    (P : IsContinuousLatticeProjection A B) :
    P.incl.comp P.retr ≤ ScottMap.idMap :=
  P.incl_retr_le

/-- A Scott functor sends a projection `A ◃ B` to a projection `Q(A) ◃ Q(B)`. -/
noncomputable def IsQuantumPowerModel.mapProjection
    {Q : (D : Type u) → [CompleteLattice D] → Type u} [inst : IsQuantumPowerModel Q]
    {A B : Type u} [CompleteLattice A] [CompleteLattice B]
    (P : IsContinuousLatticeProjection A B) :
    IsContinuousLatticeProjection (Q A) (Q B) :=
  letI := inst.str A
  letI := inst.str B
  { incl := inst.map P.incl
    retr := inst.map P.retr
    retr_incl := by
      intro d
      have hcomp := inst.map_comp (f := P.retr) (g := P.incl)
      have hid := inst.map_id (D := A)
      have hri := P.retr_incl_comp
      have : (inst.map P.retr).comp (inst.map P.incl) = ScottMap.idMap := by
        rw [← hcomp, hri, hid]
      exact congrArg (fun f : ScottMap (Q A) (Q A) => (f : Q A → Q A) d) this
    incl_retr_le := by
      intro d
      have hcomp := inst.map_comp (f := P.incl) (g := P.retr)
      have hid := inst.map_id (D := B)
      have hle := inst.map_mono (f := P.incl.comp P.retr) (g := ScottMap.idMap)
        P.incl_retr_le_comp
      have : (inst.map P.incl).comp (inst.map P.retr) ≤ ScottMap.idMap :=
        calc (inst.map P.incl).comp (inst.map P.retr)
            = inst.map (P.incl.comp P.retr) := hcomp.symm
          _ ≤ inst.map ScottMap.idMap := hle
          _ = ScottMap.idMap := hid
      exact this d }

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

end Scott1972.ContinuousLattice
