/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Order.CompleteSublattice
import Mathlib.Order.Hom.CompleteLattice
import QLambda.Domain.Enriched

/-!
# Projection chains and bilimits
-/

namespace QLambda.Domain

universe u

/-- An inverse chain of complete lattices.  The projection maps preserve
all infima and suprema; in particular they preserve ω-chain limits. -/
structure ProjectionChain where
  Stage : ℕ → Type u
  complete : ∀ n, CompleteLattice (Stage n)
  project : ∀ n, CompleteLatticeHom (Stage (n + 1)) (Stage n)

attribute [instance] ProjectionChain.complete

namespace ProjectionChain

variable (C : ProjectionChain.{u})

/-- Compatibility equations for a sequence of approximants. -/
def Compatible (x : ∀ n, C.Stage n) : Prop :=
  ∀ n, C.project n (x (n + 1)) = x n

private theorem compatible_sSup {s : Set (∀ n, C.Stage n)}
    (hs : s ⊆ {x | C.Compatible x}) :
    C.Compatible (sSup s) := by
  intro n
  simp only [sSup_eq_iSup, iSup_apply]
  rw [map_iSup]
  apply iSup_congr
  intro x
  rw [map_iSup]
  apply iSup_congr
  intro hx
  exact hs hx n

private theorem compatible_sInf {s : Set (∀ n, C.Stage n)}
    (hs : s ⊆ {x | C.Compatible x}) :
    C.Compatible (sInf s) := by
  intro n
  simp only [sInf_eq_iInf, iInf_apply]
  rw [map_iInf]
  apply iInf_congr
  intro x
  rw [map_iInf]
  apply iInf_congr
  intro hx
  exact hs hx n

/-- Compatible sequences form a complete sublattice of the pointwise
function lattice. -/
def compatibleSublattice : CompleteSublattice (∀ n, C.Stage n) :=
  CompleteSublattice.mk' {x | C.Compatible x}
    (fun _ hs => C.compatible_sSup hs)
    (fun _ hs => C.compatible_sInf hs)

/-- The bilimit carrier of the projection chain. -/
abbrev Bilimit : Type u :=
  C.compatibleSublattice

/-- The `n`th finite approximation of a bilimit element. -/
def projection (n : ℕ) : C.Bilimit → C.Stage n :=
  fun x => x.1 n

@[simp] theorem projection_compatible (x : C.Bilimit) (n : ℕ) :
    C.project n (C.projection (n + 1) x) = C.projection n x :=
  by
    have hx : C.Compatible x := x.2
    exact hx n

/-- The bilimit is automatically a pointed ωCPO because it is a
complete lattice. -/
noncomputable def bilimitOmegaObject : OmegaObject where
  Carrier := C.Bilimit
  partialOrder := inferInstance
  omegaComplete := inferInstance

/-- Equality is determined by all finite approximants. -/
theorem ext {x y : C.Bilimit}
    (h : ∀ n, C.projection n x = C.projection n y) : x = y := by
  apply Subtype.ext
  funext n
  exact h n

/-- The tail chain drops the zeroth approximation. -/
abbrev tail : ProjectionChain where
  Stage n := C.Stage (n + 1)
  complete n := C.complete (n + 1)
  project n := C.project (n + 1)

/-- Unfold a compatible chain by dropping its zeroth approximation. -/
def shiftForward (x : C.Bilimit) : C.tail.Bilimit :=
  ⟨fun n => x.1 (n + 1), fun n => x.2 (n + 1)⟩

/-- Fold a tail-compatible chain by restoring the uniquely determined zeroth
approximation. -/
def shiftBackward (x : C.tail.Bilimit) : C.Bilimit where
  val
    | 0 => C.project 0 (x.1 0)
    | n + 1 => x.1 n
  property := by
    intro n
    cases n with
    | zero => rfl
    | succ n => exact x.2 n

@[simp] theorem shiftForward_shiftBackward (x : C.tail.Bilimit) :
    C.shiftForward (C.shiftBackward x) = x := by
  apply C.tail.ext
  intro n
  rfl

@[simp] theorem shiftBackward_shiftForward (x : C.Bilimit) :
    C.shiftBackward (C.shiftForward x) = x := by
  apply C.ext
  intro n
  cases n with
  | zero => exact x.2 0
  | succ n => rfl

/-- Dropping the zeroth approximation is ω-continuous. -/
noncomputable def shiftForwardMap :
    OmegaMap C.bilimitOmegaObject C.tail.bilimitOmegaObject where
  toFun := C.shiftForward
  monotone := by
    intro x y h
    exact fun n => h (n + 1)
  map_ωSup c hc := by
    change (ℕ → C.Bilimit) at c
    change C.shiftForward (⨆ k, c k) =
      ⨆ k, C.shiftForward (c k)
    apply C.tail.ext
    intro n
    simp only [projection, shiftForward, CompleteSublattice.coe_iSup]
    rw [iSup_apply, iSup_apply]

/-- Restoring the uniquely determined zeroth approximation is
ω-continuous. -/
noncomputable def shiftBackwardMap :
    OmegaMap C.tail.bilimitOmegaObject C.bilimitOmegaObject where
  toFun := C.shiftBackward
  monotone := by
    intro x y h
    intro n
    cases n with
    | zero =>
        have hxy : x.1 0 ⊔ y.1 0 = y.1 0 :=
          sup_eq_right.mpr (h 0)
        calc
          C.project 0 (x.1 0) ≤
              C.project 0 (x.1 0) ⊔ C.project 0 (y.1 0) := le_sup_left
          _ = C.project 0 (x.1 0 ⊔ y.1 0) :=
            (map_sup (C.project 0) _ _).symm
          _ = C.project 0 (y.1 0) :=
            congrArg (C.project 0) hxy
    | succ n => exact h n
  map_ωSup c hc := by
    change (ℕ → C.tail.Bilimit) at c
    change C.shiftBackward (⨆ k, c k) =
      ⨆ k, C.shiftBackward (c k)
    apply C.ext
    intro n
    cases n with
    | zero =>
        simp only [projection, shiftBackward, CompleteSublattice.coe_iSup]
        rw [iSup_apply, iSup_apply]
        simp only
        simpa [tail] using
          (map_iSup (C.project 0) (fun i => (c i).1 0))
    | succ n =>
        simp only [projection, shiftBackward, CompleteSublattice.coe_iSup]
        rw [iSup_apply, iSup_apply]

/-- Every projection-chain bilimit is continuously isomorphic to the
bilimit of its tail.  These are the generic fold/unfold maps used by
strictly-positive recursive-object chains. -/
noncomputable def shiftIso :
    OmegaCategory.Iso omegaMapCategory
      C.bilimitOmegaObject C.tail.bilimitOmegaObject where
  hom := C.shiftForwardMap
  inv := C.shiftBackwardMap
  hom_inv := by
    apply OmegaMap.ext
    intro x
    exact C.shiftForward_shiftBackward x
  inv_hom := by
    apply OmegaMap.ext
    intro x
    exact C.shiftBackward_shiftForward x

end ProjectionChain

end QLambda.Domain
