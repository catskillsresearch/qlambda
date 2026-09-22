/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Order.CompleteSublattice
import Mathlib.Order.Hom.CompleteLattice
import QLambda.Domain.Enriched

/-!
# Bilimits of finite recursive-type approximants

The carrier constructed here is concrete: an element is a compatible
sequence of finite-stage approximants.  No universal untyped domain is
used.  A recursive type supplies its own chain.
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
  orderBot := inferInstance
  omegaComplete := inferInstance

/-- Equality is determined by all finite approximants. -/
theorem ext {x y : C.Bilimit}
    (h : ∀ n, C.projection n x = C.projection n y) : x = y := by
  apply Subtype.ext
  funext n
  exact h n

end ProjectionChain

/-- A fold/unfold solution of a locally continuous recursive-object
equation.  Concrete models construct this record from a projection
chain; clients consume the proved isomorphism rather than an axiom. -/
structure RecursiveObject (C : OmegaCategory) (F : C.Functor C) where
  carrier : C.Obj
  fold : C.Hom (F.obj carrier) carrier
  unfold : C.Hom carrier (F.obj carrier)
  fold_unfold : C.comp fold unfold = C.id
  unfold_fold : C.comp unfold fold = C.id

end QLambda.Domain
