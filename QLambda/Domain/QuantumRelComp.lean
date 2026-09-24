/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumRel
/-!
# Composition, dagger, and quantum functions
-/

open Matrix

namespace QLambda.Domain

namespace QuantumRel

variable {X Y Z W : QuantumSet}

/-- Identity relation: scalar multiples of `1` on matching atoms. -/
def id (X : QuantumSet) [DecidableEq X.Atom] : QuantumRel X X where
  component x y :=
    if h : x = y then
      h ▸ Submodule.span ℂ
        {(1 : Matrix (Fin (X.dim x)) (Fin (X.dim x)) ℂ)}
    else
      ⊥

/-- Finite products of operators through one intermediate atom. -/
def compThrough (S : QuantumRel Y Z) (R : QuantumRel X Y)
    (x : X.Atom) (y : Y.Atom) (z : Z.Atom) : OpSpace X Z x z :=
  Submodule.span ℂ
    { (s * r : QuantumSet.Op X Z x z) |
      (r : QuantumSet.Op X Y x y)
      (s : QuantumSet.Op Y Z y z)
      (_ : r ∈ R.component x y)
      (_ : s ∈ S.component y z) }

/-- Relational composition as the join of all intermediate atoms. -/
def comp (S : QuantumRel Y Z) (R : QuantumRel X Y) : QuantumRel X Z where
  component x z := ⨆ y, S.compThrough R x y z

/-- The dagger / converse relation. -/
def dagger (R : QuantumRel X Y) : QuantumRel Y X where
  component y x :=
    Submodule.span ℂ
      { (rᴴ : QuantumSet.Op Y X y x) |
        (r : QuantumSet.Op X Y x y) (_ : r ∈ R.component x y) }

/-- A function is a relation satisfying the ordinary graph equations
`F ∘ F† ≤ I` and `F† ∘ F ≥ I`. -/
def IsFunction [DecidableEq X.Atom] [DecidableEq Y.Atom]
    (F : QuantumRel X Y) : Prop :=
  (F.comp F.dagger) ≤ id Y ∧ id X ≤ (F.dagger.comp F)

theorem ext {R S : QuantumRel X Y}
    (h : ∀ x y, R.component x y = S.component x y) : R = S := by
  cases R
  cases S
  congr 1
  funext x y
  exact h x y

theorem le_def {R S : QuantumRel X Y} :
    R ≤ S ↔ ∀ x y, R.component x y ≤ S.component x y :=
  Iff.rfl

@[simp] theorem id_component_eq [DecidableEq X.Atom] (x : X.Atom) :
    (id X).component x x =
      Submodule.span ℂ
        {(1 : Matrix (Fin (X.dim x)) (Fin (X.dim x)) ℂ)} := by
  simp [id]

@[simp] theorem id_component_ne [DecidableEq X.Atom] {x y : X.Atom}
    (hxy : x ≠ y) :
    (id X).component x y = ⊥ := by
  simp [id, hxy]

theorem comp_mono_left {S₁ S₂ : QuantumRel Y Z} (R : QuantumRel X Y)
    (h : S₁ ≤ S₂) :
    S₁.comp R ≤ S₂.comp R := by
  intro x z
  refine iSup_mono ?_
  intro y
  apply Submodule.span_mono
  rintro _ ⟨r, s, hr, hs, rfl⟩
  exact ⟨r, s, hr, h y z hs, rfl⟩

theorem comp_mono_right {S : QuantumRel Y Z} {R₁ R₂ : QuantumRel X Y}
    (h : R₁ ≤ R₂) :
    S.comp R₁ ≤ S.comp R₂ := by
  intro x z
  refine iSup_mono ?_
  intro y
  apply Submodule.span_mono
  rintro _ ⟨r, s, hr, hs, rfl⟩
  exact ⟨r, s, h x y hr, hs, rfl⟩

theorem comp_mono {S₁ S₂ : QuantumRel Y Z} {R₁ R₂ : QuantumRel X Y}
    (hS : S₁ ≤ S₂) (hR : R₁ ≤ R₂) :
    S₁.comp R₁ ≤ S₂.comp R₂ :=
  (comp_mono_left R₁ hS).trans (comp_mono_right hR)

theorem dagger_mono {R S : QuantumRel X Y} (h : R ≤ S) :
    R.dagger ≤ S.dagger := by
  intro y x
  apply Submodule.span_mono
  rintro _ ⟨r, hr, rfl⟩
  exact ⟨r, h x y hr, rfl⟩

theorem mem_dagger {R : QuantumRel X Y} {x : X.Atom} {y : Y.Atom}
    {r : QuantumSet.Op X Y x y} (hr : r ∈ R.component x y) :
    rᴴ ∈ R.dagger.component y x :=
  Submodule.subset_span ⟨r, hr, rfl⟩

@[simp] theorem dagger_dagger (R : QuantumRel X Y) :
    R.dagger.dagger = R := by
  apply ext
  intro x y
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, hs, rfl⟩
    change sᴴ ∈ R.component x y
    refine Submodule.span_induction
      (p := fun t _ => tᴴ ∈ R.component x y)
      (fun _ ht => by
        obtain ⟨r, hr, rfl⟩ := ht
        simpa using hr)
      (by simp)
      (fun a b _ _ ha hb => by
        rw [Matrix.conjTranspose_add]
        exact add_mem ha hb)
      (fun c a _ ha => by
        rw [Matrix.conjTranspose_smul]
        exact Submodule.smul_mem _ (star c) ha)
      hs
  · intro r hr
    simpa using (mem_dagger (mem_dagger hr))


end QuantumRel

end QLambda.Domain
