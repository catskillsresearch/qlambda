/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumRelFunction
/-!
# Atomic restriction and assembly
-/

open Matrix

namespace QLambda.Domain

namespace QuantumRel

variable {X Y Z W : QuantumSet}

/-- Restrict the domain of a relation to one atomic summand. -/
def restrictAtom (R : QuantumRel X Y) (x : X.Atom) :
    QuantumRel (.atomic (X.dim x)) Y where
  component := fun _ y => R.component x y

/-- Reassemble a relation from its restrictions to all domain atoms. -/
def assembleAtoms
    (K : ∀ x : X.Atom, QuantumRel (.atomic (X.dim x)) Y) :
    QuantumRel X Y where
  component := fun x y => (K x).component PUnit.unit y

@[simp] theorem restrictAtom_assembleAtoms
    (K : ∀ x : X.Atom, QuantumRel (.atomic (X.dim x)) Y)
    (x : X.Atom) :
    restrictAtom (assembleAtoms K) x = K x := by
  apply ext
  intro u y
  cases u
  rfl

@[simp] theorem assembleAtoms_restrictAtom (R : QuantumRel X Y) :
    assembleAtoms (fun x => restrictAtom R x) = R := by
  apply ext
  intro x y
  rfl

theorem restrictAtom_mono {R S : QuantumRel X Y} (h : R ≤ S)
    (x : X.Atom) :
    restrictAtom R x ≤ restrictAtom S x := by
  intro u y
  exact h x y

@[simp] theorem restrictAtom_comp (S : QuantumRel Y Z)
    (R : QuantumRel X Y) (x : X.Atom) :
    restrictAtom (S.comp R) x = S.comp (restrictAtom R x) := by
  apply ext
  intro u z
  cases u
  rfl

theorem restrictAtom_comp_dagger_le (R : QuantumRel X Y) (x : X.Atom) :
    (restrictAtom R x).comp (restrictAtom R x).dagger ≤
      R.comp R.dagger := by
  intro y z
  calc
    ((restrictAtom R x).comp
        (restrictAtom R x).dagger).component y z =
        (restrictAtom R x).compThrough
          (restrictAtom R x).dagger y
            (default : (QuantumSet.atomic (X.dim x)).Atom) z :=
      by
        change (⨆ u : (QuantumSet.atomic (X.dim x)).Atom,
          (restrictAtom R x).compThrough
            (restrictAtom R x).dagger y u z) =
          (restrictAtom R x).compThrough
            (restrictAtom R x).dagger y default z
        exact iSup_unique
          (f := fun u : (QuantumSet.atomic (X.dim x)).Atom =>
            (restrictAtom R x).compThrough
              (restrictAtom R x).dagger y u z)
    _ = R.compThrough R.dagger y x z := by rfl
    _ ≤ (R.comp R.dagger).component y z :=
      le_iSup (fun x' => R.compThrough R.dagger y x' z) x

theorem restrictAtom_dagger_comp_self_component (R : QuantumRel X Y)
    (x : X.Atom) (u v : (QuantumSet.atomic (X.dim x)).Atom) :
    ((restrictAtom R x).dagger.comp (restrictAtom R x)).component u v =
      (R.dagger.comp R).component x x := by
  cases u
  cases v
  rfl

theorem restrictAtom_isFunction [DecidableEq X.Atom] [DecidableEq Y.Atom]
    {R : QuantumRel X Y} (hR : R.IsFunction) (x : X.Atom) :
    (restrictAtom R x).IsFunction := by
  constructor
  · exact (restrictAtom_comp_dagger_le R x).trans hR.1
  · intro u v
    have hu : u = default := Subsingleton.elim _ _
    have hv : v = default := Subsingleton.elim _ _
    subst u
    subst v
    rw [id_component_eq]
    rw [restrictAtom_dagger_comp_self_component]
    change
      Submodule.span ℂ
          {(1 : Matrix (Fin (X.dim x)) (Fin (X.dim x)) ℂ)} ≤
        (R.dagger.comp R).component x x
    simpa only [id_component_eq] using hR.2 x x

theorem assembleAtoms_isFunction [DecidableEq X.Atom] [DecidableEq Y.Atom]
    (K : ∀ x : X.Atom, QuantumRel (.atomic (X.dim x)) Y)
    (hK : ∀ x, (K x).IsFunction) :
    (assembleAtoms K).IsFunction := by
  constructor
  · intro y z
    apply iSup_le
    intro x
    have hx := (hK x).1 y z
    change (K x).compThrough (K x).dagger y
        (default : (QuantumSet.atomic (X.dim x)).Atom) z ≤
      (id Y).component y z
    exact (le_iSup
      (fun u => (K x).compThrough (K x).dagger y u z)
      (default : (QuantumSet.atomic (X.dim x)).Atom)).trans hx
  · intro x x'
    by_cases hxx : x = x'
    · subst x'
      rw [id_component_eq]
      apply Submodule.span_le.mpr
      rintro _ rfl
      have hone :
          (1 : Matrix (Fin (X.dim x)) (Fin (X.dim x)) ℂ) ∈
            (id (QuantumSet.atomic (X.dim x))).component
              default default := by
        rw [id_component_eq]
        exact Submodule.subset_span
          (Set.mem_singleton
            (1 : Matrix (Fin (X.dim x)) (Fin (X.dim x)) ℂ))
      exact (hK x).2 default default hone
    · rw [id_component_ne hxx]
      exact bot_le


end QuantumRel

end QLambda.Domain
