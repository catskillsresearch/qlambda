/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumRelChains
/-!
# Unitaries, qubit measurement, and PVM channels
-/

open Matrix

namespace QLambda.Domain

namespace QuantumRel

variable {X Y Z W : QuantumSet}

/-- Conjugation by a unitary on an atomic quantum set. -/
def ofUnitary {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) : QuantumRel (.atomic n) (.atomic n) where
  component _ _ := Submodule.span ℂ {U}

theorem ofUnitary_dagger {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) :
    (ofUnitary U).dagger = ofUnitary Uᴴ := by
  apply ext
  intro x y
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hr
    have : rᴴ = star c • Uᴴ := by
      rw [← hc]
      exact Matrix.conjTranspose_smul (R := ℂ) (M := U) c
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    rintro m rfl
    refine Submodule.subset_span ⟨U, Submodule.subset_span (Set.mem_singleton _), rfl⟩

theorem ofUnitary_comp {n : ℕ}
    (S R : Matrix (Fin n) (Fin n) ℂ) :
    (ofUnitary S).comp (ofUnitary R) = ofUnitary (S * R) := by
  apply ext
  intro x z
  simp only [comp]
  trans (ofUnitary S).compThrough (ofUnitary R) x
      (default : (QuantumSet.atomic n).Atom) z
  · exact iSup_unique
      (f := fun y : (QuantumSet.atomic n).Atom =>
        (ofUnitary S).compThrough (ofUnitary R) x y z)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, s, hr, hs, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hr
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hs
    have : s * r = (d * c) • (S * R) := by
      rw [← hc, ← hd]
      calc
        (d • S) * (c • R)
          = d • (S * (c • R)) := Matrix.smul_mul d S (c • R)
        _ = d • (c • (S * R)) := by rw [Matrix.mul_smul]
        _ = (d * c) • (S * R) := smul_smul d c (S * R)
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    rintro m rfl
    refine Submodule.subset_span ⟨R, S,
      Submodule.subset_span (Set.mem_singleton _),
      Submodule.subset_span (Set.mem_singleton _), rfl⟩

theorem ofUnitary_one {n : ℕ} :
    ofUnitary (1 : Matrix (Fin n) (Fin n) ℂ) = id (.atomic n) := by
  apply ext
  intro x y
  have hx : x = default := Subsingleton.elim _ _
  have hy : y = default := Subsingleton.elim _ _
  subst hx
  subst hy
  simp only [ofUnitary]
  exact (id_component_eq (default : (QuantumSet.atomic n).Atom)).symm

theorem ofUnitary_isFunction {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hL : Uᴴ * U = 1) (hR : U * Uᴴ = 1) :
    (ofUnitary U).IsFunction := by
  constructor
  · rw [ofUnitary_dagger, ofUnitary_comp, hR, ofUnitary_one]
  · rw [ofUnitary_dagger, ofUnitary_comp, hL, ofUnitary_one]

/-- Computational-basis bras used to present measurement as a function. -/
def bra0 : KrausOperator 2 1 :=
  !![(1 : ℂ), 0]

def bra1 : KrausOperator 2 1 :=
  !![(0 : ℂ), 1]

/-- Computational-basis measurement of one qubit. -/
def qubitMeasure : QuantumRel .qubit .bit where
  component _
    | false => Submodule.span ℂ {bra0}
    | true => Submodule.span ℂ {bra1}

/-- A projection-valued measurement from an atomic system onto a
classical finite set.  The component at outcome `b` is the operators
that factor through the corresponding projector. -/
def ofPVM {n : ℕ} {α : Type} [Fintype α]
    (π : α → Matrix (Fin n) (Fin n) ℂ) :
    QuantumRel (.atomic n) (.liftSet α) where
  component _ b :=
    Submodule.span ℂ
      { (v : KrausOperator n 1) | v * (1 - π b) = 0 }

/-- The zero-state allocation channel `1 → qubit`. -/
def new0 : QuantumRel .unit .qubit where
  component _ _ :=
    Submodule.span ℂ {!![(1 : ℂ); 0]}

end QuantumRel

end QLambda.Domain
