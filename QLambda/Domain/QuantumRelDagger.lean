/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumRelComp
/-!
# Dagger and unit laws for quantum relations
-/

open Matrix

namespace QLambda.Domain

namespace QuantumRel

variable {X Y Z W : QuantumSet}

theorem adjoint_mem_span {n m : ℕ}
    {s : Set (Matrix (Fin m) (Fin n) ℂ)}
    {a : Matrix (Fin m) (Fin n) ℂ}
    (ha : a ∈ Submodule.span ℂ s) :
    aᴴ ∈ Submodule.span ℂ { bᴴ | b ∈ s } := by
  refine Submodule.span_induction
    (p := fun x _ => xᴴ ∈ Submodule.span ℂ { bᴴ | b ∈ s })
    (fun b hb => Submodule.subset_span ⟨b, hb, rfl⟩)
    (by simp [conjTranspose_zero])
    (fun x y _ _ hx hy => by
      rw [conjTranspose_add]
      exact add_mem hx hy)
    (fun c x _ hx => by
      rw [Matrix.conjTranspose_smul]
      exact Submodule.smul_mem _ (star c) hx)
    ha

theorem dagger_compThrough (S : QuantumRel Y Z) (R : QuantumRel X Y)
    (x : X.Atom) (y : Y.Atom) (z : Z.Atom) :
    Submodule.span ℂ { vᴴ | v ∈ S.compThrough R x y z } ≤
      R.dagger.compThrough S.dagger z y x := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  have hvadj := adjoint_mem_span (s :=
      { (s * r : QuantumSet.Op X Z x z) |
        (r : QuantumSet.Op X Y x y)
        (s : QuantumSet.Op Y Z y z)
        (_ : r ∈ R.component x y)
        (_ : s ∈ S.component y z) }) hv
  refine (Submodule.span_le.mpr ?_) hvadj
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨r, s, hr, hs, rfl⟩ := hw
  refine Submodule.subset_span ⟨sᴴ, rᴴ, mem_dagger hs, mem_dagger hr, ?_⟩
  exact (Matrix.conjTranspose_mul s r).symm

theorem dagger_comp (S : QuantumRel Y Z) (R : QuantumRel X Y) :
    (S.comp R).dagger = R.dagger.comp S.dagger := by
  apply ext
  intro z x
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    have hu' :
        u ∈ Submodule.span ℂ
          (⋃ y, (S.compThrough R x y z : Set _)) := by
      simpa [comp, Submodule.iSup_eq_span] using hu
    have hspan := adjoint_mem_span hu'
    refine (Submodule.span_le.mpr ?_) hspan
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨y, hv'⟩ := Set.mem_iUnion.mp hv
    apply (le_iSup (fun y => R.dagger.compThrough S.dagger z y x) y)
    exact dagger_compThrough S R x y z (Submodule.subset_span ⟨v, hv', rfl⟩)
  · apply iSup_le
    intro y
    apply Submodule.span_le.mpr
    rintro _ ⟨rFromS, sFromR, hrFromS, hsFromR, rfl⟩
    have hs' :
        sFromR ∈ Submodule.span ℂ
          { rᴴ | r ∈ R.component x y } := by
      simpa [dagger] using hsFromR
    have hr' :
        rFromS ∈ Submodule.span ℂ
          { sᴴ | s ∈ S.component y z } := by
      simpa [dagger] using hrFromS
    refine Submodule.span_induction₂
      (p := fun sa ra _ _ => sa * ra ∈ (S.comp R).dagger.component z x)
      (fun rT sT hrT hsT => by
        obtain ⟨r, hr, rfl⟩ := hrT
        obtain ⟨s, hs, rfl⟩ := hsT
        rw [← Matrix.conjTranspose_mul]
        exact mem_dagger
          (le_iSup (fun y => S.compThrough R x y z) y
            (Submodule.subset_span ⟨r, s, hr, hs, rfl⟩)))
      (fun sa _ => by
        rw [Matrix.zero_mul]
        exact zero_mem _)
      (fun ra _ => by
        rw [Matrix.mul_zero]
        exact zero_mem _)
      (fun a b c _ _ _ ha hb => by
        rw [Matrix.add_mul]
        exact add_mem ha hb)
      (fun a b c _ _ _ ha hb => by
        rw [Matrix.mul_add]
        exact add_mem ha hb)
      (fun c ra sa _ _ h => by
        rw [Matrix.smul_mul c ra sa]
        exact Submodule.smul_mem _ c h)
      (fun c ra sa _ _ h => by
        rw [Matrix.mul_smul ra c sa]
        exact Submodule.smul_mem _ c h)
      hs' hr'

def mulRightLM {n m p : ℕ} (u : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin p) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin n) ℂ where
  toFun t := t * u
  map_add' := fun _ _ => Matrix.add_mul _ _ _
  map_smul' := fun c t => Matrix.smul_mul c t u

def mulLeftLM {n m p : ℕ} (t : Matrix (Fin p) (Fin m) ℂ) :
    Matrix (Fin m) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin n) ℂ where
  toFun u := t * u
  map_add' := fun _ _ => Matrix.mul_add _ _ _
  map_smul' := fun c u => Matrix.mul_smul t c u

theorem id_comp [DecidableEq Y.Atom] (R : QuantumRel X Y) :
    (id Y).comp R = R := by
  apply ext
  intro x z
  apply le_antisymm
  · apply iSup_le
    intro y
    apply Submodule.span_le.mpr
    rintro m ⟨r, s, hr, hs, rfl⟩
    by_cases hyz : y = z
    · subst z
      have hs' :
          s ∈ Submodule.span ℂ
            {(1 : Matrix (Fin (Y.dim y)) (Fin (Y.dim y)) ℂ)} := by
        simpa [id] using hs
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hs'
      have : s * r = c • r := by
        rw [← hc, Matrix.smul_mul, Matrix.one_mul]
      rw [this]
      exact Submodule.smul_mem _ c hr
    · have : s ∈ (⊥ : OpSpace Y Y y z) := by
        simpa [id, hyz] using hs
      have hs0 : s = 0 := by
        simpa [Submodule.mem_bot] using this
      rw [hs0, Matrix.zero_mul]
      exact zero_mem _
  · refine le_trans ?_ (le_iSup (fun y => (id Y).compThrough R x y z) z)
    intro m hm
    refine Submodule.subset_span
      ⟨m, (1 : Matrix (Fin (Y.dim z)) (Fin (Y.dim z)) ℂ), hm, ?_,
        Matrix.one_mul m⟩
    simpa [id] using Submodule.subset_span
      (Set.mem_singleton (1 : Matrix (Fin (Y.dim z)) (Fin (Y.dim z)) ℂ))

theorem comp_id [DecidableEq X.Atom] (R : QuantumRel X Y) :
    R.comp (id X) = R := by
  apply ext
  intro x z
  apply le_antisymm
  · apply iSup_le
    intro y
    apply Submodule.span_le.mpr
    rintro m ⟨r, s, hr, hs, rfl⟩
    by_cases hxy : x = y
    · subst y
      have hr' :
          r ∈ Submodule.span ℂ
            {(1 : Matrix (Fin (X.dim x)) (Fin (X.dim x)) ℂ)} := by
        simpa [id] using hr
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hr'
      have : s * r = c • s := by
        rw [← hc, Matrix.mul_smul, Matrix.mul_one]
      rw [this]
      exact Submodule.smul_mem _ c hs
    · have : r ∈ (⊥ : OpSpace X X x y) := by
        simpa [id, hxy] using hr
      have hr0 : r = 0 := by
        simpa [Submodule.mem_bot] using this
      rw [hr0, Matrix.mul_zero]
      exact zero_mem _
  · refine le_trans ?_ (le_iSup (fun y => R.compThrough (id X) x y z) x)
    intro m hm
    refine Submodule.subset_span
      ⟨(1 : Matrix (Fin (X.dim x)) (Fin (X.dim x)) ℂ), m, ?_, hm,
        Matrix.mul_one m⟩
    simpa [id] using Submodule.subset_span
      (Set.mem_singleton (1 : Matrix (Fin (X.dim x)) (Fin (X.dim x)) ℂ))

theorem assoc (T : QuantumRel Z W) (S : QuantumRel Y Z) (R : QuantumRel X Y) :
    (T.comp S).comp R = T.comp (S.comp R) := by
  apply ext
  intro x w
  apply le_antisymm
  · apply iSup_le
    intro y
    apply Submodule.span_le.mpr
    rintro m ⟨r, t, hr, ht, rfl⟩
    have : t * r ∈
        Submodule.map (mulRightLM (p := W.dim w) r)
          ((T.comp S).component y w) :=
      Submodule.mem_map.mpr ⟨t, ht, rfl⟩
    rw [show (T.comp S).component y w = ⨆ z, T.compThrough S y z w from rfl,
      Submodule.map_iSup] at this
    refine (iSup_le (fun z => ?_) : _ ≤ (T.comp (S.comp R)).component x w) this
    dsimp only [compThrough]
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨s, t', hs, ht', rfl⟩, rfl⟩
    change (t' * s) * r ∈ (T.comp (S.comp R)).component x w
    rw [Matrix.mul_assoc]
    apply (le_iSup (fun z => T.compThrough (S.comp R) x z w) z)
    refine Submodule.subset_span ⟨s * r, t', ?_, ht', rfl⟩
    apply (le_iSup (fun y => S.compThrough R x y z) y)
    exact Submodule.subset_span ⟨r, s, hr, hs, rfl⟩
  · apply iSup_le
    intro z
    apply Submodule.span_le.mpr
    rintro m ⟨u, t, hu, ht, rfl⟩
    have : t * u ∈
        Submodule.map (mulLeftLM (n := X.dim x) t)
          ((S.comp R).component x z) :=
      Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    rw [show (S.comp R).component x z = ⨆ y, S.compThrough R x y z from rfl,
      Submodule.map_iSup] at this
    refine (iSup_le (fun y => ?_) : _ ≤ ((T.comp S).comp R).component x w) this
    dsimp only [compThrough]
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨r, s, hr, hs, rfl⟩, rfl⟩
    change t * (s * r) ∈ ((T.comp S).comp R).component x w
    rw [← Matrix.mul_assoc]
    apply (le_iSup (fun y => (T.comp S).compThrough R x y w) y)
    refine Submodule.subset_span ⟨r, t * s, hr, ?_, rfl⟩
    apply (le_iSup (fun z => T.compThrough S y z w) z)
    exact Submodule.subset_span ⟨s, t, hs, ht, rfl⟩

theorem id_dagger [DecidableEq X.Atom] : (id X).dagger = id X := by
  apply ext
  intro y x
  by_cases hxy : x = y
  · subst y
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨r, hr, rfl⟩
      have hr' :
          r ∈ Submodule.span ℂ
            {(1 : Matrix (Fin (X.dim x)) (Fin (X.dim x)) ℂ)} := by
        simpa [id] using hr
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hr'
      have : rᴴ = star c • (1 : Matrix (Fin (X.dim x)) (Fin (X.dim x)) ℂ) := by
        rw [← hc, Matrix.conjTranspose_smul, conjTranspose_one]
      rw [this]
      simp [id]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    · intro m hm
      have hm' :
          m ∈ Submodule.span ℂ
            {(1 : Matrix (Fin (X.dim x)) (Fin (X.dim x)) ℂ)} := by
        simpa [id] using hm
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm'
      refine Submodule.subset_span ⟨star c • (1 : Matrix (Fin (X.dim x)) (Fin (X.dim x)) ℂ), ?_, ?_⟩
      · simp [id]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
      · rw [Matrix.conjTranspose_smul, conjTranspose_one, star_star, hc]
  · have hne : y ≠ x := Ne.symm hxy
    simp [id, dagger, hxy, hne]


end QuantumRel

end QLambda.Domain
