/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.DiscreteSet
import QLambda.Domain.QuantumCategory

/-!
# Classical sets inside quantum relations

Ordinary sets embed as one-dimensional quantum sets.  The nonlinear hom order
used by the LNL construction is discrete, so the graph construction is
monotone; this avoids the false graph map from pointwise-ordered `OmegaMap`.
-/

namespace QLambda.Domain

namespace QuantumRel

private theorem span_one_one_eq_top :
    Submodule.span ℂ
        {(1 : Matrix (Fin 1) (Fin 1) ℂ)} = ⊤ := by
  apply top_unique
  intro m hm
  apply Submodule.mem_span_singleton.mpr
  refine ⟨m 0 0, ?_⟩
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  simp

/-- Graph of an ordinary function as a relation between classical quantum
sets. -/
noncomputable def graph {A B : Type}
    (f : (QuantumSet.liftSet A).Atom → (QuantumSet.liftSet B).Atom) :
    QuantumRel (.liftSet A) (.liftSet B) where
  component x y :=
    @ite _ (f x = y) (Classical.propDecidable _)
      (Submodule.span ℂ {(1 : Matrix (Fin 1) (Fin 1) ℂ)}) ⊥

@[simp] theorem graph_component_eq {A B : Type}
    (f : (QuantumSet.liftSet A).Atom → (QuantumSet.liftSet B).Atom)
    (x : (QuantumSet.liftSet A).Atom) :
    (graph f).component x (f x) = ⊤ := by
  classical
  simp only [graph, ↓reduceIte]
  exact span_one_one_eq_top

@[simp] theorem graph_component_ne {A B : Type}
    (f : (QuantumSet.liftSet A).Atom → (QuantumSet.liftSet B).Atom)
    (x : (QuantumSet.liftSet A).Atom)
    (y : (QuantumSet.liftSet B).Atom) (h : f x ≠ y) :
    (graph f).component x y = ⊥ := by
  classical
  simp only [graph, h, ↓reduceIte]

@[simp] theorem graph_id {A : Type} [DecidableEq A] :
    graph (A := A) (B := A) (fun x => x) =
      id (QuantumSet.liftSet A) := by
  apply ext
  intro x y
  by_cases h : x = y
  · subst y
    rw [graph_component_eq, id_component_eq]
    exact span_one_one_eq_top.symm
  · rw [graph_component_ne _ _ _ h, id_component_ne h]

@[simp] theorem graph_comp {A B C : Type}
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (g : (QuantumSet.liftSet B).Atom →
      (QuantumSet.liftSet C).Atom)
    (f : (QuantumSet.liftSet A).Atom →
      (QuantumSet.liftSet B).Atom) :
    graph (fun x => g (f x)) = (graph g).comp (graph f) := by
  apply ext
  intro x z
  by_cases hxz : g (f x) = z
  · rw [show z = g (f x) from hxz.symm, graph_component_eq]
    apply Eq.symm
    apply top_unique
    rw [show ((graph g).comp (graph f)).component x (g (f x)) =
        ⨆ y, (graph g).compThrough (graph f) x y (g (f x)) from rfl]
    refine le_trans ?_
      (le_iSup
        (fun y => (graph g).compThrough (graph f) x y (g (f x)))
        (f x))
    have hgen :
        (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈
          (graph g).compThrough (graph f) x (f x) (g (f x)) := by
      apply Submodule.subset_span
      refine
        ⟨(1 : Matrix (Fin 1) (Fin 1) ℂ),
          (1 : Matrix (Fin 1) (Fin 1) ℂ), ?_, ?_, ?_⟩
      · rw [graph_component_eq]
        exact Submodule.mem_top
      · rw [graph_component_eq]
        exact Submodule.mem_top
      · exact Matrix.one_mul _
    have hspan :
        Submodule.span ℂ {(1 : Matrix (Fin 1) (Fin 1) ℂ)} ≤
          (graph g).compThrough (graph f) x (f x) (g (f x)) := by
      apply Submodule.span_le.mpr
      intro m hm
      simpa only [Set.mem_singleton_iff] using hm ▸ hgen
    change (⊤ : Submodule ℂ (Matrix (Fin 1) (Fin 1) ℂ)) ≤
      (graph g).compThrough (graph f) x (f x) (g (f x))
    simpa only [span_one_one_eq_top] using hspan
  · rw [show (graph (fun x => g (f x))).component x z = ⊥ from
      graph_component_ne _ _ _ hxz]
    apply Eq.symm
    apply le_antisymm
    · change (⨆ y, (graph g).compThrough (graph f) x y z) ≤ ⊥
      apply iSup_le
      intro y
      apply Submodule.span_le.mpr
      rintro _ ⟨r, s, hr, hs, rfl⟩
      by_cases hxy : f x = y
      · subst y
        rw [graph_component_ne _ _ _ hxz] at hs
        have hs0 : s = 0 := by simpa [Submodule.mem_bot] using hs
        rw [hs0, Matrix.zero_mul]
        exact zero_mem _
      · rw [graph_component_ne _ _ _ hxy] at hr
        have hr0 : r = 0 := by simpa [Submodule.mem_bot] using hr
        rw [hr0, Matrix.mul_zero]
        exact zero_mem _
    · exact bot_le

end QuantumRel

/-- Classical quantum object associated to an ordinary type. -/
noncomputable def classicalQObj (A : Type) : QObj where
  set := .liftSet A
  decidable := Classical.decEq A

end QLambda.Domain
