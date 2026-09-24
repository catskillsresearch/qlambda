/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumRelAtoms
/-!
# Countable joins/meets and composition continuity
-/

open Matrix

namespace QLambda.Domain

namespace QuantumRel

variable {X Y Z W : QuantumSet}

theorem iInf_component (S : ℕ → QuantumRel X Y) (x : X.Atom) (y : Y.Atom) :
    (⨅ n, S n).component x y = ⨅ n, (S n).component x y := by
  apply le_antisymm
  · apply le_iInf
    intro n
    exact iInf_le_of_le ⟨S n, ⟨n, rfl⟩⟩ le_rfl
  · apply le_iInf
    intro R
    obtain ⟨n, hn⟩ := R.property
    rw [← hn]
    exact iInf_le (fun n => (S n).component x y) n

@[simp] theorem restrictAtom_iInf (S : ℕ → QuantumRel X Y) (x : X.Atom) :
    restrictAtom (⨅ n, S n) x = ⨅ n, restrictAtom (S n) x := by
  apply ext
  intro u y
  rw [iInf_component]
  exact iInf_component S x y

theorem iSup_component (S : ℕ → QuantumRel X Y) (x : X.Atom) (y : Y.Atom) :
    (⨆ n, S n).component x y = ⨆ n, (S n).component x y := by
  apply le_antisymm
  · apply iSup_le
    intro ⟨R, hR⟩
    obtain ⟨n, hn⟩ := hR
    subst R
    exact le_iSup (fun n => (S n).component x y) n
  · apply iSup_le
    intro n
    exact le_iSup_of_le ⟨S n, ⟨n, rfl⟩⟩ le_rfl

theorem comp_iSup_left (S : ℕ → QuantumRel Y Z) (R : QuantumRel X Y) :
    (⨆ n, S n).comp R = ⨆ n, (S n).comp R := by
  apply le_antisymm
  · intro x z
    apply iSup_le
    intro y
    apply Submodule.span_le.mpr
    rintro m ⟨r, s, hr, hs, rfl⟩
    have : s * r ∈
        Submodule.map (mulRightLM (p := Z.dim z) r)
          ((⨆ n, S n).component y z) :=
      Submodule.mem_map.mpr ⟨s, hs, rfl⟩
    rw [iSup_component S y z, Submodule.map_iSup] at this
    refine (iSup_le (fun n => ?_) :
      _ ≤ (⨆ n, (S n).comp R).component x z) this
    intro t ht
    obtain ⟨s', hs', rfl⟩ := Submodule.mem_map.mp ht
    apply (le_iSup (fun n => (S n).comp R) n)
    apply (le_iSup (fun y => (S n).compThrough R x y z) y)
    exact Submodule.subset_span ⟨r, s', hr, hs', rfl⟩
  · apply iSup_le
    intro n
    exact comp_mono_left R (le_iSup S n)

theorem comp_iSup_right (S : QuantumRel Y Z) (R : ℕ → QuantumRel X Y) :
    S.comp (⨆ n, R n) = ⨆ n, S.comp (R n) := by
  apply le_antisymm
  · intro x z
    apply iSup_le
    intro y
    apply Submodule.span_le.mpr
    rintro m ⟨r, s, hr, hs, rfl⟩
    have : s * r ∈
        Submodule.map (mulLeftLM (n := X.dim x) s)
          ((⨆ n, R n).component x y) :=
      Submodule.mem_map.mpr ⟨r, hr, rfl⟩
    rw [iSup_component R x y, Submodule.map_iSup] at this
    refine (iSup_le (fun n => ?_) :
      _ ≤ (⨆ n, S.comp (R n)).component x z) this
    intro t ht
    obtain ⟨r', hr', rfl⟩ := Submodule.mem_map.mp ht
    apply (le_iSup (fun n => S.comp (R n)) n)
    apply (le_iSup (fun y => S.compThrough (R n) x y z) y)
    exact Submodule.subset_span ⟨r', s, hr', hs, rfl⟩
  · apply iSup_le
    intro n
    exact comp_mono_right (le_iSup R n)


end QuantumRel

end QLambda.Domain
