/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Order.Closure
import Mathlib.Order.DirSupClosed

/-!
# Scott-closed lower sets

The Hoare-style lower powerdomain uses lower sets closed under all
directed suprema that exist in the underlying preorder.  Unlike the
lattice of all lower sets, its joins apply Scott closure after union, so
a genuine directed limit need not be a compact principal element.
-/

open Set

namespace QLambda

universe u

namespace ScottLowerSet

variable {α β : Type u} [Preorder α] [Preorder β]

/-- A set is Scott-lower when it is downward closed and closed under
nonempty directed suprema that exist in the ambient preorder. -/
def IsClosed (s : Set α) : Prop :=
  IsLowerSet s ∧ DirSupClosed s

/-- The least Scott-closed lower set containing `s`. -/
def closure (s : Set α) : Set α :=
  ⋂₀ {t : Set α | s ⊆ t ∧ IsClosed t}

theorem subset_closure (s : Set α) : s ⊆ closure s := by
  intro x hx t ht
  exact ht.1 hx

theorem closure_lower (s : Set α) : IsLowerSet (closure s) := by
  intro a b hba ha t ht
  exact ht.2.1 hba (ha t ht)

theorem closure_dirSupClosed (s : Set α) : DirSupClosed (closure s) := by
  apply DirSupClosed.sInter
  intro t ht
  exact ht.2.2

theorem closure_closed (s : Set α) : IsClosed (closure s) :=
  ⟨closure_lower s, closure_dirSupClosed s⟩

theorem closure_min {s t : Set α} (hst : s ⊆ t) (ht : IsClosed t) :
    closure s ⊆ t := by
  intro x hx
  exact hx t ⟨hst, ht⟩

theorem closure_eq_self {s : Set α} (hs : IsClosed s) :
    closure s = s :=
  Set.Subset.antisymm (closure_min Subset.rfl hs) (subset_closure s)

/-- Scott-lower closure as an order-theoretic closure operator on sets. -/
def operator : ClosureOperator (Set α) :=
  ClosureOperator.ofPred closure IsClosed subset_closure closure_closed
    fun _ _ hst ht => closure_min hst ht

/-- Scott-closed lower subsets ordered by inclusion. -/
abbrev Carrier (α : Type u) [Preorder α] :=
  (operator (α := α)).Closeds

instance : CompleteLattice (Carrier α) :=
  (operator (α := α)).gi.liftCompleteLattice

instance : SetLike (Carrier α) α where
  coe A := A.1
  coe_injective A B h := by
    apply Subtype.ext
    exact h

@[ext]
theorem ext {A B : Carrier α} (h : (A : Set α) = B) : A = B :=
  SetLike.coe_injective h

theorem lower (A : Carrier α) : IsLowerSet (A : Set α) := by
  have hclosed := A.2
  change IsClosed (A : Set α) at hclosed
  exact hclosed.1

theorem dirSupClosed (A : Carrier α) : DirSupClosed (A : Set α) := by
  have hclosed := A.2
  change IsClosed (A : Set α) at hclosed
  exact hclosed.2

/-- Embed a set by taking its Scott-lower closure. -/
def ofSet (s : Set α) : Carrier α :=
  (operator (α := α)).toCloseds s

@[simp]
theorem coe_ofSet (s : Set α) : ((ofSet s : Carrier α) : Set α) = closure s :=
  rfl

theorem subset_ofSet (s : Set α) : s ⊆ ofSet s :=
  subset_closure s

theorem ofSet_le {s : Set α} {A : Carrier α} :
    ofSet s ≤ A ↔ s ⊆ A := by
  constructor
  · intro h x hx
    exact h (subset_ofSet s hx)
  · intro h
    change closure s ⊆ (A : Set α)
    have hclosed := A.2
    change IsClosed (A : Set α) at hclosed
    exact closure_min h hclosed

/-- The Scott closure of a principal lower set. -/
def principal (a : α) : Carrier α :=
  ofSet (Set.Iic a)

theorem self_mem_principal (a : α) : a ∈ principal a :=
  subset_ofSet (Set.Iic a) Set.self_mem_Iic

theorem principal_mono : Monotone (principal : α → Carrier α) := by
  intro a b hab
  rw [principal, principal, ofSet_le]
  exact (Set.Iic_subset_Iic.mpr hab).trans (subset_ofSet _)

/-- Principal Scott-lower sets are ordinary order ideals: `Iic a` is
already closed under every directed supremum that exists. -/
@[simp]
theorem coe_principal (a : α) :
    ((principal a : Carrier α) : Set α) = Set.Iic a := by
  rw [principal, coe_ofSet, closure_eq_self]
  exact ⟨isLowerSet_Iic a, dirSupClosed_Iic a⟩

@[simp]
theorem mem_principal {a b : α} :
    b ∈ principal a ↔ b ≤ a := by
  change b ∈ ((principal a : Carrier α) : Set α) ↔ b ≤ a
  rw [coe_principal]
  exact Set.mem_Iic

theorem principal_le_iff_mem {a : α} {A : Carrier α} :
    principal a ≤ A ↔ a ∈ A := by
  rw [principal, ofSet_le]
  constructor
  · intro h
    exact h Set.self_mem_Iic
  · intro ha b hba
    exact lower A hba ha

/-- Preservation of all nonempty directed suprema which happen to exist
in a basis.  This is the appropriate continuity notion before taking a
dcpo completion. -/
def PreservesExistingDirectedSup (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d →
    ∀ ⦃a : α⦄, IsLUB d a → IsLUB (f '' d) (f a)

theorem preservesExistingDirectedSup_id :
    PreservesExistingDirectedSup (id : α → α) := by
  intro d _ _ a ha
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact ha.1 hx
  · intro b hb
    exact ha.2 fun x hx => hb ⟨x, hx, rfl⟩

theorem PreservesExistingDirectedSup.comp {γ : Type u} [Preorder γ]
    {f : α →o β} {g : β →o γ}
    (hg : PreservesExistingDirectedSup g)
    (hf : PreservesExistingDirectedSup f) :
    PreservesExistingDirectedSup ((g : β → γ) ∘ (f : α → β)) := by
  intro d hd hdir a ha
  have hfLUB := hf hd hdir ha
  have himg_nonempty := hd.image f
  have himg_directed : DirectedOn (· ≤ ·) (f '' d) := by
    intro _ hx _ hy
    obtain ⟨x, hxd, rfl⟩ := hx
    obtain ⟨y, hyd, rfl⟩ := hy
    obtain ⟨z, hzd, hxz, hyz⟩ := hdir x hxd y hyd
    exact ⟨f z, ⟨z, hzd, rfl⟩, f.mono hxz, f.mono hyz⟩
  simpa only [Set.image_image, Function.comp_apply] using
    hg himg_nonempty himg_directed hfLUB

/-- Inverse image along a continuous basis map preserves Scott-lower
closedness. -/
theorem isClosed_preimage (f : α →o β)
    (hf : PreservesExistingDirectedSup f) {s : Set β} (hs : IsClosed s) :
    IsClosed (f ⁻¹' s) := by
  constructor
  · intro a b hab ha
    exact hs.1 (f.mono hab) ha
  · intro d hd hne hdir a ha
    have himg : f '' d ⊆ s := by
      rintro _ ⟨x, hxd, rfl⟩
      exact hd hxd
    exact hs.2 himg (hne.image f)
      (by
        intro _ hx _ hy
        obtain ⟨x, hxd, rfl⟩ := hx
        obtain ⟨y, hyd, rfl⟩ := hy
        obtain ⟨z, hzd, hxz, hyz⟩ := hdir x hxd y hyd
        exact ⟨f z, ⟨z, hzd, rfl⟩, f.mono hxz, f.mono hyz⟩)
      (hf hne hdir ha)

/-- Direct image followed by Scott-lower closure. -/
def map (f : α →o β) (A : Carrier α) : Carrier β :=
  ofSet (f '' (A : Set α))

theorem map_mono (f : α →o β) : Monotone (map f) := by
  intro A B hAB
  rw [map, map, ofSet_le]
  exact (Set.image_mono hAB).trans (subset_ofSet _)

/-- Preimage as a map between Scott-lower carriers. -/
def comap (f : α →o β) (hf : PreservesExistingDirectedSup f)
    (B : Carrier β) : Carrier α :=
  ⟨f ⁻¹' (B : Set β), by
    change IsClosed (f ⁻¹' (B : Set β))
    have hB := B.2
    change IsClosed (B : Set β) at hB
    exact isClosed_preimage f hf hB⟩

theorem map_le_iff_le_comap (f : α →o β)
    (hf : PreservesExistingDirectedSup f) {A : Carrier α} {B : Carrier β} :
    map f A ≤ B ↔ A ≤ comap f hf B := by
  rw [map, ofSet_le]
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    exact h hx

@[simp]
theorem map_id (A : Carrier α) :
    map OrderHom.id A = A := by
  apply ext
  change closure (OrderHom.id '' (A : Set α)) = (A : Set α)
  have hA := A.2
  change IsClosed (A : Set α) at hA
  convert closure_eq_self hA using 1
  ext x
  simp

theorem map_comp {γ : Type u} [Preorder γ]
    (g : β →o γ) (hg : PreservesExistingDirectedSup g)
    (f : α →o β) (A : Carrier α) :
    map (g.comp f) A = map g (map f A) := by
  apply le_antisymm
  · rw [map, ofSet_le]
    rintro _ ⟨x, hx, rfl⟩
    exact subset_ofSet _
      ⟨f x, subset_ofSet _ ⟨x, hx, rfl⟩, rfl⟩
  · rw [map_le_iff_le_comap g hg, map, ofSet_le]
    rintro _ ⟨x, hx, rfl⟩
    exact subset_ofSet _ ⟨x, hx, rfl⟩

end ScottLowerSet

/-- Scott-closed lower subsets ordered by inclusion. -/
abbrev ScottLowerSet (α : Type u) [Preorder α] :=
  ScottLowerSet.Carrier α

end QLambda
