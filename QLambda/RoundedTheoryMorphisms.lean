/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.RoundedTheory

/-!
# Morphisms of rounded-theory completions

A function from source basis elements to rounded target theories extends
canonically by taking the union of its values over all generators present in
the source theory.  This construction preserves arbitrary suprema, hence is
Scott-continuous.  No compatibility between the two basis relations is
needed: roundedness is supplied by the target values themselves.
-/

open Set

namespace QLambda

open Scott1972.ContinuousLattice

universe u v w

namespace RoundedTheory

variable {α : Type u} {β : Type v} {γ : Type w}
variable (B : AbstractBasis α) (C : AbstractBasis β) (K : AbstractBasis γ)

/-- Extend rounded target data given on source basis elements. -/
noncomputable def extend (φ : α → Carrier C) (A : Carrier B) : Carrier C :=
  sSup (φ '' A.carrier)

theorem mem_extend {φ : α → Carrier C} {A : Carrier B} {b : β} :
    b ∈ extend B C φ A ↔ ∃ a ∈ A, b ∈ φ a := by
  rw [extend, mem_sSup]
  constructor
  · rintro ⟨T, ⟨a, ha, rfl⟩, hb⟩
    exact ⟨a, ha, hb⟩
  · rintro ⟨a, ha, hb⟩
    exact ⟨φ a, ⟨a, ha, rfl⟩, hb⟩

theorem extend_mono (φ : α → Carrier C) :
    Monotone (extend B C φ) := by
  intro A A' hAA' b
  change b ∈ extend B C φ A → b ∈ extend B C φ A'
  rw [mem_extend, mem_extend]
  rintro ⟨a, ha, hb⟩
  exact ⟨a, hAA' ha, hb⟩

/-- Rounded extension preserves every supremum, not only directed ones. -/
theorem extend_sSup (φ : α → Carrier C) (S : Set (Carrier B)) :
    extend B C φ (sSup S) = sSup (extend B C φ '' S) := by
  apply ext
  ext b
  change b ∈ extend B C φ (sSup S) ↔
    b ∈ (sSup (extend B C φ '' S) : Carrier C)
  rw [mem_extend, mem_sSup]
  constructor
  · rintro ⟨a, ha, hb⟩
    obtain ⟨A, hAS, haA⟩ := (mem_sSup (B := B)).mp ha
    exact ⟨extend B C φ A, ⟨A, hAS, rfl⟩,
      (mem_extend (B := B) (C := C)).2 ⟨a, haA, hb⟩⟩
  · rintro ⟨_, ⟨A, hAS, rfl⟩, hb⟩
    obtain ⟨a, haA, hba⟩ :=
      (mem_extend (B := B) (C := C)).mp hb
    exact ⟨a, (mem_sSup (B := B)).2 ⟨A, hAS, haA⟩, hba⟩

/-- The Scott map induced by rounded data on basis elements. -/
noncomputable def extendScott (φ : α → Carrier C) :
    ScottMap (Carrier B) (Carrier C) :=
  ⟨extend B C φ, continuous_of_preservesDirectedSup fun S _ _ =>
    extend_sSup B C φ S⟩

@[simp]
theorem extendScott_apply (φ : α → Carrier C) (A : Carrier B) :
    extendScott B C φ A = extend B C φ A :=
  rfl

theorem extendScott_sSup (φ : α → Carrier C) (S : Set (Carrier B)) :
    extendScott B C φ (sSup S) = sSup (extendScott B C φ '' S) :=
  extend_sSup B C φ S

/-- Value on a rounded principal, expressed solely in terms of basis data. -/
theorem extend_principal (φ : α → Carrier C) (a : α) :
    extend B C φ (principal B a) =
      sSup (φ '' {x | B.below x a}) := by
  apply ext
  ext b
  change b ∈ extend B C φ (principal B a) ↔
    b ∈ (sSup (φ '' {x | B.below x a}) : Carrier C)
  rw [mem_extend, mem_sSup]
  constructor
  · rintro ⟨x, hx, hb⟩
    exact ⟨φ x, ⟨x, (mem_principal (B := B)).mp hx, rfl⟩, hb⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, hb⟩
    exact ⟨x, (mem_principal (B := B)).2 hx, hb⟩

/-- Every rounded theory is the union of its rounded principals. -/
theorem sSup_principals_mem (A : Carrier B) :
    sSup (principal B '' A.carrier) = A := by
  apply ext
  ext a
  change a ∈ (sSup (principal B '' A.carrier) : Carrier B) ↔ a ∈ A
  rw [mem_sSup]
  constructor
  · rintro ⟨_, ⟨b, hbA, rfl⟩, hab⟩
    exact principal_le B hbA hab
  · intro haA
    have haround : a ∈ round B A.carrier := by
      rw [A.rounded]
      exact haA
    obtain ⟨b, hbA, hab⟩ := haround
    exact ⟨principal B b, ⟨b, hbA, rfl⟩,
      (mem_principal (B := B)).2 hab⟩

/-- Principal data gives the identity rounded extension. -/
@[simp]
theorem extend_principal_id (A : Carrier B) :
    extend B B (principal B) A = A :=
  sSup_principals_mem B A

@[simp]
theorem extendScott_principal_id :
    extendScott B B (principal B) =
      (ScottMap.idMap : ScottMap (Carrier B) (Carrier B)) := by
  apply ScottMap.ext
  intro A
  exact extend_principal_id B A

/-- Extending twice is extension by the Kleisli-composite basis data. -/
theorem extend_comp (φ : α → Carrier C) (ψ : β → Carrier K)
    (A : Carrier B) :
    extend C K ψ (extend B C φ A) =
      extend B K (fun a => extend C K ψ (φ a)) A := by
  apply ext
  ext c
  constructor
  · intro hc
    obtain ⟨b, hb, hcb⟩ :=
      (mem_extend (B := C) (C := K)).mp hc
    obtain ⟨a, ha, hba⟩ :=
      (mem_extend (B := B) (C := C)).mp hb
    exact (mem_extend (B := B) (C := K)).2
      ⟨a, ha, (mem_extend (B := C) (C := K)).2 ⟨b, hba, hcb⟩⟩
  · intro hc
    obtain ⟨a, ha, hca⟩ :=
      (mem_extend (B := B) (C := K)).mp hc
    obtain ⟨b, hba, hcb⟩ :=
      (mem_extend (B := C) (C := K)).mp hca
    exact (mem_extend (B := C) (C := K)).2
      ⟨b, (mem_extend (B := B) (C := C)).2 ⟨a, ha, hba⟩, hcb⟩

theorem extendScott_comp (φ : α → Carrier C) (ψ : β → Carrier K) :
    (extendScott C K ψ).comp (extendScott B C φ) =
      extendScott B K (fun a => extend C K ψ (φ a)) := by
  apply ScottMap.ext
  intro A
  exact extend_comp B C K φ ψ A

/-- Relation-valued basis data, rounded in the target basis. -/
noncomputable def principalData (R : α → β → Prop) (a : α) : Carrier C :=
  sSup (principal C '' {b | R a b})

theorem mem_principalData {R : α → β → Prop} {a : α} {b : β} :
    b ∈ principalData C R a ↔
      ∃ c, R a c ∧ C.below b c := by
  rw [principalData, mem_sSup]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, hbc⟩
    exact ⟨c, hc, (mem_principal (B := C)).mp hbc⟩
  · rintro ⟨c, hc, hbc⟩
    exact ⟨principal C c, ⟨c, hc, rfl⟩,
      (mem_principal (B := C)).2 hbc⟩

/-- Rounded extension generated by a derivation relation on basis tokens. -/
noncomputable def extendRelation (R : α → β → Prop) :
    ScottMap (Carrier B) (Carrier C) :=
  extendScott B C (principalData C R)

theorem mem_extendRelation {R : α → β → Prop}
    {A : Carrier B} {b : β} :
    b ∈ extendRelation B C R A ↔
      ∃ a ∈ A, ∃ c, R a c ∧ C.below b c := by
  rw [extendRelation, extendScott_apply, mem_extend]
  constructor
  · rintro ⟨a, ha, hb⟩
    obtain ⟨c, hc, hbc⟩ := (mem_principalData (C := C)).mp hb
    exact ⟨a, ha, c, hc, hbc⟩
  · rintro ⟨a, ha, c, hc, hbc⟩
    exact ⟨a, ha, (mem_principalData (C := C)).2 ⟨c, hc, hbc⟩⟩

end RoundedTheory

end QLambda
