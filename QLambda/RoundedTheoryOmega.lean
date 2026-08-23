/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.RoundedTheory
import QLambda.QuantumPower

/-!
# Countably based rounded theories are in `ωQVA`

For an encodable abstract basis, finite joins of single-membership gates
give a sequence of quantum-factorable, finitely separated approximants.
-/

open Set
open scoped MatrixOrder ComplexOrder

namespace QLambda

open Scott1972.ContinuousLattice

universe u v

namespace RoundedTheory

variable {α : Type u} (B : AbstractBasis α)

/-- A nonzero one-dimensional sub-normalized density, used as a Boolean marker. -/
def booleanMarker : SubNormalizedDensity 1 where
  mat := 1
  posSemidef := Matrix.PosSemidef.one
  trace_le_one := by simp [Matrix.trace]

theorem booleanMarker_ne_bot :
    booleanMarker ≠ (⊥ : SubNormalizedDensity 1) := by
  intro h
  have hm := congrArg SubNormalizedDensity.mat h
  have h00 := congrFun (congrFun hm (0 : Fin 1)) (0 : Fin 1)
  simp [booleanMarker, SubNormalizedDensity.mat_bot] at h00

theorem booleanMarker_not_le_bot :
    ¬ booleanMarker ≤ (⊥ : SubNormalizedDensity 1) := by
  intro h
  exact booleanMarker_ne_bot (le_antisymm h bot_le)

/-- The gate for `b` returns its rounded principal exactly when `b` belongs
to the input theory. -/
noncomputable def membershipGate (b : α) : ScottMap (Carrier B) (Carrier B) :=
  by
    classical
    exact
      ⟨fun A => if b ∈ A then principal B b else ⊥,
        continuous_of_preservesDirectedSup <| by
      intro S hS hdir
      by_cases hb : b ∈ (sSup S : Carrier B)
      · obtain ⟨A, hAS, hbA⟩ := (mem_sSup (B := B)).mp hb
        change (if b ∈ (sSup S : Carrier B) then principal B b else ⊥) =
          sSup ((fun A : Carrier B =>
            if b ∈ A then principal B b else ⊥) '' S)
        rw [if_pos hb]
        apply le_antisymm
        · have hmem :
              principal B b ∈
                (fun A : Carrier B => if b ∈ A then principal B b else ⊥) '' S :=
            ⟨A, hAS, by simp [hbA]⟩
          exact le_sSup hmem
        · refine sSup_le ?_
          rintro C ⟨A, hAS, rfl⟩
          by_cases hbA' : b ∈ A
          · simp [hbA']
          · simp [hbA']
      · change (if b ∈ (sSup S : Carrier B) then principal B b else ⊥) =
          sSup ((fun A : Carrier B =>
            if b ∈ A then principal B b else ⊥) '' S)
        rw [if_neg hb]
        apply le_antisymm bot_le
        refine sSup_le ?_
        rintro C ⟨A, hAS, rfl⟩
        have hbA : b ∉ A := by
          intro h
          apply hb
          exact (mem_sSup (B := B)).mpr ⟨A, hAS, h⟩
        simp [hbA]⟩

theorem membershipGate_apply_of_mem {b : α} {A : Carrier B} (hb : b ∈ A) :
    membershipGate B b A = principal B b := by
  classical
  simp [membershipGate, hb]

theorem membershipGate_apply_of_not_mem {b : α} {A : Carrier B} (hb : b ∉ A) :
    membershipGate B b A = ⊥ := by
  classical
  simp [membershipGate, hb]

theorem membershipGate_le_id (b : α) (A : Carrier B) :
    membershipGate B b A ≤ A := by
  by_cases hb : b ∈ A
  · rw [membershipGate_apply_of_mem B hb]
    exact principal_le B hb
  · rw [membershipGate_apply_of_not_mem B hb]
    exact bot_le

/-- A single membership gate factors through one one-dimensional density
block, with `booleanMarker` representing true and `⊥` false. -/
noncomputable def membershipGate_factorable (b : α) :
    QFactorable (membershipGate B b) := by
  classical
  exact
    { dims := [1]
      enc := fun A => (if b ∈ A then booleanMarker else ⊥, ⟨⟩)
      recon := fun v => if booleanMarker ≤ v.1 then principal B b else ⊥
      enc_mono := by
        intro A C hAC
        by_cases hbA : b ∈ A
        · have hbC : b ∈ C := hAC hbA
          simp only [hbA, hbC, ↓reduceIte]
          exact ⟨le_rfl, le_rfl⟩
        · by_cases hbC : b ∈ C
          · simp only [hbA, hbC, ↓reduceIte]
            exact ⟨bot_le, le_rfl⟩
          · simp only [hbA, hbC, ↓reduceIte]
            exact ⟨le_rfl, le_rfl⟩
      recon_mono := by
        intro v w hvw
        by_cases hv : booleanMarker ≤ v.1
        · have hw : booleanMarker ≤ w.1 := hv.trans hvw.1
          simp [hv, hw]
        · by_cases hw : booleanMarker ≤ w.1
          · simp [hv, hw]
          · simp [hv, hw]
      factor := fun A => by
        by_cases hb : b ∈ A
        · rw [membershipGate_apply_of_mem B hb]
          change principal B b =
            if booleanMarker ≤ (if b ∈ A then booleanMarker else ⊥)
            then principal B b else ⊥
          rw [if_pos hb, if_pos le_rfl]
        · rw [membershipGate_apply_of_not_mem B hb]
          change (⊥ : Carrier B) =
            if booleanMarker ≤ (if b ∈ A then booleanMarker else ⊥)
            then principal B b else ⊥
          rw [if_neg hb, if_neg booleanMarker_not_le_bot] }

theorem membershipGate_separated (b : α) :
    FinitelySeparated (membershipGate B b) := by
  classical
  refine ⟨{⊥, principal B b}, fun A => ?_⟩
  by_cases hb : b ∈ A
  · refine ⟨principal B b, by simp, ?_, principal_le B hb⟩
    rw [membershipGate_apply_of_mem B hb]
  · refine ⟨⊥, by simp, ?_, bot_le⟩
    rw [membershipGate_apply_of_not_mem B hb]

section Encodable

variable [Encodable α]

/-- The gate selected by the `n`-th decoded basis element. Missing decoder
entries contribute the bottom map. -/
noncomputable def decodedGate (n : ℕ) : ScottMap (Carrier B) (Carrier B) :=
  match Encodable.decode (α := α) n with
  | some b => membershipGate B b
  | none => ⊥

noncomputable def decodedGate_factorable (n : ℕ) :
    QFactorable (decodedGate B n) := by
  unfold decodedGate
  split
  · exact membershipGate_factorable B _
  · exact FunctionSpaceOmega.QFactorable.bot

theorem decodedGate_separated (n : ℕ) :
    FinitelySeparated (decodedGate B n) := by
  unfold decodedGate
  split
  · exact membershipGate_separated B _
  · exact FunctionSpaceOmega.finitelySeparated_bot (X := Carrier B)

theorem decodedGate_le_id (n : ℕ) (A : Carrier B) :
    decodedGate B n A ≤ A := by
  unfold decodedGate
  split
  · exact membershipGate_le_id B _ A
  · rw [ScottMap.bot_apply]
    exact bot_le

/-- The finite prefix join of decoded membership gates. -/
noncomputable def prefixApprox : ℕ → ScottMap (Carrier B) (Carrier B)
  | 0 => ⊥
  | n + 1 => prefixApprox n ⊔ decodedGate B n

noncomputable def prefixApprox_factorable (n : ℕ) :
    QFactorable (prefixApprox B n) := by
  induction n with
  | zero => exact FunctionSpaceOmega.QFactorable.bot
  | succ n ih =>
      rw [prefixApprox]
      exact FunctionSpaceOmega.QFactorable.sup ih (decodedGate_factorable B n)

theorem prefixApprox_separated (n : ℕ) :
    FinitelySeparated (prefixApprox B n) := by
  induction n with
  | zero =>
      exact FunctionSpaceOmega.finitelySeparated_bot (X := Carrier B)
  | succ n ih =>
      rw [prefixApprox]
      exact FunctionSpaceOmega.finitelySeparated_sup ih
        (decodedGate_separated B n)

theorem prefixApprox_le_id (n : ℕ) (A : Carrier B) :
    prefixApprox B n A ≤ A := by
  induction n with
  | zero =>
      change (⊥ : ScottMap (Carrier B) (Carrier B)) A ≤ A
      rw [ScottMap.bot_apply]
      exact bot_le
  | succ n ih =>
      rw [prefixApprox, ScottMap.sup_apply]
      exact sup_le ih (decodedGate_le_id B n A)

theorem prefixApprox_mono : Monotone (prefixApprox B) := by
  intro i j hij
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, prefixApprox]
      exact ih.trans le_sup_left

theorem iSup_prefixApprox :
    (⨆ n, prefixApprox B n) = (ScottMap.idMap : ScottMap (Carrier B) (Carrier B)) := by
  apply ScottMap.ext
  intro A
  rw [scottMap_iSup_apply, ScottMap.idMap_apply]
  apply le_antisymm
  · exact iSup_le fun n => prefixApprox_le_id B n A
  · intro a ha
    have haRound : a ∈ round B A.carrier := by
      rw [A.rounded]
      exact ha
    obtain ⟨b, hbA, hab⟩ := haRound
    let k := Encodable.encode b
    have hdecode : Encodable.decode (α := α) k = some b :=
      Encodable.encodek b
    have haGate : a ∈ decodedGate B k A := by
      rw [decodedGate, hdecode, membershipGate_apply_of_mem B hbA,
        mem_principal]
      exact hab
    have hle : decodedGate B k ≤ prefixApprox B (k + 1) := by
      rw [prefixApprox]
      exact le_sup_right
    exact le_iSup (fun n => (prefixApprox B n : Carrier B → Carrier B) A) (k + 1)
      (hle A haGate)

/-- Rounded theories over an encodable abstract basis form an `ωQVA`. -/
@[instance_reducible] noncomputable def isOmegaQVA : IsOmegaQVA (Carrier B) where
  isContinuousLattice := isContinuousLattice B
  approx := prefixApprox B
  qfactorable := prefixApprox_factorable B
  separated := prefixApprox_separated B
  monotone_approx := prefixApprox_mono B
  iSup_approx := iSup_prefixApprox B

end Encodable

end RoundedTheory

/-- Token theories over an encodable output index form an `ωQVA`. -/
@[instance_reducible] noncomputable def tokenTheory_isOmegaQVA
    (n : ℕ) {ι : Type v} [Encodable ι]
    {D : Type u} [CompleteLattice D] (C : OutputCode ι D) :
    IsOmegaQVA (TokenTheory n C) :=
  RoundedTheory.isOmegaQVA (CodedToken.roundedBasis (n := n) C)

noncomputable instance TokenTheory.instIsOmegaQVA
    (n : ℕ) {ι : Type v} [Encodable ι]
    {D : Type u} [CompleteLattice D] (C : OutputCode ι D) :
    IsOmegaQVA (TokenTheory n C) :=
  tokenTheory_isOmegaQVA n C

/-- The canonical token theory of an `ωQVA` is itself an `ωQVA`. -/
@[instance_reducible] noncomputable def omegaTokenTheory_isOmegaQVA
    (n : ℕ) (D : Type u) [CompleteLattice D] [IsOmegaQVA D] :
    IsOmegaQVA (OmegaTokenTheory n D) :=
  inferInstance

end QLambda
