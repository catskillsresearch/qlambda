/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Data.Nat.Bitwise
import QLambda.Composer.MatrixSemantics
import QLambda.CQ.Scratch

/-!
# Data-wire commutation

Lifting a logical operator onto `dataWire` commutes with scratch
initialization.
-/

open Matrix
open scoped BigOperators

namespace QLambda.Compiler

open QLambda.CQ
open QLambda.Composer

theorem testBit_lt_pow {n k : ℕ} (h : n < 2 ^ k) : n.testBit k = false :=
  Nat.testBit_eq_false_of_lt h

theorem testBit_of_twoPow_le {n k : ℕ}
    (hle : 2 ^ k ≤ n) (hlt : n < 2 ^ (k + 1)) :
    n.testBit k = true := by
  have hpos : 0 < 2 ^ k := pow_pos (by decide) k
  have hdiv : n / 2 ^ k = 1 := by
    have hlo : 1 ≤ n / 2 ^ k :=
      (Nat.le_div_iff_mul_le hpos).2 (by simpa using hle)
    have hhi : n / 2 ^ k < 2 :=
      (Nat.div_lt_iff_lt_mul hpos).2 (by simpa [pow_succ, mul_comm] using hlt)
    omega
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]

theorem initZero_conjTranspose_mul_initOne (q : ℕ) :
    (initZero q)ᴴ * initOne q = 0 := by
  have h := congrArg conjTranspose (initOne_conjTranspose_mul_initZero q)
  simpa [conjTranspose_mul, conjTranspose_zero] using h

theorem zeroIndex_testBit_scratch {q : ℕ} (j : Fin (QDim q)) :
    (zeroIndex q j).val.testBit q = false :=
  testBit_lt_pow j.isLt

theorem dataWire_injective_ne {q : ℕ} {i j : Fin q} (h : i ≠ j) :
    dataWire i ≠ dataWire j :=
  fun hc => h (Fin.castSucc_injective q hc)

/-- A data-wire operator commutes with scratch-zero embedding. -/
theorem onWire_data_mul_initZero {q : ℕ} (w : Fin q) (U : QubitMatrix) :
    onWire (dataWire w) U * initZero q = initZero q * onWire w U := by
  ext i j
  simp only [Matrix.mul_apply]
  have hL :
      (∑ k : Fin (QDim (q + 1)),
          onWire (dataWire w) U i k * initZero q k j) =
        onWire (dataWire w) U i (zeroIndex q j) := by
    trans onWire (dataWire w) U i (zeroIndex q j) * initZero q (zeroIndex q j) j
    · refine Fintype.sum_eq_single (zeroIndex q j) ?_
      intro k hk
      have hne : k.val ≠ j.val := fun h => hk (Fin.ext h)
      simp [initZero, hne]
    · simp [initZero]
  have hR :
      (∑ k : Fin (QDim q), initZero q i k * onWire w U k j) =
        if h : i.val < QDim q then onWire w U ⟨i.val, h⟩ j else 0 := by
    by_cases hi : i.val < QDim q
    · rw [dif_pos hi]
      trans initZero q i (⟨i.val, hi⟩ : Fin (QDim q)) *
          onWire w U (⟨i.val, hi⟩ : Fin (QDim q)) j
      · refine Fintype.sum_eq_single (⟨i.val, hi⟩ : Fin (QDim q)) ?_
        intro k hk
        have hne : i.val ≠ k.val := fun h => hk (Fin.ext h.symm)
        simp [initZero, hne]
      · simp [initZero]
    · rw [dif_neg hi]
      apply Finset.sum_eq_zero
      intro k _
      have hne : i.val ≠ k.val := by
        have := k.isLt
        omega
      simp [initZero, hne]
  rw [hL, hR, onWire_apply]
  by_cases hi : i.val < QDim q
  · rw [dif_pos hi, onWire_apply]
    have hothers :
        ((fun u : {v : Fin (q + 1) // v ≠ dataWire w} =>
            basisBits i u.1) =
          (fun u => basisBits (zeroIndex q j) u.1)) ↔
        ((fun u : {v : Fin q // v ≠ w} =>
            basisBits (⟨i.val, hi⟩ : Fin (QDim q)) u.1) =
          (fun u => basisBits j u.1)) := by
      constructor
      · intro h
        funext u
        have hu : (u.1.castSucc : Fin (q + 1)) ≠ dataWire w := by
          intro hc
          exact u.2 (Fin.castSucc_injective q (by simpa [dataWire] using hc))
        have := congrFun h ⟨u.1.castSucc, hu⟩
        simpa [basisBits, dataWire] using this
      · intro h
        funext u
        by_cases hs : u.1 = scratchWire q
        · have hi0 : i.val.testBit q = false := testBit_lt_pow hi
          have hj0 : j.val.testBit q = false := testBit_lt_pow j.isLt
          simp [basisBits, hs, scratchWire, hi0, hj0]
        · have hvlt : u.1.val < q := by
            have := u.1.isLt
            have hne : u.1.val ≠ q := by
              intro hval
              apply hs
              exact Fin.ext (by simp [scratchWire, hval])
            omega
          have hne : (⟨u.1.val, hvlt⟩ : Fin q) ≠ w := by
            intro hvw
            apply u.2
            apply Fin.ext
            simpa [dataWire] using congrArg Fin.val hvw
          have := congrFun h ⟨⟨u.1.val, hvlt⟩, hne⟩
          simpa [basisBits, dataWire] using this
    by_cases hphys :
        (fun u : {v : Fin (q + 1) // v ≠ dataWire w} => basisBits i u.1) =
          (fun u => basisBits (zeroIndex q j) u.1)
    · have hlog := hothers.mp hphys
      rw [if_pos hphys, if_pos hlog]
      simp [basisBits, dataWire]
    · have hlog :
          ¬ ((fun u : {v : Fin q // v ≠ w} =>
                basisBits (⟨i.val, hi⟩ : Fin (QDim q)) u.1) =
              (fun u => basisBits j u.1)) :=
        fun h => hphys (hothers.mpr h)
      rw [if_neg hphys, if_neg hlog]
      simp
  · rw [dif_neg hi]
    have hscratch_i : i.val.testBit q = true := by
      have hle : 2 ^ q ≤ i.val := Nat.le_of_not_gt hi
      have hlt : i.val < 2 ^ (q + 1) := i.isLt
      simpa [QDim] using testBit_of_twoPow_le hle hlt
    have hscratch_j : j.val.testBit q = false := testBit_lt_pow j.isLt
    have hne :
        (fun u : {v : Fin (q + 1) // v ≠ dataWire w} => basisBits i u.1) ≠
          (fun u => basisBits (zeroIndex q j) u.1) := by
      intro h
      have hs : scratchWire q ≠ dataWire w := (dataWire_ne_scratch w).symm
      have hbit := congrFun h ⟨scratchWire q, hs⟩
      simp [basisBits, scratchWire, hscratch_i, hscratch_j] at hbit
    simp [hne]

theorem onWire_data_mul_initZero_conj {q : ℕ} (w : Fin q) (U : QubitMatrix) :
    (initZero q)ᴴ * (onWire (dataWire w) U)ᴴ =
      (onWire w U)ᴴ * (initZero q)ᴴ := by
  have h := congrArg conjTranspose (onWire_data_mul_initZero w U)
  simpa [conjTranspose_mul] using h

theorem applyMat_discard_onWire_data {q : ℕ} (w : Fin q) (U : QubitMatrix)
    (ρ : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) :
    KrausFamily.applyMat (discardScratch q).kraus
      ((onWire (dataWire w) U) *
        (initZero q * ρ * (initZero q)ᴴ) *
        (onWire (dataWire w) U)ᴴ) =
      onWire w U * ρ * (onWire w U)ᴴ := by
  have hembed :
      onWire (dataWire w) U * (initZero q * ρ * (initZero q)ᴴ) *
          (onWire (dataWire w) U)ᴴ =
        initZero q * (onWire w U * ρ * (onWire w U)ᴴ) * (initZero q)ᴴ := by
    have hA := onWire_data_mul_initZero w U
    have hA' := onWire_data_mul_initZero_conj w U
    calc
      onWire (dataWire w) U * (initZero q * ρ * (initZero q)ᴴ) *
          (onWire (dataWire w) U)ᴴ
          = (onWire (dataWire w) U * initZero q) * ρ *
              ((initZero q)ᴴ * (onWire (dataWire w) U)ᴴ) := by
            simp [Matrix.mul_assoc]
      _ = (initZero q * onWire w U) * ρ *
            ((onWire w U)ᴴ * (initZero q)ᴴ) := by
            rw [hA, hA']
      _ = initZero q * (onWire w U * ρ * (onWire w U)ᴴ) * (initZero q)ᴴ := by
            simp [Matrix.mul_assoc]
  have hdisc :=
    applyMat_discard_initialize q (onWire w U * ρ * (onWire w U)ᴴ)
  rw [KrausFamily.applyMat_comp, initializeScratch_kraus,
    KrausFamily.applyMat_single] at hdisc
  rw [hembed]
  exact hdisc

theorem onWire_data_isometry {q : ℕ} (w : Fin q) (U : QubitMatrix)
    (hU : Uᴴ * U = 1) :
    (onWire (dataWire w) U)ᴴ * onWire (dataWire w) U = 1 := by
  simp [onWire_conjTranspose, onWire_mul, hU, onWire_one]

theorem onWire_isometry {q : ℕ} (w : Fin q) (U : QubitMatrix)
    (hU : Uᴴ * U = 1) :
    (onWire w U)ᴴ * onWire w U = 1 := by
  simp [onWire_conjTranspose, onWire_mul, hU, onWire_one]

/-- Hidden observation of a data-wire isometry is the logical isometry. -/
theorem hideScratch_ofIsometry_data {q c : ℕ} (w : Fin q) (U : QubitMatrix)
    (hU : Uᴴ * U = 1) :
    CQ.Eq
      (hideScratch (fun s : CStore (c + 1) =>
        FiniteInstrumentComp.ofOperation
          (QuantumOperation.ofIsometry (onWire (dataWire w) U)
            (onWire_data_isometry w U hU))
          s))
      (fun s : CStore c =>
        FiniteInstrumentComp.ofOperation
          (QuantumOperation.ofIsometry (onWire w U) (onWire_isometry w U hU))
          s) := by
  intro s P ρ
  have hunit :=
    FiniteInstrumentComp.wpKraus_ofOperation_semEq
      (QuantumOperation.ofIsometry (onWire w U) (onWire_isometry w U hU))
      s P ρ
  refine _root_.Eq.trans ?_ hunit.symm
  have hhide :=
    hideComp_applyMat_wpKraus
      (FiniteInstrumentComp.ofOperation
        (QuantumOperation.ofIsometry (onWire (dataWire w) U)
          (onWire_data_isometry w U hU))
        (initStore s))
      (P ∘ hideStore) ρ
  change
    KrausFamily.applyMat
      ((hideComp
        (FiniteInstrumentComp.ofOperation
          (QuantumOperation.ofIsometry (onWire (dataWire w) U)
            (onWire_data_isometry w U hU))
          (initStore s))).wpKraus (P ∘ hideStore)) ρ =
      KrausFamily.applyMat
        (KrausFamily.comp (P s)
          (QuantumOperation.ofIsometry (onWire w U)
            (onWire_isometry w U hU)).kraus) ρ
  rw [hhide]
  have hop :=
    FiniteInstrumentComp.wpKraus_ofOperation_semEq
      (QuantumOperation.ofIsometry (onWire (dataWire w) U)
        (onWire_data_isometry w U hU))
      (initStore s) (hidePost (P ∘ hideStore))
      (KrausFamily.applyMat (initializeScratch q).kraus ρ)
  rw [hop]
  simp only [hidePost, hideStore_initStore, Function.comp_apply,
    QuantumOperation.ofIsometry, KrausFamily.applyMat_comp,
    initializeScratch_kraus, KrausFamily.applyMat_single]
  rw [applyMat_discard_onWire_data]
  have hdisc :=
    applyMat_discard_initialize q
      (KrausFamily.applyMat (P s) (onWire w U * ρ * (onWire w U)ᴴ))
  rw [KrausFamily.applyMat_comp, initializeScratch_kraus,
    KrausFamily.applyMat_single] at hdisc
  exact hdisc

/-- Scratch-zero computational-basis labels have scratch bit `false`. -/
theorem basisBits_scratch_of_lt {q : ℕ} (i : Fin (QDim (q + 1)))
    (h : i.val < QDim q) :
    basisBits i (scratchWire q) = false := by
  simpa [basisBits, scratchWire] using testBit_lt_pow h

/-- Scratch-one computational-basis labels have scratch bit `true`. -/
theorem basisBits_scratch_of_ge {q : ℕ} (i : Fin (QDim (q + 1)))
    (h : QDim q ≤ i.val) :
    basisBits i (scratchWire q) = true := by
  have hlt : i.val < 2 ^ (q + 1) := i.isLt
  simpa [basisBits, scratchWire, QDim] using
    testBit_of_twoPow_le (by simpa [QDim] using h) hlt

theorem basisBits_scratch_false_iff {q : ℕ} (i : Fin (QDim (q + 1))) :
    basisBits i (scratchWire q) = false ↔ i.val < QDim q := by
  constructor
  · intro h
    by_contra hge
    have := basisBits_scratch_of_ge i (Nat.le_of_not_gt hge)
    exact Bool.false_ne_true (h.symm.trans this)
  · exact basisBits_scratch_of_lt i

theorem basisBits_scratch_true_iff {q : ℕ} (i : Fin (QDim (q + 1))) :
    basisBits i (scratchWire q) = true ↔ QDim q ≤ i.val := by
  constructor
  · intro h
    by_contra hlt
    have := basisBits_scratch_of_lt i (Nat.lt_of_not_ge hlt)
    exact Bool.false_ne_true (this.symm.trans h)
  · exact basisBits_scratch_of_ge i

private theorem dataWire_ne_last {q : ℕ} (k : Fin q) :
    k.castSucc ≠ scratchWire q := by
  simp [scratchWire]

/-- Data-wire bits agree iff the indices agree modulo the logical dimension. -/
theorem others_scratch_iff {q : ℕ} (i j : Fin (QDim (q + 1))) :
    ((fun u : {v : Fin (q + 1) // v ≠ scratchWire q} =>
        basisBits i u.1) =
      (fun u => basisBits j u.1)) ↔
    i.val % QDim q = j.val % QDim q := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < q
    · have hbit : i.val.testBit k = j.val.testBit k := by
        have := congrFun h ⟨(⟨k, hk⟩ : Fin q).castSucc, dataWire_ne_last _⟩
        simpa [basisBits] using this
      simp [Nat.testBit_mod_two_pow, QDim, hk, hbit]
    · simp [Nat.testBit_mod_two_pow, QDim, hk]
  · intro h
    funext u
    have hvlt : u.1.val < q := by
      have := u.1.isLt
      have hne : u.1.val ≠ q := by
        intro hval
        apply u.2
        exact Fin.ext (by simp [scratchWire, hval])
      omega
    have hbit : i.val.testBit u.1.val = j.val.testBit u.1.val := by
      have hi : (i.val % QDim q).testBit u.1.val = i.val.testBit u.1.val := by
        simp [Nat.testBit_mod_two_pow, QDim, hvlt]
      have hj : (j.val % QDim q).testBit u.1.val = j.val.testBit u.1.val := by
        simp [Nat.testBit_mod_two_pow, QDim, hvlt]
      simpa [hi, hj] using congrArg (fun n => n.testBit u.1.val) h
    simpa [basisBits] using hbit

theorem val_eq_of_others_scratch_zero {q : ℕ}
    {i j : Fin (QDim (q + 1))}
    (hi : i.val < QDim q) (hj : j.val < QDim q)
    (hoth :
      (fun u : {v : Fin (q + 1) // v ≠ scratchWire q} =>
          basisBits i u.1) =
        (fun u => basisBits j u.1)) :
    i = j :=
  Fin.ext (by
    have := (others_scratch_iff i j).mp hoth
    simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using this)

theorem resetKraus_scratch_false (q : ℕ) :
    resetKraus (scratchWire q) false = initZero q * (initZero q)ᴴ := by
  ext i j
  rw [resetKraus, onWire_apply, initZero_projector_apply]
  simp only [reset₂]
  by_cases h0 : basisBits i (scratchWire q) = false ∧
      basisBits j (scratchWire q) = false
  · have hi : i.val < QDim q := (basisBits_scratch_false_iff i).mp h0.1
    have hj : j.val < QDim q := (basisBits_scratch_false_iff j).mp h0.2
    by_cases hoth :
        (fun u : {v : Fin (q + 1) // v ≠ scratchWire q} =>
            basisBits i u.1) =
          (fun u => basisBits j u.1)
    · have hij := val_eq_of_others_scratch_zero hi hj hoth
      simp [h0, hoth, hij, hi, hj]
    · have hij : i ≠ j := fun h => hoth (by simp [h])
      simp [h0, hoth, hij, hi]
  · have hneg : ¬ (i = j ∧ i.val < QDim q) := by
      intro h
      apply h0
      have hi := h.2
      have hj : j.val < QDim q := by
        simpa [h.1] using hi
      exact ⟨(basisBits_scratch_false_iff i).mpr hi,
        (basisBits_scratch_false_iff j).mpr hj⟩
    simp [h0, hneg]

theorem oneIndex_val_div (q : ℕ) {j : Fin (QDim (q + 1))}
    (hj : QDim q ≤ j.val) :
    j.val / QDim q = 1 := by
  have hpos : 0 < QDim q := pow_pos (by decide) q
  have hlo : 1 ≤ j.val / QDim q :=
    (Nat.le_div_iff_mul_le hpos).2 (by simpa [QDim] using hj)
  have hhi : j.val / QDim q < 2 :=
    (Nat.div_lt_iff_lt_mul hpos).2 (by
      simpa [QDim, pow_succ, mul_comm] using j.isLt)
  omega

theorem val_eq_oneIndex_of_others {q : ℕ}
    {i : Fin (QDim q)} {j : Fin (QDim (q + 1))}
    (hj : QDim q ≤ j.val)
    (hmod : j.val % QDim q = i.val) :
    j.val = QDim q + i.val := by
  have hdiv := oneIndex_val_div q hj
  have hdecomp := Nat.div_add_mod j.val (QDim q)
  calc
    j.val = QDim q * (j.val / QDim q) + j.val % QDim q := hdecomp.symm
    _ = QDim q * 1 + i.val := by rw [hdiv, hmod]
    _ = QDim q + i.val := by ring

theorem resetKraus_scratch_true (q : ℕ) :
    resetKraus (scratchWire q) true = initZero q * (initOne q)ᴴ := by
  ext i j
  rw [resetKraus, onWire_apply]
  simp only [reset₂, Matrix.mul_apply, conjTranspose_apply]
  by_cases h01 : basisBits i (scratchWire q) = false ∧
      basisBits j (scratchWire q) = true
  · have hi : i.val < QDim q := (basisBits_scratch_false_iff i).mp h01.1
    have hj : QDim q ≤ j.val := (basisBits_scratch_true_iff j).mp h01.2
    rw [Finset.sum_eq_single ⟨i.val, hi⟩]
    · simp only [initZero, initOne]
      by_cases hoth :
          (fun u : {v : Fin (q + 1) // v ≠ scratchWire q} =>
              basisBits i u.1) =
            (fun u => basisBits j u.1)
      · have hmod := (others_scratch_iff i j).mp hoth
        have hjval : j.val = QDim q + i.val :=
          val_eq_oneIndex_of_others (i := ⟨i.val, hi⟩) hj (by
            change j.val % QDim q = i.val
            rw [← Nat.mod_eq_of_lt hi]
            exact hmod.symm)
        simp [h01, hoth, hjval]
      · have hne : j.val ≠ QDim q + i.val := by
          intro hjval
          apply hoth
          apply (others_scratch_iff i j).mpr
          have : j.val % QDim q = i.val := by
            rw [hjval, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
            exact Nat.mod_eq_of_lt hi
          rw [Nat.mod_eq_of_lt hi, this]
        simp [h01, hoth, hne]
    · intro b _ hbi
      have hne : i.val ≠ b.val := fun h => hbi (Fin.ext h.symm)
      simp [initZero, hne]
    · simp
  · rw [if_neg h01, zero_mul]
    refine (Finset.sum_eq_zero ?_).symm
    intro b _
    by_cases hbi : i.val = b.val
    · have hi : i.val < QDim q := hbi ▸ b.isLt
      have hi0 : basisBits i (scratchWire q) = false :=
        (basisBits_scratch_false_iff i).mpr hi
      have hne : j.val ≠ QDim q + b.val := by
        intro hjval
        have hj : QDim q ≤ j.val := by
          simpa [hjval] using Nat.le_add_right (QDim q) b.val
        have hj1 : basisBits j (scratchWire q) = true :=
          (basisBits_scratch_true_iff j).mpr hj
        exact h01 ⟨hi0, hj1⟩
      simp [initZero, initOne, hbi, hne]
    · simp [initZero, hbi]

/-- Resetting the reserved wire is initialize-after-discard. -/
theorem applyMat_reset_scratch (q : ℕ)
    (ρ : Matrix (Fin (QDim (q + 1))) (Fin (QDim (q + 1))) ℂ) :
    KrausFamily.applyMat (reset (scratchWire q)).kraus ρ =
      KrausFamily.applyMat (initializeScratch q).kraus
        (KrausFamily.applyMat (discardScratch q).kraus ρ) := by
  simp only [reset, initializeScratch_kraus, discardScratch_kraus,
    KrausFamily.applyMat_cons, KrausFamily.applyMat_single,
    KrausFamily.applyMat_nil, add_zero]
  rw [resetKraus_scratch_false, resetKraus_scratch_true]
  have h0 :
      (initZero q * (initZero q)ᴴ) * ρ * (initZero q * (initZero q)ᴴ)ᴴ =
        initZero q * ((initZero q)ᴴ * ρ * initZero q) * (initZero q)ᴴ := by
    simp [conjTranspose_mul, Matrix.mul_assoc]
  have h1 :
      (initZero q * (initOne q)ᴴ) * ρ * (initZero q * (initOne q)ᴴ)ᴴ =
        initZero q * ((initOne q)ᴴ * ρ * initOne q) * (initZero q)ᴴ := by
    simp [conjTranspose_mul, Matrix.mul_assoc]
  rw [h0, h1]
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- Coin-angle RY maps the scratch-zero embedding to the weighted superposition. -/
theorem ry_coin_mul_initZero (q : ℕ) (p : Probability) :
    ryMatrix (AngleExpr.coin p).eval (scratchWire q) * initZero q =
      (Real.sqrt p.real : ℂ) • initZero q +
        (Real.sqrt (1 - p.real) : ℂ) • initOne q := by
  ext i j
  simp only [ryMatrix, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply]
  have hL :
      (∑ k : Fin (QDim (q + 1)),
          onWire (scratchWire q) (ry₂ (AngleExpr.coin p).eval) i k *
            initZero q k j) =
        onWire (scratchWire q) (ry₂ (AngleExpr.coin p).eval)
          i (zeroIndex q j) := by
    trans onWire (scratchWire q) (ry₂ (AngleExpr.coin p).eval)
        i (zeroIndex q j) * initZero q (zeroIndex q j) j
    · refine Fintype.sum_eq_single (zeroIndex q j) ?_
      intro k hk
      have hne : k.val ≠ j.val := fun h => hk (Fin.ext h)
      simp [initZero, hne]
    · simp [initZero]
  rw [hL, onWire_apply]
  have hj0 : basisBits (zeroIndex q j) (scratchWire q) = false :=
    basisBits_scratch_of_lt (zeroIndex q j) (by
      simpa [zeroIndex] using j.isLt)
  have hamp := ry₂_coin_zero p
  by_cases hi : i.val < QDim q
  · have hi0 : basisBits i (scratchWire q) = false :=
      basisBits_scratch_of_lt i hi
    by_cases hoth :
        (fun u : {v : Fin (q + 1) // v ≠ scratchWire q} =>
            basisBits i u.1) =
          (fun u => basisBits (zeroIndex q j) u.1)
    · have hij : i.val = j.val := by
        have := val_eq_of_others_scratch_zero hi (by
          simpa [zeroIndex] using j.isLt) hoth
        simpa [zeroIndex] using congrArg Fin.val this
      have hne1 : i.val ≠ QDim q + j.val := by
        have := j.isLt
        omega
      simp [hi0, hj0, hoth, initZero, initOne, hij, hne1, hamp.1]
    · have hne0 : i.val ≠ j.val := by
        intro hij
        apply hoth
        apply (others_scratch_iff i (zeroIndex q j)).mpr
        simp [zeroIndex, hij, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt j.isLt]
      have hne1 : i.val ≠ QDim q + j.val := by
        have := j.isLt
        omega
      simp [hi0, hj0, hoth, initZero, initOne, hne0, hne1]
  · have hi1 : basisBits i (scratchWire q) = true :=
      basisBits_scratch_of_ge i (Nat.le_of_not_gt hi)
    by_cases hoth :
        (fun u : {v : Fin (q + 1) // v ≠ scratchWire q} =>
            basisBits i u.1) =
          (fun u => basisBits (zeroIndex q j) u.1)
    · have hij : i.val = QDim q + j.val :=
        val_eq_oneIndex_of_others (i := j) (Nat.le_of_not_gt hi) (by
          have := (others_scratch_iff i (zeroIndex q j)).mp hoth
          simpa [zeroIndex, Nat.mod_eq_of_lt j.isLt] using this)
      have hne0 : i.val ≠ j.val := by
        have := j.isLt
        omega
      simp [hi1, hj0, hoth, initZero, initOne, hij, hne0, hamp.2]
    · have hne1 : i.val ≠ QDim q + j.val := by
        intro hij
        apply hoth
        apply (others_scratch_iff i (zeroIndex q j)).mpr
        have : i.val % QDim q = j.val := by
          rw [hij, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
          exact Nat.mod_eq_of_lt j.isLt
        simpa [zeroIndex, Nat.mod_eq_of_lt j.isLt] using this
      have hne0 : i.val ≠ j.val := by
        have := j.isLt
        omega
      simp [hi1, hj0, hoth, initZero, initOne, hne0, hne1]

theorem projector_scratch_false (q : ℕ) :
    projector (scratchWire q) false = initZero q * (initZero q)ᴴ := by
  have h : proj₂ false = reset₂ false := by
    ext i j
    cases i <;> cases j <;> simp [proj₂, reset₂]
  simpa [projector, resetKraus, h] using resetKraus_scratch_false q

theorem projector_scratch_true (q : ℕ) :
    projector (scratchWire q) true = initOne q * (initOne q)ᴴ := by
  ext i j
  rw [projector, onWire_apply, initOne_projector_apply]
  simp only [proj₂]
  by_cases h1 : basisBits i (scratchWire q) = true ∧
      basisBits j (scratchWire q) = true
  · have hi : QDim q ≤ i.val := (basisBits_scratch_true_iff i).mp h1.1
    have hj : QDim q ≤ j.val := (basisBits_scratch_true_iff j).mp h1.2
    by_cases hoth :
        (fun u : {v : Fin (q + 1) // v ≠ scratchWire q} =>
            basisBits i u.1) =
          (fun u => basisBits j u.1)
    · have hdiv_i := oneIndex_val_div q hi
      have hdiv_j := oneIndex_val_div q hj
      have hmod := (others_scratch_iff i j).mp hoth
      have hij : i = j := by
        apply Fin.ext
        calc
          i.val = QDim q * (i.val / QDim q) + i.val % QDim q :=
            (Nat.div_add_mod i.val (QDim q)).symm
          _ = QDim q + j.val % QDim q := by
            rw [hdiv_i, hmod, mul_one]
          _ = QDim q * (j.val / QDim q) + j.val % QDim q := by
            rw [hdiv_j, mul_one]
          _ = j.val := Nat.div_add_mod j.val (QDim q)
      simp [h1, hoth, hij, hi, hj]
    · have hne : i ≠ j := by
        intro h
        apply hoth
        simp [h]
      simp [h1, hoth, hne, hi]
  · have hneg : ¬ (i = j ∧ QDim q ≤ i.val) := by
      intro h
      apply h1
      have hi := h.2
      have hj : QDim q ≤ j.val := by simpa [h.1] using hi
      exact ⟨(basisBits_scratch_true_iff i).mpr hi,
        (basisBits_scratch_true_iff j).mpr hj⟩
    simp [h1, hneg]

/-- Reset after scratch-zero embedding is the identity embedding. -/
theorem applyMat_reset_scratch_init (q : ℕ)
    (ρ : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) :
    KrausFamily.applyMat (reset (scratchWire q)).kraus
      (initZero q * ρ * (initZero q)ᴴ) =
      initZero q * ρ * (initZero q)ᴴ := by
  rw [applyMat_reset_scratch]
  have hdisc := applyMat_discard_initialize q ρ
  rw [KrausFamily.applyMat_comp, initializeScratch_kraus,
    KrausFamily.applyMat_single] at hdisc
  rw [initializeScratch_kraus, KrausFamily.applyMat_single, hdisc]

/-- Reset then coin-angle RY on the reserved wire, starting from `|0⟩`,
prepares the weighted scratch superposition. -/
theorem physicalCoin_amplitudes (q : ℕ) (p : Probability)
    (ρ : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) :
    ryMatrix (AngleExpr.coin p).eval (scratchWire q) *
        (KrausFamily.applyMat (reset (scratchWire q)).kraus
          (initZero q * ρ * (initZero q)ᴴ)) *
        (ryMatrix (AngleExpr.coin p).eval (scratchWire q))ᴴ =
      ((Real.sqrt p.real : ℂ) • initZero q +
          (Real.sqrt (1 - p.real) : ℂ) • initOne q) *
        ρ *
        ((Real.sqrt p.real : ℂ) • initZero q +
            (Real.sqrt (1 - p.real) : ℂ) • initOne q)ᴴ := by
  rw [applyMat_reset_scratch_init]
  have hRY := ry_coin_mul_initZero q p
  calc
    ryMatrix (AngleExpr.coin p).eval (scratchWire q) *
          (initZero q * ρ * (initZero q)ᴴ) *
          (ryMatrix (AngleExpr.coin p).eval (scratchWire q))ᴴ =
        (ryMatrix (AngleExpr.coin p).eval (scratchWire q) * initZero q) * ρ *
          ((initZero q)ᴴ *
            (ryMatrix (AngleExpr.coin p).eval (scratchWire q))ᴴ) := by
      simp [Matrix.mul_assoc]
    _ = (ryMatrix (AngleExpr.coin p).eval (scratchWire q) * initZero q) * ρ *
          (ryMatrix (AngleExpr.coin p).eval (scratchWire q) * initZero q)ᴴ := by
      simp [conjTranspose_mul]
    _ = ((Real.sqrt p.real : ℂ) • initZero q +
            (Real.sqrt (1 - p.real) : ℂ) • initOne q) * ρ *
          ((Real.sqrt p.real : ℂ) • initZero q +
              (Real.sqrt (1 - p.real) : ℂ) • initOne q)ᴴ := by
      rw [hRY]


theorem initOne_isometry (q : ℕ) :
    (initOne q)ᴴ * initOne q = 1 := by
  ext i j
  simp only [Matrix.mul_apply, conjTranspose_apply, initOne, one_apply]
  by_cases hij : i = j
  · subst j
    rw [Finset.sum_eq_single (oneIndex q i)]
    · simp [oneIndex]
    · intro b _ hbi
      have hne : b.val ≠ QDim q + i.val := by
        intro h
        apply hbi
        apply Fin.ext
        exact h
      simp [hne]
    · simp
  · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hbi : b.val = QDim q + i.val
    · have hbj : b.val ≠ QDim q + j.val := by omega
      simp [hbi, hv]
    · simp [hbi]

/-- Discard after a scratch-zero embedding is the identity on the data register. -/
theorem applyMat_discard_embed (q : ℕ)
    (ρ : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) :
    KrausFamily.applyMat (discardScratch q).kraus
      (initZero q * ρ * (initZero q)ᴴ) = ρ := by
  have h := applyMat_discard_initialize q ρ
  simpa [KrausFamily.applyMat_comp, initializeScratch_kraus,
    KrausFamily.applyMat_single] using h

/-- An operator commuting with scratch-zero embedding pushes through discard
on states supported in that subspace. -/
theorem applyMat_discard_comm_init {q : ℕ}
    (U : KrausOperator (QDim (q + 1)) (QDim (q + 1)))
    (V : KrausOperator (QDim q) (QDim q))
    (h : U * initZero q = initZero q * V)
    (ρ : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) :
    KrausFamily.applyMat (discardScratch q).kraus
      (U * (initZero q * ρ * (initZero q)ᴴ) * Uᴴ) =
      V * ρ * Vᴴ := by
  have hU' : (initZero q)ᴴ * Uᴴ = Vᴴ * (initZero q)ᴴ := by
    simpa [conjTranspose_mul] using congrArg conjTranspose h
  have hembed :
      U * (initZero q * ρ * (initZero q)ᴴ) * Uᴴ =
        initZero q * (V * ρ * Vᴴ) * (initZero q)ᴴ := by
    calc
      U * (initZero q * ρ * (initZero q)ᴴ) * Uᴴ
          = (U * initZero q) * ρ * ((initZero q)ᴴ * Uᴴ) := by
            simp [Matrix.mul_assoc]
      _ = (initZero q * V) * ρ * (Vᴴ * (initZero q)ᴴ) := by
            rw [h, hU']
      _ = initZero q * (V * ρ * Vᴴ) * (initZero q)ᴴ := by
            simp [Matrix.mul_assoc]
  rw [hembed]
  exact applyMat_discard_embed q (V * ρ * Vᴴ)

/-- Hidden observation of a physical isometry that preserves scratch zero. -/
theorem hideScratch_ofIsometry_comm {q c : ℕ}
    (U : KrausOperator (QDim (q + 1)) (QDim (q + 1)))
    (V : KrausOperator (QDim q) (QDim q))
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (hcomm : U * initZero q = initZero q * V) :
    CQ.Eq
      (hideScratch (fun s : CStore (c + 1) =>
        FiniteInstrumentComp.ofOperation
          (QuantumOperation.ofIsometry U hU) s))
      (fun s : CStore c =>
        FiniteInstrumentComp.ofOperation
          (QuantumOperation.ofIsometry V hV) s) := by
  intro s P ρ
  have hunit :=
    FiniteInstrumentComp.wpKraus_ofOperation_semEq
      (QuantumOperation.ofIsometry V hV) s P ρ
  refine _root_.Eq.trans ?_ hunit.symm
  have hhide :=
    hideComp_applyMat_wpKraus
      (FiniteInstrumentComp.ofOperation
        (QuantumOperation.ofIsometry U hU) (initStore s))
      (P ∘ hideStore) ρ
  simp only [hideScratch, FiniteInstrumentComp.wpKraus_map]
  rw [hhide]
  have hop :=
    FiniteInstrumentComp.wpKraus_ofOperation_semEq
      (QuantumOperation.ofIsometry U hU) (initStore s)
      (hidePost (P ∘ hideStore))
      (KrausFamily.applyMat (initializeScratch q).kraus ρ)
  rw [hop]
  simp only [hidePost, hideStore_initStore, Function.comp_apply,
    QuantumOperation.ofIsometry, KrausFamily.applyMat_comp,
    initializeScratch_kraus, KrausFamily.applyMat_single]
  rw [applyMat_discard_comm_init U V hcomm]
  have hdisc :=
    applyMat_discard_initialize q
      (KrausFamily.applyMat (P s) (V * ρ * Vᴴ))
  rw [KrausFamily.applyMat_comp, initializeScratch_kraus,
    KrausFamily.applyMat_single] at hdisc
  exact hdisc

theorem highIndex_sub_lt {q : ℕ} {i : Fin (QDim (q + 1))}
    (hi : QDim q ≤ i.val) :
    i.val - QDim q < QDim q := by
  have hdim : QDim (q + 1) = QDim q * 2 := by
    simp [QDim, pow_succ]
  have hphys : i.val < QDim q * 2 := by
    simpa [hdim] using i.isLt
  omega

theorem testBit_div_two (n k : ℕ) :
    n.testBit (k + 1) = (n / 2).testBit k := by
  simp only [Nat.testBit, ← Nat.bodd_eq_one_and_ne_zero, Nat.shiftRight_add]
  rw [← Nat.shiftRight_add, Nat.add_comm k 1, Nat.shiftRight_add, Nat.shiftRight_one]

theorem two_pow_succ_pred {q : ℕ} (hq : 1 ≤ q) :
    2 ^ q = 2 * 2 ^ (q - 1) := by
  calc
    2 ^ q = 2 ^ (q - 1 + 1) := by rw [Nat.sub_add_cancel hq]
    _ = 2 ^ (q - 1) * 2 := by rw [pow_succ]
    _ = 2 * 2 ^ (q - 1) := by rw [mul_comm]

theorem testBit_add_two_pow {q k m : ℕ} (hk : k < q) :
    (2 ^ q + m).testBit k = m.testBit k := by
  induction k generalizing q m with
  | zero =>
      have hpow := two_pow_succ_pred (Nat.succ_le_of_lt hk)
      simp only [Nat.testBit, Nat.shiftRight_zero, ← Nat.bodd_eq_one_and_ne_zero]
      rw [hpow, Nat.bodd_add, Nat.bodd_mul, Nat.bodd_two]
      simp
  | succ k ih =>
      have hkq : k < q - 1 := by omega
      have hpow := two_pow_succ_pred (by omega : 1 ≤ q)
      have hdiv : (2 ^ q + m) / 2 = 2 ^ (q - 1) + m / 2 := by
        rw [hpow, add_comm, Nat.add_mul_div_left _ _ (by decide : 0 < 2), add_comm]
      rw [testBit_div_two, testBit_div_two, hdiv]
      exact ih hkq

theorem basisBits_dataWire_zeroIndex {q : ℕ} (j : Fin (QDim q)) (w : Fin q) :
    basisBits (zeroIndex q j) (dataWire w) = basisBits j w := by
  simp [basisBits, zeroIndex, dataWire]

theorem basisBits_dataWire_oneIndex {q : ℕ} (j : Fin (QDim q)) (w : Fin q) :
    basisBits (oneIndex q j) (dataWire w) = basisBits j w := by
  simp only [basisBits, dataWire, oneIndex, QDim]
  exact testBit_add_two_pow w.isLt

theorem highIndex_eq_oneIndex {q : ℕ} {i : Fin (QDim (q + 1))}
    (hi : QDim q ≤ i.val) :
    i = oneIndex q ⟨i.val - QDim q, highIndex_sub_lt hi⟩ := by
  apply Fin.ext
  simp [oneIndex, Nat.add_sub_of_le hi]

/-- A data-wire operator preserves the scratch-one subspace. -/
theorem onWire_data_mul_initOne {q : ℕ} (w : Fin q) (U : QubitMatrix) :
    onWire (dataWire w) U * initOne q = initOne q * onWire w U := by
  ext i j
  simp only [Matrix.mul_apply]
  have hL :
      (∑ k : Fin (QDim (q + 1)),
          onWire (dataWire w) U i k * initOne q k j) =
        onWire (dataWire w) U i (oneIndex q j) := by
    trans onWire (dataWire w) U i (oneIndex q j) * initOne q (oneIndex q j) j
    · refine Fintype.sum_eq_single (oneIndex q j) ?_
      intro k hk
      have hne : k.val ≠ QDim q + j.val := fun h => hk (Fin.ext h)
      simp [initOne, hne]
    · simp [initOne, oneIndex]
  have hR :
      (∑ k : Fin (QDim q), initOne q i k * onWire w U k j) =
        if h : QDim q ≤ i.val then
          onWire w U ⟨i.val - QDim q, highIndex_sub_lt h⟩ j
        else 0 := by
    by_cases hi : QDim q ≤ i.val
    · rw [dif_pos hi]
      let k0 : Fin (QDim q) := ⟨i.val - QDim q, highIndex_sub_lt hi⟩
      trans initOne q i k0 * onWire w U k0 j
      · refine Fintype.sum_eq_single k0 ?_
        intro k hk
        have hne : i.val ≠ QDim q + k.val := by
          intro h
          apply hk
          apply Fin.ext
          have hk0 : k0.val = i.val - QDim q := rfl
          omega
        simp [initOne, hne]
      · simp [initOne, k0, Nat.add_sub_of_le hi]
    · rw [dif_neg hi]
      apply Finset.sum_eq_zero
      intro k _
      have hne : i.val ≠ QDim q + k.val := by omega
      simp [initOne, hne]
  rw [hL, hR, onWire_apply]
  by_cases hi : QDim q ≤ i.val
  · rw [dif_pos hi, onWire_apply]
    let r : Fin (QDim q) := ⟨i.val - QDim q, highIndex_sub_lt hi⟩
    have hi_eq : i = oneIndex q r := highIndex_eq_oneIndex hi
    have hothers :
        ((fun u : {v : Fin (q + 1) // v ≠ dataWire w} => basisBits i u.1) =
          (fun u => basisBits (oneIndex q j) u.1)) ↔
        ((fun u : {v : Fin q // v ≠ w} => basisBits r u.1) =
          (fun u => basisBits j u.1)) := by
      constructor
      · intro h
        funext u
        have hu : (u.1.castSucc : Fin (q + 1)) ≠ dataWire w := by
          intro hc
          exact u.2 (Fin.castSucc_injective q (by simpa [dataWire] using hc))
        have hbit := congrFun h ⟨u.1.castSucc, hu⟩
        simp only [basisBits, dataWire, Fin.coe_castSucc] at hbit
        rw [hi_eq] at hbit
        simp only [oneIndex, QDim] at hbit
        rw [testBit_add_two_pow u.1.isLt, testBit_add_two_pow u.1.isLt] at hbit
        simpa [basisBits] using hbit
      · intro h
        funext u
        by_cases hs : u.1 = scratchWire q
        · have hi1 : basisBits i (scratchWire q) = true :=
            basisBits_scratch_of_ge i hi
          have hj1 : basisBits (oneIndex q j) (scratchWire q) = true :=
            basisBits_scratch_of_ge (oneIndex q j) (by
              simpa [oneIndex] using Nat.le_add_right (QDim q) j.val)
          simp [hs, hi1, hj1]
        · have hvlt : u.1.val < q := by
            have := u.1.isLt
            have hne : u.1.val ≠ q := by
              intro hval
              apply hs
              exact Fin.ext (by simp [scratchWire, hval])
            omega
          have hne : (⟨u.1.val, hvlt⟩ : Fin q) ≠ w := by
            intro hvw
            apply u.2
            apply Fin.ext
            simpa [dataWire] using congrArg Fin.val hvw
          have hbit := congrFun h ⟨⟨u.1.val, hvlt⟩, hne⟩
          simp only [basisBits] at hbit
          rw [hi_eq]
          simp only [basisBits, oneIndex, dataWire, QDim]
          rw [testBit_add_two_pow hvlt, testBit_add_two_pow hvlt]
          exact hbit
    by_cases hphys :
        (fun u : {v : Fin (q + 1) // v ≠ dataWire w} => basisBits i u.1) =
          (fun u => basisBits (oneIndex q j) u.1)
    · have hlog := hothers.mp hphys
      rw [if_pos hphys, if_pos hlog]
      have hival : i.val = QDim q + r.val := by
        simpa [oneIndex] using congrArg Fin.val hi_eq
      simp only [basisBits, dataWire, oneIndex, Fin.val_castSucc, QDim]
      rw [hival, testBit_add_two_pow w.isLt, testBit_add_two_pow w.isLt,
        Nat.add_sub_of_le hi]
    · have hlog :
          ¬ ((fun u : {v : Fin q // v ≠ w} => basisBits r u.1) =
              (fun u => basisBits j u.1)) :=
        fun h => hphys (hothers.mpr h)
      rw [if_neg hphys, if_neg hlog]
      simp
  · rw [dif_neg hi]
    have hscratch_i : basisBits i (scratchWire q) = false :=
      basisBits_scratch_of_lt i (Nat.lt_of_not_ge hi)
    have hscratch_j : basisBits (oneIndex q j) (scratchWire q) = true :=
      basisBits_scratch_of_ge (oneIndex q j) (by
        simpa [oneIndex] using Nat.le_add_right (QDim q) j.val)
    have hne :
        (fun u : {v : Fin (q + 1) // v ≠ dataWire w} => basisBits i u.1) ≠
          (fun u => basisBits (oneIndex q j) u.1) := by
      intro h
      have hs : scratchWire q ≠ dataWire w := (dataWire_ne_scratch w).symm
      have hbit := congrFun h ⟨scratchWire q, hs⟩
      simp only [basisBits, scratchWire] at hscratch_i hscratch_j hbit
      rw [hbit] at hscratch_i
      exact Bool.false_ne_true (hscratch_i.symm.trans hscratch_j)
    simp [hne]

theorem initZero_conj_mul_subspace {q : ℕ}
    (K : KrausOperator (QDim (q + 1)) (QDim (q + 1)))
    (V : KrausOperator (QDim q) (QDim q))
    (h0 : K * initZero q = initZero q * V)
    (h1 : K * initOne q = initOne q * V) :
    (initZero q)ᴴ * K = V * (initZero q)ᴴ := by
  have hK :
      K = initZero q * V * (initZero q)ᴴ + initOne q * V * (initOne q)ᴴ := by
    calc
      K = K * 1 := (Matrix.mul_one K).symm
      _ = K * (initZero q * (initZero q)ᴴ + initOne q * (initOne q)ᴴ) := by
            rw [← discard_complete]
      _ = K * (initZero q * (initZero q)ᴴ) +
            K * (initOne q * (initOne q)ᴴ) := by
            rw [Matrix.mul_add]
      _ = (K * initZero q) * (initZero q)ᴴ +
            (K * initOne q) * (initOne q)ᴴ := by
            simp [Matrix.mul_assoc]
      _ = initZero q * V * (initZero q)ᴴ +
            initOne q * V * (initOne q)ᴴ := by
            rw [h0, h1]
  have hzero :
      (initZero q)ᴴ * (initZero q * V * (initZero q)ᴴ) = V * (initZero q)ᴴ := by
    calc
      (initZero q)ᴴ * (initZero q * V * (initZero q)ᴴ)
          = ((initZero q)ᴴ * initZero q) * (V * (initZero q)ᴴ) := by
            simp [Matrix.mul_assoc]
      _ = V * (initZero q)ᴴ := by
            simp [initZero_isometry, Matrix.mul_assoc]
  have hone :
      (initZero q)ᴴ * (initOne q * V * (initOne q)ᴴ) = 0 := by
    calc
      (initZero q)ᴴ * (initOne q * V * (initOne q)ᴴ)
          = ((initZero q)ᴴ * initOne q) * (V * (initOne q)ᴴ) := by
            simp [Matrix.mul_assoc]
      _ = 0 := by
            simp [initZero_conjTranspose_mul_initOne]
  calc
    (initZero q)ᴴ * K
        = (initZero q)ᴴ * (initZero q * V * (initZero q)ᴴ) +
            (initZero q)ᴴ * (initOne q * V * (initOne q)ᴴ) := by
          rw [hK, Matrix.mul_add]
    _ = V * (initZero q)ᴴ := by
          rw [hzero, hone, add_zero]

theorem initOne_conj_mul_subspace {q : ℕ}
    (K : KrausOperator (QDim (q + 1)) (QDim (q + 1)))
    (V : KrausOperator (QDim q) (QDim q))
    (h0 : K * initZero q = initZero q * V)
    (h1 : K * initOne q = initOne q * V) :
    (initOne q)ᴴ * K = V * (initOne q)ᴴ := by
  have hK :
      K = initZero q * V * (initZero q)ᴴ + initOne q * V * (initOne q)ᴴ := by
    calc
      K = K * 1 := (Matrix.mul_one K).symm
      _ = K * (initZero q * (initZero q)ᴴ + initOne q * (initOne q)ᴴ) := by
            rw [← discard_complete]
      _ = K * (initZero q * (initZero q)ᴴ) +
            K * (initOne q * (initOne q)ᴴ) := by
            rw [Matrix.mul_add]
      _ = (K * initZero q) * (initZero q)ᴴ +
            (K * initOne q) * (initOne q)ᴴ := by
            simp [Matrix.mul_assoc]
      _ = initZero q * V * (initZero q)ᴴ +
            initOne q * V * (initOne q)ᴴ := by
            rw [h0, h1]
  have hzero :
      (initOne q)ᴴ * (initZero q * V * (initZero q)ᴴ) = 0 := by
    calc
      (initOne q)ᴴ * (initZero q * V * (initZero q)ᴴ)
          = ((initOne q)ᴴ * initZero q) * (V * (initZero q)ᴴ) := by
            simp [Matrix.mul_assoc]
      _ = 0 := by
            simp [initOne_conjTranspose_mul_initZero]
  have hone :
      (initOne q)ᴴ * (initOne q * V * (initOne q)ᴴ) = V * (initOne q)ᴴ := by
    calc
      (initOne q)ᴴ * (initOne q * V * (initOne q)ᴴ)
          = ((initOne q)ᴴ * initOne q) * (V * (initOne q)ᴴ) := by
            simp [Matrix.mul_assoc]
      _ = V * (initOne q)ᴴ := by
            simp [initOne_isometry, Matrix.mul_assoc]
  calc
    (initOne q)ᴴ * K
        = (initOne q)ᴴ * (initZero q * V * (initZero q)ᴴ) +
            (initOne q)ᴴ * (initOne q * V * (initOne q)ᴴ) := by
          rw [hK, Matrix.mul_add]
    _ = V * (initOne q)ᴴ := by
          rw [hzero, hone, zero_add]

theorem subspace_conj_right_zero {q : ℕ}
    (K : KrausOperator (QDim (q + 1)) (QDim (q + 1)))
    (V : KrausOperator (QDim q) (QDim q))
    (h0 : K * initZero q = initZero q * V)
    (h1 : K * initOne q = initOne q * V) :
    Kᴴ * initZero q = initZero q * Vᴴ := by
  simpa [conjTranspose_mul] using
    congrArg conjTranspose (initZero_conj_mul_subspace K V h0 h1)

theorem subspace_conj_right_one {q : ℕ}
    (K : KrausOperator (QDim (q + 1)) (QDim (q + 1)))
    (V : KrausOperator (QDim q) (QDim q))
    (h0 : K * initZero q = initZero q * V)
    (h1 : K * initOne q = initOne q * V) :
    Kᴴ * initOne q = initOne q * Vᴴ := by
  simpa [conjTranspose_mul] using
    congrArg conjTranspose (initOne_conj_mul_subspace K V h0 h1)

/-- Discarding scratch commutes with an operator that acts as `V` on both
scratch subspaces. -/
theorem applyMat_discard_subspace {q : ℕ}
    (K : KrausOperator (QDim (q + 1)) (QDim (q + 1)))
    (V : KrausOperator (QDim q) (QDim q))
    (h0 : K * initZero q = initZero q * V)
    (h1 : K * initOne q = initOne q * V)
    (ρ : Matrix (Fin (QDim (q + 1))) (Fin (QDim (q + 1))) ℂ) :
    KrausFamily.applyMat (discardScratch q).kraus (K * ρ * Kᴴ) =
      V * KrausFamily.applyMat (discardScratch q).kraus ρ * Vᴴ := by
  have hL0 := initZero_conj_mul_subspace K V h0 h1
  have hR0 := subspace_conj_right_zero K V h0 h1
  have hL1 := initOne_conj_mul_subspace K V h0 h1
  have hR1 := subspace_conj_right_one K V h0 h1
  simp only [discardScratch_kraus, KrausFamily.applyMat_cons,
    KrausFamily.applyMat_single, KrausFamily.applyMat_nil, add_zero,
    conjTranspose_conjTranspose]
  have hterm0 :
      (initZero q)ᴴ * (K * ρ * Kᴴ) * initZero q =
        V * ((initZero q)ᴴ * ρ * initZero q) * Vᴴ := by
    calc
      (initZero q)ᴴ * (K * ρ * Kᴴ) * initZero q
          = ((initZero q)ᴴ * K) * ρ * (Kᴴ * initZero q) := by
            simp [Matrix.mul_assoc]
      _ = (V * (initZero q)ᴴ) * ρ * (initZero q * Vᴴ) := by
            rw [hL0, hR0]
      _ = V * ((initZero q)ᴴ * ρ * initZero q) * Vᴴ := by
            simp [Matrix.mul_assoc]
  have hterm1 :
      (initOne q)ᴴ * (K * ρ * Kᴴ) * initOne q =
        V * ((initOne q)ᴴ * ρ * initOne q) * Vᴴ := by
    calc
      (initOne q)ᴴ * (K * ρ * Kᴴ) * initOne q
          = ((initOne q)ᴴ * K) * ρ * (Kᴴ * initOne q) := by
            simp [Matrix.mul_assoc]
      _ = (V * (initOne q)ᴴ) * ρ * (initOne q * Vᴴ) := by
            rw [hL1, hR1]
      _ = V * ((initOne q)ᴴ * ρ * initOne q) * Vᴴ := by
            simp [Matrix.mul_assoc]
  rw [hterm0, hterm1]
  simp [Matrix.mul_add, Matrix.add_mul]

/-- A subspace-preserving isometry factors through scratch hiding. -/
theorem factorsScratch_ofIsometry_subspace {q c : ℕ}
    (U : KrausOperator (QDim (q + 1)) (QDim (q + 1)))
    (V : KrausOperator (QDim q) (QDim q))
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (h0 : U * initZero q = initZero q * V)
    (h1 : U * initOne q = initOne q * V) :
    FactorsScratch (fun s : CStore (c + 1) =>
      FiniteInstrumentComp.ofOperation
        (QuantumOperation.ofIsometry U hU) s) := by
  intro s P ρ
  have hhide :=
    hideScratch_ofIsometry_comm (q := q) (c := c) U V hU hV h0
  have hop :=
    FiniteInstrumentComp.wpKraus_ofOperation_semEq
      (QuantumOperation.ofIsometry U hU) s (hidePost (P ∘ hideStore)) ρ
  refine hop.trans ?_
  simp only [hidePost, Function.comp_apply, QuantumOperation.ofIsometry,
    KrausFamily.applyMat_comp, KrausFamily.applyMat_single]
  rw [applyMat_discard_subspace U V h0 h1]
  refine congrArg (KrausFamily.applyMat (initializeScratch q).kraus) ?_
  have hsandwich :
      (P (hideStore s)).applyMat
          (V * (discardScratch q).kraus.applyMat ρ * Vᴴ) =
        ((P (hideStore s)).comp
            (QuantumOperation.ofIsometry V hV).kraus).applyMat
          ((discardScratch q).kraus.applyMat ρ) := by
    simp [KrausFamily.applyMat_comp, QuantumOperation.ofIsometry,
      KrausFamily.applyMat_single]
  exact hsandwich.trans
    (((FiniteInstrumentComp.wpKraus_ofOperation_semEq
          (QuantumOperation.ofIsometry V hV) (hideStore s) P
          ((discardScratch q).kraus.applyMat ρ)).symm.trans
        (hhide (hideStore s) P ((discardScratch q).kraus.applyMat ρ)).symm))

theorem factorsScratch_onWire_data {q c : ℕ} (w : Fin q) (U : QubitMatrix)
    (hU : Uᴴ * U = 1) :
    FactorsScratch (fun s : CStore (c + 1) =>
      FiniteInstrumentComp.ofOperation
        (QuantumOperation.ofIsometry (onWire (dataWire w) U)
          (onWire_data_isometry w U hU)) s) :=
  factorsScratch_ofIsometry_subspace
    (onWire (dataWire w) U) (onWire w U)
    (onWire_data_isometry w U hU) (onWire_isometry w U hU)
    (onWire_data_mul_initZero w U) (onWire_data_mul_initOne w U)

theorem applyMat_discard_reset_data {q : ℕ} (w : Fin q)
    (ρ : Matrix (Fin (QDim (q + 1))) (Fin (QDim (q + 1))) ℂ) :
    KrausFamily.applyMat (discardScratch q).kraus
      (KrausFamily.applyMat (reset (dataWire w)).kraus ρ) =
      KrausFamily.applyMat (reset w).kraus
        (KrausFamily.applyMat (discardScratch q).kraus ρ) := by
  simp only [reset, resetKraus, KrausFamily.applyMat_cons,
    KrausFamily.applyMat_nil, add_zero]
  rw [KrausFamily.applyMat_add]
  rw [applyMat_discard_subspace _ _
      (onWire_data_mul_initZero w (reset₂ false))
      (onWire_data_mul_initOne w (reset₂ false))]
  rw [applyMat_discard_subspace _ _
      (onWire_data_mul_initZero w (reset₂ true))
      (onWire_data_mul_initOne w (reset₂ true))]

/-- A two-qubit operator on distinct data wires commutes with scratch-zero
embedding. -/
theorem onWires_data_mul_initZero {q : ℕ} (control target : Fin q)
    (hne : control ≠ target)
    (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    onWires (dataWire control) (dataWire target)
        (dataWire_injective_ne hne) U *
      initZero q =
      initZero q * onWires control target hne U := by
  ext i j
  simp only [Matrix.mul_apply]
  have hneW := dataWire_injective_ne hne
  have hL :
      (∑ k : Fin (QDim (q + 1)),
          onWires (dataWire control) (dataWire target) hneW U i k *
            initZero q k j) =
        onWires (dataWire control) (dataWire target) hneW U i
          (zeroIndex q j) := by
    trans onWires (dataWire control) (dataWire target) hneW U i
        (zeroIndex q j) * initZero q (zeroIndex q j) j
    · refine Fintype.sum_eq_single (zeroIndex q j) ?_
      intro k hk
      have hkne : k.val ≠ j.val := fun h => hk (Fin.ext h)
      simp [initZero, hkne]
    · simp [initZero]
  have hR :
      (∑ k : Fin (QDim q),
          initZero q i k * onWires control target hne U k j) =
        if h : i.val < QDim q then
          onWires control target hne U ⟨i.val, h⟩ j
        else 0 := by
    by_cases hi : i.val < QDim q
    · rw [dif_pos hi]
      trans initZero q i (⟨i.val, hi⟩ : Fin (QDim q)) *
          onWires control target hne U (⟨i.val, hi⟩ : Fin (QDim q)) j
      · refine Fintype.sum_eq_single (⟨i.val, hi⟩ : Fin (QDim q)) ?_
        intro k hk
        have hkne : i.val ≠ k.val := fun h => hk (Fin.ext h.symm)
        simp [initZero, hkne]
      · simp [initZero]
    · rw [dif_neg hi]
      apply Finset.sum_eq_zero
      intro k _
      have hkne : i.val ≠ k.val := by
        have := k.isLt
        omega
      simp [initZero, hkne]
  rw [hL, hR, onWires_apply]
  by_cases hi : i.val < QDim q
  · rw [dif_pos hi, onWires_apply]
    let r : Fin (QDim q) := ⟨i.val, hi⟩
    have hi_eq : i = zeroIndex q r := by
      apply Fin.ext
      simp [zeroIndex, r]
    have hothers :
        ((fun u : {v : Fin (q + 1) //
            v ≠ dataWire control ∧ v ≠ dataWire target} =>
            basisBits i u.1) =
          (fun u => basisBits (zeroIndex q j) u.1)) ↔
        ((fun u : {v : Fin q // v ≠ control ∧ v ≠ target} =>
            basisBits r u.1) =
          (fun u => basisBits j u.1)) := by
      constructor
      · intro h
        funext u
        have hu : dataWire u.1 ≠ dataWire control ∧
            dataWire u.1 ≠ dataWire target :=
          ⟨dataWire_injective_ne u.2.1, dataWire_injective_ne u.2.2⟩
        have hbit := congrFun h ⟨dataWire u.1, hu⟩
        simp only [basisBits, dataWire, Fin.val_castSucc] at hbit
        rw [hi_eq] at hbit
        simpa [basisBits, zeroIndex, dataWire] using hbit
      · intro h
        funext u
        by_cases hs : u.1 = scratchWire q
        · have hi0 : basisBits i (scratchWire q) = false :=
            basisBits_scratch_of_lt i hi
          have hj0 : basisBits (zeroIndex q j) (scratchWire q) = false :=
            basisBits_scratch_of_lt (zeroIndex q j) (by
              simpa [zeroIndex] using j.isLt)
          simp [hs, hi0, hj0]
        · have hvlt : u.1.val < q := by
            have := u.1.isLt
            have hval : u.1.val ≠ q := by
              intro hv
              apply hs
              exact Fin.ext (by simp [scratchWire, hv])
            omega
          let v : Fin q := ⟨u.1.val, hvlt⟩
          have hvne : v ≠ control ∧ v ≠ target := by
            constructor
            · intro hc
              apply u.2.1
              apply Fin.ext
              simpa [dataWire, v] using congrArg Fin.val hc
            · intro ht
              apply u.2.2
              apply Fin.ext
              simpa [dataWire, v] using congrArg Fin.val ht
          have hbit := congrFun h ⟨v, hvne⟩
          rw [hi_eq]
          simpa [basisBits, zeroIndex, dataWire, v] using hbit
    by_cases hphys :
        (fun u : {v : Fin (q + 1) //
            v ≠ dataWire control ∧ v ≠ dataWire target} =>
            basisBits i u.1) =
          (fun u => basisBits (zeroIndex q j) u.1)
    · have hlog := hothers.mp hphys
      rw [if_pos hphys, if_pos hlog]
      simp [basisBits, dataWire, zeroIndex, hi_eq, Fin.val_castSucc]
    · have hlog :
          ¬ ((fun u : {v : Fin q // v ≠ control ∧ v ≠ target} =>
                basisBits r u.1) =
              (fun u => basisBits j u.1)) :=
        fun h => hphys (hothers.mpr h)
      rw [if_neg hphys, if_neg hlog]
      simp
  · rw [dif_neg hi]
    have hscratch_i : basisBits i (scratchWire q) = true :=
      basisBits_scratch_of_ge i (Nat.le_of_not_gt hi)
    have hscratch_j : basisBits (zeroIndex q j) (scratchWire q) = false :=
      basisBits_scratch_of_lt (zeroIndex q j) (by
        simpa [zeroIndex] using j.isLt)
    have hneBits :
        (fun u : {v : Fin (q + 1) //
            v ≠ dataWire control ∧ v ≠ dataWire target} =>
            basisBits i u.1) ≠
          (fun u => basisBits (zeroIndex q j) u.1) := by
      intro h
      have hs : scratchWire q ≠ dataWire control ∧
          scratchWire q ≠ dataWire target :=
        ⟨(dataWire_ne_scratch control).symm, (dataWire_ne_scratch target).symm⟩
      have hbit := congrFun h ⟨scratchWire q, hs⟩
      simp only [basisBits, scratchWire] at hscratch_i hscratch_j hbit
      rw [hbit] at hscratch_i
      exact Bool.false_ne_true (hscratch_j.symm.trans hscratch_i)
    simp [hneBits]

/-- A two-qubit operator on distinct data wires preserves the scratch-one
subspace. -/
theorem onWires_data_mul_initOne {q : ℕ} (control target : Fin q)
    (hne : control ≠ target)
    (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    onWires (dataWire control) (dataWire target)
        (dataWire_injective_ne hne) U *
      initOne q =
      initOne q * onWires control target hne U := by
  ext i j
  simp only [Matrix.mul_apply]
  have hneW := dataWire_injective_ne hne
  have hL :
      (∑ k : Fin (QDim (q + 1)),
          onWires (dataWire control) (dataWire target) hneW U i k *
            initOne q k j) =
        onWires (dataWire control) (dataWire target) hneW U i
          (oneIndex q j) := by
    trans onWires (dataWire control) (dataWire target) hneW U i
        (oneIndex q j) * initOne q (oneIndex q j) j
    · refine Fintype.sum_eq_single (oneIndex q j) ?_
      intro k hk
      have hkne : k.val ≠ QDim q + j.val := fun h => hk (Fin.ext h)
      simp [initOne, hkne]
    · simp [initOne, oneIndex]
  have hR :
      (∑ k : Fin (QDim q),
          initOne q i k * onWires control target hne U k j) =
        if h : QDim q ≤ i.val then
          onWires control target hne U ⟨i.val - QDim q, highIndex_sub_lt h⟩ j
        else 0 := by
    by_cases hi : QDim q ≤ i.val
    · rw [dif_pos hi]
      let k0 : Fin (QDim q) := ⟨i.val - QDim q, highIndex_sub_lt hi⟩
      trans initOne q i k0 * onWires control target hne U k0 j
      · refine Fintype.sum_eq_single k0 ?_
        intro k hk
        have hkne : i.val ≠ QDim q + k.val := by
          intro h
          apply hk
          apply Fin.ext
          have hk0 : k0.val = i.val - QDim q := rfl
          omega
        simp [initOne, hkne]
      · simp [initOne, k0, Nat.add_sub_of_le hi]
    · rw [dif_neg hi]
      apply Finset.sum_eq_zero
      intro k _
      have hkne : i.val ≠ QDim q + k.val := by omega
      simp [initOne, hkne]
  rw [hL, hR, onWires_apply]
  by_cases hi : QDim q ≤ i.val
  · rw [dif_pos hi, onWires_apply]
    let r : Fin (QDim q) := ⟨i.val - QDim q, highIndex_sub_lt hi⟩
    have hi_eq : i = oneIndex q r := highIndex_eq_oneIndex hi
    have hothers :
        ((fun u : {v : Fin (q + 1) //
            v ≠ dataWire control ∧ v ≠ dataWire target} =>
            basisBits i u.1) =
          (fun u => basisBits (oneIndex q j) u.1)) ↔
        ((fun u : {v : Fin q // v ≠ control ∧ v ≠ target} =>
            basisBits r u.1) =
          (fun u => basisBits j u.1)) := by
      constructor
      · intro h
        funext u
        have hu : dataWire u.1 ≠ dataWire control ∧
            dataWire u.1 ≠ dataWire target :=
          ⟨dataWire_injective_ne u.2.1, dataWire_injective_ne u.2.2⟩
        have hbit := congrFun h ⟨dataWire u.1, hu⟩
        simp only [basisBits, dataWire, Fin.val_castSucc] at hbit
        rw [hi_eq] at hbit
        simp only [oneIndex, QDim] at hbit
        rw [testBit_add_two_pow u.1.isLt, testBit_add_two_pow u.1.isLt] at hbit
        simpa [basisBits] using hbit
      · intro h
        funext u
        by_cases hs : u.1 = scratchWire q
        · have hi1 : basisBits i (scratchWire q) = true :=
            basisBits_scratch_of_ge i hi
          have hj1 : basisBits (oneIndex q j) (scratchWire q) = true :=
            basisBits_scratch_of_ge (oneIndex q j) (by
              simpa [oneIndex] using Nat.le_add_right (QDim q) j.val)
          simp [hs, hi1, hj1]
        · have hvlt : u.1.val < q := by
            have := u.1.isLt
            have hval : u.1.val ≠ q := by
              intro hv
              apply hs
              exact Fin.ext (by simp [scratchWire, hv])
            omega
          let v : Fin q := ⟨u.1.val, hvlt⟩
          have hvne : v ≠ control ∧ v ≠ target := by
            constructor
            · intro hc
              apply u.2.1
              apply Fin.ext
              simpa [dataWire, v] using congrArg Fin.val hc
            · intro ht
              apply u.2.2
              apply Fin.ext
              simpa [dataWire, v] using congrArg Fin.val ht
          have hbit := congrFun h ⟨v, hvne⟩
          rw [hi_eq]
          simp only [basisBits, oneIndex, dataWire, QDim, v]
          rw [testBit_add_two_pow hvlt, testBit_add_two_pow hvlt]
          exact hbit
    by_cases hphys :
        (fun u : {v : Fin (q + 1) //
            v ≠ dataWire control ∧ v ≠ dataWire target} =>
            basisBits i u.1) =
          (fun u => basisBits (oneIndex q j) u.1)
    · have hlog := hothers.mp hphys
      rw [if_pos hphys, if_pos hlog]
      have hival : i.val = QDim q + r.val := by
        simpa [oneIndex] using congrArg Fin.val hi_eq
      simp only [basisBits, dataWire, oneIndex, Fin.val_castSucc, QDim]
      rw [hival, testBit_add_two_pow control.isLt,
        testBit_add_two_pow target.isLt,
        testBit_add_two_pow control.isLt,
        testBit_add_two_pow target.isLt, Nat.add_sub_of_le hi]
    · have hlog :
          ¬ ((fun u : {v : Fin q // v ≠ control ∧ v ≠ target} =>
                basisBits r u.1) =
              (fun u => basisBits j u.1)) :=
        fun h => hphys (hothers.mpr h)
      rw [if_neg hphys, if_neg hlog]
      simp
  · rw [dif_neg hi]
    have hscratch_i : basisBits i (scratchWire q) = false :=
      basisBits_scratch_of_lt i (Nat.lt_of_not_ge hi)
    have hscratch_j : basisBits (oneIndex q j) (scratchWire q) = true :=
      basisBits_scratch_of_ge (oneIndex q j) (by
        simpa [oneIndex] using Nat.le_add_right (QDim q) j.val)
    have hneBits :
        (fun u : {v : Fin (q + 1) //
            v ≠ dataWire control ∧ v ≠ dataWire target} =>
            basisBits i u.1) ≠
          (fun u => basisBits (oneIndex q j) u.1) := by
      intro h
      have hs : scratchWire q ≠ dataWire control ∧
          scratchWire q ≠ dataWire target :=
        ⟨(dataWire_ne_scratch control).symm, (dataWire_ne_scratch target).symm⟩
      have hbit := congrFun h ⟨scratchWire q, hs⟩
      simp only [basisBits, scratchWire] at hscratch_i hscratch_j hbit
      rw [hbit] at hscratch_i
      exact Bool.false_ne_true (hscratch_i.symm.trans hscratch_j)
    simp [hneBits]

theorem cxMatrix_data_mul_initZero {q : ℕ} (control target : Fin q) :
    cxMatrix (dataWire control) (dataWire target) * initZero q =
      initZero q * cxMatrix control target := by
  classical
  by_cases h : control = target
  · simp [cxMatrix, h]
  · have hneW := dataWire_injective_ne h
    simp only [cxMatrix, dif_neg h, dif_neg hneW]
    exact onWires_data_mul_initZero control target h cx₄

theorem cxMatrix_data_mul_initOne {q : ℕ} (control target : Fin q) :
    cxMatrix (dataWire control) (dataWire target) * initOne q =
      initOne q * cxMatrix control target := by
  classical
  by_cases h : control = target
  · simp [cxMatrix, h]
  · have hneW := dataWire_injective_ne h
    simp only [cxMatrix, dif_neg h, dif_neg hneW]
    exact onWires_data_mul_initOne control target h cx₄

theorem factorsScratch_cx {q c : ℕ} (control target : Fin q) :
    FactorsScratch (fun s : CStore (c + 1) =>
      FiniteInstrumentComp.ofOperation
        (QuantumOperation.ofIsometry
          (cxMatrix (dataWire control) (dataWire target))
          (cxMatrix_isometry (dataWire control) (dataWire target))) s) :=
  factorsScratch_ofIsometry_subspace
    (cxMatrix (dataWire control) (dataWire target))
    (cxMatrix control target)
    (cxMatrix_isometry _ _) (cxMatrix_isometry _ _)
    (cxMatrix_data_mul_initZero control target)
    (cxMatrix_data_mul_initOne control target)

theorem hideScratch_cx {q c : ℕ} (control target : Fin q) :
    CQ.Eq
      (hideScratch (fun s : CStore (c + 1) =>
        FiniteInstrumentComp.ofOperation
          (QuantumOperation.ofIsometry
            (cxMatrix (dataWire control) (dataWire target))
            (cxMatrix_isometry (dataWire control) (dataWire target))) s))
      (fun s : CStore c =>
        FiniteInstrumentComp.ofOperation
          (QuantumOperation.ofIsometry (cxMatrix control target)
            (cxMatrix_isometry control target)) s) :=
  hideScratch_ofIsometry_comm
    (cxMatrix (dataWire control) (dataWire target))
    (cxMatrix control target)
    (cxMatrix_isometry _ _) (cxMatrix_isometry _ _)
    (cxMatrix_data_mul_initZero control target)

theorem applyMat_discard_reset_embedded {q : ℕ} (w : Fin q)
    (ρ : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) :
    KrausFamily.applyMat (discardScratch q).kraus
        (KrausFamily.applyMat (reset (dataWire w)).kraus
          (initZero q * ρ * (initZero q)ᴴ)) =
      KrausFamily.applyMat (reset w).kraus ρ := by
  refine (applyMat_discard_reset_data w (initZero q * ρ * (initZero q)ᴴ)).trans ?_
  refine congrArg (KrausFamily.applyMat (reset w).kraus) ?_
  have hback := applyMat_discard_initialize q ρ
  rw [KrausFamily.applyMat_comp, initializeScratch_kraus,
    KrausFamily.applyMat_single] at hback
  exact hback

/-- Hidden observation of a data-wire reset is the logical reset. -/
theorem hideScratch_reset_data {q c : ℕ} (w : Fin q) :
    CQ.Eq
      (hideScratch (fun s : CStore (c + 1) =>
        FiniteInstrumentComp.ofOperation (reset (dataWire w)) s))
      (fun s : CStore c =>
        FiniteInstrumentComp.ofOperation (reset w) s) := by
  intro s P ρ
  have hunit :=
    FiniteInstrumentComp.wpKraus_ofOperation_semEq (reset w) s P ρ
  refine _root_.Eq.trans ?_ hunit.symm
  simp only [hideScratch, FiniteInstrumentComp.wpKraus_map]
  rw [hideComp_applyMat_wpKraus]
  rw [FiniteInstrumentComp.wpKraus_ofOperation_semEq]
  simp only [hidePost, Function.comp_apply, hideStore_initStore]
  rw [KrausFamily.applyMat_comp, KrausFamily.applyMat_comp,
    KrausFamily.applyMat_comp]
  have hcancel :=
    applyMat_discard_initialize q
      (KrausFamily.applyMat (P s)
        (KrausFamily.applyMat (discardScratch q).kraus
          (KrausFamily.applyMat (reset (dataWire w)).kraus
            (KrausFamily.applyMat (initializeScratch q).kraus ρ))))
  rw [KrausFamily.applyMat_comp] at hcancel
  rw [hcancel]
  rw [initializeScratch_kraus, KrausFamily.applyMat_single]
  rw [applyMat_discard_reset_embedded]
  rw [KrausFamily.applyMat_comp]

theorem factorsScratch_reset_data {q c : ℕ} (w : Fin q) :
    FactorsScratch (fun s : CStore (c + 1) =>
      FiniteInstrumentComp.ofOperation (reset (dataWire w)) s) := by
  intro s P ρ
  have hop :=
    FiniteInstrumentComp.wpKraus_ofOperation_semEq (reset (dataWire w)) s
      (hidePost (P ∘ hideStore)) ρ
  refine hop.trans ?_
  simp only [hidePost, Function.comp_apply, KrausFamily.applyMat_comp]
  rw [applyMat_discard_reset_data]
  refine congrArg (KrausFamily.applyMat (initializeScratch q).kraus) ?_
  have hlog :
      (P (hideStore s)).applyMat
          (KrausFamily.applyMat (reset w).kraus
            (KrausFamily.applyMat (discardScratch q).kraus ρ)) =
        ((FiniteInstrumentComp.ofOperation (reset w) (hideStore s)).wpKraus
            P).applyMat
          (KrausFamily.applyMat (discardScratch q).kraus ρ) := by
    simpa [KrausFamily.applyMat_comp] using
      (FiniteInstrumentComp.wpKraus_ofOperation_semEq (reset w) (hideStore s) P
        (KrausFamily.applyMat (discardScratch q).kraus ρ)).symm
  exact hlog.trans
    (hideScratch_reset_data w (hideStore s) P
      (KrausFamily.applyMat (discardScratch q).kraus ρ)).symm

theorem applyMat_discard_projector_data {q : ℕ} (w : Fin q) (b : Bool)
    (ρ : Matrix (Fin (QDim (q + 1))) (Fin (QDim (q + 1))) ℂ) :
    KrausFamily.applyMat (discardScratch q).kraus
        (KrausFamily.applyMat [projector (dataWire w) b] ρ) =
      KrausFamily.applyMat [projector w b]
        (KrausFamily.applyMat (discardScratch q).kraus ρ) := by
  simp only [projector, KrausFamily.applyMat_single]
  exact applyMat_discard_subspace _ _
    (onWire_data_mul_initZero w (proj₂ b))
    (onWire_data_mul_initOne w (proj₂ b)) ρ

/-- False-branch projector extracts the scratch-zero amplitude `√p`. -/
theorem projector_false_coin {q : ℕ} (p : Probability)
    (ρ : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) :
    let amp0 := (Real.sqrt p.real : ℂ)
    let amp1 := (Real.sqrt (1 - p.real) : ℂ)
    let super := amp0 • initZero q + amp1 • initOne q
    projector (scratchWire q) false * (super * ρ * superᴴ) *
        (projector (scratchWire q) false)ᴴ =
      (p.real : ℂ) • (initZero q * ρ * (initZero q)ᴴ) := by
  intro amp0 amp1 super
  have hP := projector_scratch_false q
  have hself : (projector (scratchWire q) false)ᴴ =
      projector (scratchWire q) false := projector_conjTranspose _ _
  rw [hself, hP]
  have hE0 : (initZero q)ᴴ * super = amp0 • (1 : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) := by
    simp only [super, Matrix.mul_add, Matrix.mul_smul, initZero_isometry,
      initZero_conjTranspose_mul_initOne, smul_zero, add_zero]
  have hE1 : superᴴ * initZero q = star amp0 • (1 : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) := by
    have h := congrArg conjTranspose hE0
    simpa [conjTranspose_mul, conjTranspose_smul, conjTranspose_one, super] using h
  have hscale : amp0 * star amp0 = (p.real : ℂ) := by
    simp only [amp0, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    norm_cast
    simpa [pow_two] using Real.sq_sqrt p.real_nonneg
  have hsandwich :
      (initZero q * (initZero q)ᴴ) * (super * ρ * superᴴ) *
          (initZero q * (initZero q)ᴴ) =
        initZero q * (((initZero q)ᴴ * super) * ρ * (superᴴ * initZero q)) *
          (initZero q)ᴴ := by
    simp [Matrix.mul_assoc]
  rw [hsandwich, hE0, hE1]
  simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one,
    smul_smul, mul_comm]
  have hcoeff : amp0 * starRingEnd ℂ amp0 = (p.real : ℂ) := by
    simpa [Complex.star_def] using hscale
  rw [hcoeff]
  rw [← algebraMap_smul ℂ p.real]
  simp

/-- True-branch projector extracts the scratch-one amplitude `√(1-p)`. -/
theorem projector_true_coin {q : ℕ} (p : Probability)
    (ρ : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) :
    let amp0 := (Real.sqrt p.real : ℂ)
    let amp1 := (Real.sqrt (1 - p.real) : ℂ)
    let super := amp0 • initZero q + amp1 • initOne q
    projector (scratchWire q) true * (super * ρ * superᴴ) *
        (projector (scratchWire q) true)ᴴ =
      ((1 - p.real : ℝ) : ℂ) • (initOne q * ρ * (initOne q)ᴴ) := by
  intro amp0 amp1 super
  have hP := projector_scratch_true q
  have hself : (projector (scratchWire q) true)ᴴ =
      projector (scratchWire q) true := projector_conjTranspose _ _
  rw [hself, hP]
  have hF0 : (initOne q)ᴴ * super = amp1 • (1 : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) := by
    simp only [super, Matrix.mul_add, Matrix.mul_smul, initOne_isometry,
      initOne_conjTranspose_mul_initZero, smul_zero, zero_add]
  have hF1 : superᴴ * initOne q = star amp1 • (1 : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) := by
    have h := congrArg conjTranspose hF0
    simpa [conjTranspose_mul, conjTranspose_smul, conjTranspose_one, super] using h
  have hscale : amp1 * star amp1 = ((1 - p.real : ℝ) : ℂ) := by
    have hp' : 0 ≤ 1 - p.real := sub_nonneg.mpr p.real_le_one
    simp only [amp1, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    norm_cast
    simpa [pow_two] using Real.sq_sqrt hp'
  have hsandwich :
      (initOne q * (initOne q)ᴴ) * (super * ρ * superᴴ) *
          (initOne q * (initOne q)ᴴ) =
        initOne q * (((initOne q)ᴴ * super) * ρ * (superᴴ * initOne q)) *
          (initOne q)ᴴ := by
    simp [Matrix.mul_assoc]
  rw [hsandwich, hF0, hF1]
  simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one,
    smul_smul, mul_comm]
  have hcoeff : amp1 * starRingEnd ℂ amp1 = ((1 - p.real : ℝ) : ℂ) := by
    simpa [Complex.star_def] using hscale
  rw [hcoeff, Complex.ofReal_sub, Complex.ofReal_one]

theorem discard_projector_false_coin {q : ℕ} (p : Probability)
    (ρ : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) :
    let amp0 := (Real.sqrt p.real : ℂ)
    let amp1 := (Real.sqrt (1 - p.real) : ℂ)
    let super := amp0 • initZero q + amp1 • initOne q
    KrausFamily.applyMat (discardScratch q).kraus
        (projector (scratchWire q) false * (super * ρ * superᴴ) *
          (projector (scratchWire q) false)ᴴ) =
      (p.real : ℂ) • ρ := by
  intro amp0 amp1 super
  rw [projector_false_coin, KrausFamily.applyMat_smul]
  have hdisc := applyMat_discard_initialize q ρ
  rw [KrausFamily.applyMat_comp, initializeScratch_kraus,
    KrausFamily.applyMat_single] at hdisc
  rw [hdisc]

theorem discard_projector_true_coin {q : ℕ} (p : Probability)
    (ρ : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) :
    let amp0 := (Real.sqrt p.real : ℂ)
    let amp1 := (Real.sqrt (1 - p.real) : ℂ)
    let super := amp0 • initZero q + amp1 • initOne q
    KrausFamily.applyMat (discardScratch q).kraus
        (projector (scratchWire q) true * (super * ρ * superᴴ) *
          (projector (scratchWire q) true)ᴴ) =
      ((1 - p.real : ℝ) : ℂ) • ρ := by
  intro amp0 amp1 super
  rw [projector_true_coin, KrausFamily.applyMat_smul]
  have hdisc :
      KrausFamily.applyMat (discardScratch q).kraus
          (initOne q * ρ * (initOne q)ᴴ) = ρ := by
    simp only [discardScratch_kraus, KrausFamily.applyMat_cons,
      KrausFamily.applyMat_single, KrausFamily.applyMat_nil, add_zero,
      conjTranspose_conjTranspose]
    have h0 :
        (initZero q)ᴴ * (initOne q * ρ * (initOne q)ᴴ) * initZero q = 0 := by
      calc
        (initZero q)ᴴ * (initOne q * ρ * (initOne q)ᴴ) * initZero q
            = ((initZero q)ᴴ * initOne q) * (ρ * ((initOne q)ᴴ * initZero q)) := by
              simp [Matrix.mul_assoc]
        _ = 0 := by
              simp [initZero_conjTranspose_mul_initOne,
                initOne_conjTranspose_mul_initZero]
    have h1 :
        (initOne q)ᴴ * (initOne q * ρ * (initOne q)ᴴ) * initOne q = ρ := by
      calc
        (initOne q)ᴴ * (initOne q * ρ * (initOne q)ᴴ) * initOne q
            = ((initOne q)ᴴ * initOne q) * ρ * ((initOne q)ᴴ * initOne q) := by
              simp [Matrix.mul_assoc]
        _ = ρ := by
              simp [initOne_isometry]
    rw [h0, h1, zero_add]
  rw [hdisc]

theorem applyMat_discard_projector_embedded {q : ℕ} (w : Fin q) (b : Bool)
    (ρ : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) :
    KrausFamily.applyMat (discardScratch q).kraus
        (KrausFamily.applyMat [projector (dataWire w) b]
          (initZero q * ρ * (initZero q)ᴴ)) =
      KrausFamily.applyMat [projector w b] ρ := by
  refine (applyMat_discard_projector_data w b
      (initZero q * ρ * (initZero q)ᴴ)).trans ?_
  refine congrArg (KrausFamily.applyMat [projector w b]) ?_
  have hback := applyMat_discard_initialize q ρ
  rw [KrausFamily.applyMat_comp, initializeScratch_kraus,
    KrausFamily.applyMat_single] at hback
  exact hback

end QLambda.Compiler



