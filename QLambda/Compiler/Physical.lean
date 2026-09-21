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

end QLambda.Compiler



