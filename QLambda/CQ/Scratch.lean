/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.CQ.Domain

/-!
# Reserved scratch resources

The physical compiler reserves the final qubit and classical bit. This module
defines the corresponding register isometry, discard channel, store maps, and
the logical observation of a physical CQ computation.
-/

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace QLambda.CQ

/-- Include a logical wire among the data wires of the physical register. -/
def dataWire {q : ℕ} (i : Fin q) : Fin (q + 1) :=
  i.castSucc

/-- The final physical wire reserved by the compiler. -/
def scratchWire (q : ℕ) : Fin (q + 1) :=
  Fin.last q

/-- Include a logical bit among the data bits of the physical store. -/
def dataBit {c : ℕ} (i : Fin c) : Fin (c + 1) :=
  i.castSucc

/-- The final physical classical bit reserved by the compiler. -/
def scratchBit (c : ℕ) : Fin (c + 1) :=
  Fin.last c

theorem dataWire_ne_scratch {q : ℕ} (i : Fin q) :
    dataWire i ≠ scratchWire q := by
  simp [dataWire, scratchWire]

theorem dataBit_ne_scratch {c : ℕ} (i : Fin c) :
    dataBit i ≠ scratchBit c := by
  simp [dataBit, scratchBit]

/-- Initialize the reserved classical bit to false. -/
def initStore {c : ℕ} (s : CStore c) : CStore (c + 1) :=
  fun i =>
    if h : i.val < c then s ⟨i.val, h⟩ else false

/-- Forget the reserved classical bit. -/
def hideStore {c : ℕ} (s : CStore (c + 1)) : CStore c :=
  fun i => s i.castSucc

@[simp] theorem hideStore_initStore {c : ℕ} (s : CStore c) :
    hideStore (initStore s) = s := by
  funext i
  simp [hideStore, initStore]

theorem hideStore_update_data_any {c : ℕ} (s : CStore (c + 1))
    (i : Fin c) (b : Bool) :
    hideStore (Function.update s (dataBit i) b) =
      Function.update (hideStore s) i b := by
  funext j
  change Function.update s (dataBit i) b j.castSucc =
    Function.update (hideStore s) i b j
  by_cases hij : j.castSucc = dataBit i
  · have hj : j = i := Fin.castSucc_injective c (by
      simpa [dataBit] using hij)
    rw [Function.update_apply, if_pos hij, Function.update_apply, if_pos hj]
  · have hj : j ≠ i := fun h => hij (by simp [dataBit, h])
    rw [Function.update_apply, if_neg hij, Function.update_apply, if_neg hj]
    rfl

theorem hideStore_update_scratch {c : ℕ} (s : CStore (c + 1)) (b : Bool) :
    hideStore (Function.update s (scratchBit c) b) = hideStore s := by
  funext i
  have hne : (i.castSucc : Fin (c + 1)) ≠ scratchBit c := by
    simp [scratchBit]
  simp [hideStore, Function.update, hne]

theorem hideStore_update_init_scratch {c : ℕ} (s : CStore c) (b : Bool) :
    hideStore (Function.update (initStore s) (scratchBit c) b) = s := by
  rw [hideStore_update_scratch, hideStore_initStore]

theorem hideStore_update_data {c : ℕ} (s : CStore c) (i : Fin c) (b : Bool) :
    hideStore (Function.update (initStore s) (dataBit i) b) =
      Function.update s i b := by
  funext j
  change Function.update (initStore s) (dataBit i) b j.castSucc =
    Function.update s i b j
  by_cases hij : j.castSucc = dataBit i
  · have hj : j = i := Fin.castSucc_injective c (by
      simpa [dataBit] using hij)
    rw [Function.update_apply, if_pos hij, Function.update_apply, if_pos hj]
  · have hj : j ≠ i := fun h => hij (by simp [dataBit, h])
    rw [Function.update_apply, if_neg hij, Function.update_apply, if_neg hj]
    simp [initStore, j.isLt]

theorem initStore_update_data {c : ℕ} (s : CStore c) (i : Fin c) (b : Bool) :
    initStore (Function.update s i b) =
      Function.update (initStore s) (dataBit i) b := by
  funext k
  by_cases hk : k.val < c
  · rw [show initStore (Function.update s i b) k =
          Function.update s i b ⟨k.val, hk⟩ by simp [initStore, hk]]
    by_cases hi : (⟨k.val, hk⟩ : Fin c) = i
    · have hk' : k = dataBit i := by
        apply Fin.ext
        simpa [dataBit] using congrArg Fin.val hi
      rw [Function.update_apply, if_pos hi, Function.update_apply, if_pos hk']
    · have hk' : k ≠ dataBit i := by
        intro h
        apply hi
        apply Fin.ext
        simpa [dataBit] using congrArg Fin.val h
      rw [Function.update_apply, if_neg hi, Function.update_apply, if_neg hk']
      simp [initStore, hk]
  · have hne : k ≠ dataBit i := by
      intro h
      subst h
      exact hk i.isLt
    rw [Function.update_apply, if_neg hne]
    simp [initStore, hk]

theorem logical_lt_physical (q : ℕ) : QDim q < QDim (q + 1) := by
  simp only [QDim, pow_succ]
  have hp : 0 < 2 ^ q := pow_pos (by decide) q
  omega

/-- Basis inclusion `|i⟩ ↦ |0⟩_scratch ⊗ |i⟩_data`.

The first half of the chosen finite basis represents scratch zero. -/
def initZero (q : ℕ) : KrausOperator (QDim q) (QDim (q + 1)) :=
  fun i j => if i.val = j.val then 1 else 0

/-- Basis inclusion into the scratch-one half of the physical register. -/
def initOne (q : ℕ) : KrausOperator (QDim q) (QDim (q + 1)) :=
  fun i j => if i.val = QDim q + j.val then 1 else 0

/-- Embedding of a logical basis vector into the scratch-zero half. -/
def zeroIndex (q : ℕ) (i : Fin (QDim q)) : Fin (QDim (q + 1)) :=
  ⟨i.val, i.isLt.trans (logical_lt_physical q)⟩

/-- Embedding of a logical basis vector into the scratch-one half. -/
def oneIndex (q : ℕ) (i : Fin (QDim q)) : Fin (QDim (q + 1)) :=
  ⟨QDim q + i.val, by
    simp only [QDim, pow_succ] at i ⊢
    omega⟩

theorem initZero_apply (q : ℕ) (i : Fin (QDim (q + 1))) (j : Fin (QDim q)) :
    initZero q i j = if i.val = j.val then 1 else 0 :=
  rfl

theorem initOne_apply (q : ℕ) (i : Fin (QDim (q + 1))) (j : Fin (QDim q)) :
    initOne q i j = if i.val = QDim q + j.val then 1 else 0 :=
  rfl

@[simp] theorem zeroIndex_val (q : ℕ) (i : Fin (QDim q)) :
    (zeroIndex q i).val = i.val :=
  rfl

@[simp] theorem oneIndex_val (q : ℕ) (i : Fin (QDim q)) :
    (oneIndex q i).val = QDim q + i.val :=
  rfl

/-- Initialization is an isometry. -/
theorem initZero_isometry (q : ℕ) :
    (initZero q)ᴴ * initZero q = 1 := by
  ext i j
  simp only [Matrix.mul_apply, conjTranspose_apply, initZero, one_apply]
  by_cases hij : i = j
  · subst j
    rw [Finset.sum_eq_single (zeroIndex q i)]
    · simp [zeroIndex]
    · intro b _ hbi
      have hne : b.val ≠ i.val := by
        intro h
        apply hbi
        apply Fin.ext
        exact h
      simp [hne]
    · simp
  · have hv : i.val ≠ j.val := by
      intro h
      exact hij (Fin.ext h)
    rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hbi : b.val = i.val
    · have hbj : b.val ≠ j.val := by omega
      simp [hbi, hbj, hv]
    · simp [hbi]

theorem initZero_projector_apply (q : ℕ)
    (i j : Fin (QDim (q + 1))) :
    (initZero q * (initZero q)ᴴ) i j =
      if i = j ∧ i.val < QDim q then 1 else 0 := by
  classical
  simp only [Matrix.mul_apply, conjTranspose_apply]
  by_cases hi : i.val < QDim q
  · rw [Finset.sum_eq_single ⟨i.val, hi⟩]
    · simp only [initZero, if_pos rfl, one_mul]
      simp [hi, Fin.ext_iff, eq_comm]
    · intro b _ hbi
      have hne : i.val ≠ b.val := by
        intro h
        apply hbi
        apply Fin.ext
        exact h.symm
      simp [initZero, hne]
    · simp
  · have hne (b : Fin (QDim q)) : i.val ≠ b.val := by omega
    simp [initZero, hi, hne]

theorem initOne_projector_apply (q : ℕ)
    (i j : Fin (QDim (q + 1))) :
    (initOne q * (initOne q)ᴴ) i j =
      if i = j ∧ QDim q ≤ i.val then 1 else 0 := by
  classical
  by_cases hi : QDim q ≤ i.val
  · have hibound : i.val - QDim q < QDim q := by
      have hdim : QDim (q + 1) = QDim q * 2 := by
        simp [QDim, pow_succ]
      have hphys : i.val < QDim q * 2 :=
        i.isLt.trans_le hdim.le
      omega
    simp only [Matrix.mul_apply, conjTranspose_apply]
    rw [Finset.sum_eq_single ⟨i.val - QDim q, hibound⟩]
    · simp only [initOne, Nat.add_sub_of_le hi, if_pos rfl, one_mul]
      simp [hi, Fin.ext_iff, eq_comm]
    · intro b _ hbi
      have hne : i.val ≠ QDim q + b.val := by
        intro h
        apply hbi
        apply Fin.ext
        simp [h]
      simp [initOne, hne]
    · simp
  · have hne (b : Fin (QDim q)) : i.val ≠ QDim q + b.val := by omega
    simp [Matrix.mul_apply, conjTranspose_apply, initOne, hi, hne]

/-- The two extraction maps are complete: discarding the scratch qubit is
trace preserving. -/
theorem discard_complete (q : ℕ) :
    initZero q * (initZero q)ᴴ + initOne q * (initOne q)ᴴ = 1 := by
  ext i j
  rw [Matrix.add_apply, initZero_projector_apply, initOne_projector_apply]
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val < QDim q
    · simp [hi]
    · simp [hi, Nat.le_of_not_gt hi]
  · simp [hij]

/-- Physical initialization operation for the reserved qubit. -/
def initializeScratch (q : ℕ) :
    QuantumOperation (QDim q) (QDim (q + 1)) :=
  QuantumOperation.ofIsometry (initZero q) (initZero_isometry q)

/-- Trace-preserving discard of the reserved qubit. -/
def discardScratch (q : ℕ) :
    QuantumOperation (QDim (q + 1)) (QDim q) where
  kraus := [(initZero q)ᴴ, (initOne q)ᴴ]
  trace_nonincreasing := by
    intro ρ _
    simp only [KrausFamily.applyMat, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    have htrace :
        Matrix.trace
            ((initZero q)ᴴ * ρ * (initZero q)ᴴᴴ +
              (initOne q)ᴴ * ρ * (initOne q)ᴴᴴ) =
          Matrix.trace ρ := by
      rw [Matrix.trace_add,
        Matrix.trace_mul_comm ((initZero q)ᴴ * ρ) (initZero q)ᴴᴴ,
        Matrix.trace_mul_comm ((initOne q)ᴴ * ρ) (initOne q)ᴴᴴ]
      simp only [conjTranspose_conjTranspose]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.trace_add,
        ← Matrix.add_mul, discard_complete, Matrix.one_mul]
    rw [htrace]

/-- Initialize and then discard scratch around a physical computation. -/
def hideComp {q : ℕ} {D : Type*} (μ : FiniteInstrumentComp (QDim (q + 1)) D) :
    FiniteInstrumentComp (QDim q) D where
  Outcome := μ.Outcome
  outcomeFintype := μ.outcomeFintype
  branch := fun o =>
    KrausFamily.comp (discardScratch q).kraus
      (KrausFamily.comp (μ.branch o) (initializeScratch q).kraus)
  value := μ.value
  trace_nonincreasing := by
    intro ρ hρ
    let ρi : Matrix (Fin (QDim (q + 1))) (Fin (QDim (q + 1))) ℂ :=
      KrausFamily.applyMat (initializeScratch q).kraus ρ
    have hρi : ρi.PosSemidef :=
      KrausFamily.applyMat_posSemidef (initializeScratch q).kraus hρ
    have hdiscard :
        (∑ o : μ.Outcome,
            (Matrix.trace
              (KrausFamily.applyMat
                (KrausFamily.comp (discardScratch q).kraus
                  (KrausFamily.comp (μ.branch o) (initializeScratch q).kraus))
                ρ)).re) ≤
          ∑ o : μ.Outcome,
            (Matrix.trace (KrausFamily.applyMat (μ.branch o) ρi)).re := by
      apply Finset.sum_le_sum
      intro o _
      rw [KrausFamily.applyMat_comp, KrausFamily.applyMat_comp]
      exact (discardScratch q).trace_nonincreasing
        _ (KrausFamily.applyMat_posSemidef _ hρi)
    exact hdiscard.trans
      ((μ.trace_nonincreasing ρi hρi).trans
        ((initializeScratch q).trace_nonincreasing ρ hρ))

/-- Logical observation of a physical CQ meaning: initialize both reserved
resources, execute, then discard/project them. -/
def hideScratch {q c : ℕ} (F : Sem (q + 1) (c + 1)) : Sem q c :=
  fun s => FiniteInstrumentComp.map hideStore (hideComp (F (initStore s)))

theorem initOne_conjTranspose_mul_initZero (q : ℕ) :
    (initOne q)ᴴ * initZero q = 0 := by
  ext i j
  simp only [Matrix.mul_apply, conjTranspose_apply, initOne, initZero,
    Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk0 : k.val = j.val
  · have hk1 : j.val ≠ QDim q + i.val := by
      have := j.isLt
      omega
    simp [hk0, hk1]
  · simp [hk0]

@[simp] theorem initializeScratch_kraus (q : ℕ) :
    (initializeScratch q).kraus = [initZero q] :=
  rfl

@[simp] theorem discardScratch_kraus (q : ℕ) :
    (discardScratch q).kraus = [(initZero q)ᴴ, (initOne q)ᴴ] :=
  rfl

theorem applyMat_discard_initialize (q : ℕ)
    (ρ : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) :
    KrausFamily.applyMat
      (KrausFamily.comp (discardScratch q).kraus (initializeScratch q).kraus) ρ =
      ρ := by
  rw [KrausFamily.applyMat_comp, initializeScratch_kraus,
    KrausFamily.applyMat_single, discardScratch_kraus,
    KrausFamily.applyMat_cons, KrausFamily.applyMat_single]
  have h0 :
      (initZero q)ᴴ * (initZero q * ρ * (initZero q)ᴴ) * ((initZero q)ᴴ)ᴴ =
        ρ := by
    simp only [conjTranspose_conjTranspose]
    calc
      (initZero q)ᴴ * (initZero q * ρ * (initZero q)ᴴ) * initZero q
          = ((initZero q)ᴴ * initZero q) * ρ *
              ((initZero q)ᴴ * initZero q) := by
            simp [Matrix.mul_assoc]
      _ = ρ := by
            simp [initZero_isometry]
  have h1 :
      (initOne q)ᴴ * (initZero q * ρ * (initZero q)ᴴ) * ((initOne q)ᴴ)ᴴ =
        0 := by
    simp only [conjTranspose_conjTranspose]
    have horth := initOne_conjTranspose_mul_initZero q
    calc
      (initOne q)ᴴ * (initZero q * ρ * (initZero q)ᴴ) * initOne q
          = ((initOne q)ᴴ * initZero q) * ρ *
              ((initZero q)ᴴ * initOne q) := by
            simp [Matrix.mul_assoc]
      _ = 0 := by
            rw [horth]
            simp
  rw [h0, h1, add_zero]

/-- Physical postcondition that discards scratch, applies a logical
postcondition, then re-embeds. -/
def hidePost {q : ℕ} {D : Type*} (P : D → KrausFamily (QDim q) (QDim q)) :
    D → KrausFamily (QDim (q + 1)) (QDim (q + 1)) :=
  fun d =>
    KrausFamily.comp (initializeScratch q).kraus
      (KrausFamily.comp (P d) (discardScratch q).kraus)

theorem applyMat_zero {n m : ℕ} (K : KrausFamily n m) :
    KrausFamily.applyMat K (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  have hz : (0 : Matrix (Fin n) (Fin n) ℂ) = (0 : ℂ) • 0 :=
    (zero_smul ℂ (0 : Matrix (Fin n) (Fin n) ℂ)).symm
  rw [hz, KrausFamily.applyMat_smul, zero_smul]

theorem applyMat_sum {n m : ℕ} {ι : Type*} [Fintype ι]
    (K : KrausFamily n m) (f : ι → Matrix (Fin n) (Fin n) ℂ) :
    KrausFamily.applyMat K (∑ i, f i) = ∑ i, KrausFamily.applyMat K (f i) := by
  classical
  have h : ∀ s : Finset ι,
      KrausFamily.applyMat K (∑ i ∈ s, f i) =
        ∑ i ∈ s, KrausFamily.applyMat K (f i) := by
    intro s
    induction s using Finset.induction with
    | empty => simp [applyMat_zero]
    | insert a s ha ih =>
        simp [Finset.sum_insert ha, KrausFamily.applyMat_add, ih]
  exact h Finset.univ

theorem hideComp_applyMat_wpKraus {q : ℕ} {D : Type*} [Preorder D]
    (μ : FiniteInstrumentComp (QDim (q + 1)) D)
    (P : D → KrausFamily (QDim q) (QDim q))
    (ρ : Matrix (Fin (QDim q)) (Fin (QDim q)) ℂ) :
    KrausFamily.applyMat ((hideComp μ).wpKraus P) ρ =
      KrausFamily.applyMat (discardScratch q).kraus
        (KrausFamily.applyMat (μ.wpKraus (hidePost P))
          (KrausFamily.applyMat (initializeScratch q).kraus ρ)) := by
  rw [FiniteInstrumentComp.applyMat_wpKraus,
    FiniteInstrumentComp.applyMat_wpKraus, applyMat_sum]
  refine Finset.sum_congr rfl ?_
  intro o _
  let o' : μ.Outcome := o
  change
    KrausFamily.applyMat
      (KrausFamily.comp (P (μ.value o'))
        (KrausFamily.comp (discardScratch q).kraus
          (KrausFamily.comp (μ.branch o') (initializeScratch q).kraus))) ρ =
      KrausFamily.applyMat (discardScratch q).kraus
        (KrausFamily.applyMat
          (KrausFamily.comp (hidePost P (μ.value o')) (μ.branch o'))
          (KrausFamily.applyMat (initializeScratch q).kraus ρ))
  simp only [hidePost, KrausFamily.applyMat_comp]
  conv_rhs => rw [← KrausFamily.applyMat_comp]
  rw [applyMat_discard_initialize]

theorem hideComp_congr {q : ℕ} {D : Type*} [Preorder D]
    {μ ν : FiniteInstrumentComp (QDim (q + 1)) D} (h : CompEq μ ν) :
    CompEq (hideComp μ) (hideComp ν) := by
  intro P ρ
  rw [hideComp_applyMat_wpKraus, hideComp_applyMat_wpKraus]
  exact congrArg (KrausFamily.applyMat (discardScratch q).kraus)
    (h (hidePost P) _)

theorem hideScratch_congr {q c : ℕ} {F G : Sem (q + 1) (c + 1)}
    (h : Eq F G) : Eq (hideScratch F) (hideScratch G) := by
  intro s
  exact CompEq.map hideStore (hideComp_congr (h (initStore s)))

theorem hideScratch_skip {q c : ℕ} :
    Eq (hideScratch (skip : Sem (q + 1) (c + 1))) skip := by
  intro s P ρ
  change
    KrausFamily.applyMat
      ((hideComp (FiniteInstrumentComp.unit (initStore s))).wpKraus
        (P ∘ hideStore)) ρ =
    KrausFamily.applyMat ((FiniteInstrumentComp.unit s).wpKraus P) ρ
  rw [FiniteInstrumentComp.applyMat_wpKraus]
  have hunit :=
    FiniteInstrumentComp.wpKraus_unit_semEq (n := QDim q) s P ρ
  refine _root_.Eq.trans ?_ hunit.symm
  change
    (∑ _ : Unit,
      KrausFamily.applyMat
        (KrausFamily.comp ((P ∘ hideStore) (initStore s))
          (KrausFamily.comp (discardScratch q).kraus
            (KrausFamily.comp
              (KrausFamily.identity (QDim (q + 1)))
              (initializeScratch q).kraus))) ρ) =
      KrausFamily.applyMat (P s) ρ
  simp only [Function.comp_apply, hideStore_initStore, Fintype.sum_unique,
    KrausFamily.applyMat_comp, KrausFamily.applyMat_identity]
  congr 1
  rw [← KrausFamily.applyMat_comp, applyMat_discard_initialize]

theorem hideScratch_select {q c : ℕ}
    (g : CStore (c + 1) → Bool) (F G : Sem (q + 1) (c + 1))
    (g' : CStore c → Bool) (hg : ∀ s, g (initStore s) = g' s) :
    hideScratch (select g F G) =
      select g' (hideScratch F) (hideScratch G) := by
  funext s
  simp only [hideScratch, select, hg]
  split_ifs <;> rfl

theorem hideComp_map {q : ℕ} {D E : Type*} (f : D → E)
    (μ : FiniteInstrumentComp (QDim (q + 1)) D) :
    hideComp (μ.map f) = (hideComp μ).map f :=
  rfl

/-- A physical computation whose hidden observation does not depend on the
incoming scratch qubit or reserved bit. -/
def ScratchInsensitive {q c : ℕ} (G : Sem (q + 1) (c + 1)) : Prop :=
  ∀ (s : CStore (c + 1)) (P : CStore c → KrausFamily (QDim q) (QDim q))
    (ρ : Matrix (Fin (QDim (q + 1))) (Fin (QDim (q + 1))) ℂ),
    KrausFamily.applyMat (discardScratch q).kraus
      (KrausFamily.applyMat
        ((G s).wpKraus (hidePost (P ∘ hideStore))) ρ) =
      KrausFamily.applyMat
        ((hideScratch G (hideStore s)).wpKraus P)
        (KrausFamily.applyMat (discardScratch q).kraus ρ)

theorem hideScratch_seq_skip {q c : ℕ} (G : Sem (q + 1) (c + 1)) :
    Eq (hideScratch (seq (skip : Sem (q + 1) (c + 1)) G))
      (seq (hideScratch (skip : Sem (q + 1) (c + 1))) (hideScratch G)) := by
  refine Eq.trans (hideScratch_congr (skip_seq G)) ?_
  exact Eq.trans (Eq.symm (skip_seq (hideScratch G)))
    (seq_congr (Eq.symm hideScratch_skip) (Eq.refl _))

theorem applyMat_discard_hidePost {q : ℕ} {D : Type*}
    (P : D → KrausFamily (QDim q) (QDim q)) (d : D)
    (ρ : Matrix (Fin (QDim (q + 1))) (Fin (QDim (q + 1))) ℂ) :
    KrausFamily.applyMat (discardScratch q).kraus
      (KrausFamily.applyMat (hidePost P d) ρ) =
    KrausFamily.applyMat (P d)
      (KrausFamily.applyMat (discardScratch q).kraus ρ) := by
  simp only [hidePost, KrausFamily.applyMat_comp]
  have h :=
    applyMat_discard_initialize q
      (KrausFamily.applyMat (P d)
        (KrausFamily.applyMat (discardScratch q).kraus ρ))
  rw [KrausFamily.applyMat_comp, initializeScratch_kraus,
    KrausFamily.applyMat_single] at h
  rw [initializeScratch_kraus, KrausFamily.applyMat_single]
  exact h

theorem scratchInsensitive_skip {q c : ℕ} :
    ScratchInsensitive (skip : Sem (q + 1) (c + 1)) := by
  intro s P ρ
  have hunit :=
    FiniteInstrumentComp.wpKraus_unit_semEq (n := QDim (q + 1)) s
      (hidePost (P ∘ hideStore)) ρ
  have hL :
      KrausFamily.applyMat (discardScratch q).kraus
        (KrausFamily.applyMat
          ((skip s).wpKraus (hidePost (P ∘ hideStore))) ρ) =
      KrausFamily.applyMat (P (hideStore s))
        (KrausFamily.applyMat (discardScratch q).kraus ρ) := by
    simpa [skip] using
      (congrArg (KrausFamily.applyMat (discardScratch q).kraus) hunit).trans
        (applyMat_discard_hidePost (P ∘ hideStore) s ρ)
  have hR := hideScratch_skip (q := q) (c := c) (hideStore s) P
    (KrausFamily.applyMat (discardScratch q).kraus ρ)
  have hunit' :=
    FiniteInstrumentComp.wpKraus_unit_semEq (n := QDim q)
      (hideStore s) P (KrausFamily.applyMat (discardScratch q).kraus ρ)
  exact hL.trans (hunit'.symm.trans hR.symm)

theorem scratchInsensitive_select {q c : ℕ}
    (g : CStore (c + 1) → Bool) (F G : Sem (q + 1) (c + 1))
    (hg : ∀ s, g s = g (initStore (hideStore s)))
    (hF : ScratchInsensitive F) (hG : ScratchInsensitive G) :
    ScratchInsensitive (select g F G) := by
  intro s P ρ
  have hsel :=
    hideScratch_select g F G (fun t => g (initStore t)) (fun _ => rfl)
  by_cases hgval : g s
  · have hginit : g (initStore (hideStore s)) = true :=
      (hg s).symm.trans (by simp [hgval])
    have hGsel : hideScratch (select g F G) (hideStore s) =
        hideScratch G (hideStore s) := by
      rw [hsel]
      simp [select, hginit]
    change
      KrausFamily.applyMat (discardScratch q).kraus
        (KrausFamily.applyMat
          ((select g F G s).wpKraus (hidePost (P ∘ hideStore))) ρ) =
      KrausFamily.applyMat
        ((hideScratch (select g F G) (hideStore s)).wpKraus P)
        (KrausFamily.applyMat (discardScratch q).kraus ρ)
    simp only [select, hgval, hGsel]
    exact hG s P ρ
  · have hginit : g (initStore (hideStore s)) = false :=
      (hg s).symm.trans (by simp [hgval])
    have hFsel : hideScratch (select g F G) (hideStore s) =
        hideScratch F (hideStore s) := by
      rw [hsel]
      simp [select, hginit]
    change
      KrausFamily.applyMat (discardScratch q).kraus
        (KrausFamily.applyMat
          ((select g F G s).wpKraus (hidePost (P ∘ hideStore))) ρ) =
      KrausFamily.applyMat
        ((hideScratch (select g F G) (hideStore s)).wpKraus P)
        (KrausFamily.applyMat (discardScratch q).kraus ρ)
    simp only [select, hgval, hFsel]
    exact hF s P ρ

set_option maxHeartbeats 800000 in
/-- Hidden sequencing is compositional when the continuation ignores leftover
scratch. -/
theorem hideScratch_seq_of_insensitive {q c : ℕ}
    (F G : Sem (q + 1) (c + 1)) (hG : ScratchInsensitive G) :
    Eq (hideScratch (seq F G))
      (seq (hideScratch F) (hideScratch G)) := by
  intro s
  change
    CompEq
      (FiniteInstrumentComp.map hideStore
        (hideComp ((F (initStore s)).bind G)))
      (((hideComp (F (initStore s))).map hideStore).bind (hideScratch G))
  intro P ρ
  let μ := F (initStore s)
  have hL := hideComp_applyMat_wpKraus (μ.bind G) (P ∘ hideStore) ρ
  have hbind :=
    FiniteInstrumentComp.wpKraus_bind_semEq μ G (hidePost (P ∘ hideStore))
      (KrausFamily.applyMat (initializeScratch q).kraus ρ)
  have hRbind :=
    FiniteInstrumentComp.wpKraus_bind_semEq
      ((hideComp μ).map hideStore) (hideScratch G) P ρ
  have hR :=
    hideComp_applyMat_wpKraus μ
      (fun t => (hideScratch G (hideStore t)).wpKraus P) ρ
  have hRmap :
      ((hideComp μ).map hideStore).wpKraus
        (fun t => (hideScratch G t).wpKraus P) =
      (hideComp μ).wpKraus
        (fun t => (hideScratch G (hideStore t)).wpKraus P) :=
    FiniteInstrumentComp.wpKraus_map hideStore (hideComp μ)
      (fun t => (hideScratch G t).wpKraus P)
  refine hL.trans ?_
  refine (congrArg (KrausFamily.applyMat (discardScratch q).kraus) hbind).trans ?_
  refine _root_.Eq.trans ?_ hRbind.symm
  rw [hRmap]
  refine _root_.Eq.trans ?_ hR.symm
  rw [FiniteInstrumentComp.applyMat_wpKraus,
    FiniteInstrumentComp.applyMat_wpKraus, applyMat_sum, applyMat_sum]
  refine Finset.sum_congr rfl ?_
  intro o _
  simp only [KrausFamily.applyMat_comp]
  exact (hG (μ.value o) P
    (KrausFamily.applyMat (μ.branch o)
      (KrausFamily.applyMat (initializeScratch q).kraus ρ))).trans
    (applyMat_discard_hidePost
      (fun t => (hideScratch G (hideStore t)).wpKraus P)
      (μ.value o)
      (KrausFamily.applyMat (μ.branch o)
        (KrausFamily.applyMat (initializeScratch q).kraus ρ))).symm

/-- A physical computation whose logical postconditions factor through
scratch initialization and discard. -/
def FactorsScratch {q c : ℕ} (G : Sem (q + 1) (c + 1)) : Prop :=
  ∀ (s : CStore (c + 1)) (P : CStore c → KrausFamily (QDim q) (QDim q))
    (ρ : Matrix (Fin (QDim (q + 1))) (Fin (QDim (q + 1))) ℂ),
    KrausFamily.applyMat ((G s).wpKraus (hidePost (P ∘ hideStore))) ρ =
      KrausFamily.applyMat
        (hidePost (fun t => (hideScratch G t).wpKraus P) (hideStore s)) ρ

theorem applyMat_hidePost_point {q : ℕ} {D : Type*}
    (d : D) {P Q : D → KrausFamily (QDim q) (QDim q)}
    (h : KrausFamily.SemEq (P d) (Q d))
    (ρ : Matrix (Fin (QDim (q + 1))) (Fin (QDim (q + 1))) ℂ) :
    KrausFamily.applyMat (hidePost P d) ρ =
      KrausFamily.applyMat (hidePost Q d) ρ := by
  simp only [hidePost, KrausFamily.applyMat_comp]
  exact congrArg (KrausFamily.applyMat (initializeScratch q).kraus)
    (h (KrausFamily.applyMat (discardScratch q).kraus ρ))

theorem applyMat_hidePost_congr {q : ℕ} {D : Type*}
    {P Q : D → KrausFamily (QDim q) (QDim q)}
    (h : ∀ d, KrausFamily.SemEq (P d) (Q d)) (d : D)
    (ρ : Matrix (Fin (QDim (q + 1))) (Fin (QDim (q + 1))) ℂ) :
    KrausFamily.applyMat (hidePost P d) ρ =
      KrausFamily.applyMat (hidePost Q d) ρ :=
  applyMat_hidePost_point d (h d) ρ

theorem scratchInsensitive_of_factorsScratch {q c : ℕ}
    {G : Sem (q + 1) (c + 1)} (hG : FactorsScratch G) :
    ScratchInsensitive G := by
  intro s P ρ
  refine (congrArg (KrausFamily.applyMat (discardScratch q).kraus)
    (hG s P ρ)).trans ?_
  exact applyMat_discard_hidePost
    (fun t => (hideScratch G t).wpKraus P) (hideStore s) ρ

theorem factorsScratch_congr {q c : ℕ} {F G : Sem (q + 1) (c + 1)}
    (hFG : Eq F G) (hF : FactorsScratch F) : FactorsScratch G := by
  intro s P ρ
  have hleft :=
    ((hFG s) (hidePost (P ∘ hideStore)) ρ).symm
  refine hleft.trans ((hF s P ρ).trans ?_)
  refine applyMat_hidePost_congr ?_ (hideStore s) ρ
  intro t
  exact hideScratch_congr hFG t P

theorem factorsScratch_skip {q c : ℕ} :
    FactorsScratch (skip : Sem (q + 1) (c + 1)) := by
  intro s P ρ
  have hL :=
    FiniteInstrumentComp.wpKraus_unit_semEq (n := QDim (q + 1)) s
      (hidePost (P ∘ hideStore)) ρ
  refine hL.trans ?_
  refine (applyMat_hidePost_congr ?_ (hideStore s) ρ).symm
  intro t
  exact KrausFamily.applySemEq_trans (hideScratch_skip t P)
    (FiniteInstrumentComp.wpKraus_unit_semEq (n := QDim q) t P)

theorem factorsScratch_select {q c : ℕ}
    (g : CStore (c + 1) → Bool) (F G : Sem (q + 1) (c + 1))
    (hg : ∀ s, g s = g (initStore (hideStore s)))
    (hF : FactorsScratch F) (hG : FactorsScratch G) :
    FactorsScratch (select g F G) := by
  intro s P ρ
  have hsel :=
    hideScratch_select g F G (fun t => g (initStore t)) (fun _ => rfl)
  by_cases hgval : g s
  · have hginit : g (initStore (hideStore s)) = true :=
      (hg s).symm.trans (by simp [hgval])
    have hbranch :
        hideScratch (select g F G) (hideStore s) =
          hideScratch G (hideStore s) := by
      rw [hsel]
      simp [select, hginit]
    simp only [select, hgval]
    refine (hG s P ρ).trans ?_
    refine applyMat_hidePost_point (hideStore s) ?_ ρ
    rw [hbranch]
    exact KrausFamily.applySemEq_refl _
  · have hginit : g (initStore (hideStore s)) = false :=
      (hg s).symm.trans (by simp [hgval])
    have hbranch :
        hideScratch (select g F G) (hideStore s) =
          hideScratch F (hideStore s) := by
      rw [hsel]
      simp [select, hginit]
    simp only [select, hgval]
    refine (hF s P ρ).trans ?_
    refine applyMat_hidePost_point (hideStore s) ?_ ρ
    rw [hbranch]
    exact KrausFamily.applySemEq_refl _

set_option maxHeartbeats 800000 in
theorem factorsScratch_seq {q c : ℕ}
    (F G : Sem (q + 1) (c + 1))
    (hF : FactorsScratch F) (hG : FactorsScratch G) :
    FactorsScratch (seq F G) := by
  intro s P ρ
  let Q : CStore c → KrausFamily (QDim q) (QDim q) :=
    fun t => (hideScratch G t).wpKraus P
  have hGsem :
      ∀ d, KrausFamily.SemEq
        ((G d).wpKraus (hidePost (P ∘ hideStore)))
        (hidePost (Q ∘ hideStore) d) := by
    intro d σ
    simpa [Q, hidePost, Function.comp_apply] using hG d P σ
  have hbind :=
    FiniteInstrumentComp.wpKraus_bind_semEq (F s) G
      (hidePost (P ∘ hideStore)) ρ
  have hpred :=
    FiniteInstrumentComp.wpKraus_semEq_pred (F s) hGsem ρ
  have hfac := hF s Q ρ
  have hseq :=
    hideScratch_seq_of_insensitive F G (scratchInsensitive_of_factorsScratch hG)
  refine hbind.trans ?_
  refine hpred.trans ?_
  refine hfac.trans ?_
  refine applyMat_hidePost_congr ?_ (hideStore s) ρ
  intro t
  exact KrausFamily.applySemEq_trans
    (KrausFamily.applySemEq_symm
      (FiniteInstrumentComp.wpKraus_bind_semEq
        (hideScratch F t) (hideScratch G) P))
    (KrausFamily.applySemEq_symm (hseq t P))

end QLambda.CQ
