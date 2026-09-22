/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import QLambda.Composer.Model

/-!
# Canonical matrix semantics for Composer

The least-significant bit is wire zero.  Gates are first defined on the
selected Boolean coordinates and are then reindexed into the canonical
`Fin (2 ^ q)` computational basis.
-/

open Matrix
open scoped BigOperators ComplexConjugate Kronecker

namespace QLambda.Composer

/-- Computational-basis bit strings, with wire zero the least-significant bit. -/
abbrev BasisBits (q : ℕ) := Fin q → Bool

/-- Decode a basis index into its little-endian bit string. -/
def basisBits {q : ℕ} (i : Fin (CQ.QDim q)) : BasisBits q :=
  fun w => i.val.testBit w.val

/-- Encode a little-endian bit string as a basis index. -/
def basisIndex {q : ℕ} (x : BasisBits q) : Fin (CQ.QDim q) :=
  ⟨Nat.ofBits x, Nat.ofBits_lt_two_pow x⟩

@[simp] theorem basisBits_basisIndex {q : ℕ} (x : BasisBits q) :
    basisBits (basisIndex x) = x := by
  funext w
  exact Nat.testBit_ofBits_lt x w.val w.isLt

@[simp] theorem basisIndex_basisBits {q : ℕ} (i : Fin (CQ.QDim q)) :
    basisIndex (basisBits i) = i := by
  apply Fin.ext
  change Nat.ofBits (fun w : Fin q => i.val.testBit w.val) = i.val
  rw [Nat.ofBits_testBit]
  exact Nat.mod_eq_of_lt i.isLt

/-- The canonical equivalence between integer and bit-string basis labels. -/
def basisEquiv (q : ℕ) : Fin (CQ.QDim q) ≃ BasisBits q where
  toFun := basisBits
  invFun := basisIndex
  left_inv := basisIndex_basisBits
  right_inv := basisBits_basisIndex

/-- All wires other than `w`. -/
abbrev OtherBits {q : ℕ} (w : Fin q) := {v : Fin q // v ≠ w} → Bool

/-- Split one selected wire from a computational-basis bit string. -/
def splitWire {q : ℕ} (w : Fin q) : BasisBits q ≃ Bool × OtherBits w where
  toFun x := (x w, fun v => x v.1)
  invFun p v := if h : v = w then p.1 else p.2 ⟨v, h⟩
  left_inv x := by
    funext v
    by_cases h : v = w
    · subst v
      simp
    · simp [h]
  right_inv p := by
    apply Prod.ext
    · simp
    · funext v
      simp [v.2]

/-- Split a selected wire directly from the integer basis label. -/
def registerSplit {q : ℕ} (w : Fin q) :
    Fin (CQ.QDim q) ≃ Bool × OtherBits w :=
  (basisEquiv q).trans (splitWire w)

/-- All wires other than two distinct selected wires. -/
abbrev OtherBits₂ {q : ℕ} (control target : Fin q) :=
  {v : Fin q // v ≠ control ∧ v ≠ target} → Bool

/-- Split two distinct wires from a computational-basis bit string. -/
def splitWires {q : ℕ} (control target : Fin q) (hne : control ≠ target) :
    BasisBits q ≃ (Bool × Bool) × OtherBits₂ control target where
  toFun x := ((x control, x target), fun v => x v.1)
  invFun p v :=
    if hc : v = control then p.1.1
    else if ht : v = target then p.1.2
    else p.2 ⟨v, hc, ht⟩
  left_inv x := by
    funext v
    by_cases hc : v = control
    · subst v
      simp
    · by_cases ht : v = target
      · subst v
        simp [hc]
      · simp [hc, ht]
  right_inv p := by
    apply Prod.ext
    · apply Prod.ext
      · simp
      · simp [Ne.symm hne]
    · funext v
      simp [v.2.1, v.2.2]

/-- Split two distinct wires directly from the integer basis label. -/
def registerSplit₂ {q : ℕ} (control target : Fin q) (hne : control ≠ target) :
    Fin (CQ.QDim q) ≃ (Bool × Bool) × OtherBits₂ control target :=
  (basisEquiv q).trans (splitWires control target hne)

abbrev QubitMatrix := Matrix Bool Bool ℂ

/-- Pauli X in the Boolean computational basis. -/
def x₂ : QubitMatrix :=
  fun i j => if i = !j then 1 else 0

/-- Hadamard in the Boolean computational basis. -/
noncomputable def sqrtTwoHalf : ℂ :=
  Real.sqrt 2 / 2

noncomputable def h₂ : QubitMatrix :=
  fun i j => if i && j then -sqrtTwoHalf else sqrtTwoHalf

/-- Primitive eighth root of unity used by the `T` gate. -/
noncomputable def tPhase : ℂ :=
  sqrtTwoHalf + sqrtTwoHalf * Complex.I

/-- The `T = diag(1, exp(iπ/4))` phase gate. -/
noncomputable def t₂ : QubitMatrix :=
  fun i j => if i = j then if i then tPhase else 1 else 0

noncomputable def cosHalf (θ : ℝ) : ℂ :=
  (Real.cos (θ / 2) : ℝ)

noncomputable def sinHalf (θ : ℝ) : ℂ :=
  (Real.sin (θ / 2) : ℝ)

@[simp] theorem cosHalf_def (θ : ℝ) :
    cosHalf θ = (Real.cos (θ / 2) : ℝ) :=
  rfl

@[simp] theorem sinHalf_def (θ : ℝ) :
    sinHalf θ = (Real.sin (θ / 2) : ℝ) :=
  rfl

/-- Rotation about the Y axis in the Boolean computational basis. -/
noncomputable def ry₂ (θ : ℝ) : QubitMatrix :=
  fun i j =>
    match i, j with
    | false, false => cosHalf θ
    | false, true => -sinHalf θ
    | true, false => sinHalf θ
    | true, true => cosHalf θ

/-- Computational-basis projector on one Boolean qubit. -/
def proj₂ (b : Bool) : QubitMatrix :=
  fun i j => if i = b ∧ j = b then 1 else 0

/-- The reset Kraus operator `|0⟩⟨b|`. -/
def reset₂ (b : Bool) : QubitMatrix :=
  fun i j => if i = false ∧ j = b then 1 else 0

/-- Controlled X on two Boolean coordinates `(control, target)`. -/
def cx₄ : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun i j => if i = (j.1, Bool.xor j.2 j.1) then 1 else 0

theorem x₂_isometry : x₂ᴴ * x₂ = 1 := by
  ext i j
  cases i <;> cases j <;> simp [x₂, Matrix.mul_apply]

private theorem sqrtTwoHalf_sq :
    sqrtTwoHalf * sqrtTwoHalf = (1 / 2 : ℂ) := by
  norm_num [sqrtTwoHalf, div_mul_div_comm, ← Complex.ofReal_mul,
    Real.mul_self_sqrt]

@[simp] private theorem star_sqrtTwoHalf : star sqrtTwoHalf = sqrtTwoHalf := by
  simp [sqrtTwoHalf]

@[simp] theorem star_tPhase_mul_tPhase : star tPhase * tPhase = 1 := by
  have hstar : star tPhase =
      sqrtTwoHalf - sqrtTwoHalf * Complex.I := by
    simp [tPhase]
    ring
  rw [hstar]
  simp only [tPhase]
  ring_nf
  have hs : sqrtTwoHalf ^ 2 = (1 / 2 : ℂ) := by
    simpa [pow_two] using sqrtTwoHalf_sq
  rw [hs, Complex.I_sq]
  norm_num

@[simp] private theorem star_cosHalf (θ : ℝ) : star (cosHalf θ) = cosHalf θ := by
  exact Complex.conj_ofReal _

@[simp] private theorem star_sinHalf (θ : ℝ) : star (sinHalf θ) = sinHalf θ := by
  exact Complex.conj_ofReal _

theorem h₂_isometry : h₂ᴴ * h₂ = 1 := by
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.mul_apply, conjTranspose_apply, h₂] <;>
    rw [Fintype.sum_bool] <;>
    simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true,
      Bool.true_eq_false, one_apply, ↓reduceIte, star_sqrtTwoHalf]
  ·
    repeat rw [sqrtTwoHalf_sq]
    norm_num
  ·
    simp
  ·
    simp
  ·
    rw [star_neg, star_sqrtTwoHalf, neg_mul]
    simp only [mul_neg, neg_neg]
    repeat rw [sqrtTwoHalf_sq]
    norm_num

theorem t₂_isometry : t₂ᴴ * t₂ = 1 := by
  ext i j
  cases i <;> cases j <;>
    simp [t₂, Matrix.mul_apply]
  change star tPhase * tPhase = 1
  exact star_tPhase_mul_tPhase

theorem ry₂_isometry (θ : ℝ) : (ry₂ θ)ᴴ * ry₂ θ = 1 := by
  have htrig :
      sinHalf θ * sinHalf θ + cosHalf θ * cosHalf θ = 1 := by
    simp only [sinHalf, cosHalf]
    exact_mod_cast (by
      simpa [pow_two] using Real.sin_sq_add_cos_sq (θ / 2))
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.mul_apply, conjTranspose_apply, ry₂] <;>
    rw [Fintype.sum_bool] <;>
    simp only [one_apply, ↓reduceIte, star_neg, star_cosHalf, star_sinHalf,
      neg_mul, mul_neg, neg_neg, Bool.false_eq_true, Bool.true_eq_false]
  ·
    simpa only [add_comm] using htrig
  ·
    ring
  ·
    ring
  ·
    simpa [add_comm] using htrig

theorem cx₄_isometry : cx₄ᴴ * cx₄ = 1 := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  cases i₁ <;> cases i₂ <;> cases j₁ <;> cases j₂ <;>
    simp [cx₄, Matrix.mul_apply]

@[simp] theorem proj₂_conjTranspose (b : Bool) : (proj₂ b)ᴴ = proj₂ b := by
  ext i j
  cases i <;> cases j <;> cases b <;> simp [proj₂, conjTranspose]

@[simp] theorem proj₂_mul_self (b : Bool) : proj₂ b * proj₂ b = proj₂ b := by
  ext i j
  cases i <;> cases j <;> cases b <;> simp [proj₂, Matrix.mul_apply]

theorem proj₂_completeness : proj₂ false + proj₂ true = (1 : QubitMatrix) := by
  ext i j
  cases i <;> cases j <;> simp [proj₂]

theorem reset₂_completeness :
    (reset₂ false)ᴴ * reset₂ false + (reset₂ true)ᴴ * reset₂ true =
      (1 : QubitMatrix) := by
  ext i j
  cases i <;> cases j <;> simp [reset₂, Matrix.mul_apply]

/-- Put a one-qubit matrix on an arbitrary register wire. -/
noncomputable def onWire {q : ℕ} (w : Fin q) (U : QubitMatrix) :
    KrausOperator (CQ.QDim q) (CQ.QDim q) :=
  Matrix.reindexAlgEquiv ℂ ℂ (registerSplit w).symm
    (U ⊗ₖ (1 : Matrix (OtherBits w) (OtherBits w) ℂ))

@[simp] theorem onWire_conjTranspose {q : ℕ} (w : Fin q) (U : QubitMatrix) :
    (onWire w U)ᴴ = onWire w Uᴴ := by
  change
    (Matrix.reindex (registerSplit w).symm (registerSplit w).symm
      (U ⊗ₖ (1 : Matrix (OtherBits w) (OtherBits w) ℂ)))ᴴ =
    Matrix.reindex (registerSplit w).symm (registerSplit w).symm
      (Uᴴ ⊗ₖ (1 : Matrix (OtherBits w) (OtherBits w) ℂ))
  rw [Matrix.conjTranspose_reindex,
    Matrix.conjTranspose_kronecker, conjTranspose_one]

@[simp] theorem onWire_mul {q : ℕ} (w : Fin q) (U V : QubitMatrix) :
    onWire w U * onWire w V = onWire w (U * V) := by
  classical
  rw [onWire, onWire, onWire, ← map_mul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]

@[simp] theorem onWire_add {q : ℕ} (w : Fin q) (U V : QubitMatrix) :
    onWire w U + onWire w V = onWire w (U + V) := by
  classical
  rw [onWire, onWire, onWire, ← map_add, Matrix.add_kronecker]

@[simp] theorem onWire_one {q : ℕ} (w : Fin q) :
    onWire w (1 : QubitMatrix) = 1 := by
  classical
  rw [onWire, Matrix.one_kronecker_one]
  exact map_one (Matrix.reindexAlgEquiv ℂ ℂ (registerSplit w).symm)

/-- Put a two-qubit matrix on two distinct arbitrary register wires. -/
noncomputable def onWires {q : ℕ} (control target : Fin q)
    (hne : control ≠ target) (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    KrausOperator (CQ.QDim q) (CQ.QDim q) :=
  Matrix.reindexAlgEquiv ℂ ℂ (registerSplit₂ control target hne).symm
    (U ⊗ₖ (1 : Matrix (OtherBits₂ control target) (OtherBits₂ control target) ℂ))

theorem onWires_isometry {q : ℕ} (control target : Fin q)
    (hne : control ≠ target) (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hU : Uᴴ * U = 1) :
    (onWires control target hne U)ᴴ * onWires control target hne U = 1 := by
  classical
  rw [onWires]
  have hconj :
      (Matrix.reindexAlgEquiv ℂ ℂ (registerSplit₂ control target hne).symm
        (U ⊗ₖ (1 : Matrix (OtherBits₂ control target)
          (OtherBits₂ control target) ℂ)))ᴴ =
      Matrix.reindexAlgEquiv ℂ ℂ (registerSplit₂ control target hne).symm
        (Uᴴ ⊗ₖ (1 : Matrix (OtherBits₂ control target)
          (OtherBits₂ control target) ℂ)) := by
    change
      (Matrix.reindex (registerSplit₂ control target hne).symm
        (registerSplit₂ control target hne).symm
        (U ⊗ₖ (1 : Matrix (OtherBits₂ control target)
          (OtherBits₂ control target) ℂ)))ᴴ =
      Matrix.reindex (registerSplit₂ control target hne).symm
        (registerSplit₂ control target hne).symm
        (Uᴴ ⊗ₖ (1 : Matrix (OtherBits₂ control target)
          (OtherBits₂ control target) ℂ))
    rw [Matrix.conjTranspose_reindex, Matrix.conjTranspose_kronecker,
      conjTranspose_one]
  rw [hconj, ← map_mul,
    ← Matrix.mul_kronecker_mul, hU, Matrix.one_mul,
    Matrix.one_kronecker_one]
  exact map_one
    (Matrix.reindexAlgEquiv ℂ ℂ (registerSplit₂ control target hne).symm)

/-- Canonical arbitrary-register Pauli X. -/
noncomputable def xMatrix {q : ℕ} (w : Fin q) : KrausOperator (CQ.QDim q) (CQ.QDim q) :=
  onWire w x₂

/-- Canonical arbitrary-register Hadamard. -/
noncomputable def hMatrix {q : ℕ} (w : Fin q) : KrausOperator (CQ.QDim q) (CQ.QDim q) :=
  onWire w h₂

/-- Canonical arbitrary-register `T` phase gate. -/
noncomputable def tMatrix {q : ℕ} (w : Fin q) : KrausOperator (CQ.QDim q) (CQ.QDim q) :=
  onWire w t₂

/-- Canonical arbitrary-register Y rotation. -/
noncomputable def ryMatrix {q : ℕ} (θ : ℝ) (w : Fin q) :
    KrausOperator (CQ.QDim q) (CQ.QDim q) :=
  onWire w (ry₂ θ)

/-- Canonical arbitrary-register controlled X.  A repeated wire denotes identity. -/
noncomputable def cxMatrix {q : ℕ} (control target : Fin q) :
    KrausOperator (CQ.QDim q) (CQ.QDim q) :=
  if h : control = target then 1 else onWires control target h cx₄

/-- Canonical computational-basis projector on one register wire. -/
noncomputable def projector {q : ℕ} (w : Fin q) (b : Bool) :
    KrausOperator (CQ.QDim q) (CQ.QDim q) :=
  onWire w (proj₂ b)

/-- Canonical reset Kraus operator `|0⟩⟨b|` on one register wire. -/
noncomputable def resetKraus {q : ℕ} (w : Fin q) (b : Bool) :
    KrausOperator (CQ.QDim q) (CQ.QDim q) :=
  onWire w (reset₂ b)

theorem xMatrix_isometry {q : ℕ} (w : Fin q) :
    (xMatrix w)ᴴ * xMatrix w = 1 := by
  simp [xMatrix, x₂_isometry]

theorem hMatrix_isometry {q : ℕ} (w : Fin q) :
    (hMatrix w)ᴴ * hMatrix w = 1 := by
  simp [hMatrix, h₂_isometry]

theorem tMatrix_isometry {q : ℕ} (w : Fin q) :
    (tMatrix w)ᴴ * tMatrix w = 1 := by
  simp [tMatrix, t₂_isometry]

theorem ryMatrix_isometry {q : ℕ} (θ : ℝ) (w : Fin q) :
    (ryMatrix θ w)ᴴ * ryMatrix θ w = 1 := by
  simp [ryMatrix, ry₂_isometry]

theorem cxMatrix_isometry {q : ℕ} (control target : Fin q) :
    (cxMatrix control target)ᴴ * cxMatrix control target = 1 := by
  classical
  by_cases h : control = target
  · simp [cxMatrix, h]
  · simp only [cxMatrix, dif_neg h]
    exact onWires_isometry control target h cx₄ cx₄_isometry

@[simp] theorem projector_conjTranspose {q : ℕ} (w : Fin q) (b : Bool) :
    (projector w b)ᴴ = projector w b := by
  simp [projector]

@[simp] theorem projector_mul_self {q : ℕ} (w : Fin q) (b : Bool) :
    projector w b * projector w b = projector w b := by
  simp [projector]

theorem projector_completeness {q : ℕ} (w : Fin q) :
    projector w false + projector w true = 1 := by
  classical
  rw [projector, projector, onWire_add, proj₂_completeness, onWire_one]

theorem resetKraus_completeness {q : ℕ} (w : Fin q) :
    (resetKraus w false)ᴴ * resetKraus w false +
        (resetKraus w true)ᴴ * resetKraus w true = 1 := by
  simp only [resetKraus, onWire_conjTranspose, onWire_mul]
  rw [onWire_add, reset₂_completeness, onWire_one]

/-- Two Kraus operators whose Gram matrices sum to identity preserve trace. -/
theorem trace_applyMat_pair_of_completeness {n : ℕ}
    (A B : KrausOperator n n) (h : Aᴴ * A + Bᴴ * B = 1)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (KrausFamily.applyMat [A, B] ρ) = Matrix.trace ρ := by
  rw [KrausFamily.applyMat_cons, KrausFamily.applyMat_single, Matrix.trace_add]
  rw [Matrix.trace_mul_comm (A * ρ) Aᴴ, Matrix.trace_mul_comm (B * ρ) Bᴴ]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.trace_add,
    ← Matrix.add_mul, h, Matrix.one_mul]

/-- Computational-basis measurement of an arbitrary register wire. -/
noncomputable def measure {q : ℕ} (w : Fin q) :
    QuantumInstrument (CQ.QDim q) (CQ.QDim q) 2 where
  branch i := if i = 0 then [projector w false] else [projector w true]
  trace_nonincreasing := by
    intro ρ _
    rw [Fin.sum_univ_two]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ↓reduceIte]
    rw [KrausFamily.applyMat_single, KrausFamily.applyMat_single]
    rw [Matrix.trace_mul_comm (projector w false * ρ) (projector w false)ᴴ,
      Matrix.trace_mul_comm (projector w true * ρ) (projector w true)ᴴ]
    rw [projector_conjTranspose, projector_conjTranspose,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      projector_mul_self, projector_mul_self,
      ← Complex.add_re, ← Matrix.trace_add, ← Matrix.add_mul,
      projector_completeness, Matrix.one_mul]

/-- Reset an arbitrary register wire to the computational state `|0⟩`. -/
noncomputable def reset {q : ℕ} (w : Fin q) :
    QuantumOperation (CQ.QDim q) (CQ.QDim q) where
  kraus := [resetKraus w false, resetKraus w true]
  trace_nonincreasing := by
    intro ρ _
    rw [trace_applyMat_pair_of_completeness _ _ (resetKraus_completeness w) ρ]

/-- Entrywise formula for a one-qubit operator lifted to an arbitrary wire. -/
theorem onWire_apply {q : ℕ} (w : Fin q) (U : QubitMatrix)
    (i j : Fin (CQ.QDim q)) :
    onWire w U i j =
      U (basisBits i w) (basisBits j w) *
        if (fun u : {v : Fin q // v ≠ w} => basisBits i u.1) =
            (fun u => basisBits j u.1) then 1 else 0 := by
  change
    (U ⊗ₖ (1 : Matrix (OtherBits w) (OtherBits w) ℂ))
      (registerSplit w i) (registerSplit w j) =
      U (basisBits i w) (basisBits j w) *
        if (fun u : {v : Fin q // v ≠ w} => basisBits i u.1) =
            (fun u => basisBits j u.1) then 1 else 0
  simp only [registerSplit, Equiv.trans_apply, basisEquiv, Equiv.coe_fn_mk,
    splitWire]
  rw [Matrix.kroneckerMap_apply]
  simp [Matrix.one_apply]

/-- Entrywise formula for a two-qubit operator lifted to distinct wires. -/
theorem onWires_apply {q : ℕ} (control target : Fin q) (hne : control ≠ target)
    (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (i j : Fin (CQ.QDim q)) :
    onWires control target hne U i j =
      U (basisBits i control, basisBits i target)
        (basisBits j control, basisBits j target) *
        if (fun u : {v : Fin q // v ≠ control ∧ v ≠ target} =>
              basisBits i u.1) =
            (fun u => basisBits j u.1) then 1 else 0 := by
  change
    (U ⊗ₖ (1 : Matrix (OtherBits₂ control target) (OtherBits₂ control target) ℂ))
      (registerSplit₂ control target hne i)
      (registerSplit₂ control target hne j) =
      U (basisBits i control, basisBits i target)
        (basisBits j control, basisBits j target) *
        if (fun u : {v : Fin q // v ≠ control ∧ v ≠ target} =>
              basisBits i u.1) =
            (fun u => basisBits j u.1) then 1 else 0
  simp only [registerSplit₂, Equiv.trans_apply, basisEquiv, Equiv.coe_fn_mk,
    splitWires]
  rw [Matrix.kroneckerMap_apply]
  simp [Matrix.one_apply]

/-- `RY(2·arccos(√p))` prepares amplitude `√p` on the zero state. -/
theorem coin_cos (p : Probability) :
    Real.cos ((AngleExpr.coin p).eval / 2) = Real.sqrt p.real := by
  have hsqrt0 : 0 ≤ Real.sqrt p.real := Real.sqrt_nonneg _
  have hsqrt1 : Real.sqrt p.real ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact p.real_le_one
  simp only [AngleExpr.eval]
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  exact Real.cos_arccos (le_trans (by norm_num : (-1 : ℝ) ≤ 0) hsqrt0) hsqrt1

/-- `RY(2·arccos(√p))` prepares amplitude `√(1-p)` on the one state. -/
theorem coin_sin (p : Probability) :
    Real.sin ((AngleExpr.coin p).eval / 2) = Real.sqrt (1 - p.real) := by
  have hsqrt0 : 0 ≤ Real.sqrt p.real := Real.sqrt_nonneg _
  have hsqrt1 : Real.sqrt p.real ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact p.real_le_one
  simp only [AngleExpr.eval]
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.sin_arccos,
    Real.sq_sqrt p.real_nonneg]

/-- Coin-angle amplitudes after RY on the computational zero state. -/
theorem ry₂_coin_zero (p : Probability) :
    ry₂ (AngleExpr.coin p).eval false false = Real.sqrt p.real ∧
    ry₂ (AngleExpr.coin p).eval true false = Real.sqrt (1 - p.real) := by
  constructor
  · simp [ry₂, coin_cos]
  · simp [ry₂, coin_sin]

theorem ry₂_apply_false (θ : ℝ) (j : Bool) :
    ry₂ θ false j = if j then -sinHalf θ else cosHalf θ := by
  cases j <;> simp [ry₂]

theorem ry₂_apply_true (θ : ℝ) (j : Bool) :
    ry₂ θ true j = if j then cosHalf θ else sinHalf θ := by
  cases j <;> simp [ry₂]

theorem fixture_x_one :
    (xMatrix (0 : Fin 1))ᴴ * xMatrix (0 : Fin 1) = 1 :=
  xMatrix_isometry _

theorem fixture_h_one :
    (hMatrix (0 : Fin 1))ᴴ * hMatrix (0 : Fin 1) = 1 :=
  hMatrix_isometry _

theorem fixture_t_one :
    (tMatrix (0 : Fin 1))ᴴ * tMatrix (0 : Fin 1) = 1 :=
  tMatrix_isometry _

theorem fixture_ry_one (θ : ℝ) :
    (ryMatrix θ (0 : Fin 1))ᴴ * ryMatrix θ (0 : Fin 1) = 1 :=
  ryMatrix_isometry _ _

theorem fixture_measure_one :
    projector (0 : Fin 1) false + projector (0 : Fin 1) true = 1 :=
  projector_completeness _

theorem fixture_reset_one :
    (resetKraus (0 : Fin 1) false)ᴴ * resetKraus (0 : Fin 1) false +
      (resetKraus (0 : Fin 1) true)ᴴ * resetKraus (0 : Fin 1) true = 1 :=
  resetKraus_completeness _

theorem fixture_cx_two :
    (cxMatrix (0 : Fin 2) 1)ᴴ * cxMatrix 0 1 = 1 :=
  cxMatrix_isometry _ _

theorem fixture_cx_distinct_two : (0 : Fin 2) ≠ 1 := by
  decide

theorem fixture_h_three :
    (hMatrix (2 : Fin 3))ᴴ * hMatrix 2 = 1 :=
  hMatrix_isometry _

theorem fixture_cx_three :
    (cxMatrix (0 : Fin 3) 2)ᴴ * cxMatrix 0 2 = 1 :=
  cxMatrix_isometry _ _

/-- Canonical ideal matrix model for the typed Composer core. -/
noncomputable def canonicalModel (q c : ℕ) : Model q c where
  gate
    | .x w => QuantumOperation.ofIsometry (xMatrix w) (xMatrix_isometry w)
    | .h w => QuantumOperation.ofIsometry (hMatrix w) (hMatrix_isometry w)
    | .t w => QuantumOperation.ofIsometry (tMatrix w) (tMatrix_isometry w)
    | .ry θ w =>
        QuantumOperation.ofIsometry (ryMatrix θ.eval w) (ryMatrix_isometry θ.eval w)
    | .cx control target =>
        QuantumOperation.ofIsometry (cxMatrix control target)
          (cxMatrix_isometry control target)
  measure := measure
  reset := reset

end QLambda.Composer
