/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.CPMap
import QLambda.Composer.MatrixSemantics

/-!
# Trace-nonincreasing intrinsic superoperators

The CP component is an intrinsic Choi matrix.  Trace non-increase is a
property of its action and therefore does not depend on a Kraus presentation.
Finite instruments retain their outcome branches and constrain the sum of
their branch probabilities.
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

/-- Trace non-increase for an intrinsic CP map. -/
def TraceNonincreasing {n m : ℕ} (Φ : CPMap n m) : Prop :=
  ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
    (Matrix.trace (Φ.applyMat ρ)).re ≤ (Matrix.trace ρ).re

/-- A finite-dimensional trace-nonincreasing completely positive map. -/
structure Superoperator (n m : ℕ) where
  cp : CPMap n m
  trace_nonincreasing : TraceNonincreasing cp

namespace Superoperator

variable {n m ℓ r : ℕ}

@[ext]
theorem ext {Φ Ψ : Superoperator n m} (h : Φ.cp = Ψ.cp) : Φ = Ψ := by
  cases Φ
  cases Ψ
  cases h
  rfl

/-- Build an intrinsic superoperator from a Kraus family and a proof about
its operator-sum action. -/
def ofKraus (K : KrausFamily n m)
    (hK : ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (KrausFamily.applyMat K ρ)).re ≤
        (Matrix.trace ρ).re) :
    Superoperator n m where
  cp := CPMap.ofKraus K
  trace_nonincreasing := by
    intro ρ hρ
    simpa using hK ρ hρ

/-- Forget a finite Kraus presentation while preserving its TNI proof. -/
def ofQuantumOperation (Φ : QuantumOperation n m) : Superoperator n m :=
  ofKraus Φ.kraus Φ.trace_nonincreasing

@[simp]
theorem cp_ofQuantumOperation (Φ : QuantumOperation n m) :
    (ofQuantumOperation Φ).cp = CPMap.ofKraus Φ.kraus :=
  rfl

/-- Recover an arbitrary finite Kraus presentation. -/
noncomputable def toQuantumOperation (Φ : Superoperator n m) :
    QuantumOperation n m where
  kraus := Φ.cp.toKraus
  trace_nonincreasing := Φ.trace_nonincreasing

@[simp]
theorem ofQuantumOperation_toQuantumOperation (Φ : Superoperator n m) :
    ofQuantumOperation (toQuantumOperation Φ) = Φ := by
  apply ext
  exact CPMap.ofKraus_toKraus Φ.cp

@[simp]
theorem cp_toQuantumOperation (Φ : Superoperator n m) :
    CPMap.ofKraus (toQuantumOperation Φ).kraus = Φ.cp :=
  CPMap.ofKraus_toKraus Φ.cp

/-- Identity superoperator. -/
def identity (n : ℕ) : Superoperator n n where
  cp := CPMap.identity n
  trace_nonincreasing := by
    intro ρ _
    rw [CPMap.applyMat_identity]

/-- Zero superoperator. -/
def zero : Superoperator n m where
  cp := 0
  trace_nonincreasing := by
    intro ρ hρ
    have htr : 0 ≤ Matrix.trace ρ := PosSemidef.trace_nonneg hρ
    rw [CPMap.applyMat_zero, Matrix.trace_zero, Complex.zero_re]
    exact (RCLike.nonneg_iff (K := ℂ).mp htr).1

instance : Zero (Superoperator n m) := ⟨zero⟩

@[simp]
theorem cp_zero : (0 : Superoperator n m).cp = 0 :=
  rfl

@[simp]
theorem applyMat_zero (ρ : Matrix (Fin n) (Fin n) ℂ) :
    (0 : Superoperator n m).cp.applyMat ρ = 0 :=
  CPMap.applyMat_zero ρ

/-- Sequential composition, first `Φ` and then `Ψ`. -/
noncomputable def comp (Ψ : Superoperator m ℓ) (Φ : Superoperator n m) :
    Superoperator n ℓ where
  cp := CPMap.comp Ψ.cp Φ.cp
  trace_nonincreasing := by
    intro ρ hρ
    rw [CPMap.applyMat_comp]
    exact
      (Ψ.trace_nonincreasing _ (CPMap.applyMat_posSemidef Φ.cp hρ)).trans
        (Φ.trace_nonincreasing ρ hρ)

@[simp]
theorem cp_comp (Ψ : Superoperator m ℓ) (Φ : Superoperator n m) :
    (comp Ψ Φ).cp = CPMap.comp Ψ.cp Φ.cp :=
  rfl

@[simp]
theorem identity_comp (Φ : Superoperator n m) :
    comp (identity m) Φ = Φ :=
  ext (CPMap.identity_comp Φ.cp)

@[simp]
theorem comp_identity (Φ : Superoperator n m) :
    comp Φ (identity n) = Φ :=
  ext (CPMap.comp_identity Φ.cp)

theorem comp_assoc (Χ : Superoperator ℓ r) (Ψ : Superoperator m ℓ)
    (Φ : Superoperator n m) :
    comp Χ (comp Ψ Φ) = comp (comp Χ Ψ) Φ :=
  ext (CPMap.comp_assoc Χ.cp Ψ.cp Φ.cp)

@[simp]
theorem comp_zero_left (Φ : Superoperator n m) :
    comp (0 : Superoperator m ℓ) Φ = 0 :=
  ext (CPMap.comp_zero_left Φ.cp)

@[simp]
theorem comp_zero_right (Ψ : Superoperator m ℓ) :
    comp Ψ (0 : Superoperator n m) = 0 :=
  ext (CPMap.comp_zero_right Ψ.cp)

/-- Parallel composition of finite-dimensional superoperators.  Trace
non-increase is proved through the intrinsic effect bound, hence applies to
arbitrary positive (in particular, entangled) joint inputs. -/
def tensor (Φ : Superoperator n m) (Ψ : Superoperator ℓ r) :
    Superoperator (n * ℓ) (m * r) where
  cp := CPMap.tensor Φ.cp Ψ.cp
  trace_nonincreasing :=
    CPMap.trace_nonincreasing_tensor Φ.cp Ψ.cp
      Φ.trace_nonincreasing Ψ.trace_nonincreasing

@[simp]
theorem cp_tensor (Φ : Superoperator n m) (Ψ : Superoperator ℓ r) :
    (tensor Φ Ψ).cp = CPMap.tensor Φ.cp Ψ.cp :=
  rfl

@[simp]
theorem tensor_zero_left (Ψ : Superoperator ℓ r) :
    tensor (0 : Superoperator n m) Ψ = 0 :=
  ext (CPMap.tensor_zero_left Ψ.cp)

@[simp]
theorem tensor_zero_right (Φ : Superoperator n m) :
    tensor Φ (0 : Superoperator ℓ r) = 0 :=
  ext (CPMap.tensor_zero_right Φ.cp)

/-- Parallel composition is a bifunctor: it preserves sequential
composition in both arguments. -/
theorem tensor_comp {p q : ℕ}
    (Φ₂ : Superoperator m p) (Φ₁ : Superoperator n m)
    (Ψ₂ : Superoperator r q) (Ψ₁ : Superoperator ℓ r) :
    tensor (comp Φ₂ Φ₁) (comp Ψ₂ Ψ₁) =
      comp (tensor Φ₂ Ψ₂) (tensor Φ₁ Ψ₁) :=
  ext (CPMap.tensor_comp Φ₂.cp Φ₁.cp Ψ₂.cp Ψ₁.cp)

/-- Parallel composition preserves identity maps. -/
@[simp]
theorem tensor_identity (n ℓ : ℕ) :
    tensor (identity n) (identity ℓ) = identity (n * ℓ) :=
  ext (CPMap.tensor_identity n ℓ)

/-- Action on a sub-normalized density operator. -/
noncomputable def apply (Φ : Superoperator n m) (ρ : SubNormalizedDensity n) :
    SubNormalizedDensity m where
  mat := Φ.cp.applyMat ρ.mat
  posSemidef := CPMap.applyMat_posSemidef Φ.cp ρ.posSemidef
  trace_le_one :=
    (Φ.trace_nonincreasing ρ.mat ρ.posSemidef).trans ρ.trace_le_one

@[simp]
theorem apply_mat (Φ : Superoperator n m) (ρ : SubNormalizedDensity n) :
    (apply Φ ρ).mat = Φ.cp.applyMat ρ.mat :=
  rfl

/-- A one-Kraus isometry, covering physical embeddings and unitary maps. -/
def ofIsometry (A : KrausOperator n m) (hA : Aᴴ * A = 1) :
    Superoperator n m :=
  ofQuantumOperation (QuantumOperation.ofIsometry A hA)

/-- A square isometry, named for its usual physical use. -/
def unitary (U : KrausOperator n n) (hU : Uᴴ * U = 1) :
    Superoperator n n :=
  ofIsometry U hU

@[simp]
theorem cp_ofIsometry (A : KrausOperator n m) (hA : Aᴴ * A = 1) :
    (ofIsometry A hA).cp = CPMap.ofKraus [A] :=
  rfl

theorem allocZeroMatrix_isometry (q : ℕ) :
    (CompletedCP.allocZeroMatrix q)ᴴ * CompletedCP.allocZeroMatrix q = 1 := by
  ext i j
  have hdim : CQ.QDim q ≤ CQ.QDim (q + 1) := by
    change 2 ^ q ≤ 2 ^ (q + 1)
    rw [pow_succ]
    omega
  have hi (k : Fin (CQ.QDim (q + 1))) :
      k.val = i.val ↔ k = Fin.castLE hdim i := by
    constructor
    · intro h
      apply Fin.ext
      exact h
    · intro h
      exact congrArg Fin.val h
  have hj (k : Fin (CQ.QDim (q + 1))) :
      k.val = j.val ↔ k = Fin.castLE hdim j := by
    constructor
    · intro h
      apply Fin.ext
      exact h
    · intro h
      exact congrArg Fin.val h
  simp only [CompletedCP.allocZeroMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  simp_rw [hi, hj]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

/-- Allocate one fresh qubit in state `|0⟩`. -/
noncomputable def allocateZero (q : ℕ) :
    Superoperator (CQ.QDim q) (CQ.QDim (q + 1)) :=
  ofIsometry (CompletedCP.allocZeroMatrix q) (allocZeroMatrix_isometry q)

@[simp]
theorem cp_allocateZero (q : ℕ) :
    (allocateZero q).cp =
      CPMap.ofKraus [CompletedCP.allocZeroMatrix q] :=
  rfl

noncomputable def x {q : ℕ} (w : Fin q) :
    Superoperator (CQ.QDim q) (CQ.QDim q) :=
  unitary (Composer.xMatrix w) (Composer.xMatrix_isometry w)

noncomputable def h {q : ℕ} (w : Fin q) :
    Superoperator (CQ.QDim q) (CQ.QDim q) :=
  unitary (Composer.hMatrix w) (Composer.hMatrix_isometry w)

noncomputable def t {q : ℕ} (w : Fin q) :
    Superoperator (CQ.QDim q) (CQ.QDim q) :=
  unitary (Composer.tMatrix w) (Composer.tMatrix_isometry w)

noncomputable def ry {q : ℕ} (θ : ℝ) (w : Fin q) :
    Superoperator (CQ.QDim q) (CQ.QDim q) :=
  unitary (Composer.ryMatrix θ w) (Composer.ryMatrix_isometry θ w)

noncomputable def cx {q : ℕ} (control target : Fin q) :
    Superoperator (CQ.QDim q) (CQ.QDim q) :=
  unitary (Composer.cxMatrix control target)
    (Composer.cxMatrix_isometry control target)

/-- Reset a retained wire to `|0⟩`, agreeing definitionally with the existing
two-Kraus operation. -/
noncomputable def reset {q : ℕ} (w : Fin q) :
    Superoperator (CQ.QDim q) (CQ.QDim q) :=
  ofQuantumOperation (Composer.reset w)

@[simp]
theorem cp_reset {q : ℕ} (w : Fin q) :
    (reset w).cp =
      CPMap.ofKraus [Composer.resetKraus w false, Composer.resetKraus w true] :=
  rfl

end Superoperator

/-- A finite retained-output instrument.  Branches are intrinsic CP maps;
the total outcome weight is trace-nonincreasing. -/
structure Instrument (n m outcomes : ℕ) where
  branch : Fin outcomes → CPMap n m
  trace_nonincreasing :
    ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (∑ i, (Matrix.trace ((branch i).applyMat ρ)).re) ≤
        (Matrix.trace ρ).re

namespace Instrument

variable {n m outcomes : ℕ}

/-- Convert an existing finite Kraus instrument without changing any branch
meaning. -/
def ofQuantumInstrument (Φ : QuantumInstrument n m outcomes) :
    Instrument n m outcomes where
  branch i := CPMap.ofKraus (Φ.branch i)
  trace_nonincreasing := by
    intro ρ hρ
    simpa using Φ.trace_nonincreasing ρ hρ

@[simp]
theorem branch_ofQuantumInstrument (Φ : QuantumInstrument n m outcomes)
    (i : Fin outcomes) :
    (ofQuantumInstrument Φ).branch i = CPMap.ofKraus (Φ.branch i) :=
  rfl

private theorem trace_re_nonneg (Φ : CPMap n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosSemidef) :
    0 ≤ (Matrix.trace (Φ.applyMat ρ)).re := by
  have h :=
    PosSemidef.trace_nonneg (CPMap.applyMat_posSemidef Φ hρ)
  exact (RCLike.nonneg_iff (K := ℂ).mp h).1

/-- Every branch of a finite TNI instrument is itself a superoperator. -/
noncomputable def branchSuperoperator (Φ : Instrument n m outcomes)
    (i : Fin outcomes) : Superoperator n m where
  cp := Φ.branch i
  trace_nonincreasing := by
    intro ρ hρ
    calc
      (Matrix.trace ((Φ.branch i).applyMat ρ)).re
          ≤ ∑ j, (Matrix.trace ((Φ.branch j).applyMat ρ)).re := by
            exact Finset.single_le_sum
              (fun j _ => trace_re_nonneg (Φ.branch j) ρ hρ)
              (Finset.mem_univ i)
      _ ≤ (Matrix.trace ρ).re := Φ.trace_nonincreasing ρ hρ

/-- Computational-basis measurement retaining the quantum register. -/
noncomputable def measure {q : ℕ} (w : Fin q) :
    Instrument (CQ.QDim q) (CQ.QDim q) 2 :=
  ofQuantumInstrument (Composer.measure w)

@[simp]
theorem measure_branch_zero {q : ℕ} (w : Fin q) :
    (measure w).branch 0 =
      CPMap.ofKraus [Composer.projector w false] :=
  rfl

@[simp]
theorem measure_branch_one {q : ℕ} (w : Fin q) :
    (measure w).branch 1 =
      CPMap.ofKraus [Composer.projector w true] :=
  rfl

end Instrument

end QLambda.Domain.Presheaf
