/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.SuperoperatorInstances
import QLambda.Domain.Presheaf.SuperoperatorInstrument

/-!
# Finite-support summations of superoperators
-/

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder

namespace QLambda.Domain.Presheaf

namespace SigmaMon

namespace FiniteSupport

variable {n m : ℕ}

/-- Two TNI maps are addable exactly when their CP sum remains TNI. -/
def Addable (Φ Ψ : Superoperator n m) : Prop :=
  TraceNonincreasing (Φ.cp + Ψ.cp)

/-- A defined binary sum. -/
def add (Φ Ψ : Superoperator n m) (h : Addable Φ Ψ) :
    Superoperator n m where
  cp := Φ.cp + Ψ.cp
  trace_nonincreasing := h

@[simp]
theorem cp_add (Φ Ψ : Superoperator n m) (h : Addable Φ Ψ) :
    (add Φ Ψ h).cp = Φ.cp + Ψ.cp :=
  rfl

theorem add_comm (Φ Ψ : Superoperator n m)
    (hΦΨ : Addable Φ Ψ) (hΨΦ : Addable Ψ Φ) :
    add Φ Ψ hΦΨ = add Ψ Φ hΨΦ := by
  apply Superoperator.ext
  exact _root_.add_comm Φ.cp Ψ.cp

theorem zero_addable (Φ : Superoperator n m) :
    Addable 0 Φ := by
  simpa [Addable] using Φ.trace_nonincreasing

theorem add_zeroable (Φ : Superoperator n m) :
    Addable Φ 0 := by
  simpa [Addable] using Φ.trace_nonincreasing

@[simp]
theorem add_zero (Φ : Superoperator n m) :
    add Φ 0 (add_zeroable Φ) = Φ := by
  apply Superoperator.ext
  simp

@[simp]
theorem zero_add (Φ : Superoperator n m) :
    add 0 Φ (zero_addable Φ) = Φ := by
  apply Superoperator.ext
  simp

theorem add_assoc (Φ Ψ Χ : Superoperator n m)
    (hΦΨ : Addable Φ Ψ)
    (hLeft : Addable (add Φ Ψ hΦΨ) Χ)
    (hΨΧ : Addable Ψ Χ)
    (hRight : Addable Φ (add Ψ Χ hΨΧ)) :
    add (add Φ Ψ hΦΨ) Χ hLeft =
      add Φ (add Ψ Χ hΨΧ) hRight := by
  apply Superoperator.ext
  exact _root_.add_assoc Φ.cp Ψ.cp Χ.cp

/-- The CP sum below a natural-number cutoff. -/
def cpSum (f : ℕ → Superoperator n m) (N : ℕ) : CPMap n m :=
  ∑ i ∈ Finset.range N, (f i).cp

/-- `N` supports `f` when every term at or above `N` is zero. -/
def SupportedAt (f : ℕ → Superoperator n m) (N : ℕ) : Prop :=
  ∀ i, N ≤ i → f i = 0

/-- Evidence that a countable family has a defined, finite-support TNI sum. -/
structure Summation (f : ℕ → Superoperator n m) where
  cutoff : ℕ
  supported : SupportedAt f cutoff
  trace_nonincreasing : TraceNonincreasing (cpSum f cutoff)

/-- The superoperator denoted by a supported summation witness. -/
def sum {f : ℕ → Superoperator n m} (h : Summation f) :
    Superoperator n m where
  cp := cpSum f h.cutoff
  trace_nonincreasing := h.trace_nonincreasing

@[simp]
theorem cp_sum {f : ℕ → Superoperator n m} (h : Summation f) :
    (sum h).cp = cpSum f h.cutoff :=
  rfl

private theorem cpSum_eq_of_supported {f : ℕ → Superoperator n m}
    {N M : ℕ} (hN : SupportedAt f N) (hM : SupportedAt f M) :
    cpSum f N = cpSum f M := by
  wlog hNM : N ≤ M generalizing N M
  · exact (this hM hN (le_of_not_ge hNM)).symm
  rw [cpSum, cpSum, ← Finset.sum_range_add_sum_Ico _ hNM]
  suffices (∑ i ∈ Finset.Ico N M, (f i).cp) = 0 by
    rw [this]
    exact (_root_.add_zero _).symm
  apply Finset.sum_eq_zero
  intro i hi
  rw [hN i (Finset.mem_Ico.mp hi).1]
  rfl

/-- Different valid support bounds produce the same sum. -/
theorem sum_eq {f : ℕ → Superoperator n m} (h k : Summation f) :
    sum h = sum k := by
  apply Superoperator.ext
  exact cpSum_eq_of_supported h.supported k.supported

/-- Pointwise-equal families transport summability evidence. -/
def congr {f g : ℕ → Superoperator n m} (h : Summation f)
    (hfg : ∀ i, f i = g i) : Summation g where
  cutoff := h.cutoff
  supported := by
    intro i hi
    rw [← hfg i]
    exact h.supported i hi
  trace_nonincreasing := by
    have hcp : cpSum g h.cutoff = cpSum f h.cutoff := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hfg i]
    rw [hcp]
    exact h.trace_nonincreasing

theorem sum_congr {f g : ℕ → Superoperator n m} (h : Summation f)
    (hfg : ∀ i, f i = g i) :
    sum (congr h hfg) = sum h := by
  apply Superoperator.ext
  change cpSum g h.cutoff = cpSum f h.cutoff
  unfold cpSum
  apply Finset.sum_congr rfl
  intro i _
  rw [← hfg i]

/-- The everywhere-zero family is summable. -/
def zeroSummation : Summation (fun _ : ℕ => (0 : Superoperator n m)) where
  cutoff := 0
  supported := by simp [SupportedAt]
  trace_nonincreasing := by
    simpa [cpSum] using (0 : Superoperator n m).trace_nonincreasing

@[simp]
theorem sum_zero : sum (zeroSummation : Summation
    (fun _ : ℕ => (0 : Superoperator n m))) = 0 := by
  apply Superoperator.ext
  rfl

/-- A countable family with one nonzero term. -/
def single (k : ℕ) (Φ : Superoperator n m) : ℕ → Superoperator n m :=
  fun i => if i = k then Φ else 0

@[simp]
theorem cpSum_single (k : ℕ) (Φ : Superoperator n m) :
    cpSum (single k Φ) (k + 1) = Φ.cp := by
  classical
  unfold cpSum
  rw [Finset.sum_eq_single k]
  · simp [single]
  · intro i hi hik
    simp [single, hik]
  · simp

/-- Every singleton family has a defined sum. -/
def singleSummation (k : ℕ) (Φ : Superoperator n m) :
    Summation (single k Φ) where
  cutoff := k + 1
  supported := by
    intro i hi
    simp only [single]
    split
    · rename_i hik
      subst i
      omega
    · rfl
  trace_nonincreasing := by
    rw [cpSum_single]
    exact Φ.trace_nonincreasing

@[simp]
theorem sum_single (k : ℕ) (Φ : Superoperator n m) :
    sum (singleSummation k Φ) = Φ := by
  apply Superoperator.ext
  exact cpSum_single k Φ

/-- Extend a finite family by zero to a countable family. -/
def extendFin (N : ℕ) (f : Fin N → Superoperator n m) :
    ℕ → Superoperator n m :=
  fun i => if h : i < N then f ⟨i, h⟩ else 0

theorem extendFin_supported (N : ℕ) (f : Fin N → Superoperator n m) :
    SupportedAt (extendFin N f) N := by
  intro i hi
  simp [extendFin, Nat.not_lt.mpr hi]

/-- A finite family has a defined σ-sum whenever its aggregate CP map is
trace-nonincreasing. -/
def finiteSummation (N : ℕ) (f : Fin N → Superoperator n m)
    (h : TraceNonincreasing (cpSum (extendFin N f) N)) :
    Summation (extendFin N f) where
  cutoff := N
  supported := extendFin_supported N f
  trace_nonincreasing := h

/-- A chain of finite prefixes that becomes stationary at `N` has the same
value at every later supported cutoff. -/
theorem stationary_cutoff {f : ℕ → Superoperator n m} {N M : ℕ}
    (hN : SupportedAt f N) (hNM : N ≤ M) :
    cpSum f M = cpSum f N := by
  apply cpSum_eq_of_supported
  · exact fun i hi => hN i (hNM.trans hi)
  · exact hN

end FiniteSupport


end SigmaMon

end QLambda.Domain.Presheaf
