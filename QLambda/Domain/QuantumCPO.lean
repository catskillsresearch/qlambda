/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Order.Antisymmetrization
import QLambda.QuantumInstrument
import QLambda.Composer.MatrixSemantics

/-!
# Presentation-independent finite-dimensional quantum operations

Finite Kraus lists are presentations. `CompletedCP` quotients them by the
intrinsic Choi refinement preorder, so equality is independent of a chosen
Kraus presentation. Higher-order quantum CPO structure is supplied separately
by `QuantumCPOCategory`.
-/

namespace QLambda.Domain

open scoped BigOperators ComplexConjugate MatrixOrder

structure CPPresentation (n m : ℕ) where
  kraus : KrausFamily n m

noncomputable instance instPreorderCPPresentation (n m : ℕ) :
    Preorder (CPPresentation n m) where
  le K L := KrausFamily.ResidualRefines K.kraus L.kraus
  lt K L :=
    KrausFamily.ResidualRefines K.kraus L.kraus ∧
      ¬ KrausFamily.ResidualRefines L.kraus K.kraus
  le_refl K := KrausFamily.residualRefines_refl K.kraus
  le_trans _ _ _ := KrausFamily.residualRefines_trans
  lt_iff_le_not_ge _ _ := Iff.rfl

abbrev SemanticCP (n m : ℕ) :=
  Antisymmetrization (CPPresentation n m) (· ≤ ·)

/-- Finite CP maps modulo semantic equality of Kraus presentations. -/
abbrev CompletedCP (n m : ℕ) := SemanticCP n m

namespace CompletedCP

variable {n m ℓ : ℕ}

noncomputable def ofKraus (K : KrausFamily n m) : CompletedCP n m :=
  toAntisymmetrization (· ≤ ·) ⟨K⟩

noncomputable def zero : CompletedCP n m :=
  ofKraus KrausFamily.zero

noncomputable def identity (n : ℕ) : CompletedCP n n :=
  ofKraus (KrausFamily.identity n)

def allocZeroMatrix (q : ℕ) :
    KrausOperator (CQ.QDim q) (CQ.QDim (q + 1)) :=
  fun i j => if i.val = j.val then 1 else 0

noncomputable def new0 (q : ℕ) :
    CompletedCP (CQ.QDim q) (CQ.QDim (q + 1)) :=
  ofKraus [allocZeroMatrix q]

noncomputable def x {q : ℕ} (w : Fin q) :
    CompletedCP (CQ.QDim q) (CQ.QDim q) :=
  ofKraus [Composer.xMatrix w]

noncomputable def h {q : ℕ} (w : Fin q) :
    CompletedCP (CQ.QDim q) (CQ.QDim q) :=
  ofKraus [Composer.hMatrix w]

noncomputable def t {q : ℕ} (w : Fin q) :
    CompletedCP (CQ.QDim q) (CQ.QDim q) :=
  ofKraus [Composer.tMatrix w]

noncomputable def ry {q : ℕ} (θ : ℚ) (w : Fin q) :
    CompletedCP (CQ.QDim q) (CQ.QDim q) :=
  ofKraus [Composer.ryMatrix θ w]

noncomputable def cx {q : ℕ} (control target : Fin q) :
    CompletedCP (CQ.QDim q) (CQ.QDim q) :=
  ofKraus [Composer.cxMatrix control target]

theorem ofKraus_mono {K L : KrausFamily n m}
    (hKL : KrausFamily.ResidualRefines K L) :
    ofKraus K ≤ ofKraus L := by
  exact toAntisymmetrization_mono hKL

theorem ofKraus_eq_of_semEq {K L : KrausFamily n m}
    (hKL : KrausFamily.SemEq K L) :
    ofKraus K = ofKraus L := by
  apply le_antisymm
  · exact ofKraus_mono (KrausFamily.residualRefines_of_semEq hKL)
  · exact ofKraus_mono
      (KrausFamily.residualRefines_of_semEq
        (KrausFamily.applySemEq_symm hKL))

theorem ofKraus_comp_mono_left (M : KrausFamily m ℓ)
    {K L : KrausFamily n m} (hKL : KrausFamily.ResidualRefines K L) :
    ofKraus (KrausFamily.comp M K) ≤
      ofKraus (KrausFamily.comp M L) :=
  ofKraus_mono (KrausFamily.residualRefines_comp_left M hKL)

theorem ofKraus_comp_mono_right (M : KrausFamily ℓ n)
    {K L : KrausFamily n m} (hKL : KrausFamily.ResidualRefines K L) :
    ofKraus (KrausFamily.comp K M) ≤
      ofKraus (KrausFamily.comp L M) :=
  ofKraus_mono (KrausFamily.residualRefines_comp_right M hKL)

theorem ofKraus_comp_assoc {r : ℕ}
    (M : KrausFamily ℓ r) (L : KrausFamily m ℓ)
    (K : KrausFamily n m) :
    ofKraus (KrausFamily.comp M (KrausFamily.comp L K)) =
      ofKraus (KrausFamily.comp (KrausFamily.comp M L) K) := by
  rw [KrausFamily.comp_assoc]

structure Instrument (n m outcomes : ℕ) where
  branch : Fin outcomes → CompletedCP n m

namespace Instrument

noncomputable def ofQuantumInstrument
    {outcomes : ℕ} (Φ : QuantumInstrument n m outcomes) :
    Instrument n m outcomes where
  branch o := ofKraus (Φ.branch o)

end Instrument

noncomputable def measure {q : ℕ} (w : Fin q) :
    Instrument (CQ.QDim q) (CQ.QDim q) 2 :=
  Instrument.ofQuantumInstrument (Composer.measure w)

theorem measure_probability_normalization {q : ℕ} (w : Fin q)
    (ρ : Matrix (Fin (CQ.QDim q)) (Fin (CQ.QDim q)) ℂ) :
    (∑ i : Fin 2,
      Matrix.trace
        (KrausFamily.applyMat ((Composer.measure w).branch i) ρ)).re =
      (Matrix.trace ρ).re := by
  rw [Fin.sum_univ_two]
  have hne : (1 : Fin 2) ≠ 0 := by decide
  simp only [Composer.measure, hne, ↓reduceIte]
  rw [KrausFamily.applyMat_single, KrausFamily.applyMat_single]
  rw [Matrix.trace_mul_comm
      (Composer.projector w false * ρ)
      (Composer.projector w false).conjTranspose,
    Matrix.trace_mul_comm
      (Composer.projector w true * ρ)
      (Composer.projector w true).conjTranspose]
  rw [Composer.projector_conjTranspose, Composer.projector_conjTranspose,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Composer.projector_mul_self, Composer.projector_mul_self,
    ← Matrix.trace_add, ← Matrix.add_mul,
    Composer.projector_completeness, Matrix.one_mul]

noncomputable def reset {q : ℕ} (w : Fin q) :
    CompletedCP (CQ.QDim q) (CQ.QDim q) :=
  ofKraus (Composer.reset w).kraus

end CompletedCP

end QLambda.Domain
