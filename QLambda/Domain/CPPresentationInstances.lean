/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Order.Antisymmetrization
import QLambda.QuantumInstruments
import QLambda.Composer.MatrixSemantics
import QLambda.Domain.CPPresentation
import QLambda.Domain.instPreorderCPPresentation

/-!
# Instances from `CPPresentation`

Barrel re-exporting `CPPresentation` / `CompletedCP` material that depends on
the presentation preorder.
-/

namespace QLambda.Domain

open scoped BigOperators ComplexConjugate MatrixOrder

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

end CompletedCP

end QLambda.Domain
