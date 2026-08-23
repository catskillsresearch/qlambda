/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.ObservationBasis

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QLambda

/-- A matrix in Choi coordinates whose entries are Gaussian rationals. -/
abbrev RatChoiMatrix (n : ℕ) :=
  Matrix (Fin n × Fin n) (Fin n × Fin n) RatComplex

noncomputable instance (n : ℕ) : Encodable (RatChoiMatrix n) := by
  classical
  unfold RatChoiMatrix Matrix
  infer_instance

instance (n : ℕ) : Countable (RatChoiMatrix n) :=
  Encodable.countable

namespace RatChoiMatrix

/-- Coordinatewise embedding of a rational Choi matrix into a complex matrix. -/
def toComplex {n : ℕ} (M : RatChoiMatrix n) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun i j => M i j

@[simp] theorem toComplex_apply {n : ℕ} (M : RatChoiMatrix n)
    (i j : Fin n × Fin n) :
    M.toComplex i j = (M i j : ℂ) :=
  rfl

end RatChoiMatrix

/-- A Gaussian-rational Choi matrix together with a semantic PSD certificate. -/
structure RatCPMatrix (n : ℕ) where
  matrix : RatChoiMatrix n
  posSemidef : matrix.toComplex.PosSemidef

namespace RatCPMatrix

instance (n : ℕ) : Countable (RatCPMatrix n) :=
  (show Function.Injective (matrix : RatCPMatrix n → RatChoiMatrix n) from
    fun A B h => by
    cases A
    cases B
    simp_all).countable

noncomputable instance (n : ℕ) : Encodable (RatCPMatrix n) := by
  classical
  let e : RatCPMatrix n ≃ {M : RatChoiMatrix n // M.toComplex.PosSemidef} := {
    toFun M := ⟨M.matrix, M.posSemidef⟩
    invFun M := ⟨M.1, M.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact Encodable.ofEquiv _ e

/-- The complex matrix denoted by a rational CP code. -/
def toComplex {n : ℕ} (M : RatCPMatrix n) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  M.matrix.toComplex

theorem toComplex_posSemidef {n : ℕ} (M : RatCPMatrix n) :
    M.toComplex.PosSemidef :=
  M.posSemidef

/-- A chosen finite Kraus realization of the coded rational Choi matrix. -/
noncomputable def realize {n : ℕ} (M : RatCPMatrix n) : KrausFamily n n :=
  Classical.choose (KrausFamily.exists_krausFamily_choi_eq M.posSemidef)

@[simp] theorem choi_realize {n : ℕ} (M : RatCPMatrix n) :
    KrausFamily.choi M.realize = M.toComplex :=
  Classical.choose_spec (KrausFamily.exists_krausFamily_choi_eq M.posSemidef)

theorem realize_refines {n : ℕ} {M N : RatCPMatrix n}
    (h : M.toComplex ≤ N.toComplex) :
    KrausFamily.Refines M.realize N.realize := by
  apply KrausFamily.residualRefines_of_choiRefines
  simpa [KrausFamily.ChoiRefines] using h

end RatCPMatrix

end QLambda
