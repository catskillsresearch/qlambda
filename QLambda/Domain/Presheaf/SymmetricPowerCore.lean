/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Monoidal

/-!
# Tensor-power permutations and symmetric averages

Finite tensor-factor permutations are implemented by permutation isometries.
The degree-`k` symmetric power is the concrete invariant submodule of the
representable tensor power: an element is a superoperator fixed by
postcomposition with every permutation of its `k` output tensor factors.
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped BigOperators ComplexConjugate

namespace SuperoperatorModule

/-- Strictly associated tensor-power dimensions. -/
def tensorPowerDimension (A : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => A * tensorPowerDimension A k

@[simp]
theorem tensorPowerDimension_zero (A : ℕ) :
    tensorPowerDimension A 0 = 1 :=
  rfl

@[simp]
theorem tensorPowerDimension_succ (A k : ℕ) :
    tensorPowerDimension A (k + 1) =
      A * tensorPowerDimension A k :=
  rfl

@[simp]
theorem tensorPowerDimension_one (A : ℕ) :
    tensorPowerDimension A 1 = A := by
  simp [tensorPowerDimension]

@[simp]
theorem tensorPowerDimension_eq_pow (A k : ℕ) :
    tensorPowerDimension A k = A ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [tensorPowerDimension, pow_succ, ih, Nat.mul_comm]

/-- Partitions of a fixed total degree have one common tensor-power dimension.
This makes a mixed partition sum well-typed. It does not make that sum
trace-nonincreasing. -/
theorem tensorPowerDimension_mul_add (A p q : ℕ) :
    tensorPowerDimension A p * tensorPowerDimension A q =
      tensorPowerDimension A (p + q) := by
  simp [tensorPowerDimension_eq_pow, pow_add]

/-- Split a nonempty finite tuple into its head and tail. -/
def finSuccFunctionEquiv (A k : ℕ) :
    (Fin (k + 1) → Fin A) ≃ Fin A × (Fin k → Fin A) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · funext i
      rfl

/-- A finite tuple is canonically a basis index for the corresponding
strictly associated tensor power. -/
noncomputable def tensorTupleEquiv (A : ℕ) :
    (k : ℕ) → (Fin k → Fin A) ≃ Fin (tensorPowerDimension A k)
  | 0 =>
      { toFun := fun _ => ⟨0, by simp⟩
        invFun := fun _ i => nomatch i
        left_inv := fun f => by
          funext i
          exact Fin.elim0 i
        right_inv := fun i => (Fin.eq_zero i).symm }
  | k + 1 =>
      (finSuccFunctionEquiv A k).trans
        ((Equiv.prodCongr (Equiv.refl (Fin A))
          (tensorTupleEquiv A k)).trans finProdFinEquiv)

/-- Permute the tensor factors of a tensor-power basis. -/
noncomputable def factorPermutationEquiv (A k : ℕ)
    (σ : Equiv.Perm (Fin k)) :
    Fin (tensorPowerDimension A k) ≃
      Fin (tensorPowerDimension A k) :=
  (tensorTupleEquiv A k).symm |>.trans
    ((Equiv.arrowCongr σ (Equiv.refl (Fin A))).trans
      (tensorTupleEquiv A k))

/-- The reversible channel implementing a tensor-factor permutation. -/
noncomputable def factorPermutation (A k : ℕ)
    (σ : Equiv.Perm (Fin k)) :
    Superoperator (tensorPowerDimension A k)
      (tensorPowerDimension A k) :=
  Superoperator.ofEquivalence (factorPermutationEquiv A k σ)

/-- Tensor-factor permutations form a representation of the finite
permutation group. -/
theorem factorPermutationEquiv_trans (A k : ℕ)
    (σ τ : Equiv.Perm (Fin k)) :
    (factorPermutationEquiv A k σ).trans
        (factorPermutationEquiv A k τ) =
      factorPermutationEquiv A k (σ.trans τ) := by
  apply Equiv.ext
  intro x
  simp [factorPermutationEquiv]
  funext i
  rfl

@[simp]
theorem factorPermutation_trans (A k : ℕ)
    (σ τ : Equiv.Perm (Fin k)) :
    Superoperator.comp (factorPermutation A k τ)
        (factorPermutation A k σ) =
      factorPermutation A k (σ.trans τ) := by
  rw [factorPermutation, factorPermutation, factorPermutation,
    Superoperator.ofEquivalence_comp, factorPermutationEquiv_trans]

/-- Kraus normalization for the uniform distribution on `k!`
permutations. -/
noncomputable def permutationAverageScale (k : ℕ) : ℂ :=
  (Real.sqrt ((Nat.factorial k : ℝ)⁻¹) : ℝ)

theorem permutationAverageScale_normSq (k : ℕ) :
    permutationAverageScale k * star (permutationAverageScale k) =
      ((Nat.factorial k : ℝ)⁻¹ : ℂ) := by
  rw [show star (permutationAverageScale k) =
      permutationAverageScale k by
    simp [permutationAverageScale]]
  unfold permutationAverageScale
  rw [← Complex.ofReal_mul]
  norm_cast
  simpa [pow_two] using
    Real.sq_sqrt (inv_nonneg.mpr (Nat.cast_nonneg (k.factorial)))

/-- A Kraus presentation of the uniform average of all tensor-factor
permutation channels. -/
noncomputable def symmetricAverageKraus (A k : ℕ) :
    KrausFamily (tensorPowerDimension A k)
      (tensorPowerDimension A k) :=
  ((Finset.univ : Finset (Equiv.Perm (Fin k))).toList.map fun σ =>
    permutationAverageScale k •
      Superoperator.equivalenceMatrix
        (factorPermutationEquiv A k σ))

theorem symmetricAverageKraus_effect (A k : ℕ) :
    KrausFamily.effect (symmetricAverageKraus A k) = 1 := by
  classical
  unfold KrausFamily.effect symmetricAverageKraus
  simp only [List.map_map]
  have hterm (σ : Equiv.Perm (Fin k)) :
      (permutationAverageScale k •
        Superoperator.equivalenceMatrix
          (factorPermutationEquiv A k σ))ᴴ *
      (permutationAverageScale k •
        Superoperator.equivalenceMatrix
          (factorPermutationEquiv A k σ)) =
        ((Nat.factorial k : ℝ)⁻¹ : ℂ) • 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      Superoperator.equivalenceMatrix_isometry]
    rw [smul_smul]
    congr 1
    rw [mul_comm]
    exact permutationAverageScale_normSq k
  rw [show
    List.map
      ((fun A => Aᴴ * A) ∘ fun σ =>
        permutationAverageScale k •
          Superoperator.equivalenceMatrix
            (factorPermutationEquiv A k σ))
      (Finset.univ : Finset (Equiv.Perm (Fin k))).toList =
    List.map (fun _ => ((Nat.factorial k : ℝ)⁻¹ : ℂ) • 1)
      (Finset.univ : Finset (Equiv.Perm (Fin k))).toList by
      apply List.map_congr_left
      intro σ _
      exact hterm σ]
  simp [Fintype.card_perm, nsmul_eq_mul]
  ext i j
  rw [Matrix.smul_apply, Matrix.one_apply, Matrix.natCast_apply]
  by_cases hij : i = j
  · subst j
    simp
    rw [inv_mul_cancel₀]
    exact_mod_cast Nat.factorial_ne_zero k
  · simp [hij]

/-- The trace-preserving CP projector obtained by uniformly averaging all
tensor-factor permutation channels. -/
noncomputable def symmetricAverage (A k : ℕ) :
    Superoperator (tensorPowerDimension A k)
      (tensorPowerDimension A k) :=
  Superoperator.ofKraus (symmetricAverageKraus A k) (by
    intro ρ _
    rw [KrausFamily.trace_applyMat_eq_effect,
      symmetricAverageKraus_effect, Matrix.one_mul])

private theorem list_sum_toList_eq_sum {α M : Type*}
    [DecidableEq α] [AddCommMonoid M] (s : Finset α) (f : α → M) :
    (s.toList.map f).sum = ∑ x ∈ s, f x := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      calc
        ((insert a s).toList.map f).sum =
            ((a :: s.toList).map f).sum :=
          ((Finset.toList_insert ha).map f).sum_eq
        _ = f a + (s.toList.map f).sum := by simp
        _ = f a + ∑ x ∈ s, f x := congrArg (f a + ·) ih
        _ = ∑ x ∈ insert a s, f x := by simp [ha]

theorem symmetricAverage_applyMat (A k : ℕ)
    (ρ : Matrix (Fin (tensorPowerDimension A k))
      (Fin (tensorPowerDimension A k)) ℂ) :
    (symmetricAverage A k).cp.applyMat ρ =
      ((Nat.factorial k : ℝ)⁻¹ : ℂ) •
        ∑ σ : Equiv.Perm (Fin k),
          (factorPermutation A k σ).cp.applyMat ρ := by
  classical
  unfold symmetricAverage Superoperator.ofKraus symmetricAverageKraus
  rw [CPMap.applyMat_ofKraus]
  simp only [KrausFamily.applyMat, List.map_map]
  change
    ((Finset.univ : Finset (Equiv.Perm (Fin k))).toList.map
      (fun σ =>
        (permutationAverageScale k •
          Superoperator.equivalenceMatrix
            (factorPermutationEquiv A k σ)) * ρ *
        (permutationAverageScale k •
          Superoperator.equivalenceMatrix
            (factorPermutationEquiv A k σ))ᴴ)).sum =
      _
  rw [list_sum_toList_eq_sum]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [factorPermutation,
    Superoperator.ofEquivalence, Superoperator.ofIsometry,
    Superoperator.ofQuantumOperation, QuantumOperation.ofIsometry,
    Superoperator.ofKraus, CPMap.applyMat_ofKraus,
    KrausFamily.applyMat, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul]
  rw [Matrix.smul_mul, smul_smul]
  congr 1
  rw [mul_comm]
  exact permutationAverageScale_normSq k

private theorem cpMap_applyMat_finset_sum {ι : Type*}
    [DecidableEq ι] {n m : ℕ} (Φ : CPMap n m) (s : Finset ι)
    (f : ι → Matrix (Fin n) (Fin n) ℂ) :
    Φ.applyMat (∑ i ∈ s, f i) =
      ∑ i ∈ s, Φ.applyMat (f i) := by
  induction s using Finset.induction with
  | empty =>
      simpa using Φ.applyMat_smul (0 : ℂ)
        (0 : Matrix (Fin n) (Fin n) ℂ)
  | @insert a s ha ih =>
      simp [ha, CPMap.applyMat_add, ih]

/-- Averaging lands in the fixed points of every tensor permutation. -/
theorem factorPermutation_comp_symmetricAverage (A k : ℕ)
    (τ : Equiv.Perm (Fin k)) :
    Superoperator.comp (factorPermutation A k τ)
        (symmetricAverage A k) =
      symmetricAverage A k := by
  apply Superoperator.ext
  apply CPMap.ext_apply
  intro ρ
  rw [Superoperator.cp_comp, CPMap.applyMat_comp,
    symmetricAverage_applyMat, CPMap.applyMat_smul,
    cpMap_applyMat_finset_sum]
  congr 1
  apply Finset.sum_bij (fun σ _ => σ.trans τ)
  · intro σ _
    simp
  · intro σ₁ _ σ₂ _ h
    apply Equiv.ext
    intro x
    apply τ.injective
    exact congrFun (congrArg Equiv.toFun h) x
  · intro υ _
    refine ⟨υ.trans τ.symm, by simp, ?_⟩
    apply Equiv.ext
    intro x
    simp
  · intro σ _
    rw [← CPMap.applyMat_comp]
    exact congrArg (fun Φ : Superoperator _ _ => Φ.cp.applyMat ρ)
      (factorPermutation_trans A k σ τ)

theorem factorial_average_constant (k d : ℕ)
    (x : Matrix (Fin d) (Fin d) ℂ) :
    ((Nat.factorial k : ℝ)⁻¹ : ℂ) •
        ∑ _σ : Equiv.Perm (Fin k), x = x := by
  ext i j
  rw [Matrix.smul_apply]
  rw [Matrix.sum_apply]
  rw [Algebra.smul_def]
  simp [Fintype.card_perm, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast Nat.factorial_ne_zero k

/-- The averaging channel is an idempotent CP/TNI projector. -/
theorem symmetricAverage_idempotent (A k : ℕ) :
    Superoperator.comp (symmetricAverage A k)
        (symmetricAverage A k) =
      symmetricAverage A k := by
  apply Superoperator.ext
  apply CPMap.ext_apply
  intro ρ
  rw [Superoperator.cp_comp, CPMap.applyMat_comp,
    symmetricAverage_applyMat]
  have hterm : ∀ σ : Equiv.Perm (Fin k),
      (factorPermutation A k σ).cp.applyMat
          ((symmetricAverage A k).cp.applyMat ρ) =
        (symmetricAverage A k).cp.applyMat ρ := by
    intro σ
    rw [← CPMap.applyMat_comp]
    exact congrArg (fun Φ : Superoperator _ _ => Φ.cp.applyMat ρ)
      (factorPermutation_comp_symmetricAverage A k σ)
  simp_rw [hterm]
  exact factorial_average_constant k _ _

/-- Apply a finite basis equivalence pointwise to a tensor tuple. -/
noncomputable def tensorTupleMapEquiv {A B : ℕ}
    (e : Fin A ≃ Fin B) (k : ℕ) :
    Fin (tensorPowerDimension A k) ≃
      Fin (tensorPowerDimension B k) :=
  (tensorTupleEquiv A k).symm |>.trans
    ((Equiv.arrowCongr (Equiv.refl (Fin k)) e).trans
      (tensorTupleEquiv B k))

theorem tensorTupleMapEquiv_permutation {A B : ℕ}
    (e : Fin A ≃ Fin B) (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    (tensorTupleMapEquiv e k).trans (factorPermutationEquiv B k σ) =
      (factorPermutationEquiv A k σ).trans
        (tensorTupleMapEquiv e k) := by
  apply Equiv.ext
  intro x
  apply (tensorTupleEquiv B k).symm.injective
  funext i
  simp [tensorTupleMapEquiv, factorPermutationEquiv]

@[simp]
theorem tensorTupleMapEquiv_refl (A k : ℕ) :
    tensorTupleMapEquiv (Equiv.refl (Fin A)) k =
      Equiv.refl (Fin (tensorPowerDimension A k)) := by
  apply Equiv.ext
  intro x
  apply (tensorTupleEquiv A k).symm.injective
  funext i
  simp [tensorTupleMapEquiv]

@[simp]
theorem tensorTupleMapEquiv_trans {A B C : ℕ}
    (e : Fin A ≃ Fin B) (f : Fin B ≃ Fin C) (k : ℕ) :
    tensorTupleMapEquiv (e.trans f) k =
      (tensorTupleMapEquiv e k).trans (tensorTupleMapEquiv f k) := by
  apply Equiv.ext
  intro x
  apply (tensorTupleEquiv C k).symm.injective
  funext i
  simp [tensorTupleMapEquiv]

/-- Regroup a `(p+q)`-tuple into its first `p` and last `q` tensor
coordinates. -/
noncomputable def tensorSplitEquiv (A p q : ℕ) :
    Fin (tensorPowerDimension A (p + q)) ≃
      Fin (tensorPowerDimension A p * tensorPowerDimension A q) :=
  (tensorTupleEquiv A (p + q)).symm |>.trans
    (((Equiv.arrowCongr finSumFinEquiv (Equiv.refl (Fin A))).symm).trans
      ((Equiv.sumArrowEquivProdArrow (Fin p) (Fin q) (Fin A)).trans
        ((Equiv.prodCongr (tensorTupleEquiv A p)
          (tensorTupleEquiv A q)).trans finProdFinEquiv)))

/-- Pointwise basis equivalence on a pair of homogeneous blocks. -/
noncomputable def homogeneousPairMapEquiv {A B : ℕ}
    (e : Fin A ≃ Fin B) (p q : ℕ) :
    Fin (tensorPowerDimension A p * tensorPowerDimension A q) ≃
      Fin (tensorPowerDimension B p * tensorPowerDimension B q) :=
  (tensorSplitEquiv A p q).symm |>.trans
    ((tensorTupleMapEquiv e (p + q)).trans
      (tensorSplitEquiv B p q))

theorem tensorSplitEquiv_natural {A B : ℕ}
    (e : Fin A ≃ Fin B) (p q : ℕ) :
    (tensorSplitEquiv A p q).trans
        (homogeneousPairMapEquiv e p q) =
      (tensorTupleMapEquiv e (p + q)).trans
        (tensorSplitEquiv B p q) := by
  unfold homogeneousPairMapEquiv
  rw [← Equiv.trans_assoc, Equiv.self_trans_symm,
    Equiv.refl_trans]

/-- Exchange two adjacent blocks of tensor-factor positions. -/
noncomputable def blockPermutation (p q : ℕ) :
    Equiv.Perm (Fin (p + q)) :=
  finSumFinEquiv.symm |>.trans
    ((Equiv.sumComm (Fin p) (Fin q)).trans
      (finSumFinEquiv.trans (finCongr (Nat.add_comm q p))))

/-- The braiding between two homogeneous tensor powers, defined by the
genuine block permutation of tensor factors and the canonical splittings. -/
noncomputable def homogeneousBraidingEquiv (A p q : ℕ) :
    Fin (tensorPowerDimension A p * tensorPowerDimension A q) ≃
      Fin (tensorPowerDimension A q * tensorPowerDimension A p) :=
  (tensorSplitEquiv A p q).symm |>.trans
    ((factorPermutationEquiv A (p + q) (blockPermutation p q)).trans
      ((finCongr
        (congrArg (tensorPowerDimension A) (Nat.add_comm p q))).trans
          (tensorSplitEquiv A q p)))

/-- The opposite-order split, with the source degree transported along
`p + q = q + p`. -/
noncomputable def oppositeTensorSplitEquiv (A p q : ℕ) :
    Fin (tensorPowerDimension A (p + q)) ≃
      Fin (tensorPowerDimension A q * tensorPowerDimension A p) :=
  (finCongr
    (congrArg (tensorPowerDimension A) (Nat.add_comm p q))).trans
      (tensorSplitEquiv A q p)

/-- The left tensor unitor on homogeneous dimensions. -/
noncomputable def homogeneousLeftUnitorEquiv (A q : ℕ) :
    Fin (tensorPowerDimension A 0 * tensorPowerDimension A q) ≃
      Fin (tensorPowerDimension A q) :=
  (tensorSplitEquiv A 0 q).symm |>.trans
    (finCongr
      (congrArg (tensorPowerDimension A) (Nat.zero_add q)))

/-- The right tensor unitor on homogeneous dimensions. -/
noncomputable def homogeneousRightUnitorEquiv (A p : ℕ) :
    Fin (tensorPowerDimension A p * tensorPowerDimension A 0) ≃
      Fin (tensorPowerDimension A p) :=
  (tensorSplitEquiv A p 0).symm |>.trans
    (finCongr
      (congrArg (tensorPowerDimension A) (Nat.add_zero p)))

/-- Split the first homogeneous block once more. -/
noncomputable def homogeneousLeftRefinementEquiv (A p q r : ℕ) :
    Fin (tensorPowerDimension A (p + q) * tensorPowerDimension A r) ≃
      Fin ((tensorPowerDimension A p * tensorPowerDimension A q) *
        tensorPowerDimension A r) :=
  finProdFinEquiv.symm |>.trans
    ((Equiv.prodCongr (tensorSplitEquiv A p q)
      (Equiv.refl (Fin (tensorPowerDimension A r)))).trans
        finProdFinEquiv)

/-- Canonical three-block splitting of a symmetric tensor power. -/
noncomputable def tensorTripleSplitEquiv (A p q r : ℕ) :
    Fin (tensorPowerDimension A ((p + q) + r)) ≃
      Fin ((tensorPowerDimension A p * tensorPowerDimension A q) *
        tensorPowerDimension A r) :=
  (tensorSplitEquiv A (p + q) r).trans
    (homogeneousLeftRefinementEquiv A p q r)

/-- Refinement of the left output of contraction. -/
noncomputable def contractionLeftRefinementEquiv (A p q r : ℕ) :
    Fin (tensorPowerDimension A (p + q) * tensorPowerDimension A r) ≃
      Fin ((tensorPowerDimension A p * tensorPowerDimension A q) *
        tensorPowerDimension A r) :=
  (tensorSplitEquiv A (p + q) r).symm |>.trans
    (tensorTripleSplitEquiv A p q r)

/-- Refinement of the right output of contraction, including the canonical
associativity transport of total degree. -/
noncomputable def contractionRightRefinementEquiv (A p q r : ℕ) :
    Fin (tensorPowerDimension A p * tensorPowerDimension A (q + r)) ≃
      Fin ((tensorPowerDimension A p * tensorPowerDimension A q) *
        tensorPowerDimension A r) :=
  (tensorSplitEquiv A p (q + r)).symm |>.trans
    ((finCongr (congrArg (tensorPowerDimension A)
      (Nat.add_assoc p q r).symm)).trans
        (tensorTripleSplitEquiv A p q r))

/-- Regrouping and then braiding is the block permutation followed by
regrouping in the opposite order. -/
theorem tensorSplitEquiv_braiding (A p q : ℕ) :
    (tensorSplitEquiv A p q).trans (homogeneousBraidingEquiv A p q) =
      (factorPermutationEquiv A (p + q) (blockPermutation p q)).trans
        ((finCongr
          (congrArg (tensorPowerDimension A) (Nat.add_comm p q))).trans
            (tensorSplitEquiv A q p)) := by
  apply Equiv.ext
  intro x
  simp [homogeneousBraidingEquiv]

@[simp]
theorem tensorSplitEquiv_inverse (A p q : ℕ)
    (x : Superoperator n (tensorPowerDimension A (p + q))) :
    Superoperator.comp
        (Superoperator.ofEquivalence (tensorSplitEquiv A p q).symm)
        (Superoperator.comp
          (Superoperator.ofEquivalence (tensorSplitEquiv A p q)) x) =
      x := by
  rw [Superoperator.comp_assoc, Superoperator.ofEquivalence_comp]
  convert Superoperator.identity_comp x using 2
  simp

end SuperoperatorModule

end QLambda.Domain.Presheaf
