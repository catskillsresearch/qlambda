/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.SymmetricPowerCore

/-!
# Permutation-invariant tensor-power coefficients
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

set_option maxHeartbeats 8000000

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-- Elements of the symmetric power are exactly the superoperators invariant
under every finite permutation of the output tensor factors. -/
structure SymmetricElement (A k n : ℕ) where
  val : Superoperator n (tensorPowerDimension A k)
  invariant :
    ∀ σ : Equiv.Perm (Fin k),
      Superoperator.comp (factorPermutation A k σ) val = val

namespace SymmetricElement

@[ext]
theorem ext {A k n : ℕ} {x y : SymmetricElement A k n}
    (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- Averaging any homogeneous coefficient produces a symmetric element. -/
noncomputable def ofAverage {A k n : ℕ}
    (x : Superoperator n (tensorPowerDimension A k)) :
    SymmetricElement A k n where
  val := Superoperator.comp (symmetricAverage A k) x
  invariant := by
    intro σ
    rw [Superoperator.comp_assoc,
      factorPermutation_comp_symmetricAverage]

/-- The average fixes every permutation-invariant coefficient. -/
theorem average_val {A k n : ℕ} (x : SymmetricElement A k n) :
    Superoperator.comp (symmetricAverage A k) x.val = x.val := by
  apply Superoperator.ext
  apply CPMap.ext_apply
  intro ρ
  rw [Superoperator.cp_comp, CPMap.applyMat_comp,
    symmetricAverage_applyMat]
  have hterm : ∀ σ : Equiv.Perm (Fin k),
      (factorPermutation A k σ).cp.applyMat (x.val.cp.applyMat ρ) =
        x.val.cp.applyMat ρ := by
    intro σ
    rw [← CPMap.applyMat_comp]
    exact congrArg (fun Φ : Superoperator _ _ => Φ.cp.applyMat ρ)
      (x.invariant σ)
  simp_rw [hterm]
  exact factorial_average_constant k _ _

/-- A coefficient is fixed by averaging exactly when it is invariant under
all tensor-factor permutations. -/
theorem average_fixed_iff {A k n : ℕ}
    (x : Superoperator n (tensorPowerDimension A k)) :
    Superoperator.comp (symmetricAverage A k) x = x ↔
      ∀ σ : Equiv.Perm (Fin k),
        Superoperator.comp (factorPermutation A k σ) x = x := by
  constructor
  · intro havg σ
    rw [← havg, Superoperator.comp_assoc,
      factorPermutation_comp_symmetricAverage, havg]
  · intro hinv
    exact average_val { val := x, invariant := hinv }

instance instZeroSymmetricElement (A k n : ℕ) : Zero (SymmetricElement A k n) where
  zero :=
    { val := 0
      invariant := fun _σ => Superoperator.comp_zero_right _ }

@[simp]
theorem zero_val (A k n : ℕ) :
    (0 : SymmetricElement A k n).val = 0 :=
  rfl

/-- A symmetric element is unchanged when a homogeneous split is followed
by the genuine tensor-factor braiding. -/
theorem split_braiding {A p q n : ℕ}
    (x : SymmetricElement A (p + q) n) :
    Superoperator.comp
        (Superoperator.ofEquivalence (homogeneousBraidingEquiv A p q))
        (Superoperator.comp
          (Superoperator.ofEquivalence (tensorSplitEquiv A p q)) x.val) =
      Superoperator.comp
        (Superoperator.ofEquivalence
          (oppositeTensorSplitEquiv A p q)) x.val := by
  rw [Superoperator.comp_assoc, Superoperator.ofEquivalence_comp,
    tensorSplitEquiv_braiding]
  change
    Superoperator.comp
        (Superoperator.ofEquivalence
          ((factorPermutationEquiv A (p + q) (blockPermutation p q)).trans
            (oppositeTensorSplitEquiv A p q))) x.val =
      _
  rw [← Superoperator.ofEquivalence_comp,
    ← Superoperator.comp_assoc]
  change
    Superoperator.comp
        (Superoperator.ofEquivalence (oppositeTensorSplitEquiv A p q))
        (Superoperator.comp
          (factorPermutation A (p + q) (blockPermutation p q)) x.val) =
      _
  rw [x.invariant]

/-- Transporting a symmetric element's degree is implemented on its
underlying superoperator by the corresponding finite-basis cast channel. -/
theorem val_degreeCast {A n a b : ℕ} (h : a = b)
    (x : SymmetricElement A a n) :
    Superoperator.comp
        (Superoperator.ofEquivalence
          (finCongr (congrArg (tensorPowerDimension A) h))) x.val =
      (h ▸ x).val := by
  subst b
  simp

/-- Dependent evaluation of a family of symmetric coefficients commutes
with transport of the degree. -/
theorem family_degreeCast {A n a b : ℕ}
    (x : ∀ k, SymmetricElement A k n) (h : a = b) :
    h ▸ x a = x b := by
  subst b
  rfl

/-- Degree-zero contraction followed by the left unitor is the original
coefficient. -/
theorem left_counit {A n q : ℕ}
    (x : ∀ k, SymmetricElement A k n) :
    Superoperator.comp
        (Superoperator.ofEquivalence (homogeneousLeftUnitorEquiv A q))
        (Superoperator.comp
          (Superoperator.ofEquivalence (tensorSplitEquiv A 0 q))
          (x (0 + q)).val) =
      (x q).val := by
  rw [Superoperator.comp_assoc, Superoperator.ofEquivalence_comp]
  have he :
      (tensorSplitEquiv A 0 q).trans
          (homogeneousLeftUnitorEquiv A q) =
        finCongr
          (congrArg (tensorPowerDimension A) (Nat.zero_add q)) := by
    unfold homogeneousLeftUnitorEquiv
    rw [← Equiv.trans_assoc, Equiv.self_trans_symm,
      Equiv.refl_trans]
  rw [he]
  calc
    Superoperator.comp
        (Superoperator.ofEquivalence
          (finCongr
            (congrArg (tensorPowerDimension A) (Nat.zero_add q))))
        (x (0 + q)).val =
        ((Nat.zero_add q) ▸ x (0 + q)).val :=
      val_degreeCast (Nat.zero_add q) (x (0 + q))
    _ = (x q).val :=
      congrArg SymmetricElement.val
        (family_degreeCast x (Nat.zero_add q))

/-- Degree-zero contraction followed by the right unitor is the original
coefficient. -/
theorem right_counit {A n p : ℕ}
    (x : ∀ k, SymmetricElement A k n) :
    Superoperator.comp
        (Superoperator.ofEquivalence (homogeneousRightUnitorEquiv A p))
        (Superoperator.comp
          (Superoperator.ofEquivalence (tensorSplitEquiv A p 0))
          (x (p + 0)).val) =
      (x p).val := by
  rw [Superoperator.comp_assoc, Superoperator.ofEquivalence_comp]
  have he :
      (tensorSplitEquiv A p 0).trans
          (homogeneousRightUnitorEquiv A p) =
        finCongr
          (congrArg (tensorPowerDimension A) (Nat.add_zero p)) := by
    unfold homogeneousRightUnitorEquiv
    rw [← Equiv.trans_assoc, Equiv.self_trans_symm,
      Equiv.refl_trans]
  rw [he]
  calc
    Superoperator.comp
        (Superoperator.ofEquivalence
          (finCongr
            (congrArg (tensorPowerDimension A) (Nat.add_zero p))))
        (x (p + 0)).val =
        ((Nat.add_zero p) ▸ x (p + 0)).val :=
      val_degreeCast (Nat.add_zero p) (x (p + 0))
    _ = (x p).val :=
      congrArg SymmetricElement.val
        (family_degreeCast x (Nat.add_zero p))

/-- The two coefficientwise iterates of contraction agree after the
canonical associativity transport. -/
theorem contraction_coassociative {A n p q r : ℕ}
    (x : ∀ k, SymmetricElement A k n) :
    Superoperator.comp
        (Superoperator.ofEquivalence
          (contractionLeftRefinementEquiv A p q r))
        (Superoperator.comp
          (Superoperator.ofEquivalence
            (tensorSplitEquiv A (p + q) r))
          (x ((p + q) + r)).val) =
      Superoperator.comp
        (Superoperator.ofEquivalence
          (contractionRightRefinementEquiv A p q r))
        (Superoperator.comp
          (Superoperator.ofEquivalence
            (tensorSplitEquiv A p (q + r)))
          (x (p + (q + r))).val) := by
  rw [Superoperator.comp_assoc, Superoperator.ofEquivalence_comp]
  have hleft :
      (tensorSplitEquiv A (p + q) r).trans
          (contractionLeftRefinementEquiv A p q r) =
        tensorTripleSplitEquiv A p q r := by
    unfold contractionLeftRefinementEquiv
    rw [← Equiv.trans_assoc, Equiv.self_trans_symm,
      Equiv.refl_trans]
  rw [hleft]
  rw [Superoperator.comp_assoc, Superoperator.ofEquivalence_comp]
  have hright :
      (tensorSplitEquiv A p (q + r)).trans
          (contractionRightRefinementEquiv A p q r) =
        (finCongr (congrArg (tensorPowerDimension A)
          (Nat.add_assoc p q r).symm)).trans
            (tensorTripleSplitEquiv A p q r) := by
    unfold contractionRightRefinementEquiv
    rw [← Equiv.trans_assoc, Equiv.self_trans_symm,
      Equiv.refl_trans]
  rw [hright, ← Superoperator.ofEquivalence_comp,
    ← Superoperator.comp_assoc]
  apply congrArg (fun z =>
    Superoperator.comp
      (Superoperator.ofEquivalence
        (tensorTripleSplitEquiv A p q r)) z)
  let h : p + (q + r) = (p + q) + r :=
    (Nat.add_assoc p q r).symm
  calc
    (x ((p + q) + r)).val =
        (h ▸ x (p + (q + r))).val :=
      (congrArg SymmetricElement.val
        (family_degreeCast x h)).symm
    _ = Superoperator.comp
          (Superoperator.ofEquivalence
            (finCongr (congrArg (tensorPowerDimension A) h)))
          (x (p + (q + r))).val :=
      (val_degreeCast h (x (p + (q + r)))).symm

/-- Pointwise application of a basis equivalence preserves symmetric
invariants. -/
noncomputable def mapEquivalence {A B k n : ℕ}
    (e : Fin A ≃ Fin B) (x : SymmetricElement A k n) :
    SymmetricElement B k n where
  val := Superoperator.comp
    (Superoperator.ofEquivalence (tensorTupleMapEquiv e k)) x.val
  invariant := by
    intro σ
    rw [Superoperator.comp_assoc]
    change
      Superoperator.comp
          (Superoperator.comp
            (Superoperator.ofEquivalence
              (factorPermutationEquiv B k σ))
            (Superoperator.ofEquivalence (tensorTupleMapEquiv e k)))
          x.val =
        _
    rw [Superoperator.ofEquivalence_comp,
      tensorTupleMapEquiv_permutation]
    rw [← Superoperator.ofEquivalence_comp,
      ← Superoperator.comp_assoc]
    change
      Superoperator.comp
          (Superoperator.ofEquivalence (tensorTupleMapEquiv e k))
          (Superoperator.comp (factorPermutation A k σ) x.val) =
        _
    rw [x.invariant]

end SymmetricElement

end SuperoperatorModule

end QLambda.Domain.Presheaf
