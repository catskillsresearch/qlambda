/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitChannels

/-!
# Classical bit coassociativity (Choi)
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000
open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators

theorem bitCopy_comp_dephase_choi
    (a b : Fin 4) (i j : Fin 2) :
    (Superoperator.comp bitCopySuperoperator
      bitDephaseSuperoperator).cp.choi (a, i) (b, j) =
      if i = j ∧ a.val = i.val * 3 ∧ b.val = j.val * 3 then 1 else 0 := by
  have h00 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 0)).1 =
        false := by decide
  have h01 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 1)).1 =
        true := by decide
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [Superoperator.cp_comp, CPMap.choi_comp_apply,
      bitCopySuperoperator, Superoperator.cp_ofIsometry,
      CPMap.choi_ofKraus, bitDephaseSuperoperator,
      CPMap.choi_add, Matrix.add_apply,
      Instrument.measure_branch_zero, Instrument.measure_branch_one,
      classicalCopyMatrix, KrausFamily.choiTerm,
      Matrix.conjTranspose_apply,
      Composer.projector, Composer.onWire, Composer.registerSplit,
      Composer.proj₂, CQ.QDim, h00, h01]

/-- Pair-form of the copy∘dephase Choi formula, for rewriting under tensor. -/
theorem bitCopy_comp_dephase_raw_choi_pair
    (p q : Fin 4 × Fin 2) :
    (bitCopySuperoperator.cp.comp bitDephaseSuperoperator.cp).choi p q =
      if p.2 = q.2 ∧ p.1.val = p.2.val * 3 ∧ q.1.val = q.2.val * 3 then
        (1 : ℂ) else 0 := by
  rcases p with ⟨a, i⟩
  rcases q with ⟨b, j⟩
  simpa only [← Superoperator.cp_comp] using
    bitCopy_comp_dephase_choi a b i j

theorem identity_choi_pair (n : ℕ) (p q : Fin n × Fin n) :
    (CPMap.identity n).choi p q =
      if p.1 = p.2 ∧ q.1 = q.2 then (1 : ℂ) else 0 := by
  rcases p with ⟨a, i⟩
  rcases q with ⟨b, j⟩
  simp [CPMap.identity, CPMap.choi_ofKraus, KrausFamily.identity,
    KrausFamily.choiTerm, Matrix.one_apply]
  split_ifs <;> simp_all

/-- The `2 ⊗ 2 ⊗ 2` associator is the identity on the shared `Fin 8` encoding. -/
theorem tensorAssociatorEquiv_two_two_two :
    Superoperator.tensorAssociatorEquiv 2 2 2 =
      Equiv.refl (Fin ((2 * 2) * 2)) := by
  ext x
  fin_cases x <;> decide

theorem tensorAssociator_two_two_two :
    Superoperator.tensorAssociator 2 2 2 =
      Superoperator.identity ((2 * 2) * 2) := by
  simp only [Superoperator.tensorAssociator, tensorAssociatorEquiv_two_two_two,
    Superoperator.ofEquivalence_refl]

/-- Left parenthesization of classical copy-after-dephase, before reassociation. -/
noncomputable def bitCoassocLeftPre : Superoperator 2 8 :=
  Superoperator.comp
    (Superoperator.tensor
      (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator)
      (Superoperator.identity 2))
    bitCopySuperoperator

/-- Left coassociativity composite, including the Day/tensor associator. -/
noncomputable def bitCoassocLeft : Superoperator 2 8 :=
  Superoperator.comp (Superoperator.tensorAssociator 2 2 2)
    bitCoassocLeftPre

/-- Right coassociativity composite. -/
noncomputable def bitCoassocRight : Superoperator 2 8 :=
  Superoperator.comp
    (Superoperator.tensor
      (Superoperator.identity 2)
      (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator))
    bitCopySuperoperator

theorem bitCoassocLeft_eq_pre :
    bitCoassocLeft = bitCoassocLeftPre := by
  simp only [bitCoassocLeft, tensorAssociator_two_two_two,
    Superoperator.identity_comp]

private theorem sum_fin4_coassoc (f : Fin 4 → ℂ) :
    (∑ x : Fin 4, f x) = f 0 + f 1 + f 2 + f 3 := by
  rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  simp [Finset.sum_insert]
  ring

/-- Closed Choi form of the right coassociativity composite. -/
theorem bitCoassocRight_choi
    (a b : Fin 8) (i j : Fin 2) :
    bitCoassocRight.cp.choi (a, i) (b, j) =
      if i = j ∧ a.val = i.val * 7 ∧ b.val = j.val * 7 then (1 : ℂ) else 0 := by
  simp only [bitCoassocRight, Superoperator.cp_comp, CPMap.choi_comp_apply,
    Superoperator.cp_tensor, CPMap.choi_tensor,
    Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Superoperator.identity]
  simp_rw [bitCopy_comp_dephase_raw_choi_pair, identity_choi_pair]
  simp only [bitCopySuperoperator, Superoperator.cp_ofIsometry,
    CPMap.choi_ofKraus, KrausFamily.choiTerm, classicalCopyMatrix,
    Matrix.conjTranspose_apply, CPMap.choiTensorEquiv, finProdFinEquiv,
    Fin.divNat, Fin.modNat]
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j
  all_goals
    simp [sum_fin4_coassoc, KrausFamily.choiTerm, classicalCopyMatrix,
      Matrix.conjTranspose_apply]
  all_goals norm_num

/-- Closed Choi form of the left coassociativity composite (sans identity associator). -/
theorem bitCoassocLeftPre_choi
    (a b : Fin 8) (i j : Fin 2) :
    bitCoassocLeftPre.cp.choi (a, i) (b, j) =
      if i = j ∧ a.val = i.val * 7 ∧ b.val = j.val * 7 then (1 : ℂ) else 0 := by
  simp only [bitCoassocLeftPre, Superoperator.cp_comp, CPMap.choi_comp_apply,
    Superoperator.cp_tensor, CPMap.choi_tensor,
    Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Superoperator.identity]
  simp_rw [bitCopy_comp_dephase_raw_choi_pair, identity_choi_pair]
  simp only [bitCopySuperoperator, Superoperator.cp_ofIsometry,
    CPMap.choi_ofKraus, KrausFamily.choiTerm, classicalCopyMatrix,
    Matrix.conjTranspose_apply, CPMap.choiTensorEquiv, finProdFinEquiv,
    Fin.divNat, Fin.modNat]
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j
  all_goals
    simp [sum_fin4_coassoc, KrausFamily.choiTerm, classicalCopyMatrix,
      Matrix.conjTranspose_apply]
  all_goals norm_num

/-- Classical copy-after-dephase is coassociative. -/
theorem bitCoassocLeft_eq_right :
    bitCoassocLeft = bitCoassocRight := by
  rw [bitCoassocLeft_eq_pre]
  apply Superoperator.ext
  apply CPMap.ext
  ext ai bj
  rcases ai with ⟨a, i⟩
  rcases bj with ⟨b, j⟩
  rw [bitCoassocLeftPre_choi, bitCoassocRight_choi]



end QLambda.Linear
