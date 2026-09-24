/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitModule

/-!
# Classical bit channel counit and cocommutativity lemmas
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators

/-- Swapping the two outputs of computational-basis copy changes nothing. -/
noncomputable def bitCocommutativityLeft : Superoperator 2 4 :=
  Superoperator.comp (Superoperator.tensorSwap 2 2) bitCopySuperoperator

theorem bitCocommutativityLeft_eq_copy :
    bitCocommutativityLeft = bitCopySuperoperator := by
  apply Superoperator.ext
  apply CPMap.ext
  ext ai bj
  rcases ai with ⟨a, i⟩
  rcases bj with ⟨b, j⟩
  unfold bitCocommutativityLeft
  rw [show Superoperator.tensorSwap 2 2 =
      Superoperator.ofEquivalence (Superoperator.tensorSwapEquiv 2 2)
    from rfl]
  rw [Superoperator.choi_comp_ofEquivalence_left]
  fin_cases a <;> fin_cases i <;> fin_cases b <;> fin_cases j <;>
    norm_num [bitCopySuperoperator, Superoperator.cp_ofIsometry,
      CPMap.choi_ofKraus, classicalCopyMatrix,
      KrausFamily.choiTerm, Matrix.conjTranspose_apply,
      Superoperator.tensorSwapEquiv, finProdFinEquiv,
      Fin.divNat, Fin.modNat]

/-- Discard is insensitive to computational-basis dephasing. -/
theorem bitDiscard_comp_dephase :
    Superoperator.comp SigmaMon.ChoiSum.discardTwo
      bitDephaseSuperoperator =
    SigmaMon.ChoiSum.discardTwo := by
  apply Superoperator.ext
  apply CPMap.ext_apply
  intro ρ
  ext a b
  fin_cases a
  fin_cases b
  have h00 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 0)).1 =
        false := by decide
  have h01 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 1)).1 =
        true := by decide
  simp [Superoperator.cp_comp, CPMap.applyMat_comp,
    bitDephaseSuperoperator, CPMap.applyMat_add_map,
    Instrument.measure_branch_zero, Instrument.measure_branch_one,
    CPMap.applyMat_ofKraus, KrausFamily.applyMat,
    SigmaMon.ChoiSum.discardTwo, SigmaMon.ChoiSum.basisBra,
    Composer.projector, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Composer.onWire, Composer.registerSplit, Composer.proj₂, CQ.QDim,
    h00, h01]

/-- Left discard-after-copy is identity after restricting to classical bits. -/
theorem bitClassicalLeftCounitChannel :
    Superoperator.comp bitDephaseSuperoperator
      (Superoperator.comp (Superoperator.tensorLeftUnitor 2)
        (Superoperator.comp
          (Superoperator.tensor
            (Superoperator.comp SigmaMon.ChoiSum.discardTwo
              bitDephaseSuperoperator)
            (Superoperator.identity 2))
          bitCopySuperoperator)) =
      bitDephaseSuperoperator := by
  rw [bitDiscard_comp_dephase]
  change Superoperator.comp bitDephaseSuperoperator
    bitLeftCounitSuperoperator = bitDephaseSuperoperator
  rw [bitLeftCounitSuperoperator_eq_dephase]
  exact bitDephaseSuperoperator_idempotent

/-- Right discard-after-copy is identity after restricting to classical bits. -/
theorem bitClassicalRightCounitChannel :
    Superoperator.comp bitDephaseSuperoperator
      (Superoperator.comp (Superoperator.tensorRightUnitor 2)
        (Superoperator.comp
          (Superoperator.tensor (Superoperator.identity 2)
            (Superoperator.comp SigmaMon.ChoiSum.discardTwo
              bitDephaseSuperoperator))
          bitCopySuperoperator)) =
      bitDephaseSuperoperator := by
  rw [bitDiscard_comp_dephase]
  change Superoperator.comp bitDephaseSuperoperator
    bitRightCounitSuperoperator = bitDephaseSuperoperator
  rw [bitRightCounitSuperoperator_eq_dephase]
  exact bitDephaseSuperoperator_idempotent


end QLambda.Linear
