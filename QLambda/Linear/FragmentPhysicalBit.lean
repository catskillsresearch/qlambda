/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.SemanticFragment
import QLambda.Linear.TypeInterpretation
import QLambda.Linear.PrimitiveSuperoperator
import QLambda.Domain.Presheaf.Yoneda
import QLambda.Domain.Presheaf.ClosedGeneration
import QLambda.Domain.Presheaf.DayInternalHom
import QLambda.Domain.Presheaf.SuperoperatorModule

/-!
# Physical bit copy/discard boundary

Representable-bit copy, dephasing, and the Route A no-go for counital
copy/discard on `representable 2`.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000
open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators

/-- Classical-bit discard `Bit → I` (Yoneda of `discardTwo`). -/
noncomputable def bitDiscard :
    Hom (representable 2) dayTensorUnit :=
  yonedaMap SigmaMon.ChoiSum.discardTwo

/-- Isometric classical copy embedding `|i⟩ ↦ |ii⟩` (`0 ↦ 0`, `1 ↦ 3`). -/
noncomputable def classicalCopyMatrix : Matrix (Fin 4) (Fin 2) ℂ :=
  fun pq j => if pq.val = j.val * 3 then 1 else 0

private theorem sum_fin4 (f : Fin 4 → ℂ) :
    (∑ x : Fin 4, f x) = f 0 + f 1 + f 2 + f 3 := by
  have huniv : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by
    decide
  rw [huniv]
  simp [Finset.sum_insert]
  abel

theorem classicalCopyMatrix_isometry :
    classicalCopyMatrix.conjTranspose * classicalCopyMatrix =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, classicalCopyMatrix,
      Matrix.one_apply]
    rw [sum_fin4]; simp
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, classicalCopyMatrix,
      Matrix.one_apply]
    rw [sum_fin4]; simp
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, classicalCopyMatrix,
      Matrix.one_apply]
    rw [sum_fin4]; simp
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, classicalCopyMatrix,
      Matrix.one_apply]
    rw [sum_fin4]; simp

/-- Classical-bit copy as an isometric superoperator `2 → 4`. -/
noncomputable def bitCopySuperoperator : Superoperator 2 4 :=
  Superoperator.ofIsometry classicalCopyMatrix classicalCopyMatrix_isometry

/-- Classical-bit copy into the representable tensor square. -/
noncomputable def bitCopy :
    Hom (representable 2) (dayTensorRepresentable 2 2) :=
  yonedaMap bitCopySuperoperator

/-- Computational-basis dephasing, i.e. the channel obtained by copying a
bit in the chosen basis and discarding either output.  This is the decisive
boundary for using `representable 2` as a classical comonoid: coherent
off-diagonal inputs are erased. -/
noncomputable def bitDephaseSuperoperator : Superoperator 2 2 where
  cp := (Instrument.measure (0 : Fin 1)).branch 0 +
    (Instrument.measure (0 : Fin 1)).branch 1
  trace_nonincreasing := by
    intro ρ hρ
    rw [CPMap.applyMat_add_map, Matrix.trace_add, Complex.add_re]
    have h := (Instrument.measure (0 : Fin 1)).trace_nonincreasing ρ hρ
    simpa only [Fin.sum_univ_two, Instrument.measure,
      Instrument.ofQuantumInstrument, CPMap.applyMat_ofKraus,
      KrausFamily.applyMat_single, Composer.projector_conjTranspose] using h

/-- The classical-basis copy/discard composite is not the identity on the
full quantum representable `y(2)`: it removes the `|0⟩⟨1|` coherence. -/
theorem bitDephaseSuperoperator_ne_identity :
    bitDephaseSuperoperator ≠ Superoperator.identity 2 := by
  intro h
  have happ := congrArg (fun f : Superoperator 2 2 =>
    f.cp.applyMat (KrausFamily.matrixUnit 0 1)) h
  have he := congrFun (congrFun happ 0) 1
  simp only [bitDephaseSuperoperator, CPMap.applyMat_add_map,
    Instrument.measure_branch_zero, Instrument.measure_branch_one,
    CPMap.applyMat_ofKraus, Superoperator.identity,
    CPMap.applyMat_identity] at he
  have h00 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 0)).1 =
        false := by decide
  have h01 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 1)).1 =
        true := by decide
  norm_num [KrausFamily.applyMat, Composer.projector,
    KrausFamily.matrixUnit, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Composer.onWire, Composer.registerSplit, Composer.proj₂, CQ.QDim,
    h00, h01] at he

/-- The current Route-A `representable 2` carrier cannot itself satisfy the
classical-bit copy/delete equations.  A diagonal/fixed-point carrier (or
another genuinely classical carrier) is required before open unrestricted
contexts can be interpreted soundly. -/
theorem representable_bit_copy_delete_no_go :
    bitDephaseSuperoperator ≠ Superoperator.identity 2 :=
  bitDephaseSuperoperator_ne_identity

private theorem sum_fin4_complex (f : Fin 4 → ℂ) :
    (∑ x : Fin 4, f x) = f 0 + f 1 + f 2 + f 3 := by
  rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  simp [Finset.sum_insert]
  ring

/-- The left discard-after-copy composite on the physical bit carrier. -/
noncomputable def bitLeftCounitSuperoperator : Superoperator 2 2 :=
  Superoperator.comp (Superoperator.tensorLeftUnitor 2)
    (Superoperator.comp
      (Superoperator.tensor SigmaMon.ChoiSum.discardTwo
        (Superoperator.identity 2))
      bitCopySuperoperator)

/-- The right discard-after-copy composite on the physical bit carrier. -/
noncomputable def bitRightCounitSuperoperator : Superoperator 2 2 :=
  Superoperator.comp (Superoperator.tensorRightUnitor 2)
    (Superoperator.comp
      (Superoperator.tensor (Superoperator.identity 2)
        SigmaMon.ChoiSum.discardTwo)
      bitCopySuperoperator)

theorem bitLeftCounitSuperoperator_eq_dephase :
    bitLeftCounitSuperoperator = bitDephaseSuperoperator := by
  apply Superoperator.ext
  apply CPMap.ext
  ext ai bj
  rcases ai with ⟨a, i⟩
  rcases bj with ⟨b, j⟩
  unfold bitLeftCounitSuperoperator
  rw [show Superoperator.tensorLeftUnitor 2 =
      Superoperator.ofEquivalence (Superoperator.tensorLeftUnitorEquiv 2)
    from rfl]
  rw [Superoperator.choi_comp_ofEquivalence_left]
  have h00 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 0)).1 =
        false := by decide
  have h01 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 1)).1 =
        true := by decide
  fin_cases a <;> fin_cases i <;> fin_cases b <;> fin_cases j
  all_goals
    simp only [Superoperator.cp_comp, CPMap.choi_comp_apply,
      Superoperator.cp_tensor, bitCopySuperoperator,
      Superoperator.cp_ofIsometry, CPMap.choi_tensor,
      Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply, bitDephaseSuperoperator,
      CPMap.choi_add, Matrix.add_apply, CPMap.choi_ofKraus,
      Instrument.measure_branch_zero, Instrument.measure_branch_one]
  all_goals
    norm_num [CPMap.choiTensorEquiv, classicalCopyMatrix,
      finProdFinEquiv, finOneEquiv, Equiv.punitProd,
      Fin.divNat, Fin.modNat,
      SigmaMon.ChoiSum.discardTwo, SigmaMon.ChoiSum.basisBra,
      Superoperator.identity, CPMap.identity,
      KrausFamily.choi, KrausFamily.choiTerm, KrausFamily.identity,
      Matrix.one_apply, h00, h01,
      Superoperator.tensorLeftUnitorEquiv,
      Composer.projector, Composer.onWire, Composer.registerSplit,
      Composer.proj₂, CQ.QDim]
  all_goals simp [sum_fin4_complex]

theorem bitRightCounitSuperoperator_eq_dephase :
    bitRightCounitSuperoperator = bitDephaseSuperoperator := by
  apply Superoperator.ext
  apply CPMap.ext
  ext ai bj
  rcases ai with ⟨a, i⟩
  rcases bj with ⟨b, j⟩
  unfold bitRightCounitSuperoperator
  rw [show Superoperator.tensorRightUnitor 2 =
      Superoperator.ofEquivalence (Superoperator.tensorRightUnitorEquiv 2)
    from rfl]
  rw [Superoperator.choi_comp_ofEquivalence_left]
  have h00 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 0)).1 =
        false := by decide
  have h01 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 1)).1 =
        true := by decide
  fin_cases a <;> fin_cases i <;> fin_cases b <;> fin_cases j
  all_goals
    simp only [Superoperator.cp_comp, CPMap.choi_comp_apply,
      Superoperator.cp_tensor, bitCopySuperoperator,
      Superoperator.cp_ofIsometry, CPMap.choi_tensor,
      Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply, bitDephaseSuperoperator,
      CPMap.choi_add, Matrix.add_apply, CPMap.choi_ofKraus,
      Instrument.measure_branch_zero, Instrument.measure_branch_one]
  all_goals
    norm_num [CPMap.choiTensorEquiv, classicalCopyMatrix,
      finProdFinEquiv, finOneEquiv, Equiv.prodPUnit,
      Fin.divNat, Fin.modNat,
      SigmaMon.ChoiSum.discardTwo, SigmaMon.ChoiSum.basisBra,
      Superoperator.identity, CPMap.identity,
      KrausFamily.choi, KrausFamily.choiTerm, KrausFamily.identity,
      Matrix.one_apply, h00, h01,
      Superoperator.tensorRightUnitorEquiv,
      Composer.projector, Composer.onWire, Composer.registerSplit,
      Composer.proj₂, CQ.QDim]
  all_goals simp [sum_fin4_complex]

/-- Both concrete physical-bit counit composites fail: each is dephasing,
not identity. -/
theorem concrete_bit_copy_discard_not_counital :
    bitLeftCounitSuperoperator ≠ Superoperator.identity 2 ∧
    bitRightCounitSuperoperator ≠ Superoperator.identity 2 := by
  constructor
  · rw [bitLeftCounitSuperoperator_eq_dephase]
    exact bitDephaseSuperoperator_ne_identity
  · rw [bitRightCounitSuperoperator_eq_dephase]
    exact bitDephaseSuperoperator_ne_identity

/-- The physical copy transported from the representable tensor presentation
to the genuine coend Day tensor. -/
noncomputable def physicalBitCopyDay :
    Hom (representable 2)
      (dayTensor (representable 2) (representable 2)) :=
  Hom.comp (dayTensorRepresentableIso 2 2).inv bitCopy

/-- Left counit composite for the concrete physical-bit copy. -/
noncomputable def physicalBitLeftCounit :
    Hom (representable 2) (representable 2) :=
  Hom.comp (DayTensor.leftUnitor (representable 2))
    (Hom.comp
      (DayTensor.map bitDiscard (Hom.id (representable 2)))
      physicalBitCopyDay)

private theorem physicalBitCopyDay_app_identity :
    physicalBitCopyDay.app 2 (Superoperator.identity 2) =
      (dayTensor (representable 2) (representable 2)).act
        ((DayCoend.intro (representable 2) (representable 2)).app
          (Superoperator.identity 2) (Superoperator.identity 2))
        bitCopySuperoperator := by
  let e := dayTensorRepresentableIso 2 2
  have hpres :=
    ((dayTensorRepresentablePresentation 2 2).universal
      (dayTensorPresentation
        (representable 2) (representable 2)).object).apply_symm_apply
      (dayTensorPresentation (representable 2) (representable 2)).intro
  rw [(dayTensorRepresentablePresentation 2 2).universal_apply] at hpres
  have hbase := congrArg
    (fun b : Bilinear (representable 2) (representable 2)
        (dayTensor (representable 2) (representable 2)) =>
      b.app (Superoperator.identity 2) (Superoperator.identity 2)) hpres
  dsimp only [Bilinear.postcomp] at hbase
  change
    (((dayTensorRepresentablePresentation 2 2).universal
      (dayTensorPresentation
        (representable 2) (representable 2)).object).symm
      (dayTensorPresentation
        (representable 2) (representable 2)).intro).app 4
        (Superoperator.tensor (Superoperator.identity 2)
          (Superoperator.identity 2)) =
      (DayCoend.intro (representable 2) (representable 2)).app
        (Superoperator.identity 2) (Superoperator.identity 2) at hbase
  rw [Superoperator.tensor_identity] at hbase
  change e.inv.app 4 (Superoperator.identity 4) =
    (DayCoend.intro (representable 2) (representable 2)).app
      (Superoperator.identity 2) (Superoperator.identity 2) at hbase
  have hnat := e.inv.naturality
    (Superoperator.identity 4) bitCopySuperoperator
  simp only [representable_act, Superoperator.identity_comp] at hnat
  change e.inv.app 2 bitCopySuperoperator =
    (dayTensor (representable 2) (representable 2)).act
      (e.inv.app 4 (Superoperator.identity 4)) bitCopySuperoperator at hnat
  unfold physicalBitCopyDay bitCopy
  change (dayTensorRepresentableIso 2 2).inv.app 2
      ((yonedaMap bitCopySuperoperator).app 2
        (Superoperator.identity 2)) = _
  rw [yonedaMap_app, Superoperator.comp_identity]
  rw [hnat, hbase]

theorem physicalBitLeftCounit_app_identity :
    physicalBitLeftCounit.app 2 (Superoperator.identity 2) =
      bitLeftCounitSuperoperator := by
  unfold physicalBitLeftCounit
  change (DayTensor.leftUnitor (representable 2)).app 2
      ((DayTensor.map bitDiscard
        (Hom.id (representable 2))).app 2
        (physicalBitCopyDay.app 2 (Superoperator.identity 2))) =
    bitLeftCounitSuperoperator
  rw [physicalBitCopyDay_app_identity]
  rw [(DayTensor.map bitDiscard
    (Hom.id (representable 2))).naturality]
  have hmap := DayTensor.map_intro bitDiscard
    (Hom.id (representable 2))
    (Superoperator.identity 2) (Superoperator.identity 2)
  rw [hmap]
  have hdiscard :
      bitDiscard.app 2 (Superoperator.identity 2) =
        SigmaMon.ChoiSum.discardTwo := by
    unfold bitDiscard
    rw [yonedaMap_app, Superoperator.comp_identity]
  have hid :
      (Hom.id (representable 2)).app 2
          (Superoperator.identity 2) =
        Superoperator.identity 2 := by
    rfl
  rw [hdiscard, hid]
  rw [(DayTensor.leftUnitor (representable 2)).naturality]
  have hleft := DayTensor.leftUnitor_intro
    (M := representable 2)
    SigmaMon.ChoiSum.discardTwo
    (Superoperator.identity 2)
  rw [hleft]
  unfold bitLeftCounitSuperoperator
  simp only [representable_act, Superoperator.identity_comp]
  exact (Superoperator.comp_assoc _ _ _).symm

theorem physicalBitLeftCounit_eq_dephase :
    physicalBitLeftCounit = yonedaMap bitDephaseSuperoperator := by
  apply (yonedaEquiv (representable 2) 2).injective
  change physicalBitLeftCounit.app 2 (Superoperator.identity 2) =
    (yonedaMap bitDephaseSuperoperator).app 2
      (Superoperator.identity 2)
  rw [physicalBitLeftCounit_app_identity, yonedaMap_app,
    Superoperator.comp_identity, bitLeftCounitSuperoperator_eq_dephase]

/-- Exact F2 boundary: the stated copy/discard maps on `representable 2`
violate the left counit equation in the genuine Day tensor. -/
theorem physical_bit_copy_discard_not_left_counital :
    physicalBitLeftCounit ≠ Hom.id (representable 2) := by
  intro h
  have happ := congrArg
    (fun f : Hom (representable 2) (representable 2) =>
      f.app 2 (Superoperator.identity 2)) h
  rw [physicalBitLeftCounit_app_identity] at happ
  change bitLeftCounitSuperoperator =
    Superoperator.identity 2 at happ
  rw [bitLeftCounitSuperoperator_eq_dephase] at happ
  exact bitDephaseSuperoperator_ne_identity happ

/-- Computational-basis dephasing is idempotent. -/
theorem bitDephaseSuperoperator_idempotent :
    Superoperator.comp bitDephaseSuperoperator bitDephaseSuperoperator =
      bitDephaseSuperoperator := by
  apply Superoperator.ext
  apply CPMap.ext_apply
  intro ρ
  rw [Superoperator.cp_comp, CPMap.applyMat_comp]
  have h00 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 0)).1 =
        false := by decide
  have h01 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 1)).1 =
        true := by decide
  ext a b
  fin_cases a <;> fin_cases b
  all_goals
    simp [bitDephaseSuperoperator, CPMap.applyMat_add_map,
      Instrument.measure_branch_zero, Instrument.measure_branch_one,
      CPMap.applyMat_ofKraus, KrausFamily.applyMat,
      Composer.projector, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Composer.onWire, Composer.registerSplit, Composer.proj₂, CQ.QDim,
      h00, h01]

/-- Maps into a classical bit are precisely the maps fixed by computational
basis dephasing.  This separates unrestricted classical data from the
physical qubit carrier `representable 2`. -/
abbrev ClassicalBitCarrier (n : ℕ) := {x : Superoperator n 2 //
  Superoperator.comp bitDephaseSuperoperator x = x}
end QLambda.Linear
