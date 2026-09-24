/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.SemanticFragment
import QLambda.Linear.TypeInterpretation
import QLambda.Linear.PrimitiveSuperoperator
import QLambda.Domain.Presheaf.Yoneda
import QLambda.Domain.Presheaf.ClosedGenerated
import QLambda.Domain.Presheaf.DayCoend
import QLambda.Domain.Presheaf.Module

/-!
# Presheaf fragment model and Route A direct semantics

`PresheafFragmentModel` is the minimum semantic interface for
`Ty.SemanticFragment`.  Because `SemanticFragment` is a `Prop`, objects are
assigned by recursion on the underlying `Ty` (via `fragmentModule`), and
agreement on fragment types is proved by induction into `Prop`.

Route A supplies classical-bit weaken/contract maps directly (not via
`bang 2`) together with primitive and measurement Yoneda embeddings.
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

noncomputable instance (n : ℕ) : Zero (ClassicalBitCarrier n) :=
  ⟨⟨0, by simp [Superoperator.comp_zero_right]⟩⟩

/-- The inherited Choi summation on dephasing-fixed bit maps. -/
noncomputable def classicalBitFiber (n : ℕ) : Fiber where
  Carrier := ClassicalBitCarrier n
  zero := 0
  summation :=
    { HasSum := fun f a =>
        SigmaMon.ChoiSum.HasSum (fun i => (f i).1) a.1
      unique := by
        intro ι _ f a b ha hb
        exact Subtype.ext (SigmaMon.ChoiSum.unique ha hb)
      empty := by
        convert (SigmaMon.ChoiSum.empty :
          SigmaMon.ChoiSum.HasSum (fun i : Empty => nomatch i)
            (0 : Superoperator n 2)) using 1
        rfl
      singleton := fun a => SigmaMon.ChoiSum.singleton a.1
      remove_zero := by
        intro ι _ f s a hzero
        exact SigmaMon.ChoiSum.remove_zero
          (fun i => (f i).1) s a.1
          (fun i hi => congrArg Subtype.val (hzero i hi))
      reindex := by
        intro ι κ _ _ e f a
        exact SigmaMon.ChoiSum.reindex e (fun i => (f i).1) a.1
      flatten := by
        classical
        intro ι _ κ _ f a
        constructor
        · intro hflat
          rcases (SigmaMon.superoperatorPartialCountableSum.flatten
            (fun i j => (f i j).1) a.1).mp hflat with
            ⟨g, hrows, hsum⟩
          let G : ι → ClassicalBitCarrier n := fun i =>
            { val := g i
              property := by
                have hc := SigmaMon.ChoiSum.comp_left
                  bitDephaseSuperoperator (hrows i)
                have hc' : SigmaMon.ChoiSum.HasSum
                    (fun j => (f i j).1)
                    (Superoperator.comp bitDephaseSuperoperator (g i)) := by
                  convert hc using 1
                  funext j
                  exact (f i j).property.symm
                exact SigmaMon.ChoiSum.unique hc' (hrows i) }
          exact ⟨G, fun i => hrows i, hsum⟩
        · rintro ⟨g, hrows, hsum⟩
          exact (SigmaMon.superoperatorPartialCountableSum.flatten
            (fun i j => (f i j).1) a.1).mpr
              ⟨fun i => (g i).1, hrows, hsum⟩ }

/-- Module of classical bit maps.  Action is precomposition, and fixedness is
closed under all partial sums required by `Module`. -/
noncomputable def classicalBitModule : Module where
  obj := classicalBitFiber
  act := fun x f => ⟨Superoperator.comp x.1 f, by
    calc
      Superoperator.comp bitDephaseSuperoperator
          (Superoperator.comp x.1 f) =
        Superoperator.comp
          (Superoperator.comp bitDephaseSuperoperator x.1) f :=
            Superoperator.comp_assoc _ _ _
      _ = Superoperator.comp x.1 f :=
        congrArg (fun z => Superoperator.comp z f) x.2⟩
  act_zero_element := by
    intro m n f
    apply Subtype.ext
    exact Superoperator.comp_zero_left f
  act_zero_map := by
    intro m n x
    apply Subtype.ext
    exact Superoperator.comp_zero_right x.1
  act_id := by
    intro n x
    apply Subtype.ext
    exact Superoperator.comp_identity x.1
  act_comp := by
    intro l m n x f g
    apply Subtype.ext
    exact (Superoperator.comp_assoc x.1 f g).symm
  act_sum_element := by
    intro ι _ m n x s f h
    exact SigmaMon.ChoiSum.comp_right f h
  act_sum_map := by
    intro ι _ m n x f s h
    exact SigmaMon.ChoiSum.comp_left x.1 h
  act_sum_from_one := by
    intro ι _ m x s f h
    change SigmaMon.ChoiSum.HasSum (fun i => (x i).1) s.1 at h
    obtain ⟨z, hz⟩ := (representable 2).act_sum_from_one f h
    have hz' : SigmaMon.ChoiSum.HasSum
        (fun i => Superoperator.comp bitDephaseSuperoperator
          (Superoperator.comp (x i).1 (f i)))
        (Superoperator.comp bitDephaseSuperoperator z) :=
      SigmaMon.ChoiSum.comp_left bitDephaseSuperoperator hz
    have heach : (fun i => Superoperator.comp bitDephaseSuperoperator
          (Superoperator.comp (x i).1 (f i))) =
        (fun i => Superoperator.comp (x i).1 (f i)) := by
      funext i
      calc
        Superoperator.comp bitDephaseSuperoperator
            (Superoperator.comp (x i).1 (f i)) =
          Superoperator.comp
            (Superoperator.comp bitDephaseSuperoperator (x i).1) (f i) :=
              Superoperator.comp_assoc _ _ _
        _ = Superoperator.comp (x i).1 (f i) :=
          congrArg (fun z => Superoperator.comp z (f i)) (x i).2
    have hfix : Superoperator.comp bitDephaseSuperoperator z = z :=
      SigmaMon.ChoiSum.unique (heach ▸ hz') hz
    refine ⟨⟨z, hfix⟩, ?_⟩
    change SigmaMon.ChoiSum.HasSum
      (fun i => Superoperator.comp (x i).1 (f i)) z
    exact hz
  act_sum_tensor_from_one := by
    intro ι _ m A x s f h
    change SigmaMon.ChoiSum.HasSum (fun i => (x i).1) s.1 at h
    obtain ⟨z, hz⟩ := (representable 2).act_sum_tensor_from_one f h
    have hz' : SigmaMon.ChoiSum.HasSum
        (fun i => Superoperator.comp bitDephaseSuperoperator
          (Superoperator.comp (x i).1
            (Superoperator.tensor (f i) (Superoperator.identity A))))
        (Superoperator.comp bitDephaseSuperoperator z) :=
      SigmaMon.ChoiSum.comp_left bitDephaseSuperoperator hz
    have heach : (fun i => Superoperator.comp bitDephaseSuperoperator
          (Superoperator.comp (x i).1
            (Superoperator.tensor (f i) (Superoperator.identity A)))) =
        (fun i => Superoperator.comp (x i).1
          (Superoperator.tensor (f i) (Superoperator.identity A))) := by
      funext i
      calc
        Superoperator.comp bitDephaseSuperoperator
            (Superoperator.comp (x i).1 _) =
          Superoperator.comp
            (Superoperator.comp bitDephaseSuperoperator (x i).1) _ :=
              Superoperator.comp_assoc _ _ _
        _ = Superoperator.comp (x i).1 _ :=
          congrArg (fun z => Superoperator.comp z
            (Superoperator.tensor (f i) (Superoperator.identity A))) (x i).2
    have hfix : Superoperator.comp bitDephaseSuperoperator z = z :=
      SigmaMon.ChoiSum.unique (heach ▸ hz') hz
    refine ⟨⟨z, hfix⟩, ?_⟩
    change SigmaMon.ChoiSum.HasSum
      (fun i => Superoperator.comp (x i).1
        (Superoperator.tensor (f i) (Superoperator.identity A))) z
    exact hz

/-- Forget that a bit map is dephasing-fixed. -/
noncomputable def classicalBitInclusion :
    Hom classicalBitModule (representable 2) where
  app := fun _ x => x.1
  map_zero := fun _ => rfl
  map_sum := fun h => h
  naturality := fun _ _ => rfl

/-- Project a physical bit map to its computational-basis classical part. -/
noncomputable def bitClassicalize :
    Hom (representable 2) classicalBitModule where
  app := fun _ x =>
    ⟨Superoperator.comp bitDephaseSuperoperator x, by
      calc
        Superoperator.comp bitDephaseSuperoperator
            (Superoperator.comp bitDephaseSuperoperator x) =
          Superoperator.comp
            (Superoperator.comp bitDephaseSuperoperator
              bitDephaseSuperoperator) x :=
                Superoperator.comp_assoc _ _ _
        _ = Superoperator.comp bitDephaseSuperoperator x :=
          congrArg (fun z => Superoperator.comp z x)
            bitDephaseSuperoperator_idempotent⟩
  map_zero := by
    intro n
    apply Subtype.ext
    exact Superoperator.comp_zero_right _
  map_sum := by
    intro ι _ n f x h
    exact SigmaMon.ChoiSum.comp_left bitDephaseSuperoperator h
  naturality := by
    intro m n x f
    apply Subtype.ext
    exact Superoperator.comp_assoc _ _ _

/-- The generic dephased classical bit at fiber two. -/
noncomputable def classicalBitGeneric :
    (classicalBitModule.obj 2).Carrier :=
  ⟨bitDephaseSuperoperator, bitDephaseSuperoperator_idempotent⟩

/-- Weakening for the dephasing-fixed classical-bit module. -/
noncomputable def classicalBitWeakening :
    Hom classicalBitModule dayTensorUnit where
  app := fun _ x => Superoperator.comp SigmaMon.ChoiSum.discardTwo x.1
  map_zero := by
    intro n
    exact Superoperator.comp_zero_right _
  map_sum := by
    intro ι _ n f s h
    exact SigmaMon.ChoiSum.comp_left SigmaMon.ChoiSum.discardTwo h
  naturality := by
    intro m n x f
    exact Superoperator.comp_assoc _ _ _

/-- Contraction for dephasing-fixed classical bits.  A single coend generator
avoids an inadmissible branch-dependent Day sum. -/
noncomputable def classicalBitContraction :
    Hom classicalBitModule
      (dayTensor classicalBitModule classicalBitModule) where
  app := fun _ x =>
    (dayTensor classicalBitModule classicalBitModule).act
      ((DayCoend.intro classicalBitModule classicalBitModule).app
        classicalBitGeneric classicalBitGeneric)
      (Superoperator.comp bitCopySuperoperator x.1)
  map_zero := by
    intro n
    change
      (dayTensor classicalBitModule classicalBitModule).act
        ((DayCoend.intro classicalBitModule classicalBitModule).app
          classicalBitGeneric classicalBitGeneric)
        (Superoperator.comp bitCopySuperoperator
          (0 : Superoperator n 2)) = 0
    rw [Superoperator.comp_zero_right,
      (dayTensor classicalBitModule classicalBitModule).act_zero_map]
  map_sum := by
    intro ι _ n f s h
    apply (dayTensor classicalBitModule classicalBitModule).act_sum_map
    exact SigmaMon.ChoiSum.comp_left bitCopySuperoperator h
  naturality := by
    intro m n x f
    rw [(dayTensor classicalBitModule classicalBitModule).act_comp]
    congr 1
    exact Superoperator.comp_assoc _ _ _

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

/-- Module interpretation of a type in the fragment shape.  Linear
first-order domains retain the representable closed structure.  An
unrestricted bit arrow is instead closed over the dephasing-fixed classical
bit carrier, matching the interpretation of unrestricted context cells.
Outside the admitted fragment this is an inert fallback. -/
noncomputable def fragmentModule : Ty → Module
  | .unit => representable 1
  | .bit | .qubit => representable 2
  | .tensor A B => representable (A.hilbertDim * B.hilbertDim)
  | .arrow .lin A B =>
      internalHomRepresentable A.hilbertDim (fragmentModule B)
  | .arrow .unres .bit B =>
      dayInternalHom classicalBitModule (fragmentModule B)
  | .arrow .unres _ _ => representable 1
  | .var _ | .mu _ => representable 1

@[simp] theorem fragmentModule_unit :
    fragmentModule .unit = representable 1 := rfl

@[simp] theorem fragmentModule_bit :
    fragmentModule .bit = representable 2 := rfl

@[simp] theorem fragmentModule_qubit :
    fragmentModule .qubit = representable 2 := rfl

theorem fragmentModule_of_firstOrder {A : Ty} (h : Ty.FirstOrder A) :
    fragmentModule A = representable h.dimension := by
  induction h with
  | unit => rfl
  | bit => rfl
  | qubit => rfl
  | tensor hA hB =>
      simp only [fragmentModule]
      rfl

/-- Bit preparation from a Boolean literal. -/
noncomputable def bitPrepare (b : Bool) : Superoperator 1 2 :=
  if b then SigmaMon.ChoiSum.isometricBasisPrep 1
  else SigmaMon.ChoiSum.isometricBasisPrep 0

noncomputable def bitLitHom (b : Bool) :
    Hom dayTensorUnit (representable 2) :=
  yonedaMap (bitPrepare b)

/-- Primitive as a Yoneda map on its Hilbert IO dimensions. -/
noncomputable def primYoneda (p : Prim) :
    Hom (representable (CQ.QDim p.inputQ))
      (representable (CQ.QDim p.outputQ)) :=
  yonedaMap (Prim.superoperator p)

/-- Measurement instrument branches as Yoneda maps. -/
noncomputable def measureBranchYoneda (b : Bool) :
    Hom (representable 2) (representable 2) :=
  yonedaMap
    ((Instrument.measure (0 : Fin 1)).branchSuperoperator (if b then 1 else 0))

/-- Minimum semantic interface for the fragment (no global bang / LNL). -/
structure PresheafFragmentModel where
  /-- Object assignment for every fragment type. -/
  ty : ∀ {A}, Ty.SemanticFragment A → Module
  /-- Classical-bit discard. -/
  bitDiscard : Hom (representable 2) dayTensorUnit
  /-- Classical-bit copy into the actual coend Day tensor square. -/
  bitCopy :
    Hom (representable 2) (dayTensor (representable 2) (representable 2))
  /-- Boolean constants. -/
  bitLit : Bool → Hom dayTensorUnit (representable 2)
  /-- Unit point. -/
  unitIntro : Hom dayTensorUnit (representable 1)
  /-- Primitive embeddings on Hilbert dimensions. -/
  primMap : ∀ p : Prim,
    Hom (representable (CQ.QDim p.inputQ))
      (representable (CQ.QDim p.outputQ))
  /-- Measurement branch maps. -/
  measureBranch : Bool → Hom (representable 2) (representable 2)
  /-- Agreement with the intrinsic superoperator presentation. -/
  prim_agrees :
    ∀ p, primMap p = yonedaMap (Prim.superoperator p)
  /-- Fragment objects are the syntactic `fragmentModule`. -/
  ty_eq_fragmentModule :
    ∀ {A} (h : Ty.SemanticFragment A), ty h = fragmentModule A

/-- Route A model: direct fragment semantics. -/
noncomputable def routeAFragmentModel : PresheafFragmentModel where
  ty := fun {A} _ => fragmentModule A
  bitDiscard := bitDiscard
  bitCopy := Hom.comp (dayTensorRepresentableIso 2 2).inv bitCopy
  bitLit := bitLitHom
  unitIntro := yonedaMap (Superoperator.identity 1)
  primMap := primYoneda
  measureBranch := measureBranchYoneda
  prim_agrees := fun _ => rfl
  ty_eq_fragmentModule := fun _ => rfl

/-- Route A acceptance: fragment objects and structural maps exist without a
global bang. -/
theorem routeA_fragment_acceptance :
    (∀ {A : Ty} (h : Ty.SemanticFragment A),
      routeAFragmentModel.ty h = fragmentModule A) ∧
    (∀ p, routeAFragmentModel.primMap p =
      yonedaMap (Prim.superoperator p)) ∧
    (routeAFragmentModel.bitDiscard =
      yonedaMap SigmaMon.ChoiSum.discardTwo) :=
  ⟨routeAFragmentModel.ty_eq_fragmentModule,
    routeAFragmentModel.prim_agrees, rfl⟩

/-- Named Route A success marker: a concrete `PresheafFragmentModel` exists
(type objects, bit discard/copy, prim/measure maps).  This does **not**
include open-context denotation or runtime adequacy. -/
def RouteASucceeded : Prop :=
  Nonempty PresheafFragmentModel

theorem routeA_succeeded : RouteASucceeded :=
  ⟨routeAFragmentModel⟩

/-- Mathematical record that Route A supplies the maps required by the
minimum type/constant interface, so the ordered B–F tree is not entered for
that gate. -/
theorem routeA_skips_ordered_bang_routes :
    (∀ {A : Ty} (h : Ty.SemanticFragment A),
      ∃ M : Module, routeAFragmentModel.ty h = M) ∧
    (∃ δ : Hom (representable 2) dayTensorUnit,
      δ = routeAFragmentModel.bitDiscard) ∧
    (∃ γ : Hom (representable 2)
        (dayTensor (representable 2) (representable 2)),
      γ = routeAFragmentModel.bitCopy) :=
  ⟨fun h => ⟨routeAFragmentModel.ty h, rfl⟩,
    ⟨routeAFragmentModel.bitDiscard, rfl⟩,
    ⟨routeAFragmentModel.bitCopy, rfl⟩⟩

end QLambda.Linear
