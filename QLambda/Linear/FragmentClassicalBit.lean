/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentPhysicalBitInstances

/-!
# Dephasing-fixed classical bit module

`classicalBitModule`, inclusion/classicalize, weakening/contraction, and
channel-level counit/coassoc lemmas.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000
open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators

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

/-- Classical bits are fixed points of `bitClassicalize`. -/
theorem bitClassicalize_comp_classicalBitInclusion :
    Hom.comp bitClassicalize classicalBitInclusion =
      Hom.id classicalBitModule := by
  ext n x
  apply Subtype.ext
  change Superoperator.comp bitDephaseSuperoperator x.1 = x.1
  exact x.2

/-- Computational-basis preparations are fixed by dephasing. -/
theorem bitDephase_comp_isometricBasisPrep (i : Fin 2) :
    Superoperator.comp bitDephaseSuperoperator
        (SigmaMon.ChoiSum.isometricBasisPrep i) =
      SigmaMon.ChoiSum.isometricBasisPrep i := by
  apply Superoperator.ext
  apply CPMap.ext
  funext p q
  have h00 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 0)).1 =
        false := by decide
  have h01 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 1)).1 =
        true := by decide
  rcases p with ⟨a, u⟩
  rcases q with ⟨b, v⟩
  fin_cases u; fin_cases v
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [Superoperator.cp_comp, CPMap.choi_comp_apply,
      bitDephaseSuperoperator, CPMap.choi_add, Matrix.add_apply,
      Instrument.measure_branch_zero, Instrument.measure_branch_one,
      CPMap.choi_ofKraus, KrausFamily.choiTerm,
      SigmaMon.ChoiSum.isometricBasisPrep, SigmaMon.ChoiSum.basisKet,
      Matrix.conjTranspose_apply,
      Composer.projector, Composer.onWire, Composer.registerSplit,
      Composer.proj₂, CQ.QDim, h00, h01]

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


end QLambda.Linear
