/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitChannels

/-!
# Copy∘dephase Choi (entrywise)
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

end QLambda.Linear
