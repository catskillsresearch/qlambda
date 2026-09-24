/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitCoassoc.bitCoassocLeft
import QLambda.Linear.FragmentClassicalBitCoassoc.tensorAssociator_two_two_two

/-!
# `bitCoassocLeft` equals the pre-associator form
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators


theorem bitCoassocLeft_eq_pre :
    bitCoassocLeft = bitCoassocLeftPre := by
  simp only [bitCoassocLeft, tensorAssociator_two_two_two,
    Superoperator.identity_comp]

end QLambda.Linear
