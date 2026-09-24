/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitChannels

/-!
# `bitCoassocRight` definition
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators


/-- Right coassociativity composite. -/
noncomputable def bitCoassocRight : Superoperator 2 8 :=
  Superoperator.comp
    (Superoperator.tensor
      (Superoperator.identity 2)
      (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator))
    bitCopySuperoperator

end QLambda.Linear
