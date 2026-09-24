/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitChannels

/-!
# `bitCoassocLeftPre` definition
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators


/-- Left parenthesization of classical copy-after-dephase, before reassociation. -/
noncomputable def bitCoassocLeftPre : Superoperator 2 8 :=
  Superoperator.comp
    (Superoperator.tensor
      (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator)
      (Superoperator.identity 2))
    bitCopySuperoperator

end QLambda.Linear
