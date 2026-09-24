/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitCoassoc.bitCoassocLeftPre

/-!
# `bitCoassocLeft` definition
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators


/-- Left coassociativity composite, including the Day/tensor associator. -/
noncomputable def bitCoassocLeft : Superoperator 2 8 :=
  Superoperator.comp (Superoperator.tensorAssociator 2 2 2)
    bitCoassocLeftPre

end QLambda.Linear
