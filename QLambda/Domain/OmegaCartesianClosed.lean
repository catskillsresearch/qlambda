/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.CartesianClosed

/-!
# Cartesian closed structure on pointed ωCPOs
-/

namespace QLambda.Domain

universe u

set_option linter.checkUnivs false

open OmegaCategory

/-- Terminal pointed ωCPO. -/
noncomputable def omegaTerminal : OmegaObject where
  Carrier := PUnit
  partialOrder := inferInstance
  omegaComplete := inferInstance

/-- Product pointed ωCPO. -/
noncomputable def omegaProduct (A B : OmegaObject) : OmegaObject where
  Carrier := A × B
  partialOrder := inferInstance
  omegaComplete := inferInstance

/-- Pointed ωCPO of continuous maps. -/
noncomputable def omegaExponential (A B : OmegaObject) : OmegaObject where
  Carrier := OmegaMap A B
  partialOrder := inferInstance
  omegaComplete := inferInstance

attribute [reducible] omegaTerminal omegaProduct omegaExponential

/-- The ordinary category of pointed ωCPOs is Cartesian closed.  This
serves as the nonlinear side of concrete LNL models. -/
noncomputable def omegaCartesianClosed :
    CartesianClosed (omegaMapCategory.{u}) where
  terminal := omegaTerminal
  product := omegaProduct
  exponential := omegaExponential
  terminate :=
    { toFun := fun _ => PUnit.unit
      monotone := fun _ _ _ => le_rfl
      map_ωSup := fun _ _ => by
        exact (OmegaComplete.ωSup_const PUnit.unit).symm }
  fst := OmegaMap.fst
  snd := OmegaMap.snd
  pair := OmegaMap.pair
  eval := OmegaMap.eval
  curry := OmegaMap.curry
  terminal_unique := by
    intro A f
    apply OmegaMap.ext
    intro x
    exact Subsingleton.elim _ _
  fst_pair := by
    intro X A B f g
    apply OmegaMap.ext
    intro x
    rfl
  snd_pair := by
    intro X A B f g
    apply OmegaMap.ext
    intro x
    rfl
  pair_eta := by
    intro X A B f
    apply OmegaMap.ext
    intro x
    exact Prod.eta _
  beta := by
    intro X A B f
    apply OmegaMap.ext
    intro p
    cases p
    rfl
  curry_mono := by
    intro X A B f g h x a
    exact h (x, a)
  curry_ωSup := by
    intro X A B c hc
    apply OmegaMap.ext
    intro x
    apply OmegaMap.ext
    intro a
    rfl

end QLambda.Domain
