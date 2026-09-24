/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.LNLModel
import QLambda.Domain.OmegaCartesianClosed
import QLambda.Domain.OmegaSymmetricMonoidalClosed

/-!
# Identity LNL model on pointed ωCPOs
-/

namespace QLambda.Domain

universe u

set_option linter.checkUnivs false

open OmegaCategory

private noncomputable def omegaIdentityFunctor :
    (omegaMapCategory.{u}).PlainFunctor omegaMapCategory where
  obj := id
  map := id
  map_id := rfl
  map_comp := fun _ _ => rfl

/-- The identity adjunction supplies a fully concrete classical LNL
model.  The intended quantum model instead uses the published category of
pointed quantum CPOs as its linear side.  Finite CP maps and instruments embed
the circuit fragment into that category; they are not themselves asserted to
form the higher-order monoidal-closed category. -/
noncomputable def omegaIdentityLNL : LNLModel.{u + 1, u} where
  nonlinear := omegaMapCategory
  linear := omegaMapCategory
  nonlinearClosed := omegaCartesianClosed
  linearClosed := omegaSymmetricMonoidalClosed
  F := omegaIdentityFunctor
  G := omegaIdentityFunctor
  toLinear := fun f => f
  toNonlinear := fun f => f
  toLinear_toNonlinear := fun _ => rfl
  toNonlinear_toLinear := fun _ => rfl
  adjunction_mono := by
    intro A B f g h
    exact h
  F_unit :=
    { hom := OmegaMap.id
      inv := OmegaMap.id
      hom_inv := OmegaMap.id_comp _
      inv_hom := OmegaMap.id_comp _ }
  F_tensor := fun _ _ =>
    { hom := OmegaMap.id
      inv := OmegaMap.id
      hom_inv := OmegaMap.id_comp _
      inv_hom := OmegaMap.id_comp _ }

end QLambda.Domain
