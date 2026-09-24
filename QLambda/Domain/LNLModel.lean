/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.CartesianClosed
import QLambda.Domain.SymmetricMonoidalClosed

/-!
# Linear/nonlinear model (strong monoidal adjunction)
-/

namespace QLambda.Domain

universe u v

open OmegaCategory

-- `u`/`v` only appear paired as `OmegaCategory.{u,v}` in this structure.
set_option linter.checkUnivs false in
/-- A strong symmetric monoidal adjunction between CPO-enriched categories.
The adjunction functors are ordinary functors: important models such as
`Set ⊣ qRel` do not preserve the selected hom orders in both directions. -/
structure LNLModel where
  nonlinear : OmegaCategory.{u, v}
  linear : OmegaCategory.{u, v}
  nonlinearClosed : CartesianClosed nonlinear
  linearClosed : SymmetricMonoidalClosed linear
  F : nonlinear.PlainFunctor linear
  G : linear.PlainFunctor nonlinear
  toLinear :
    {A : nonlinear.Obj} → {B : linear.Obj} →
      nonlinear.Hom A (G.obj B) → linear.Hom (F.obj A) B
  toNonlinear :
    {A : nonlinear.Obj} → {B : linear.Obj} →
      linear.Hom (F.obj A) B → nonlinear.Hom A (G.obj B)
  toLinear_toNonlinear :
    ∀ {A : nonlinear.Obj} {B : linear.Obj}
      (f : linear.Hom (F.obj A) B),
      toLinear (toNonlinear f) = f
  toNonlinear_toLinear :
    ∀ {A : nonlinear.Obj} {B : linear.Obj}
      (f : nonlinear.Hom A (G.obj B)),
      toNonlinear (toLinear f) = f
  adjunction_mono :
    ∀ {A : nonlinear.Obj} {B : linear.Obj},
      Monotone (@toLinear A B)
  F_unit : linear.Iso (F.obj nonlinearClosed.terminal) linearClosed.unit
  F_tensor :
    ∀ A B : nonlinear.Obj,
      linear.Iso (F.obj (nonlinearClosed.product A B))
        (linearClosed.tensor (F.obj A) (F.obj B))

end QLambda.Domain
