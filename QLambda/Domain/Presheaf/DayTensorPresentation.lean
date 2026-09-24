/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Bilinear

/-!
# Day tensor universal-property package
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u v w

/-- Universal-property package for one genuine Day tensor.  Constructing this
for all modules is the categorical gate not supplied by the representable
fragment below. -/
structure DayTensorPresentation (M : Module.{u}) (N : Module.{v}) where
  object : Module.{w}
  intro : Bilinear M N object
  universal : ∀ L : Module.{u}, Hom object L ≃ Bilinear M N L
  universal_apply :
    ∀ (L : Module.{u}) (f : Hom object L),
      universal L f = Bilinear.postcomp f intro

end SuperoperatorModule

end QLambda.Domain.Presheaf
