/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Domain.Presheaf.OmegaEnriched
public import QLambda.Domain.Presheaf.instOrderBotSuperoperator
public import QLambda.Domain.Presheaf.unitHomPartialOrder

@[expose] public section

/-!
# Instance `unitHomOrderBot`
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable instance unitHomOrderBot (P : Module) :
    OrderBot (Hom P dayTensorUnit) where
  bot := 0
  bot_le f := by
    intro n x
    exact bot_le

end SuperoperatorModule
end QLambda.Domain.Presheaf
