/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.OmegaObjectInstances
import QLambda.Domain.OmegaCategory

/-!
# Canonical category of pointed ωCPOs and ω-continuous maps
-/

namespace QLambda.Domain

universe u

set_option linter.checkUnivs false

/-- The canonical ωCPO-enriched category of pointed ωCPOs and
ω-continuous maps. -/
noncomputable def omegaMapCategory : OmegaCategory.{u + 1, u} where
  Obj := OmegaObject.{u}
  hom A B :=
    { Carrier := OmegaMap A B
      partialOrder := inferInstance
      omegaComplete := OmegaMap.instOmegaCompleteFunctionSpace }
  id := OmegaMap.id
  comp := OmegaMap.comp
  comp_mono_left g := by
    intro f₁ f₂ h x
    exact h (g x)
  comp_mono_right f := by
    intro g₁ g₂ h x
    exact f.monotone (h x)
  comp_ωSup_left c hc g := by
    apply OmegaMap.ext
    intro x
    rfl
  comp_ωSup_right f c hc := by
    apply OmegaMap.ext
    intro x
    exact f.map_ωSup (fun n => c n x)
      (fun _ _ h => hc h x)
  id_comp := OmegaMap.id_comp
  comp_id := OmegaMap.comp_id
  assoc := OmegaMap.comp_assoc

attribute [reducible] omegaMapCategory

end QLambda.Domain
