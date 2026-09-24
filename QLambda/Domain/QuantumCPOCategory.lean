/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumCPO
import QLambda.Domain.ScottFunctionInstances

/-!
# Quantum CPO morphisms

Barrel re-exporting `QuantumCPO`, `ScottFunction`, and the enriched category
`qCPOCategory`.
-/

namespace QLambda.Domain

/-- Theorem 3.3.5: quantum CPOs and Scott-continuous quantum functions
form an ωCPO-enriched category. -/
noncomputable def qCPOCategory : OmegaCategory.{1, 0} where
  Obj := QuantumCPO
  hom P Q :=
    { Carrier := ScottFunction P Q
      partialOrder := inferInstance
      omegaComplete := ScottFunction.instOmegaComplete P Q }
  id := fun {P} => ScottFunction.id P
  comp := ScottFunction.comp
  comp_mono_left := ScottFunction.comp_mono_left
  comp_mono_right := ScottFunction.comp_mono_right
  comp_ωSup_left := ScottFunction.comp_ωSup_left
  comp_ωSup_right := ScottFunction.comp_ωSup_right
  id_comp := ScottFunction.id_comp
  comp_id := ScottFunction.comp_id
  assoc := ScottFunction.assoc

end QLambda.Domain
