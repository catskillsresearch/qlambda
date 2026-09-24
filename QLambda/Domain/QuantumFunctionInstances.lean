/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumFunction
import QLambda.Domain.instLEQuantumFunction
import QLambda.Domain.instPartialOrderQuantumFunction

/-!
# Instances from `QuantumFunction`
-/

namespace QLambda.Domain
namespace QuantumFunction

/-- Functions compose, and the composite remains monotone. -/
def comp {P Q R : QuantumPoset}
    (G : QuantumFunction Q R) (F : QuantumFunction P Q) :
    QuantumFunction P R where
  rel := G.rel.comp F.rel
  isFunction := G.isFunction.comp F.isFunction
  monotone := by
    calc
      (G.rel.comp F.rel).comp P.order
          = G.rel.comp (F.rel.comp P.order) :=
            QuantumRel.assoc _ _ _
      _ ≤ G.rel.comp (Q.order.comp F.rel) :=
            QuantumRel.comp_mono_right F.monotone
      _ = (G.rel.comp Q.order).comp F.rel :=
            (QuantumRel.assoc _ _ _).symm
      _ ≤ (R.order.comp G.rel).comp F.rel :=
            QuantumRel.comp_mono_left _ G.monotone
      _ = R.order.comp (G.rel.comp F.rel) :=
            QuantumRel.assoc _ _ _

/-- Identity of a quantum poset is a quantum function. -/
def idFun (P : QuantumPoset) : QuantumFunction P P where
  rel := QuantumRel.id P.carrier
  isFunction := by
    constructor
    · rw [QuantumRel.id_dagger, QuantumRel.comp_id]
    · rw [QuantumRel.id_dagger, QuantumRel.id_comp]
  monotone := by
    rw [QuantumRel.comp_id, QuantumRel.id_comp]

end QuantumFunction
end QLambda.Domain
