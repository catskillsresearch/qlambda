/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumPoset
import QLambda.Domain.QuantumRelInstances

/-!
# Monotone quantum functions
-/

open Matrix

namespace QLambda.Domain

/-- A monotone quantum function between quantum posets. -/
structure QuantumFunction (P Q : QuantumPoset) where
  rel : QuantumRel P.carrier Q.carrier
  isFunction : rel.IsFunction
  monotone : rel.comp P.order ≤ Q.order.comp rel

namespace QuantumFunction

theorem ext {P Q : QuantumPoset} {F G : QuantumFunction P Q}
    (h : F.rel = G.rel) : F = G := by
  cases F
  cases G
  congr

/-- Restriction of a quantum function to one atom of its domain. -/
def restrictAtom {P Q : QuantumPoset} (F : QuantumFunction P Q)
    (x : P.carrier.Atom) :
    QuantumFunction (QuantumPoset.discrete
      (.atomic (P.carrier.dim x))) Q where
  rel := QuantumRel.restrictAtom F.rel x
  isFunction := QuantumRel.restrictAtom_isFunction F.isFunction x
  monotone := by
    change
      (QuantumRel.restrictAtom F.rel x).comp
          (QuantumRel.id (.atomic (P.carrier.dim x))) ≤
        Q.order.comp (QuantumRel.restrictAtom F.rel x)
    rw [QuantumRel.comp_id]
    calc
      QuantumRel.restrictAtom F.rel x =
          (QuantumRel.id Q.carrier).comp
            (QuantumRel.restrictAtom F.rel x) :=
        (QuantumRel.id_comp _).symm
      _ ≤ Q.order.comp (QuantumRel.restrictAtom F.rel x) :=
        QuantumRel.comp_mono_left _ Q.reflexive


end QuantumFunction

end QLambda.Domain
