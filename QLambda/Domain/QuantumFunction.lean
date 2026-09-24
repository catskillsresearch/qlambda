/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumPoset

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

/-- Pointwise order on quantum functions (Kornell--Lindenhovius--Mislove,
Lemma 2.6.6): `F ⊑ G` iff `G ≤ S ∘ F`, where `S` is the codomain order. -/
instance instLEQuantumFunction {P Q : QuantumPoset} : LE (QuantumFunction P Q) where
  le F G := G.rel ≤ Q.order.comp F.rel

theorem le_def {P Q : QuantumPoset} {F G : QuantumFunction P Q} :
    F ≤ G ↔ G.rel ≤ Q.order.comp F.rel :=
  Iff.rfl

theorem restrictAtom_mono {P Q : QuantumPoset}
    {F G : QuantumFunction P Q} (h : F ≤ G) (x : P.carrier.Atom) :
    restrictAtom F x ≤ restrictAtom G x := by
  change QuantumRel.restrictAtom G.rel x ≤
    Q.order.comp (QuantumRel.restrictAtom F.rel x)
  rw [← QuantumRel.restrictAtom_comp]
  exact QuantumRel.restrictAtom_mono h x

/-- The fifth characterization of the pointwise order from KLM Lemma 2.6.6. -/
theorem comp_dagger_le_order {P Q : QuantumPoset}
    {F G : QuantumFunction P Q} (h : F ≤ G) :
    G.rel.comp F.rel.dagger ≤ Q.order := by
  calc
    G.rel.comp F.rel.dagger
        ≤ (Q.order.comp F.rel).comp F.rel.dagger :=
          QuantumRel.comp_mono_left F.rel.dagger h
    _ = Q.order.comp (F.rel.comp F.rel.dagger) :=
          QuantumRel.assoc _ _ _
    _ ≤ Q.order.comp (QuantumRel.id Q.carrier) :=
          QuantumRel.comp_mono_right F.isFunction.1
    _ = Q.order := QuantumRel.comp_id _

/-- Quantum-function homs carry the published pointwise partial order. -/
instance instPartialOrderQuantumFunction {P Q : QuantumPoset} : PartialOrder (QuantumFunction P Q) where
  le_refl F := by
    calc
      F.rel = (QuantumRel.id Q.carrier).comp F.rel :=
        (QuantumRel.id_comp F.rel).symm
      _ ≤ Q.order.comp F.rel :=
        QuantumRel.comp_mono_left F.rel Q.reflexive
  le_trans F G H hFG hGH := by
    calc
      H.rel ≤ Q.order.comp G.rel := hGH
      _ ≤ Q.order.comp (Q.order.comp F.rel) :=
        QuantumRel.comp_mono_right hFG
      _ = (Q.order.comp Q.order).comp F.rel :=
        (QuantumRel.assoc _ _ _).symm
      _ ≤ Q.order.comp F.rel :=
        QuantumRel.comp_mono_left F.rel Q.transitive
  le_antisymm F G hFG hGF := by
    apply ext
    have hGFdag :
        G.rel.comp F.rel.dagger ≤ Q.order.dagger := by
      have h := QuantumRel.dagger_mono (comp_dagger_le_order hGF)
      rw [QuantumRel.dagger_comp, QuantumRel.dagger_dagger] at h
      exact h
    have hFGdag :
        F.rel.comp G.rel.dagger ≤ Q.order.dagger := by
      have h := QuantumRel.dagger_mono (comp_dagger_le_order hFG)
      rw [QuantumRel.dagger_comp, QuantumRel.dagger_dagger] at h
      exact h
    have hid :
        G.rel.comp F.rel.dagger ≤ QuantumRel.id Q.carrier :=
      (le_inf (comp_dagger_le_order hFG) hGFdag).trans Q.antisymmetric
    have hid' :
        F.rel.comp G.rel.dagger ≤ QuantumRel.id Q.carrier :=
      (le_inf (comp_dagger_le_order hGF) hFGdag).trans Q.antisymmetric
    apply le_antisymm
    · calc
        F.rel = F.rel.comp (QuantumRel.id P.carrier) :=
          (QuantumRel.comp_id F.rel).symm
        _ ≤ F.rel.comp (G.rel.dagger.comp G.rel) :=
          QuantumRel.comp_mono_right G.isFunction.2
        _ = (F.rel.comp G.rel.dagger).comp G.rel :=
          (QuantumRel.assoc _ _ _).symm
        _ ≤ (QuantumRel.id Q.carrier).comp G.rel :=
          QuantumRel.comp_mono_left G.rel hid'
        _ = G.rel := QuantumRel.id_comp _
    · calc
        G.rel = G.rel.comp (QuantumRel.id P.carrier) :=
          (QuantumRel.comp_id G.rel).symm
        _ ≤ G.rel.comp (F.rel.dagger.comp F.rel) :=
          QuantumRel.comp_mono_right F.isFunction.2
        _ = (G.rel.comp F.rel.dagger).comp F.rel :=
          (QuantumRel.assoc _ _ _).symm
        _ ≤ (QuantumRel.id Q.carrier).comp F.rel :=
          QuantumRel.comp_mono_left F.rel hid
        _ = F.rel := QuantumRel.id_comp _

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

end QuantumFunction
/-- Identity of a quantum poset is a quantum function. -/
def idFun (P : QuantumPoset) : QuantumFunction P P where
  rel := QuantumRel.id P.carrier
  isFunction := by
    constructor
    · rw [QuantumRel.id_dagger, QuantumRel.comp_id]
    · rw [QuantumRel.id_dagger, QuantumRel.id_comp]
  monotone := by
    rw [QuantumRel.comp_id, QuantumRel.id_comp]


end QLambda.Domain
