/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.LinearNonlinear
import QLambda.Domain.QuantumRelational

/-!
# ωCPO-enriched quantum relations

Quantum relations already form a complete lattice, so each hom-set is a
pointed ωCPO.  Composition preserves countable directed joins in each
argument.  That is enough to install the linear category of the LNL
interface.  This module also proves the state-family/relation bijection
that a future adjunction must use.

It does not claim a concrete `LNLModel`: the ordinary graph map from
pointwise-ordered `OmegaMap` homs to relations is not monotone.  A valid
model must instead supply an ordered qCPO morphism construction together
with monoidal closure and an enriched adjunction.
-/

namespace QLambda.Domain

open OmegaCategory

/-- A quantum set with decidable atoms, packaged as a linear object. -/
structure QObj where
  set : QuantumSet
  [decidable : DecidableEq set.Atom]

attribute [instance] QObj.decidable

namespace QObj

def qubit : QObj := ⟨.qubit⟩
def bit : QObj := ⟨.bit⟩
def unit : QObj := ⟨.unit⟩

def tensor (X Y : QObj) : QObj where
  set := X.set.tensor Y.set
  decidable := inferInstanceAs (DecidableEq (X.set.Atom × Y.set.Atom))

def dual (X : QObj) : QObj where
  set := X.set.dual
  decidable := inferInstanceAs (DecidableEq X.set.Atom)

def ofPoset (P : QuantumPoset) : QObj where
  set := P.carrier

end QObj

/-- Hom-object of quantum relations, as a pointed ωCPO. -/
noncomputable def qRelHom (X Y : QObj) : OmegaObject where
  Carrier := QuantumRel X.set Y.set
  partialOrder := inferInstance
  omegaComplete := inferInstance

attribute [reducible] qRelHom

/-- The ωCPO-enriched category of quantum sets and quantum relations. -/
noncomputable def qRelCategory : OmegaCategory where
  Obj := QObj
  hom := qRelHom
  id := fun {X} => QuantumRel.id X.set
  comp := fun {X Y Z} S R => S.comp R
  comp_mono_left := fun {X Y Z} R => by
    intro S₁ S₂ h
    exact QuantumRel.comp_mono_left (X := X.set) (Y := Y.set) (Z := Z.set) R h
  comp_mono_right := fun {X Y Z} S => by
    intro R₁ R₂ h
    exact QuantumRel.comp_mono_right (X := X.set) (Y := Y.set) (Z := Z.set) h
  comp_ωSup_left := fun {X Y Z} c hc R => by
    change (⨆ n, c n).comp R = ⨆ n, (c n).comp R
    exact QuantumRel.comp_iSup_left (Y := Y.set) (Z := Z.set) c R
  comp_ωSup_right := fun {X Y Z} S c hc => by
    change S.comp (⨆ n, c n) = ⨆ n, S.comp (c n)
    exact QuantumRel.comp_iSup_right (X := X.set) (Y := Y.set) S c
  id_comp := fun {X Y} R => QuantumRel.id_comp (X := X.set) (Y := Y.set) R
  comp_id := fun {X Y} R => QuantumRel.comp_id (X := X.set) (Y := Y.set) R
  assoc := fun {X Y Z W} T S R =>
    QuantumRel.assoc (X := X.set) (Y := Y.set) (Z := Z.set) (W := W.set) T S R

/-- Relations out of the monoidal unit form a pointed ωCPO. -/
noncomputable def states (A : QObj) : OmegaObject :=
  qRelHom QObj.unit A

/-- Reinterpret a relation `liftSet D → A` as a function `D → Rel(I, A)`. -/
def relToStateFun {D : Type} [DecidableEq D] {A : QObj}
    (R : QuantumRel (.liftSet D) A.set) :
    D → QuantumRel .unit A.set :=
  fun x =>
    { component := fun _ a => R.component x a }

/-- Reassemble a family of states into a relation out of `liftSet D`. -/
def stateFunToRel {D : Type} [DecidableEq D] {A : QObj}
    (f : D → QuantumRel .unit A.set) :
    QuantumRel (.liftSet D) A.set where
  component := fun x a => (f x).component PUnit.unit a

theorem relToStateFun_stateFunToRel {D : Type} [DecidableEq D] {A : QObj}
    (f : D → QuantumRel .unit A.set) :
    relToStateFun (stateFunToRel f) = f := by
  funext x
  apply QuantumRel.ext
  intro u a
  cases u
  rfl

theorem stateFunToRel_relToStateFun {D : Type} [DecidableEq D] {A : QObj}
    (R : QuantumRel (.liftSet D) A.set) :
    stateFunToRel (relToStateFun R) = R := by
  apply QuantumRel.ext
  intro x a
  rfl

end QLambda.Domain
