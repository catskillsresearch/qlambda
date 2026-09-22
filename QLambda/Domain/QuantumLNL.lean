/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumClassical
import QLambda.Domain.QuantumMonoidal

/-!
# The concrete `Set ⊣ qRel` linear/nonlinear model

The nonlinear category is ordinary sets with discrete hom orders.  The linear
category is the quantaloid of quantum relations.  The left adjoint sends a set
to one-dimensional atoms and a function to its graph.  The right adjoint sends
a quantum set to its set of relations from the monoidal unit.

The adjunction is ordinary rather than order-enriched in both directions:
postcomposition of states is not monotone into a discrete hom order.  This is
why `LNLModel` correctly asks its adjunction functors only for the ordinary
functor laws while retaining CPO enrichment on both semantic categories.
-/

namespace QLambda.Domain

/-- Classical-set inclusion into quantum relations. -/
noncomputable def classicalToQRel :
    discreteSetCategory.PlainFunctor qRelCategory := by
  classical
  exact
    { obj := classicalQObj
      map := fun f => QuantumRel.graph f.toFun
      map_id := QuantumRel.graph_id
      map_comp := fun g f => QuantumRel.graph_comp g.toFun f.toFun }

/-- The state-set functor, right adjoint to classical inclusion. -/
noncomputable def qRelStates :
    qRelCategory.PlainFunctor discreteSetCategory where
  obj A := QuantumRel .unit A.set
  map R :=
    ⟨fun S => R.comp S⟩
  map_id := by
    intro A
    letI := A.decidable
    apply SetHom.ext
    intro S
    exact QuantumRel.id_comp S
  map_comp R S := by
    apply SetHom.ext
    intro T
    exact QuantumRel.assoc R S T

/-- The classical singleton object and the qRel tensor unit are canonically
isomorphic. -/
noncomputable def classicalUnitIso :
    qRelCategory.Iso
      (classicalQObj PUnit) QObj.unit :=
  qRelIsoOfEquiv _ _
    (Equiv.refl PUnit)
    (fun _ => rfl)

/-- Classical pairing agrees with the tensor of one-dimensional quantum
atoms. -/
noncomputable def classicalTensorIso (A B : Type) :
    qRelCategory.Iso
      (classicalQObj (A × B))
      (QObj.tensor (classicalQObj A) (classicalQObj B)) :=
  qRelIsoOfEquiv _ _
    (Equiv.refl (A × B))
    (fun _ => rfl)

/-- The concrete quantum linear/nonlinear model. -/
noncomputable def quantumLNL : LNLModel where
  nonlinear := discreteSetCategory
  linear := qRelCategory
  nonlinearClosed := discreteSetCartesianClosed
  linearClosed := qRelSymmetricMonoidalClosed
  F := classicalToQRel
  G := qRelStates
  toLinear := by
    classical
    exact fun f => stateFunToRel f.toFun
  toNonlinear := by
    classical
    exact fun R => ⟨relToStateFun R⟩
  toLinear_toNonlinear := by
    classical
    exact fun R => stateFunToRel_relToStateFun R
  toNonlinear_toLinear := by
    classical
    intro A B f
    apply SetHom.ext
    intro x
    exact congrFun (relToStateFun_stateFunToRel f.toFun) x
  adjunction_mono := by
    intro A B f g h
    subst g
    exact le_rfl
  F_unit := classicalUnitIso
  F_tensor := classicalTensorIso

end QLambda.Domain
