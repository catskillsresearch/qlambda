/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumRelations

/-!
# Quantum posets
-/

open Matrix

namespace QLambda.Domain

/-- A quantum poset in the sense of Weaver / Kornell–Lindenhovius–Mislove. -/
structure QuantumPoset where
  carrier : QuantumSet
  [decidable : DecidableEq carrier.Atom]
  order : QuantumRel carrier carrier
  reflexive : QuantumRel.id carrier ≤ order
  transitive : order.comp order ≤ order
  antisymmetric : order ⊓ order.dagger ≤ QuantumRel.id carrier

attribute [instance] QuantumPoset.decidable

namespace QuantumPoset

/-- The discrete order.  Discrete quantum posets are quantum CPOs because
comparable functions are equal, so every increasing function-chain is
constant. -/
def discrete (X : QuantumSet) [DecidableEq X.Atom] : QuantumPoset where
  carrier := X
  order := QuantumRel.id X
  reflexive := le_rfl
  transitive := by rw [QuantumRel.id_comp]
  antisymmetric := inf_le_left

/-- The qubit with the discrete order. -/
def qubit : QuantumPoset :=
  discrete .qubit

/-- The classical bit with the discrete order. -/
def bit : QuantumPoset :=
  discrete .bit

/-- The monoidal unit. -/
def unit : QuantumPoset :=
  discrete .unit

/-- Tensor of discrete quantum posets is the discrete order on the
tensor quantum set. -/
def tensorDiscrete (X Y : QuantumSet)
    [DecidableEq X.Atom] [DecidableEq Y.Atom] : QuantumPoset :=
  discrete (X.tensor Y)

end QuantumPoset

namespace QuantumPoset

/-- A quantum order is idempotent under relational composition. -/
theorem order_comp_self (P : QuantumPoset) :
    P.order.comp P.order = P.order := by
  apply le_antisymm P.transitive
  calc
    P.order = P.order.comp (QuantumRel.id P.carrier) :=
      (QuantumRel.comp_id _).symm
    _ ≤ P.order.comp P.order :=
      QuantumRel.comp_mono_right P.reflexive

end QuantumPoset

/-- The published completeness property of a quantum CPO, stated for
atomic probes `H_d` (Def. 5.2). -/
def IsQuantumCPO (P : QuantumPoset) : Prop :=
  ∀ (d : ℕ) (K : ℕ → QuantumRel (.atomic d) P.carrier),
    (∀ n, (K n).IsFunction) →
      (∀ n, K (n + 1) ≤ P.order.comp (K n)) →
      ∃ Kinf : QuantumRel (.atomic d) P.carrier,
        Kinf.IsFunction ∧
          P.order.comp Kinf = ⨅ n, P.order.comp (K n)

/-- Discrete quantum posets are qCPOs: an increasing sequence of
functions is constant, so the relational limit is the first term. -/
theorem discrete_isQuantumCPO (X : QuantumSet) [DecidableEq X.Atom] :
    IsQuantumCPO (QuantumPoset.discrete X) := by
  intro d K hfun hinc
  refine ⟨K 0, hfun 0, ?_⟩
  have hord :
      (QuantumPoset.discrete X).order =
        QuantumRel.id (QuantumPoset.discrete X).carrier :=
    rfl
  have hconst : ∀ n, K n = K 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hle : K (n + 1) ≤ K n := by
        have h := hinc n
        rw [hord, QuantumRel.id_comp] at h
        exact h
      exact (QuantumRel.function_eq_of_le (hfun (n + 1)) (hfun n) hle).trans ih
  rw [hord]
  have : (fun n => (QuantumRel.id (QuantumPoset.discrete X).carrier).comp (K n)) =
      fun _ => (QuantumRel.id (QuantumPoset.discrete X).carrier).comp (K 0) := by
    funext n
    rw [hconst n]
  rw [this]
  exact iInf_const.symm

theorem qubit_isQuantumCPO : IsQuantumCPO .qubit :=
  discrete_isQuantumCPO .qubit

theorem bit_isQuantumCPO : IsQuantumCPO .bit :=
  discrete_isQuantumCPO .bit

theorem unit_isQuantumCPO : IsQuantumCPO .unit :=
  discrete_isQuantumCPO .unit

end QLambda.Domain
