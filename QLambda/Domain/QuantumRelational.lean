/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Composer.MatrixSemantics
import QLambda.Domain.QuantumCPO
import QLambda.Domain.QuantumRel

/-!
# Published quantum posets / qCPOs and the finite circuit embedding

A quantum poset is a quantum set equipped with a Weaver order: a
reflexive, transitive, antisymmetric quantum relation.  A quantum CPO
asks that every increasing sequence of functions out of each atomic
probe `H_d` has a relational limit
`R ∘ K_∞ = ⨅ n, R ∘ K_n` (arXiv:2109.02196, Def. 5.1–5.2).

This file constructs the discrete and classical examples used by the
typed calculus and embeds the Composer gate set as quantum functions on
those objects.  Completely positive maps remain the first-order physical
presentation of those functions; they are not themselves the
higher-order monoidal-closed category.

See arXiv:2109.02196.
-/

open Matrix
open QLambda.Composer

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
instance {P Q : QuantumPoset} : LE (QuantumFunction P Q) where
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
instance {P Q : QuantumPoset} : PartialOrder (QuantumFunction P Q) where
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

/-- Square isometries over `ℂ` are unitaries. -/
theorem unitary_of_isometry {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (h : Uᴴ * U = 1) : U * Uᴴ = 1 :=
  (mul_eq_one_comm (a := Uᴴ) (b := U)).mp h

namespace CircuitEmbedding

/-- Hadamard as a quantum function on the discrete qubit. -/
noncomputable def h : QuantumRel .qubit .qubit :=
  QuantumRel.ofUnitary (hMatrix (0 : Fin 1))

/-- Pauli-X as a quantum function on the discrete qubit. -/
noncomputable def x : QuantumRel .qubit .qubit :=
  QuantumRel.ofUnitary (xMatrix (0 : Fin 1))

/-- T as a quantum function on the discrete qubit. -/
noncomputable def t : QuantumRel .qubit .qubit :=
  QuantumRel.ofUnitary (tMatrix (0 : Fin 1))

/-- Rational-angle `RY` as a quantum function on the discrete qubit. -/
noncomputable def ry (θ : ℚ) : QuantumRel .qubit .qubit :=
  QuantumRel.ofUnitary (ryMatrix (θ : ℝ) (0 : Fin 1))

/-- Saturated `CX` as a quantum function on a four-dimensional atom,
isomorphic to the two-qubit tensor. -/
noncomputable def cx : QuantumRel (.atomic 4) (.atomic 4) :=
  QuantumRel.ofUnitary (cxMatrix (0 : Fin 2) (1 : Fin 2))

/-- Computational-basis measurement, as a relation from the qubit to the
classical bit. -/
def measure : QuantumRel .qubit .bit :=
  QuantumRel.qubitMeasure

/-- Fresh `|0⟩` allocation.  This is an isometry-shaped relation, not a
Weaver function into the two-dimensional atom. -/
def new0 : QuantumRel .unit .qubit :=
  QuantumRel.new0

theorem h_isFunction : h.IsFunction :=
  QuantumRel.ofUnitary_isFunction _
    (hMatrix_isometry (0 : Fin 1))
    (unitary_of_isometry _ (hMatrix_isometry (0 : Fin 1)))

theorem x_isFunction : x.IsFunction :=
  QuantumRel.ofUnitary_isFunction _
    (xMatrix_isometry (0 : Fin 1))
    (unitary_of_isometry _ (xMatrix_isometry (0 : Fin 1)))

theorem t_isFunction : t.IsFunction :=
  QuantumRel.ofUnitary_isFunction _
    (tMatrix_isometry (0 : Fin 1))
    (unitary_of_isometry _ (tMatrix_isometry (0 : Fin 1)))

theorem ry_isFunction (θ : ℚ) : (ry θ).IsFunction :=
  QuantumRel.ofUnitary_isFunction _
    (ryMatrix_isometry (θ : ℝ) (0 : Fin 1))
    (unitary_of_isometry _ (ryMatrix_isometry (θ : ℝ) (0 : Fin 1)))

theorem cx_isFunction : cx.IsFunction :=
  QuantumRel.ofUnitary_isFunction _
    (cxMatrix_isometry (0 : Fin 2) (1 : Fin 2))
    (unitary_of_isometry _ (cxMatrix_isometry (0 : Fin 2) (1 : Fin 2)))

/-- Discrete-qubit Hadamard as a monotone quantum function. -/
noncomputable def hFun : QuantumFunction .qubit .qubit where
  rel := h
  isFunction := h_isFunction
  monotone := by
    change h.comp (QuantumRel.id .qubit) ≤ (QuantumRel.id .qubit).comp h
    rw [QuantumRel.comp_id, QuantumRel.id_comp]

noncomputable def xFun : QuantumFunction .qubit .qubit where
  rel := x
  isFunction := x_isFunction
  monotone := by
    change x.comp (QuantumRel.id .qubit) ≤ (QuantumRel.id .qubit).comp x
    rw [QuantumRel.comp_id, QuantumRel.id_comp]

noncomputable def tFun : QuantumFunction .qubit .qubit where
  rel := t
  isFunction := t_isFunction
  monotone := by
    change t.comp (QuantumRel.id .qubit) ≤ (QuantumRel.id .qubit).comp t
    rw [QuantumRel.comp_id, QuantumRel.id_comp]

end CircuitEmbedding

/-- The first-order CP presentation of a unitary quantum function is the
singleton Kraus family. -/
noncomputable def completedCP_ofUnitary {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) :
    CompletedCP n n :=
  CompletedCP.ofKraus [U]

@[simp] theorem completedCP_ofUnitary_h :
    completedCP_ofUnitary (hMatrix (0 : Fin 1)) = CompletedCP.h (0 : Fin 1) :=
  rfl

@[simp] theorem completedCP_ofUnitary_x :
    completedCP_ofUnitary (xMatrix (0 : Fin 1)) = CompletedCP.x (0 : Fin 1) :=
  rfl

@[simp] theorem completedCP_ofUnitary_t :
    completedCP_ofUnitary (tMatrix (0 : Fin 1)) = CompletedCP.t (0 : Fin 1) :=
  rfl

@[simp] theorem completedCP_ofUnitary_ry (θ : ℚ) :
    completedCP_ofUnitary (ryMatrix (θ : ℝ) (0 : Fin 1)) =
      CompletedCP.ry θ (0 : Fin 1) :=
  rfl

@[simp] theorem completedCP_ofUnitary_cx :
    completedCP_ofUnitary (cxMatrix (0 : Fin 2) (1 : Fin 2)) =
      CompletedCP.cx (0 : Fin 2) (1 : Fin 2) :=
  rfl

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
