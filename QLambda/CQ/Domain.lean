/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.InstrumentPower

/-!
# Finite classical--quantum circuit semantics

This module defines the semantic target of the Composer fragment.  A circuit
with `q` qubits and `c` classical bits denotes a state transformer whose
quantum component is a finite Kraus instrument on the `2 ^ q` dimensional
register and whose classical result is a new store.

This is the ideal, finite-register semantic layer.  It is deliberately not
called an `IsQuantumPowerModel`: `FiniteInstrumentComp` is a presentation
type, not a Scott-complete powerdomain.  Equality of presentations is the
existing observational equivalence from `InstrumentPower`.
-/

namespace QLambda

namespace CQ

/-- Hilbert-space dimension of a register containing `q` qubits. -/
abbrev QDim (q : ℕ) : ℕ := 2 ^ q

/-- A fixed finite classical bit store. -/
abbrev CStore (c : ℕ) := Fin c → Bool

/-- Ideal classical--quantum meaning of a circuit.

Given an initial classical store, it returns a finite quantum instrument whose
classical outcomes are final stores.  The quantum register is threaded by the
instrument and cannot be copied by copying a source-level handle. -/
abbrev Sem (q c : ℕ) :=
  CStore c → FiniteInstrumentComp (QDim q) (CStore c)

/-- Strong observational equality of finite computations.

It quantifies over all Kraus-valued postconditions. This presentation-
independent equality is a congruence for bind even when the classical store
does not carry a semantic monotonicity invariant. -/
def CompEq {n : ℕ} {D : Type*} [Preorder D]
    (μ ν : FiniteInstrumentComp n D) : Prop :=
  ∀ P : D → KrausFamily n n,
    KrausFamily.SemEq (μ.wpKraus P) (ν.wpKraus P)

/-- Pointwise strong observational equality of CQ meanings. -/
def Eq {q c : ℕ} (F G : Sem q c) : Prop :=
  ∀ s, CompEq (F s) (G s)

/-- The identity circuit. -/
def skip {q c : ℕ} : Sem q c :=
  fun s => FiniteInstrumentComp.unit s

/-- Sequential composition, implemented by instrument bind. -/
def seq {q c : ℕ} (F G : Sem q c) : Sem q c :=
  fun s => (F s).bind G

/-- Ideal external classical selection. -/
def select {q c : ℕ} (guard : CStore c → Bool) (F G : Sem q c) : Sem q c :=
  fun s => if guard s then G s else F s

theorem Eq.refl {q c : ℕ} (F : Sem q c) : Eq F F := by
  intro s P
  exact KrausFamily.applySemEq_refl _

theorem Eq.symm {q c : ℕ} {F G : Sem q c} (h : Eq F G) : Eq G F := by
  intro s P
  exact KrausFamily.applySemEq_symm (h s P)

theorem Eq.trans {q c : ℕ} {F G H : Sem q c}
    (hFG : Eq F G) (hGH : Eq G H) : Eq F H := by
  intro s P
  exact KrausFamily.applySemEq_trans (hFG s P) (hGH s P)

theorem skip_seq {q c : ℕ} (F : Sem q c) : Eq (seq skip F) F := by
  intro s P
  exact KrausFamily.applySemEq_trans
    (FiniteInstrumentComp.wpKraus_bind_semEq
      (FiniteInstrumentComp.unit (n := QDim q) s) F P)
    (FiniteInstrumentComp.wpKraus_unit_semEq s fun t => (F t).wpKraus P)

theorem seq_skip {q c : ℕ} (F : Sem q c) : Eq (seq F skip) F := by
  intro s P
  exact KrausFamily.applySemEq_trans
    (FiniteInstrumentComp.wpKraus_bind_semEq
      (F s) (FiniteInstrumentComp.unit (n := QDim q)) P)
    (FiniteInstrumentComp.wpKraus_semEq_pred (F s) fun t =>
      FiniteInstrumentComp.wpKraus_unit_semEq t P)

theorem seq_assoc {q c : ℕ} (F G H : Sem q c) :
    Eq (seq (seq F G) H) (seq F (seq G H)) := by
  intro s P
  exact KrausFamily.applySemEq_trans
    (FiniteInstrumentComp.wpKraus_bind_semEq ((F s).bind G) H P)
    (KrausFamily.applySemEq_trans
      (FiniteInstrumentComp.wpKraus_bind_semEq
        (F s) G fun t => (H t).wpKraus P)
      (KrausFamily.applySemEq_trans
        (FiniteInstrumentComp.wpKraus_semEq_pred (F s) fun t =>
          KrausFamily.applySemEq_symm
            (FiniteInstrumentComp.wpKraus_bind_semEq (G t) H P))
        (KrausFamily.applySemEq_symm
          (FiniteInstrumentComp.wpKraus_bind_semEq
            (F s) (fun t => (G t).bind H) P))))

/-- CQ sequencing respects semantic equality in both arguments. -/
theorem seq_congr {q c : ℕ} {F F' G G' : Sem q c}
    (hF : Eq F F') (hG : Eq G G') :
    Eq (seq F G) (seq F' G') := by
  intro s P
  exact KrausFamily.applySemEq_trans
    (FiniteInstrumentComp.wpKraus_bind_semEq (F s) G P)
    (KrausFamily.applySemEq_trans
      (hF s fun t => (G t).wpKraus P)
      (KrausFamily.applySemEq_trans
        (FiniteInstrumentComp.wpKraus_semEq_pred (F' s) fun t => hG t P)
        (KrausFamily.applySemEq_symm
          (FiniteInstrumentComp.wpKraus_bind_semEq (F' s) G' P))))

/-- Classical selection respects semantic equality branchwise. -/
theorem select_congr {q c : ℕ} (guard : CStore c → Bool)
    {F F' G G' : Sem q c} (hF : Eq F F') (hG : Eq G G') :
    Eq (select guard F G) (select guard F' G') := by
  intro s
  by_cases h : guard s
  · simpa [select, h] using hG s
  · simpa [select, h] using hF s

@[simp] theorem select_true {q c : ℕ} (F G : Sem q c) :
    select (fun _ => true) F G = G := by
  funext s
  simp [select]

@[simp] theorem select_false {q c : ℕ} (F G : Sem q c) :
    select (fun _ => false) F G = F := by
  funext s
  simp [select]

end CQ

end QLambda
