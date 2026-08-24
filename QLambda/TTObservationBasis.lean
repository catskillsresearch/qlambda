/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.RationalCP

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QLambda

universe u

/-- Raw finite data underlying a rational step postcondition. -/
abbrev RatStepPostData (n : ℕ) :=
  Σ k : ℕ, (Fin k → ℕ) × ((Fin k → Bool) → RatTNICPMatrix n)

/-- A finite table of rational trace-nonincreasing CP codes indexed by the
Boolean signature of finitely many coded Scott opens. -/
structure RatStepPostCode (n : ℕ) where
  arity : ℕ
  opens : Fin arity → ℕ
  table : (Fin arity → Bool) → RatTNICPMatrix n
  table_mono : ∀ ⦃s t⦄,
    (∀ i, @LE.le Bool Bool.instLE (s i) (t i)) →
    (table s).toComplex ≤ (table t).toComplex

namespace RatStepPostCode

noncomputable instance (n : ℕ) : Encodable (RatStepPostCode n) := by
  classical
  let valid (d : RatStepPostData n) : Prop :=
    ∀ ⦃s t⦄, (∀ i, @LE.le Bool Bool.instLE (s i) (t i)) →
      (d.2.2 s).toComplex ≤ (d.2.2 t).toComplex
  let e : RatStepPostCode n ≃ {d : RatStepPostData n // valid d} := {
    toFun c := ⟨⟨c.arity, c.opens, c.table⟩, c.table_mono⟩
    invFun d := ⟨d.1.1, d.1.2.1, d.1.2.2, d.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact Encodable.ofEquiv _ e

instance (n : ℕ) : Countable (RatStepPostCode n) :=
  Encodable.countable

/-- Boolean membership signature of a point against the finitely many
Scott opens selected by a step code. -/
noncomputable def signature {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) (c : RatStepPostCode n) (d : D) :
    Fin c.arity → Bool := by
  classical
  exact fun i => if d ∈ C.observe (c.opens i) then true else false

theorem signature_mono {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) (c : RatStepPostCode n) ⦃d e : D⦄
    (hde : d ≤ e) (i : Fin c.arity) :
    @LE.le Bool Bool.instLE (c.signature C d i) (c.signature C e i) := by
  classical
  by_cases hd : d ∈ C.observe (c.opens i)
  · have he : e ∈ C.observe (c.opens i) :=
      (C.observe (c.opens i)).isScottOpen.isUpperSet hde hd
    simp [signature, hd, he]
  · by_cases he : e ∈ C.observe (c.opens i) <;>
      simp [signature, hd, he]

/-- Rational TNI code selected by the signature of `d`. -/
noncomputable def decodedTNI {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) (c : RatStepPostCode n) (d : D) :
    RatTNICPMatrix n :=
  c.table (c.signature C d)

theorem decodedTNI_mono {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) (c : RatStepPostCode n) ⦃d e : D⦄ (hde : d ≤ e) :
    (c.decodedTNI C d).toComplex ≤ (c.decodedTNI C e).toComplex :=
  c.table_mono (fun i => c.signature_mono C hde i)

/-- The underlying rational CP matrix of the selected TNI code.  This keeps
the pre-TNI matrix-level interface available to downstream proofs. -/
noncomputable def decodedMatrix {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) (c : RatStepPostCode n) (d : D) :
    RatCPMatrix n :=
  (c.decodedTNI C d).cp

theorem decodedMatrix_mono {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) (c : RatStepPostCode n) ⦃d e : D⦄ (hde : d ≤ e) :
    (c.decodedMatrix C d).toComplex ≤ (c.decodedMatrix C e).toComplex :=
  c.decodedTNI_mono C hde

/-- Physical quantum operation selected at `d`. -/
noncomputable def decodedOperation {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) (c : RatStepPostCode n) (d : D) :
    QuantumOperation n n :=
  (c.decodedTNI C d).toQuantumOperation

/-- Kraus realization of the rational matrix selected at `d`. -/
noncomputable def decodedKraus {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) (c : RatStepPostCode n) (d : D) :
    KrausFamily n n :=
  (c.decodedOperation C d).kraus

@[simp] theorem choi_decodedKraus {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) (c : RatStepPostCode n) (d : D) :
    KrausFamily.choi (c.decodedKraus C d) =
      (c.decodedMatrix C d).toComplex :=
  RatTNICPMatrix.choi_realize _

theorem choi_decodedKraus_tni {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) (c : RatStepPostCode n) (d : D) :
    KrausFamily.choi (c.decodedKraus C d) =
      (c.decodedTNI C d).toComplex :=
  RatTNICPMatrix.choi_realize _

theorem decodedKraus_mono {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) (c : RatStepPostCode n) ⦃d e : D⦄ (hde : d ≤ e) :
    KrausFamily.Refines (c.decodedKraus C d) (c.decodedKraus C e) :=
  RatTNICPMatrix.realize_refines (c.decodedTNI_mono C hde)

theorem decodedKraus_trace_nonincreasing
    {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) (c : RatStepPostCode n) (d : D) :
    ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (KrausFamily.applyMat (c.decodedKraus C d) ρ)).re ≤
        (Matrix.trace ρ).re :=
  (c.decodedOperation C d).trace_nonincreasing

/-- Decode a finite rational TNI step table as a monotone Kraus
postcondition.  Its values are the Kraus families of physical quantum
operations; `FiniteInstrumentComp.Refines` remains the legacy quantification
over all monotone Kraus postconditions. -/
noncomputable def decode {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) (c : RatStepPostCode n) :
    FiniteInstrumentComp.KrausPost n D where
  pred := c.decodedKraus C
  mono := c.decodedKraus_mono C

@[simp] theorem decode_apply {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) (c : RatStepPostCode n) (d : D) :
    c.decode C d = c.decodedKraus C d :=
  rfl

/-- Every Kraus value supplied by a decoded step postcondition is
trace-nonincreasing. -/
theorem decode_trace_nonincreasing {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) (c : RatStepPostCode n) (d : D) :
    ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (KrausFamily.applyMat (c.decode C d) ρ)).re ≤
        (Matrix.trace ρ).re :=
  c.decodedKraus_trace_nonincreasing C d

end RatStepPostCode

/-- A TT observation tests the weakest precondition induced by one
finite rational step postcondition. -/
structure TTObservationAtom (n : ℕ) where
  post : RatStepPostCode n
  choi : ChoiTest n

namespace TTObservationAtom

noncomputable instance (n : ℕ) : Encodable (TTObservationAtom n) :=
  Encodable.ofEquiv (RatStepPostCode n × ChoiTest n) {
    toFun a := (a.post, a.choi)
    invFun a := ⟨a.1, a.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }

instance (n : ℕ) : Countable (TTObservationAtom n) :=
  Encodable.countable

/-- Satisfaction by strict quadratic evaluation of the Choi matrix of
the decoded weakest precondition. -/
def Holds {D : Type u} [CompleteLattice D] (C : OutputCode ℕ D)
    (a : TTObservationAtom n) (μ : FiniteInstrumentComp n D) : Prop :=
  a.choi.threshold <
    a.choi.eval (KrausFamily.choi (μ.wpKraus (a.post.decode C)))

theorem eval_nonneg {D : Type u} [CompleteLattice D] (C : OutputCode ℕ D)
    (a : TTObservationAtom n) (μ : FiniteInstrumentComp n D) :
    0 ≤ a.choi.eval (KrausFamily.choi (μ.wpKraus (a.post.decode C))) :=
  a.choi.eval_nonneg (KrausFamily.choi_posSemidef _)

theorem holds_of_threshold_le {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) {a b : TTObservationAtom n}
    (hpost : a.post = b.post) (hvec : a.choi.1 = b.choi.1)
    (hthreshold : a.choi.threshold ≤ b.choi.threshold)
    {μ : FiniteInstrumentComp n D} (hμ : Holds C b μ) :
    Holds C a μ := by
  have heval :
      b.choi.eval (KrausFamily.choi (μ.wpKraus (b.post.decode C))) =
        a.choi.eval (KrausFamily.choi (μ.wpKraus (a.post.decode C))) := by
    simp only [ChoiTest.eval, ChoiTest.vector]
    rw [← hpost, ← hvec]
  exact hthreshold.trans_lt (hμ.trans_eq heval)

theorem holds_mono {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) {μ ν : FiniteInstrumentComp n D}
    (hμν : μ ≤ ν) {a : TTObservationAtom n} (ha : Holds C a μ) :
    Holds C a ν := by
  apply ha.trans_le
  apply a.choi.eval_mono
  exact KrausFamily.choiRefines_of_residualRefines (hμν (a.post.decode C))

end TTObservationAtom

/-- Finite conjunctions of rational TT observation atoms. -/
abbrev TTObservationToken (n : ℕ) :=
  List (TTObservationAtom n)

noncomputable instance (n : ℕ) : Encodable (TTObservationToken n) :=
  inferInstance

instance (n : ℕ) : Countable (TTObservationToken n) :=
  Encodable.countable

namespace TTObservationToken

def Holds {D : Type u} [CompleteLattice D] (C : OutputCode ℕ D)
    (t : TTObservationToken n) (μ : FiniteInstrumentComp n D) : Prop :=
  ∀ a ∈ t, a.Holds C μ

theorem nil_holds {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) (μ : FiniteInstrumentComp n D) :
    Holds C [] μ := by
  simp [Holds]

theorem holds_mono {D : Type u} [CompleteLattice D]
    (C : OutputCode ℕ D) {μ ν : FiniteInstrumentComp n D}
    (hμν : μ ≤ ν) {t : TTObservationToken n} (ht : Holds C t μ) :
    Holds C t ν := by
  intro a ha
  exact TTObservationAtom.holds_mono C hμν (ht a ha)

end TTObservationToken

end QLambda
