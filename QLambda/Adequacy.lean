/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.TTComputationChoice
import QLambda.TTPhysicalPrimitives

/-!
# Operational evaluation and partial adequacy

The finitely presented primitive fragment is evaluated as a finite TNI
instrument.  Observing the TT denotation at a finitely presented result
continuation recovers exactly the tokens of that operational instrument.

General closed-term adequacy is stated only under an explicit finite-
denotation hypothesis together with a `CodedTestRepresentation` density
assumption.  The finite physical image is not claimed to contain every
denotation: it is not closed under directed suprema, and higher-order
recursion may leave it.
-/

namespace QLambda

open Scott1972.ContinuousLattice
open TTPhysicalPrimitives

universe u

namespace PrimitiveEvaluation

variable {n : ℕ} {D E : Type u}

/-- Operational meaning of a closed qubit primitive. -/
def eval : QubitPrimitive D → FiniteInstrumentComp 2 D :=
  finiteInstrument

@[simp] theorem eval_ret (d : D) :
    eval (.ret d) = FiniteInstrumentComp.unit (n := 2) d :=
  rfl

@[simp] theorem eval_pauliX (d : D) :
    eval (.pauliX d) = FiniteInstrumentComp.ofOperation Qubit.pauliXOp d :=
  rfl

@[simp] theorem eval_measureZ (d₀ d₁ : D) :
    eval (.measureZ d₀ d₁) =
      Qubit.measureZComp.map (fun b => if b then d₁ else d₀) :=
  rfl

/-- Finite physical sequencing. -/
def evalBind (μ : FiniteInstrumentComp n D)
    (f : D → FiniteInstrumentComp n E) :
    FiniteInstrumentComp n E :=
  μ.bind f

variable [CompleteLattice D] [CompleteLattice E]

/-- Operational weighted combination of two result instruments. -/
noncomputable def evalWeighted
    (p : Prob) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (μ ν : FiniteInstrumentComp n PUnit.{1}) :
    FiniteInstrumentComp n PUnit.{1} :=
  μ.weightedResult p hp₀ hp₁ ν

/-- Environment selection of an external alternative. -/
def evalSelect (tag : Bool) (μ ν : FiniteInstrumentComp n D) :
    FiniteInstrumentComp n D :=
  if tag then ν else μ

/-- Token observation of a finite instrument after a finitely presented
result continuation. -/
noncomputable def observe
    (μ : FiniteInstrumentComp n D)
    (ξ : D → FiniteInstrumentComp n PUnit.{1}) :
    TTContinuation.TTResult n :=
  (μ.bind ξ).satisfiedTTTheory TTContinuation.resultCode

end PrimitiveEvaluation

namespace PrimitiveEvaluation

variable {D : Type}
variable [CompleteLattice D]

/-- First-order programs built from qubit primitives and the three
choice constructors.  Application and recursion are excluded.
The value type is in `Type` because `Term` is not universe-polymorphic. -/
inductive FirstOrder : Term (QubitPrimitive D) → Prop
  | prim (p : QubitPrimitive D) : FirstOrder (.prim p)
  | intern {M N : Term (QubitPrimitive D)} :
      FirstOrder M → FirstOrder N → FirstOrder (.intern M N)
  | extern {M N : Term (QubitPrimitive D)} :
      FirstOrder M → FirstOrder N → FirstOrder (.extern M N)
  | prob (p : Prob) {M N : Term (QubitPrimitive D)} :
      FirstOrder M → FirstOrder N → FirstOrder (.prob p M N)

/-- Operational tagged denotation of a first-order primitive program.
Non-first-order constructors are sent to bottom. -/
noncomputable def denoteFirstOrder :
    Term (QubitPrimitive D) →
      TTContinuation.TTExternalContinuationPower 2 D
  | .prim p => denote p
  | .intern M N =>
      TTContinuation.liftTaggedBinary
        (TTContinuation.internalChoice (n := 2) (D := D))
        (denoteFirstOrder M, denoteFirstOrder N)
  | .extern M N =>
      TTContinuation.externalChoice (denoteFirstOrder M, denoteFirstOrder N)
  | .prob p M N =>
      TTContinuation.liftTaggedBinary
        (TTContinuation.probChoice (n := 2) (D := D) p)
        (denoteFirstOrder M, denoteFirstOrder N)
  | _ => ⊥

end PrimitiveEvaluation

namespace Adequacy

open PrimitiveEvaluation
open TTPhysicalEmbedding
open TTContinuation

variable {n : ℕ} {D E : Type u}
variable [CompleteLattice D] [CompleteLattice E]

/-- A result continuation is presented by finite result instruments at
the values returned by `μ`. -/
def PresentedAt (μ : FiniteInstrumentComp n D)
    (k : ScottMap D (TTResult n))
    (ξ : D → FiniteInstrumentComp n PUnit.{1}) : Prop :=
  ∀ o : μ.Outcome,
    k (μ.value o) =
      (ξ (μ.value o)).satisfiedTTTheory resultCode

/-- Membership in a binary join of rounded theories is membership in
one of the two theories. -/
theorem mem_sup_iff {A C : TTResult n} {t : TTObservationToken n} :
    t ∈ A ⊔ C ↔ t ∈ A ∨ t ∈ C := by
  constructor
  · intro ht
    have hmem : t ∈ (sSup {A, C} : TTResult n) := by
      rwa [sSup_pair]
    obtain ⟨T, hT, htT⟩ :=
      (RoundedTheory.mem_sSup (S := ({A, C} : Set _))).mp hmem
    rcases Set.mem_insert_iff.mp hT with rfl | hT'
    · exact Or.inl htT
    · exact Or.inr ((Set.mem_singleton_iff.mp hT').symm ▸ htT)
  · intro h
    have hpair : (A ⊔ C : TTResult n) = sSup {A, C} := sSup_pair.symm
    rw [hpair]
    apply (RoundedTheory.mem_sSup (S := ({A, C} : Set _))).2
    rcases h with ht | ht
    · exact ⟨A, Set.mem_insert _ _, ht⟩
    · exact ⟨C, Set.mem_insert_of_mem _ (Set.mem_singleton _), ht⟩

/-- Token-by-token adequacy for a physical embedding. -/
theorem token_of_embed
    (μ : FiniteInstrumentComp n D)
    (ξ : D → FiniteInstrumentComp n PUnit.{1})
    (k : ScottMap D (TTResult n))
    (hk : PresentedAt μ k ξ)
    (t : TTObservationToken n) :
    t ∈ (embed μ k) ↔
      TTObservationToken.Holds resultCode t (μ.bind ξ) := by
  rw [embed_satisfied μ ξ k hk,
    FiniteInstrumentComp.mem_satisfiedTTTheory]

/-- The same observation, at every unresolved external tag. -/
theorem token_of_taggedEmbed
    (μ : FiniteInstrumentComp n D)
    (ξ : D → FiniteInstrumentComp n PUnit.{1})
    (k : ScottMap D (TTResult n))
    (hk : PresentedAt μ k ξ)
    (i : ℕ) (t : TTObservationToken n) :
    t ∈ (taggedEmbed μ i k) ↔
      TTObservationToken.Holds resultCode t (μ.bind ξ) :=
  token_of_embed μ ξ k hk t

/-- Deterministic return is token-adequate. -/
theorem token_of_ret (d : D)
    (ξ : D → FiniteInstrumentComp n PUnit.{1})
    (k : ScottMap D (TTResult n))
    (hk : PresentedAt (FiniteInstrumentComp.unit (n := n) d) k ξ)
    (t : TTObservationToken n) :
    t ∈ (embed (FiniteInstrumentComp.unit (n := n) d) k) ↔
      TTObservationToken.Holds resultCode t
        ((FiniteInstrumentComp.unit (n := n) d).bind ξ) :=
  token_of_embed _ ξ k hk t

/-- Pauli-X is token-adequate. -/
theorem token_of_pauliX (d : D)
    (ξ : D → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap D (TTResult 2))
    (hk : PresentedAt
      (FiniteInstrumentComp.ofOperation Qubit.pauliXOp d) k ξ)
    (i : ℕ) (t : TTObservationToken 2) :
    t ∈ (denote (.pauliX d) i k) ↔
      TTObservationToken.Holds resultCode t
        ((FiniteInstrumentComp.ofOperation Qubit.pauliXOp d).bind ξ) :=
  token_of_taggedEmbed _ ξ k hk i t

/-- Computational-basis measurement is token-adequate. -/
theorem token_of_measureZ (d₀ d₁ : D)
    (ξ : D → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap D (TTResult 2))
    (hk : PresentedAt
      (Qubit.measureZComp.map fun b => if b then d₁ else d₀) k ξ)
    (i : ℕ) (t : TTObservationToken 2) :
    t ∈ (denote (.measureZ d₀ d₁) i k) ↔
      TTObservationToken.Holds resultCode t
        ((Qubit.measureZComp.map fun b => if b then d₁ else d₀).bind ξ) :=
  token_of_taggedEmbed _ ξ k hk i t

/-- Every qubit primitive is token-adequate for its operational
instrument. -/
theorem token_of_primitive (p : QubitPrimitive D)
    (ξ : D → FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap D (TTResult 2))
    (hk : PresentedAt (eval p) k ξ)
    (i : ℕ) (t : TTObservationToken 2) :
    t ∈ (denote p i k) ↔
      TTObservationToken.Holds resultCode t ((eval p).bind ξ) :=
  token_of_taggedEmbed (eval p) ξ k hk i t

/-- Finite physical bind is token-adequate on finitely presented
continuations. -/
theorem token_of_bind
    (μ : FiniteInstrumentComp n D)
    (f : D → FiniteInstrumentComp n E)
    (h : ScottMap D (TTExternalContinuationPower n E))
    (hh : ∀ o : μ.Outcome, h (μ.value o) = taggedEmbed (f (μ.value o)))
    (ξ : E → FiniteInstrumentComp n PUnit.{1})
    (k : ScottMap E (TTResult n))
    (hk : PresentedAt (μ.bind f) k ξ)
    (i : ℕ) (t : TTObservationToken n) :
    t ∈ (taggedBindScott h (taggedEmbed μ) i k) ↔
      TTObservationToken.Holds resultCode t ((μ.bind f).bind ξ) := by
  rw [taggedEmbed_bind_satisfied μ f h hh ξ k hk i]
  exact token_of_taggedEmbed (μ.bind f) ξ k hk i t

/-- Internal choice observes the join of the two operational theories. -/
theorem token_of_intern
    (μ ν : FiniteInstrumentComp n D)
    (ξ : D → FiniteInstrumentComp n PUnit.{1})
    (k : ScottMap D (TTResult n))
    (hμ : PresentedAt μ k ξ) (hν : PresentedAt ν k ξ)
    (i : ℕ) (t : TTObservationToken n) :
    t ∈ (liftTaggedBinary (internalChoice (n := n) (D := D))
        (taggedEmbed μ, taggedEmbed ν) i k) ↔
      TTObservationToken.Holds resultCode t (μ.bind ξ) ∨
        TTObservationToken.Holds resultCode t (ν.bind ξ) := by
  change t ∈ (internalChoice (taggedEmbed μ i, taggedEmbed ν i) k) ↔ _
  rw [internalChoice_apply, mem_sup_iff]
  simp only [taggedEmbed_apply]
  rw [token_of_embed μ ξ k hμ t, token_of_embed ν ξ k hν t]

/-- Interior probabilistic choice observes the physical weighted
combination of the two result instruments. -/
theorem token_of_prob_interior
    (p : Prob) (hp₀ : 0 < p) (hp₁ : p < 1)
    (μ ν : FiniteInstrumentComp n D)
    (ξ : D → FiniteInstrumentComp n PUnit.{1})
    (k : ScottMap D (TTResult n))
    (hμ : PresentedAt μ k ξ) (hν : PresentedAt ν k ξ)
    (i : ℕ) (t : TTObservationToken n) :
    t ∈ (liftTaggedBinary (probChoice (n := n) (D := D) p)
        (taggedEmbed μ, taggedEmbed ν) i k) ↔
      TTObservationToken.Holds resultCode t
        ((μ.bind ξ).weightedResult p hp₀.le hp₁.le (ν.bind ξ)) := by
  change t ∈ (probChoice p (taggedEmbed μ i, taggedEmbed ν i) k) ↔ _
  rw [probChoice_apply, dif_pos ⟨hp₀.le, hp₁.le⟩]
  simp only [taggedEmbed_apply]
  have hobs :
      TTWeightedAggregation.weightedResultScott p hp₀.le hp₁.le
        (embed μ k, embed ν k) =
        ((μ.bind ξ).weightedResult p hp₀.le hp₁.le
          (ν.bind ξ)).satisfiedTTTheory resultCode := by
    rw [embed_satisfied μ ξ k hμ, embed_satisfied ν ξ k hν]
    exact TTWeightedAggregation.weightedResultScott_satisfied_interior
      p hp₀ hp₁ (μ.bind ξ) (ν.bind ξ)
  rw [hobs, FiniteInstrumentComp.mem_satisfiedTTTheory]

/-- External selection recovers the selected operational instrument. -/
theorem token_of_select
    (tag : Bool)
    (μ ν : FiniteInstrumentComp n D)
    (ξ : D → FiniteInstrumentComp n PUnit.{1})
    (k : ScottMap D (TTResult n))
    (hμ : PresentedAt μ k ξ) (hν : PresentedAt ν k ξ)
    (i : ℕ) (t : TTObservationToken n) :
    t ∈ (selectBranch tag
        (externalChoice (taggedEmbed μ, taggedEmbed ν)) i k) ↔
      TTObservationToken.Holds resultCode t
        ((evalSelect tag μ ν).bind ξ) := by
  cases tag
  · rw [selectBranch_false_external]
    simp only [evalSelect, Bool.false_eq_true, ↓reduceIte]
    exact token_of_taggedEmbed μ ξ k hμ i t
  · rw [selectBranch_true_external]
    simp only [evalSelect, ↓reduceIte]
    exact token_of_taggedEmbed ν ξ k hν i t

section Interpreter

variable (D₀ : QDomain.{0})
variable (j₀ : IsContinuousLatticeProjection D₀.carrier
  (QuantumFunctor
    (QModel (TTExternalContinuationPower 2)) D₀.carrier))

/-- First-order primitive programs are interpreted by their operational
tagged denotation. -/
theorem interp_firstOrder
    {M : Term (SemanticQubitPrimitive D₀ j₀)}
    (h : FirstOrder M)
    (ρ : Env
      (SemanticValue (TTExternalContinuationPower 2) D₀ j₀)) :
    interp (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (semanticPrimitive D₀ j₀) M ρ =
      denoteFirstOrder M := by
  induction h with
  | prim p =>
      rw [interp_prim_apply]
      rfl
  | intern hM hN ihM ihN =>
      rw [interp_intern_apply, ihM, ihN]
      rfl
  | extern hM hN ihM ihN =>
      rw [interp_extern_apply, ihM, ihN]
      rfl
  | prob p hM hN ihM ihN =>
      rw [interp_prob_apply, ihM, ihN]
      rfl

/-- Primitive terms are token-adequate in the interpreter. -/
theorem interp_token_of_primitive
    (p : SemanticQubitPrimitive D₀ j₀)
    (ξ : SemanticValue (TTExternalContinuationPower 2) D₀ j₀ →
      FiniteInstrumentComp 2 PUnit.{1})
    (k : ScottMap
      (SemanticValue (TTExternalContinuationPower 2) D₀ j₀)
      (TTResult 2))
    (hk : PresentedAt (eval p) k ξ)
    (ρ : Env
      (SemanticValue (TTExternalContinuationPower 2) D₀ j₀))
    (i : ℕ) (t : TTObservationToken 2) :
    t ∈ (interp (Q := TTExternalContinuationPower 2)
        (D₀ := D₀) (j₀ := j₀) (semanticPrimitive D₀ j₀)
        (.prim p) ρ i k) ↔
      TTObservationToken.Holds resultCode t ((eval p).bind ξ) := by
  rw [interp_primitive]
  exact token_of_primitive p ξ k hk i t

end Interpreter

/-! ## General adequacy boundary -/

/-- Every source-code test of `C` has an explicit Scott representation
in the result continuation model.  This is a density/separation
assumption, not a theorem of the present development. -/
def DensityHypothesis (C : OutputCode ℕ D) : Type (max 1 u) :=
  ∀ c : RatStepPostCode n, CodedTestRepresentation C c

/-- Under density, embedding order is finitary TT refinement. -/
theorem general_adequacy_of_embed_le
    (C : OutputCode ℕ D)
    (density : DensityHypothesis (n := n) (D := D) C)
    {μ ν : FiniteInstrumentComp n D}
    (h : embed μ ≤ embed ν) :
    FiniteInstrumentComp.FinitaryTTRefines C μ ν :=
  finitaryTTRefines_of_embed_le C density h

/-- Closed-term token adequacy, available only when the denotation is a
finite embedded instrument.  The hypothesis is discharged for first-order
primitives above and is not claimed for arbitrary recursive terms. -/
theorem closed_term_token_adequacy
    {Prim : Type}
    (D₀ : QDomain.{0})
    (j₀ : IsContinuousLatticeProjection D₀.carrier
      (QuantumFunctor
        (QModel (TTExternalContinuationPower n)) D₀.carrier))
    [HasComputationChoice
      (SemanticComp (TTExternalContinuationPower n) D₀ j₀)]
    (primitive : Prim →
      SemanticComp (TTExternalContinuationPower n) D₀ j₀)
    (M : Term Prim)
    (μ : FiniteInstrumentComp n
      (SemanticValue (TTExternalContinuationPower n) D₀ j₀))
    (ρ : Env (SemanticValue (TTExternalContinuationPower n) D₀ j₀))
    (hfinite : interp (Q := TTExternalContinuationPower n)
        (D₀ := D₀) (j₀ := j₀) primitive M ρ =
      taggedEmbed μ)
    (ξ : SemanticValue (TTExternalContinuationPower n) D₀ j₀ →
      FiniteInstrumentComp n PUnit.{1})
    (k : ScottMap
      (SemanticValue (TTExternalContinuationPower n) D₀ j₀)
      (TTResult n))
    (hk : PresentedAt μ k ξ)
    (i : ℕ) (t : TTObservationToken n) :
    t ∈ (interp (Q := TTExternalContinuationPower n)
        (D₀ := D₀) (j₀ := j₀) primitive M ρ i k) ↔
      TTObservationToken.Holds resultCode t (μ.bind ξ) := by
  rw [hfinite]
  exact token_of_taggedEmbed μ ξ k hk i t

/-- The finite physical image is not a Scott retract of the continuation
space whenever a directed family of finite embeddings has a non-finite
supremum.  Higher-order recursion may produce such denotations. -/
theorem no_finite_image_retract_of_directed_sup
    {S : Set (TTContinuationPower n D)}
    (hS : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S)
    (hfinite : S ⊆ Set.range (embed (n := n) (D := D)))
    (hnot : sSup S ∉ Set.range (embed (n := n) (D := D))) :
    FiniteImageScottRetraction n D → False :=
  no_finiteImageScottRetraction_of_directedSup_not_finite
    hS hdir hfinite hnot

end Adequacy

end QLambda
