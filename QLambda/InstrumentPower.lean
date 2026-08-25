/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Order.Antisymmetrization
import QLambda.QuantumInstrument
import QLambda.QuantumPower
import QLambda.ScottLowerSet

/-!
# Fixed-register instrument powerdomain

This module separates three layers:

1. finite Kraus-presented computations;
2. their observational refinement preorder and antisymmetrization;
3. a Scott-closed lower completion.

The register dimension `n` is fixed externally.  The active
`InstrumentPower` closes lower sets under existing directed limits. This
removes the false compactness assertion made by the discarded plain
lower-set completion.
-/

open Matrix
open scoped MatrixOrder

namespace QLambda

open Scott1972.ContinuousLattice

universe u v

namespace FiniteInstrumentComp

variable {n : ℕ} {D : Type u} {E : Type v}

/-- A quantum postcondition is a Kraus-valued predicate monotone in the
residual CP order. -/
structure KrausPost (n : ℕ) (D : Type u) [Preorder D] where
  pred : D → KrausFamily n n
  mono : ∀ ⦃d e⦄, d ≤ e → KrausFamily.Refines (pred d) (pred e)

namespace KrausPost

instance [Preorder D] : CoeFun (KrausPost n D) (fun _ => D → KrausFamily n n) :=
  ⟨pred⟩

/-- Pull a quantum postcondition back along a monotone map. -/
def comap [Preorder D] [Preorder E] (P : KrausPost n E) (f : D →o E) :
    KrausPost n D where
  pred := P ∘ f
  mono := fun _ _ h => P.mono (f.mono h)

end KrausPost

/-- Weakest-precondition aggregation: execute each branch and then its
value-dependent quantum postcondition. -/
noncomputable def wpKraus [Preorder D] (μ : FiniteInstrumentComp n D)
    (P : D → KrausFamily n n) : KrausFamily n n := by
  classical
  exact Finset.univ.toList.flatMap fun o =>
    KrausFamily.comp (P (μ.value o)) (μ.branch o)

theorem applyMat_wpKraus [Preorder D] (μ : FiniteInstrumentComp n D)
    (P : D → KrausFamily n n) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    KrausFamily.applyMat (μ.wpKraus P) ρ =
      ∑ o : μ.Outcome,
        KrausFamily.applyMat
          (KrausFamily.comp (P (μ.value o)) (μ.branch o)) ρ := by
  classical
  unfold wpKraus
  rw [KrausFamily.applyMat_flatMap]
  simp

/-- Weakest-precondition action is invariant under outcome reindexing that
preserves branches and returned values. -/
theorem wpKraus_congr_of_outcome_equiv [Preorder D]
    (μ ν : FiniteInstrumentComp n D)
    (e : μ.Outcome ≃ ν.Outcome)
    (hbranch : ∀ o, ν.branch (e o) = μ.branch o)
    (hvalue : ∀ o, ν.value (e o) = μ.value o)
    (P : D → KrausFamily n n) :
    KrausFamily.SemEq (μ.wpKraus P) (ν.wpKraus P) := by
  intro ρ
  rw [applyMat_wpKraus, applyMat_wpKraus]
  refine Fintype.sum_equiv e
      (fun o => KrausFamily.applyMat
        (KrausFamily.comp (P (μ.value o)) (μ.branch o)) ρ)
      (fun q => KrausFamily.applyMat
        (KrausFamily.comp (P (ν.value q)) (ν.branch q)) ρ)
      ?_
  intro o
  rw [hbranch o, hvalue o]

theorem wpKraus_unit_semEq [Preorder D] (d : D)
    (P : D → KrausFamily n n) :
    KrausFamily.SemEq ((unit (n := n) d).wpKraus P) (P d) := by
  intro ρ
  rw [applyMat_wpKraus]
  change (∑ _ : Unit,
    KrausFamily.applyMat
      (KrausFamily.comp (P d) (KrausFamily.identity n)) ρ) =
    KrausFamily.applyMat (P d) ρ
  simp

theorem wpKraus_ofOperation_semEq [Preorder D]
    (Φ : QuantumOperation n n) (d : D)
    (P : D → KrausFamily n n) :
    KrausFamily.SemEq
      ((ofOperation Φ d).wpKraus P)
      (KrausFamily.comp (P d) Φ.kraus) := by
  intro ρ
  rw [applyMat_wpKraus]
  change
    (∑ _ : Unit,
      KrausFamily.applyMat
        (KrausFamily.comp (P d) Φ.kraus) ρ) =
      KrausFamily.applyMat
        (KrausFamily.comp (P d) Φ.kraus) ρ
  simp

theorem wpKraus_bind_semEq [Preorder D] [Preorder E]
    (μ : FiniteInstrumentComp n D) (f : D → FiniteInstrumentComp n E)
    (P : E → KrausFamily n n) :
    KrausFamily.SemEq ((μ.bind f).wpKraus P)
      (μ.wpKraus fun d => (f d).wpKraus P) := by
  intro ρ
  rw [applyMat_wpKraus, applyMat_wpKraus]
  change
    (∑ p : Σ o : μ.Outcome, (f (μ.value o)).Outcome,
      KrausFamily.applyMat
        (KrausFamily.comp
          (P ((f (μ.value p.1)).value p.2))
          (KrausFamily.comp
            ((f (μ.value p.1)).branch p.2)
            (μ.branch p.1))) ρ) =
      ∑ o : μ.Outcome,
        KrausFamily.applyMat
          (KrausFamily.comp ((f (μ.value o)).wpKraus P) (μ.branch o)) ρ
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro o _
  rw [KrausFamily.applyMat_comp, applyMat_wpKraus]
  simp only [KrausFamily.applyMat_comp]

/-- Bind then observe is likewise invariant under the same reindexing. -/
theorem bind_wpKraus_congr_of_outcome_equiv [Preorder D] [Preorder E]
    (μ ν : FiniteInstrumentComp n D)
    (e : μ.Outcome ≃ ν.Outcome)
    (hbranch : ∀ o, ν.branch (e o) = μ.branch o)
    (hvalue : ∀ o, ν.value (e o) = μ.value o)
    (ξ : D → FiniteInstrumentComp n E)
    (P : E → KrausFamily n n) :
    KrausFamily.SemEq ((μ.bind ξ).wpKraus P) ((ν.bind ξ).wpKraus P) := by
  intro ρ
  calc
    KrausFamily.applyMat ((μ.bind ξ).wpKraus P) ρ =
        KrausFamily.applyMat (μ.wpKraus fun d => (ξ d).wpKraus P) ρ :=
      wpKraus_bind_semEq μ ξ P ρ
    _ = KrausFamily.applyMat (ν.wpKraus fun d => (ξ d).wpKraus P) ρ :=
      wpKraus_congr_of_outcome_equiv μ ν e hbranch hvalue
        (fun d => (ξ d).wpKraus P) ρ
    _ = KrausFamily.applyMat ((ν.bind ξ).wpKraus P) ρ :=
      (wpKraus_bind_semEq ν ξ P ρ).symm

/-- Kraus branches whose returned values lie in `U`.  Their concatenation
denotes the sum of those CP branches and is independent of list order at
the Choi level. -/
noncomputable def selectedKraus (μ : FiniteInstrumentComp n D) (U : Set D) :
    KrausFamily n n := by
  classical
  exact ((Finset.univ.filter fun o : μ.Outcome => μ.value o ∈ U).toList).flatMap μ.branch

/-- Choi denotation of the branches selected by an outcome test. -/
noncomputable def testChoi (μ : FiniteInstrumentComp n D) (U : Set D) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ := by
  classical
  exact ∑ o : μ.Outcome,
    if μ.value o ∈ U then KrausFamily.choi (μ.branch o) else 0

/-- Weakest-precondition/TT refinement.  It quantifies over all monotone
Kraus-valued postconditions, making the order stable under monotone
value-dependent quantum continuations. -/
def Refines [Preorder D] (μ ν : FiniteInstrumentComp n D) : Prop :=
  ∀ P : KrausPost n D, KrausFamily.Refines (μ.wpKraus P) (ν.wpKraus P)

theorem refines_refl [Preorder D] (μ : FiniteInstrumentComp n D) :
    Refines μ μ :=
  fun _ => KrausFamily.residualRefines_refl _

theorem refines_trans [Preorder D] {μ ν ξ : FiniteInstrumentComp n D}
    (hμν : Refines μ ν) (hνξ : Refines ν ξ) : Refines μ ξ :=
  fun P => KrausFamily.residualRefines_trans (hμν P) (hνξ P)

noncomputable instance instPreorderFiniteInstrumentComp [Preorder D] :
    Preorder (FiniteInstrumentComp n D) where
  le := Refines
  le_refl := refines_refl
  le_trans _ _ _ := refines_trans

theorem le_def [Preorder D] {μ ν : FiniteInstrumentComp n D} :
    μ ≤ ν ↔ ∀ P : KrausPost n D,
      KrausFamily.Refines (μ.wpKraus P) (ν.wpKraus P) :=
  Iff.rfl

namespace KrausPost

/-- Pull a postcondition backwards through a refinement-monotone finite
instrument continuation. -/
noncomputable def bind [Preorder D] [Preorder E] (P : KrausPost n E)
    (f : D → FiniteInstrumentComp n E) (hf : Monotone f) :
    KrausPost n D where
  pred := fun d => (f d).wpKraus P
  mono := fun _ _ h => hf h P

end KrausPost

theorem wpKraus_mono_pred [Preorder D] (μ : FiniteInstrumentComp n D)
    {P Q : D → KrausFamily n n}
    (hPQ : ∀ d, KrausFamily.Refines (P d) (Q d)) :
    KrausFamily.Refines (μ.wpKraus P) (μ.wpKraus Q) := by
  classical
  unfold wpKraus
  apply KrausFamily.residualRefines_flatMap
  intro o _
  exact KrausFamily.residualRefines_comp_right (μ.branch o) (hPQ (μ.value o))

theorem wpKraus_semEq_pred [Preorder D] (μ : FiniteInstrumentComp n D)
    {P Q : D → KrausFamily n n}
    (hPQ : ∀ d, KrausFamily.SemEq (P d) (Q d)) :
    KrausFamily.SemEq (μ.wpKraus P) (μ.wpKraus Q) := by
  intro ρ
  rw [applyMat_wpKraus, applyMat_wpKraus]
  apply Finset.sum_congr rfl
  intro o _
  simp only [KrausFamily.applyMat_comp]
  exact hPQ (μ.value o) (KrausFamily.applyMat (μ.branch o) ρ)

theorem wpKraus_map [Preorder D] [Preorder E]
    (f : D → E) (μ : FiniteInstrumentComp n D) (P : E → KrausFamily n n) :
    (μ.map f).wpKraus P = μ.wpKraus (P ∘ f) := by
  rfl

/-- Pushforward respects TT refinement along monotone maps. -/
theorem map_mono [Preorder D] [Preorder E] (f : D →o E) :
    Monotone (FiniteInstrumentComp.map (n := n) (f : D → E)) := by
  intro μ ν hμν P
  rw [wpKraus_map, wpKraus_map]
  exact hμν (P.comap f)

/-- Pointwise larger result maps produce observationally larger
pushforwards. -/
theorem map_le_map [Preorder D] [Preorder E]
    {f g : D →o E} (hfg : f ≤ g) (μ : FiniteInstrumentComp n D) :
    μ.map f ≤ μ.map g := by
  intro P
  rw [wpKraus_map, wpKraus_map]
  exact wpKraus_mono_pred μ fun d => P.mono (hfg d)

/-- Deterministic return is monotone in its returned value. -/
theorem unit_mono [Preorder D] :
    Monotone (unit (n := n) : D → FiniteInstrumentComp n D) := by
  intro d e hde P
  exact KrausFamily.residualRefines_trans
    (KrausFamily.residualRefines_of_semEq (wpKraus_unit_semEq d P))
    (KrausFamily.residualRefines_trans
      (P.mono hde)
      (KrausFamily.residualRefines_of_semEq
        (KrausFamily.applySemEq_symm (wpKraus_unit_semEq e P))))

/-- Bind is monotone in its computation argument when the continuation
is monotone in TT refinement. -/
theorem bind_mono_left [Preorder D] [Preorder E]
    (f : D → FiniteInstrumentComp n E) (hf : Monotone f) :
    Monotone fun μ : FiniteInstrumentComp n D => μ.bind f := by
  intro μ ν hμν P
  exact KrausFamily.residualRefines_trans
    (KrausFamily.residualRefines_of_semEq (wpKraus_bind_semEq μ f P))
    (KrausFamily.residualRefines_trans
      (hμν (P.bind f hf))
      (KrausFamily.residualRefines_of_semEq
        (KrausFamily.applySemEq_symm (wpKraus_bind_semEq ν f P))))

/-- Bind is monotone in a pointwise-refined continuation. -/
theorem bind_mono_right [Preorder D] [Preorder E]
    (μ : FiniteInstrumentComp n D)
    {f g : D → FiniteInstrumentComp n E} (hfg : ∀ d, f d ≤ g d) :
    μ.bind f ≤ μ.bind g := by
  intro P
  exact KrausFamily.residualRefines_trans
    (KrausFamily.residualRefines_of_semEq (wpKraus_bind_semEq μ f P))
    (KrausFamily.residualRefines_trans
      (wpKraus_mono_pred μ fun d => hfg d P)
      (KrausFamily.residualRefines_of_semEq
        (KrausFamily.applySemEq_symm (wpKraus_bind_semEq μ g P))))

/-- Two-sided bind congruence for monotone continuations. -/
theorem bind_mono [Preorder D] [Preorder E]
    {μ ν : FiniteInstrumentComp n D} (hμν : μ ≤ ν)
    {f g : D → FiniteInstrumentComp n E} (hf : Monotone f)
    (hfg : ∀ d, f d ≤ g d) :
    μ.bind f ≤ ν.bind g :=
  (bind_mono_left f hf hμν).trans (bind_mono_right ν hfg)

/-- Mutual TT refinement, used to state finite monad laws before
antisymmetrization. -/
def Equiv [Preorder D] (μ ν : FiniteInstrumentComp n D) : Prop :=
  μ ≤ ν ∧ ν ≤ μ

theorem equiv_of_wpKraus_semEq [Preorder D]
    {μ ν : FiniteInstrumentComp n D}
    (h : ∀ P : KrausPost n D,
      KrausFamily.SemEq (μ.wpKraus P) (ν.wpKraus P)) :
    Equiv μ ν := by
  constructor <;> intro P
  · exact KrausFamily.residualRefines_of_semEq (h P)
  · exact KrausFamily.residualRefines_of_semEq
      (KrausFamily.applySemEq_symm (h P))

theorem unit_bind_equiv [Preorder D] [Preorder E]
    (d : D) (f : D → FiniteInstrumentComp n E) :
    Equiv ((unit (n := n) d).bind f) (f d) := by
  apply equiv_of_wpKraus_semEq
  intro P
  exact KrausFamily.applySemEq_trans
    (wpKraus_bind_semEq (unit (n := n) d) f P)
    (wpKraus_unit_semEq d fun x => (f x).wpKraus P)

theorem bind_unit_equiv [Preorder D] (μ : FiniteInstrumentComp n D) :
    Equiv (μ.bind (unit (n := n))) μ := by
  apply equiv_of_wpKraus_semEq
  intro P
  exact KrausFamily.applySemEq_trans
    (wpKraus_bind_semEq μ (unit (n := n)) P)
    (wpKraus_semEq_pred μ fun d => wpKraus_unit_semEq d P)

/-- Associativity of finite instrument bind, modulo mutual TT refinement. -/
theorem bind_assoc_equiv [Preorder D] [Preorder E] {F : Type u} [Preorder F]
    (μ : FiniteInstrumentComp n D)
    (f : D → FiniteInstrumentComp n E)
    (g : E → FiniteInstrumentComp n F) :
    Equiv ((μ.bind f).bind g) (μ.bind fun d => (f d).bind g) := by
  apply equiv_of_wpKraus_semEq
  intro P
  exact KrausFamily.applySemEq_trans
    (wpKraus_bind_semEq (μ.bind f) g P)
    (KrausFamily.applySemEq_trans
      (wpKraus_bind_semEq μ f fun e => (g e).wpKraus P)
      (KrausFamily.applySemEq_trans
        (wpKraus_semEq_pred μ fun d =>
          KrausFamily.applySemEq_symm (wpKraus_bind_semEq (f d) g P))
        (KrausFamily.applySemEq_symm
          (wpKraus_bind_semEq μ (fun d => (f d).bind g) P))))

theorem map_equiv_bind_unit [Preorder D] [Preorder E]
    (f : D → E) (μ : FiniteInstrumentComp n D) :
    Equiv (μ.map f) (μ.bind fun d => unit (n := n) (f d)) := by
  apply equiv_of_wpKraus_semEq
  intro P
  rw [wpKraus_map]
  exact KrausFamily.applySemEq_symm <|
    KrausFamily.applySemEq_trans
      (wpKraus_bind_semEq μ (fun d => unit (n := n) (f d)) P)
      (wpKraus_semEq_pred μ fun d => wpKraus_unit_semEq (f d) P)

/-- Pushforward as an order homomorphism on finite presentations. -/
noncomputable def mapHom [CompleteLattice D] [CompleteLattice E] (f : ScottMap D E) :
    FiniteInstrumentComp n D →o FiniteInstrumentComp n E :=
  ⟨FiniteInstrumentComp.map (n := n) (f : D → E),
    map_mono (n := n) ⟨f, f.monotone⟩⟩

end FiniteInstrumentComp

/-- Finite instruments modulo mutual observational refinement. -/
abbrev SemanticInstrument (n : ℕ) (D : Type u) [CompleteLattice D] :=
  Antisymmetrization (FiniteInstrumentComp n D) (· ≤ ·)

/-- Scott-closed Hoare completion of finite semantic instruments.
Arbitrary joins take Scott closure after union, so limit instruments are
not forced to be compact principals. -/
abbrev InstrumentPower (n : ℕ) (D : Type u) [CompleteLattice D] :=
  ScottLowerSet (SemanticInstrument n D)

namespace InstrumentPower

variable {n : ℕ} {D E : Type u} [CompleteLattice D] [CompleteLattice E]

/-- Embed a finite computation by Scott-closing its principal ideal. -/
noncomputable def ofFinite (μ : FiniteInstrumentComp n D) : InstrumentPower n D :=
  ScottLowerSet.principal (toAntisymmetrization (· ≤ ·) μ)

theorem ofFinite_le_iff {μ : FiniteInstrumentComp n D}
    {A : InstrumentPower n D} :
    ofFinite μ ≤ A ↔ toAntisymmetrization (· ≤ ·) μ ∈ A :=
  ScottLowerSet.principal_le_iff_mem

theorem ofFinite_mono :
    Monotone (ofFinite (n := n) (D := D)) := by
  intro μ ν hμν
  rw [ofFinite_le_iff]
  exact ScottLowerSet.mem_principal.mpr (toAntisymmetrization_mono hμν)

/-- Pushforward on the antisymmetrized finite semantic basis. -/
noncomputable def basisMap (f : ScottMap D E) :
    SemanticInstrument n D →o SemanticInstrument n E :=
  (FiniteInstrumentComp.mapHom f).antisymmetrization

theorem basisMap_le {f g : ScottMap D E} (hfg : f ≤ g) :
    basisMap (n := n) f ≤ basisMap (n := n) g := by
  intro a
  refine Antisymmetrization.induction_on (· ≤ ·) a ?_
  intro μ
  rw [basisMap, basisMap,
    OrderHom.antisymmetrization_apply_mk,
    OrderHom.antisymmetrization_apply_mk,
    toAntisymmetrization_le_toAntisymmetrization_iff]
  exact FiniteInstrumentComp.map_le_map
    (f := ⟨f, f.monotone⟩) (g := ⟨g, g.monotone⟩) hfg μ

@[simp] theorem basisMap_id :
    basisMap (n := n) (ScottMap.idMap : ScottMap D D) = OrderHom.id := by
  apply OrderHom.ext
  funext a
  refine Antisymmetrization.induction_on (· ≤ ·) a ?_
  intro μ
  rw [basisMap, OrderHom.antisymmetrization_apply_mk]
  change toAntisymmetrization (· ≤ ·)
      (FiniteInstrumentComp.map (n := n)
        (ScottMap.idMap : D → D) μ) =
    toAntisymmetrization (· ≤ ·) μ
  have hid : (ScottMap.idMap : D → D) = id := by
    funext d
    rfl
  rw [hid, FiniteInstrumentComp.map_id]

theorem basisMap_comp {F : Type u} [CompleteLattice F]
    (g : ScottMap E F) (f : ScottMap D E) :
    basisMap (n := n) (g.comp f) =
      (basisMap (n := n) g).comp (basisMap (n := n) f) := by
  apply OrderHom.ext
  funext a
  refine Antisymmetrization.induction_on (· ≤ ·) a ?_
  intro μ
  rw [basisMap, OrderHom.antisymmetrization_apply_mk]
  change toAntisymmetrization (· ≤ ·)
      (FiniteInstrumentComp.map (n := n)
        ((g : E → F) ∘ (f : D → E)) μ) =
    basisMap (n := n) g
      (basisMap (n := n) f (toAntisymmetrization (· ≤ ·) μ))
  rw [basisMap, basisMap,
    OrderHom.antisymmetrization_apply_mk,
    OrderHom.antisymmetrization_apply_mk]
  apply congrArg (toAntisymmetrization (· ≤ ·))
  exact FiniteInstrumentComp.map_comp (g : E → F) (f : D → E) μ

end InstrumentPower

end QLambda
