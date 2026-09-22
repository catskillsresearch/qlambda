/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.LinearNonlinear
import QLambda.Domain.QuantumCPO
import QLambda.Domain.RecursiveTypes
import QLambda.Linear.Operational

/-!
# Denotation boundary for the typed linear calculus

This file contains the strongest denotational layer justified by the current
interfaces.

* `ContextObject` gives the standard LNL object assigned to an unrestricted
  and a linear context.
* `DenotationModel` is a proof-free interface for the categorical operations
  needed by every typing rule, and `HasType.denote` is the type-indexed,
  compositional interpretation of derivations.
* `Prim.completedCP` and `qubitMeasurement` are concrete, presentation-
  independent completed CP meanings of the physical primitives.
* `OperationalMeaning` is the exact quotient by classical source reduction.
  It validates the beta, fix, and fold/unfold equations that are already
  mathematically supported by `Step`.

There is deliberately no claimed concrete `DenotationModel`.  The current
`LNLModel` interface has no chosen interpretation of base or recursive types,
no context-splitting/coherence maps, no branching object, and no map from
`CompletedCP` into linear homs.  Moreover `CompletedCP` currently exposes
finite composition monotonicity but not the Scott-continuous extension needed
to make completed CP maps an `OmegaCategory`.  Supplying any of these as an
unproved theorem premise would merely hide the missing model.
-/

namespace QLambda.Linear

open QLambda.Domain
open QLambda.Domain.OmegaCategory

universe u v

namespace ContextObject

/-- The nonlinear object carrying an unrestricted context.  A source type is
viewed nonlinearly through `G`; products account for contraction and
weakening. -/
def unrestricted (M : LNLModel.{u, v})
    (I : Ty → M.linear.Obj) : List Ty → M.nonlinear.Obj
  | [] => M.nonlinearClosed.terminal
  | A :: Γ =>
      M.nonlinearClosed.product (M.G.obj (I A)) (unrestricted M I Γ)

/-- Linear contexts retain `none` cells as tensor units, so de Bruijn indices
remain aligned across an `OSplit`. -/
def linear (M : LNLModel.{u, v})
    (I : Ty → M.linear.Obj) : List (Option Ty) → M.linear.Obj
  | [] => M.linearClosed.unit
  | none :: Δ =>
      M.linearClosed.tensor M.linearClosed.unit (linear M I Δ)
  | some A :: Δ =>
      M.linearClosed.tensor (I A) (linear M I Δ)

/-- Standard LNL context object `F⟦Γ⟧ ⊗ ⟦Δ⟧`. -/
def combined (M : LNLModel.{u, v}) (I : Ty → M.linear.Obj)
    (Γ : List Ty) (Δ : List (Option Ty)) : M.linear.Obj :=
  M.linearClosed.tensor (M.F.obj (unrestricted M I Γ)) (linear M I Δ)

end ContextObject

/-- Categorical operations required to interpret all typing derivations.

The operations are data, not axioms claiming that a concrete model exists.
Their types expose every presently missing structural map.  In particular,
`prim` and `measure` cannot yet be derived from `CompletedCP`, because the
foundations do not define a functor from completed CP maps to `M.linear`. -/
structure DenotationModel (M : LNLModel.{u, v}) where
  ty : Ty → M.linear.Obj
  varU :
    ∀ {Γ Δ n A}, Lookup Γ n A → Ty.Duplicable A → AllNone Δ →
      M.linear.Hom (ContextObject.combined M ty Γ Δ) (ty A)
  varL :
    ∀ {Γ Δ n A}, Lookup Δ n (some A) → OnlySomeAt Δ n →
      M.linear.Hom (ContextObject.combined M ty Γ Δ) (ty A)
  lamU :
    ∀ {Γ Δ A B}, Ty.Admissible A → Ty.Duplicable A → AllNone Δ →
      M.linear.Hom (ContextObject.combined M ty (A :: Γ) Δ) (ty B) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ)
        (ty (.arrow .unres A B))
  lamL :
    ∀ {Γ Δ A B}, Ty.Admissible A →
      M.linear.Hom (ContextObject.combined M ty Γ (some A :: Δ)) (ty B) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ) (ty (.arrow .lin A B))
  appL :
    ∀ {Γ Δ Δ₁ Δ₂ A B}, OSplit Δ Δ₁ Δ₂ →
      M.linear.Hom (ContextObject.combined M ty Γ Δ₁)
        (ty (.arrow .lin A B)) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ₂) (ty A) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ) (ty B)
  appU :
    ∀ {Γ Δ ΔF ΔX A B}, OSplit Δ ΔF ΔX → AllNone ΔX →
      M.linear.Hom (ContextObject.combined M ty Γ ΔF)
        (ty (.arrow .unres A B)) →
      M.linear.Hom (ContextObject.combined M ty Γ ΔX) (ty A) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ) (ty B)
  unit :
    ∀ {Γ Δ}, AllNone Δ →
      M.linear.Hom (ContextObject.combined M ty Γ Δ) (ty .unit)
  bitLit :
    ∀ {Γ Δ}, Bool → AllNone Δ →
      M.linear.Hom (ContextObject.combined M ty Γ Δ) (ty .bit)
  pair :
    ∀ {Γ Δ Δ₁ Δ₂ A B}, OSplit Δ Δ₁ Δ₂ →
      M.linear.Hom (ContextObject.combined M ty Γ Δ₁) (ty A) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ₂) (ty B) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ) (ty (.tensor A B))
  unpair :
    ∀ {Γ Δ Δ₁ Δ₂ A B C}, OSplit Δ Δ₁ Δ₂ →
      M.linear.Hom (ContextObject.combined M ty Γ Δ₁) (ty (.tensor A B)) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ₂)
        (ty (.arrow .lin A (.arrow .lin B C))) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ) (ty C)
  ite :
    ∀ {Γ Δ Δ₁ Δ₂ A}, OSplit Δ Δ₁ Δ₂ →
      M.linear.Hom (ContextObject.combined M ty Γ Δ₁) (ty .bit) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ₂) (ty A) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ₂) (ty A) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ) (ty A)
  prim :
    ∀ {Γ Δ}, (p : Prim) → AllNone Δ →
      M.linear.Hom (ContextObject.combined M ty Γ Δ) (ty (primTy p))
  measure :
    ∀ {Γ Δ Δ₁ Δ₂ A}, OSplit Δ Δ₁ Δ₂ →
      M.linear.Hom (ContextObject.combined M ty Γ Δ₁) (ty .qubit) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ₂)
        (ty (.arrow .unres .bit (.arrow .lin .qubit A))) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ) (ty A)
  fix :
    ∀ {Γ Δ A}, Ty.Admissible A → Ty.Duplicable A → AllNone Δ →
      M.linear.Hom (ContextObject.combined M ty Γ Δ)
        (ty (.arrow .unres A A)) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ) (ty A)
  fold :
    ∀ {Γ Δ A}, Ty.Admissible (.mu A) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ)
        (ty (Ty.subst 0 (.mu A) A)) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ) (ty (.mu A))
  unfold :
    ∀ {Γ Δ A}, Ty.Admissible (.mu A) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ) (ty (.mu A)) →
      M.linear.Hom (ContextObject.combined M ty Γ Δ)
        (ty (Ty.subst 0 (.mu A) A))
  interpret :
    ∀ {Γ Δ t A}, HasType Γ Δ t A →
      M.linear.Hom (ContextObject.combined M ty Γ Δ) (ty A)
  interpret_varU :
    ∀ {Γ Δ n A} (h : Lookup Γ n A)
      (hdup : Ty.Duplicable A) (hnone : AllNone Δ),
      interpret (HasType.varU h hdup hnone) = varU h hdup hnone
  interpret_varL :
    ∀ {Γ Δ n A} (h : Lookup Δ n (some A)) (honly : OnlySomeAt Δ n),
      interpret (HasType.varL (Γ := Γ) h honly) = varL (Γ := Γ) h honly
  interpret_lamU :
    ∀ {Γ Δ A B t} (hadm : Ty.Admissible A)
      (hdup : Ty.Duplicable A) (hnone : AllNone Δ)
      (h : HasType (A :: Γ) Δ t B),
      interpret (HasType.lamU hadm hdup hnone h) =
        lamU hadm hdup hnone (interpret h)
  interpret_lamL :
    ∀ {Γ Δ A B t} (hadm : Ty.Admissible A)
      (h : HasType Γ (some A :: Δ) t B),
      interpret (HasType.lamL hadm h) = lamL hadm (interpret h)
  interpret_appL :
    ∀ {Γ Δ Δ₁ Δ₂ A B F X} (hs : OSplit Δ Δ₁ Δ₂)
      (hF : HasType Γ Δ₁ F (.arrow .lin A B)) (hX : HasType Γ Δ₂ X A),
      interpret (HasType.appL hs hF hX) =
        appL hs (interpret hF) (interpret hX)
  interpret_appU :
    ∀ {Γ Δ ΔF ΔX A B F X} (hs : OSplit Δ ΔF ΔX)
      (hnone : AllNone ΔX)
      (hF : HasType Γ ΔF F (.arrow .unres A B)) (hX : HasType Γ ΔX X A),
      interpret (HasType.appU hs hnone hF hX) =
        appU hs hnone (interpret hF) (interpret hX)
  interpret_unit :
    ∀ {Γ Δ} (hnone : AllNone Δ),
      interpret (HasType.unit (Γ := Γ) hnone) = unit (Γ := Γ) hnone
  interpret_bitLit :
    ∀ {Γ Δ b} (hnone : AllNone Δ),
      interpret (HasType.bitLit (Γ := Γ) (b := b) hnone) =
        bitLit (Γ := Γ) b hnone
  interpret_pair :
    ∀ {Γ Δ Δ₁ Δ₂ A B t s} (hs : OSplit Δ Δ₁ Δ₂)
      (ht : HasType Γ Δ₁ t A) (hs' : HasType Γ Δ₂ s B),
      interpret (HasType.pair hs ht hs') =
        pair hs (interpret ht) (interpret hs')
  interpret_unpair :
    ∀ {Γ Δ Δ₁ Δ₂ A B C t k} (hs : OSplit Δ Δ₁ Δ₂)
      (ht : HasType Γ Δ₁ t (.tensor A B))
      (hk : HasType Γ Δ₂ k (.arrow .lin A (.arrow .lin B C))),
      interpret (HasType.unpair hs ht hk) =
        unpair hs (interpret ht) (interpret hk)
  interpret_ite :
    ∀ {Γ Δ Δ₁ Δ₂ A b t e} (hs : OSplit Δ Δ₁ Δ₂)
      (hb : HasType Γ Δ₁ b .bit) (ht : HasType Γ Δ₂ t A)
      (he : HasType Γ Δ₂ e A),
      interpret (HasType.ite hs hb ht he) =
        ite hs (interpret hb) (interpret ht) (interpret he)
  interpret_prim :
    ∀ {Γ Δ p} (hnone : AllNone Δ),
      interpret (HasType.prim (p := p) (Γ := Γ) hnone) =
        prim (Γ := Γ) p hnone
  interpret_measure :
    ∀ {Γ Δ Δ₁ Δ₂ A q k} (hs : OSplit Δ Δ₁ Δ₂)
      (hq : HasType Γ Δ₁ q .qubit)
      (hk : HasType Γ Δ₂ k
        (.arrow .unres .bit (.arrow .lin .qubit A))),
      interpret (HasType.measure hs hq hk) =
        measure hs (interpret hq) (interpret hk)
  interpret_fix :
    ∀ {Γ Δ A t} (hadm : Ty.Admissible A)
      (hdup : Ty.Duplicable A) (hnone : AllNone Δ)
      (ht : HasType Γ Δ t (.arrow .unres A A)),
      interpret (HasType.fix hadm hdup hnone ht) =
        fix hadm hdup hnone (interpret ht)
  interpret_fold :
    ∀ {Γ Δ A t} (hadm : Ty.Admissible (.mu A))
      (ht : HasType Γ Δ t (Ty.subst 0 (.mu A) A)),
      interpret (HasType.fold hadm ht) = fold hadm (interpret ht)
  interpret_unfold :
    ∀ {Γ Δ A t} (hadm : Ty.Admissible (.mu A))
      (ht : HasType Γ Δ t (.mu A)),
      interpret (HasType.unfold hadm ht) = unfold hadm (interpret ht)

namespace HasType

/-- Type-indexed compositional interpretation of a typing derivation.

`HasType` lives in `Prop`, so Lean cannot eliminate it into hom data.  The
interpretation and all constructor equations are explicit fields of
`DenotationModel`, rather than an illicit large elimination. -/
def denote {M : LNLModel.{u, v}} (S : DenotationModel M)
    {Γ Δ t A} (h : HasType Γ Δ t A) :
    M.linear.Hom (ContextObject.combined M S.ty Γ Δ) (S.ty A) :=
  S.interpret h

@[simp] theorem denote_varU {M : LNLModel.{u, v}} (S : DenotationModel M)
    {Γ Δ n A} (h : Lookup Γ n A) (hdup : Ty.Duplicable A)
    (hnone : AllNone Δ) :
    denote S (HasType.varU h hdup hnone) = S.varU h hdup hnone :=
  S.interpret_varU h hdup hnone

@[simp] theorem denote_appL {M : LNLModel.{u, v}} (S : DenotationModel M)
    {Γ Δ Δ₁ Δ₂ A B F X} (hs : OSplit Δ Δ₁ Δ₂)
    (hF : HasType Γ Δ₁ F (.arrow .lin A B))
    (hX : HasType Γ Δ₂ X A) :
    denote S (HasType.appL hs hF hX) =
      S.appL hs (denote S hF) (denote S hX) :=
  S.interpret_appL hs hF hX

@[simp] theorem denote_measure {M : LNLModel.{u, v}} (S : DenotationModel M)
    {Γ Δ Δ₁ Δ₂ A Q K} (hs : OSplit Δ Δ₁ Δ₂)
    (hQ : HasType Γ Δ₁ Q .qubit)
    (hK : HasType Γ Δ₂ K
      (.arrow .unres .bit (.arrow .lin .qubit A))) :
    denote S (HasType.measure hs hQ hK) =
      S.measure hs (denote S hQ) (denote S hK) :=
  S.interpret_measure hs hQ hK

end HasType

namespace Prim

/-- Number of quantum input wires used by a primitive in its first-order CP
meaning. -/
def inputQ : Prim → ℕ
  | .new0 => 0
  | .x | .h | .t | .ry _ | .reset => 1
  | .cx => 2

/-- Number of quantum output wires produced by a primitive. -/
def outputQ : Prim → ℕ
  | .new0 => 1
  | .x | .h | .t | .ry _ | .reset => 1
  | .cx => 2

/-- The isometry `|0⟩ : ℂ → ℂ²` used by allocation. -/
def ketZero : KrausOperator (CQ.QDim 0) (CQ.QDim 1) :=
  fun i _ => if i = 0 then 1 else 0

/-- Concrete finite Kraus presentation of every physical primitive. -/
noncomputable def kraus (p : Prim) :
    KrausFamily (CQ.QDim p.inputQ) (CQ.QDim p.outputQ) :=
  match p with
  | .new0 => [ketZero]
  | .x => [Composer.xMatrix (0 : Fin 1)]
  | .h => [Composer.hMatrix (0 : Fin 1)]
  | .t => [Composer.tMatrix (0 : Fin 1)]
  | .ry θ => [Composer.ryMatrix (θ : ℝ) (0 : Fin 1)]
  | .cx => [Composer.cxMatrix (0 : Fin 2) (1 : Fin 2)]
  | .reset => (Composer.reset (0 : Fin 1)).kraus

/-- Presentation-independent completed CP meaning of a primitive. -/
noncomputable def completedCP (p : Prim) :
    CompletedCP (CQ.QDim p.inputQ) (CQ.QDim p.outputQ) :=
  CompletedCP.ofKraus p.kraus

@[simp] theorem completedCP_x :
    completedCP .x =
      CompletedCP.ofKraus [Composer.xMatrix (0 : Fin 1)] :=
  rfl

@[simp] theorem completedCP_h :
    completedCP .h =
      CompletedCP.ofKraus [Composer.hMatrix (0 : Fin 1)] :=
  rfl

@[simp] theorem completedCP_t :
    completedCP .t =
      CompletedCP.ofKraus [Composer.tMatrix (0 : Fin 1)] :=
  rfl

@[simp] theorem completedCP_ry (θ : ℚ) :
    completedCP (.ry θ) =
      CompletedCP.ofKraus [Composer.ryMatrix (θ : ℝ) (0 : Fin 1)] :=
  rfl

@[simp] theorem completedCP_cx :
    completedCP .cx =
      CompletedCP.ofKraus
        [Composer.cxMatrix (0 : Fin 2) (1 : Fin 2)] :=
  rfl

@[simp] theorem completedCP_reset :
    completedCP .reset =
      CompletedCP.reset (0 : Fin 1) :=
  rfl

end Prim

/-- Concrete computational-basis qubit measurement as a two-branch completed
CP instrument. -/
noncomputable def qubitMeasurement :
    CompletedCP.Instrument (CQ.QDim 1) (CQ.QDim 1) 2 :=
  CompletedCP.measure (0 : Fin 1)

@[simp] theorem qubitMeasurement_zero :
    qubitMeasurement.branch 0 =
      CompletedCP.ofKraus [Composer.projector (0 : Fin 1) false] := by
  rfl

@[simp] theorem qubitMeasurement_one :
    qubitMeasurement.branch 1 =
      CompletedCP.ofKraus [Composer.projector (0 : Fin 1) true] := by
  rfl

/-- Symmetric-transitive closure of the deterministic classical source step.
This is an operational quotient, not a substitute for the missing concrete
LNL model. -/
inductive OperationalEq : Term → Term → Prop where
  | refl (M) : OperationalEq M M
  | step {M N} : Step M N → OperationalEq M N
  | symm {M N} : OperationalEq M N → OperationalEq N M
  | trans {M N P} : OperationalEq M N → OperationalEq N P → OperationalEq M P

instance operationalSetoid : Setoid Term where
  r := OperationalEq
  iseqv := ⟨OperationalEq.refl, OperationalEq.symm, OperationalEq.trans⟩

/-- Exact source meaning modulo deterministic classical computation. -/
abbrev OperationalMeaning := Quotient operationalSetoid

def operationalDenote (M : Term) : OperationalMeaning :=
  Quotient.mk' M

theorem step_sound {M N : Term} (h : Step M N) :
    operationalDenote M = operationalDenote N :=
  Quotient.sound (OperationalEq.step h)

theorem betaL_exact {A M V} (hV : Term.Value V) :
    operationalDenote (.app (.lam .lin A M) V) =
      operationalDenote (Term.substLin 0 V M) :=
  step_sound (.betaL hV)

theorem betaU_exact {A M V} (hV : Term.Value V) :
    operationalDenote (.app (.lam .unres A M) V) =
      operationalDenote (Term.substUnres 0 V M) :=
  step_sound (.betaU hV)

theorem unpair_exact {M N K} (hM : Term.Value M) (hN : Term.Value N) :
    operationalDenote (.unpair (.pair M N) K) =
      operationalDenote (.app (.app K M) N) :=
  step_sound (.unpairBeta hM hN)

theorem unfold_fold_exact {A V} (hV : Term.Value V) :
    operationalDenote (.unfold (.fold A V)) = operationalDenote V :=
  step_sound (.unfoldBeta hV)

theorem fix_exact {A V} (hV : Term.Value V) :
    operationalDenote (.fix A V) =
      operationalDenote (.app V (.fix A V)) :=
  step_sound (.fixBeta hV)

theorem operational_quotient_exact {M N : Term} :
    operationalDenote M = operationalDenote N ↔ OperationalEq M N :=
  Quotient.eq_iff_equiv

end QLambda.Linear
