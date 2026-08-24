/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Effects
import QLambda.Monad
import QLambda.Operational
import QLambda.Syntax
import QLambda.QuantumDomainEquation

/-!
# Denotational interpretation of `qλ`

Paper §2 and §7. Every term denotes a computation in `Q(D_∞)`, where
`D_∞ ≅ [D_∞ → Q(D_∞)]`:

* pure values enter the computation object through monadic `unit`;
* application sequences function and argument computations with `bind`;
* abstraction and application use the proved recursive-domain maps;
* primitive and choice denotations are supplied by explicit semantic
  interfaces.
-/

namespace QLambda

open Scott1972.ContinuousLattice

universe u

/-- Environments: names to elements of `D_∞`. -/
abbrev Env (Dinf : Type u) : Type u := Name → Dinf

namespace ScottMap

variable {A B C : Type u}
variable [CompleteLattice A] [CompleteLattice B] [CompleteLattice C]

/-- First projection as a Scott map. -/
noncomputable def fstMap : ScottMap (A × B) A :=
  ⟨Prod.fst, continuous_of_preservesDirectedSup fun S _ _ =>
    Prod.fst_sSup S⟩

/-- Second projection as a Scott map. -/
noncomputable def sndMap : ScottMap (A × B) B :=
  ⟨Prod.snd, continuous_of_preservesDirectedSup fun S _ _ =>
    Prod.snd_sSup S⟩

/-- Pair two Scott maps with a common source. -/
noncomputable def pairMap (f : ScottMap A B) (g : ScottMap A C) :
    ScottMap A (B × C) :=
  ⟨fun x => (f x, g x), continuous_of_preservesDirectedSup fun S hS hdir => by
    apply Prod.ext
    · change f (sSup S) =
        (sSup ((fun x => (f x, g x)) '' S) : B × C).1
      rw [f.preservesDirectedSup_coe S hS hdir, Prod.fst_sSup,
        Set.image_image]
    · change g (sSup S) =
        (sSup ((fun x => (f x, g x)) '' S) : B × C).2
      rw [g.preservesDirectedSup_coe S hS hdir, Prod.snd_sSup,
        Set.image_image]⟩

/-- Joint evaluation of a Scott map and its argument. -/
noncomputable def evalMap : ScottMap (ScottMap A B × A) B :=
  ⟨fun p => p.1 p.2, corollary_3_4_jointly_continuous⟩

@[simp] theorem fstMap_apply (p : A × B) : fstMap p = p.1 := rfl
@[simp] theorem sndMap_apply (p : A × B) : sndMap p = p.2 := rfl
@[simp] theorem pairMap_apply (f : ScottMap A B) (g : ScottMap A C)
    (x : A) : pairMap f g x = (f x, g x) := rfl
@[simp] theorem evalMap_apply (p : ScottMap A B × A) :
    evalMap p = p.1 p.2 := rfl

end ScottMap

section Semantics

variable (Q : (D : Type u) → [CompleteLattice D] → Type u)
variable [IsQuantumMonad Q]

noncomputable abbrev QModel : QuantumPowerModel :=
  quantumMonadModel Q

variable (D₀ : QDomain.{u})
variable (j₀ : IsContinuousLatticeProjection D₀.carrier
  (QuantumFunctor (QModel Q) D₀.carrier))

/-- The solved recursive value domain for the chosen quantum monad. -/
abbrev SemanticValue : Type u :=
  QDInf (QModel Q) D₀ j₀

/-- The single public codomain of term denotations. -/
abbrev SemanticComp : Type u :=
  Q (SemanticValue Q D₀ j₀)

variable {Q D₀ j₀}

/-- Lookup is Scott-continuous in a pointwise ordered environment. -/
noncomputable def envLookup (x : Name) :
    ScottMap (Env (SemanticValue Q D₀ j₀)) (SemanticValue Q D₀ j₀) :=
  ⟨fun ρ => ρ x, continuous_of_preservesDirectedSup fun S _ _ => by
    rw [sSup_apply_eq_sSup_image]⟩

/-- Update one environment entry, jointly continuously in the old
environment and the new value. -/
noncomputable def envUpdate (x : Name) :
    ScottMap (Env (SemanticValue Q D₀ j₀) × SemanticValue Q D₀ j₀)
      (Env (SemanticValue Q D₀ j₀)) :=
  ⟨fun p y => if y = x then p.2 else p.1 y,
    continuous_of_preservesDirectedSup fun S hS hdir => by
      funext y
      change
        (if y = x then (sSup S).2 else (sSup S).1 y) =
          (sSup ((fun p :
            Env (SemanticValue Q D₀ j₀) × SemanticValue Q D₀ j₀ =>
              fun z => if z = x then p.2 else p.1 z) '' S) :
            Env (SemanticValue Q D₀ j₀)) y
      rw [sSup_apply_eq_sSup_image, Set.image_image]
      by_cases hy : y = x
      · subst y
        simp only [if_pos]
        simpa only [Function.eval_apply, if_pos] using Prod.snd_sSup S
      · simp only [if_neg hy]
        rw [Prod.fst_sSup]
        rw [sSup_apply_eq_sSup_image, Set.image_image]
        congr 1
        ext d
        simp only [Set.mem_image, Function.eval_apply,
          if_neg hy]⟩

@[simp]
theorem envLookup_apply (x : Name) (ρ : Env (SemanticValue Q D₀ j₀)) :
    envLookup (Q := Q) (D₀ := D₀) (j₀ := j₀) x ρ = ρ x :=
  rfl

@[simp]
theorem envUpdate_apply (x y : Name)
    (ρ : Env (SemanticValue Q D₀ j₀)) (d : SemanticValue Q D₀ j₀) :
    envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x (ρ, d) y =
      if y = x then d else ρ y :=
  rfl

@[simp]
theorem envUpdate_same (x : Name)
    (ρ : Env (SemanticValue Q D₀ j₀)) (d : SemanticValue Q D₀ j₀) :
    envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x (ρ, d) x = d := by
  simp [envUpdate_apply]

theorem envUpdate_other {x y : Name} (hxy : y ≠ x)
    (ρ : Env (SemanticValue Q D₀ j₀)) (d : SemanticValue Q D₀ j₀) :
    envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x (ρ, d) y = ρ y := by
  simp [envUpdate_apply, hxy]

/-- A later update at the same name shadows the earlier one. -/
theorem envUpdate_shadow (x : Name)
    (ρ : Env (SemanticValue Q D₀ j₀))
    (d e : SemanticValue Q D₀ j₀) :
    envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
        (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x (ρ, d), e) =
      envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x (ρ, e) := by
  funext y
  by_cases hy : y = x <;> simp [envUpdate_apply, hy]

/-- Updates at distinct names commute. -/
theorem envUpdate_comm {x y : Name} (hxy : x ≠ y)
    (ρ : Env (SemanticValue Q D₀ j₀))
    (d e : SemanticValue Q D₀ j₀) :
    envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) y
        (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x (ρ, d), e) =
      envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
        (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) y (ρ, e), d) := by
  funext z
  by_cases hzx : z = x
  · subst z
    simp [envUpdate_apply, hxy]
  · by_cases hzy : z = y <;>
      simp [envUpdate_apply, hzx, hzy, Ne.symm hxy]

/-- Pure return for the chosen quantum monad. -/
noncomputable abbrev semanticUnit :
    ScottMap (SemanticValue Q D₀ j₀) (SemanticComp Q D₀ j₀) :=
  IsQuantumMonad.unit (Q := Q)

/-- Scott-continuous Kleisli extension for the chosen quantum monad. -/
noncomputable abbrev semanticBind :
    ScottMap
      (ScottMap (SemanticValue Q D₀ j₀) (SemanticComp Q D₀ j₀))
      (ScottMap (SemanticComp Q D₀ j₀) (SemanticComp Q D₀ j₀)) :=
  IsQuantumMonad.bind (Q := Q)

/-- Fold a continuous function value into the recursive domain. -/
noncomputable abbrev semanticFold :
    ScottMap
      (ScottMap (SemanticValue Q D₀ j₀) (SemanticComp Q D₀ j₀))
      (SemanticValue Q D₀ j₀) :=
  qProjInfInf (QModel Q) D₀ j₀

/-- Unfold a recursive-domain value into a quantum function. -/
noncomputable abbrev semanticUnfold :
    ScottMap (SemanticValue Q D₀ j₀)
      (ScottMap (SemanticValue Q D₀ j₀) (SemanticComp Q D₀ j₀)) :=
  qEmbInfInf (QModel Q) D₀ j₀

/-- The pure value denoted by a non-recursive abstraction. -/
noncomputable def lambdaValue (x : Name)
    (body : ScottMap (Env (SemanticValue Q D₀ j₀))
      (SemanticComp Q D₀ j₀)) :
    ScottMap (Env (SemanticValue Q D₀ j₀))
      (SemanticValue Q D₀ j₀) :=
  semanticFold (Q := Q) (D₀ := D₀) (j₀ := j₀) |>.comp <|
    scottLambda <|
      body.comp (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x)

/-- The environment-indexed continuation used after evaluating a function:
evaluate the argument, unfold the function value, and bind the two. -/
noncomputable def applyContinuation
    (ma : ScottMap (Env (SemanticValue Q D₀ j₀))
      (SemanticComp Q D₀ j₀)) :
    ScottMap (Env (SemanticValue Q D₀ j₀))
      (ScottMap (SemanticValue Q D₀ j₀) (SemanticComp Q D₀ j₀)) :=
  let innerPair :
      ScottMap
        (Env (SemanticValue Q D₀ j₀) × SemanticValue Q D₀ j₀)
        (ScottMap (SemanticComp Q D₀ j₀) (SemanticComp Q D₀ j₀) ×
          SemanticComp Q D₀ j₀) :=
    ScottMap.pairMap
      ((semanticBind (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp
        ((semanticUnfold (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp
          ScottMap.sndMap))
      (ma.comp ScottMap.fstMap)
  let inner :
      ScottMap
        (Env (SemanticValue Q D₀ j₀) × SemanticValue Q D₀ j₀)
        (SemanticComp Q D₀ j₀) :=
    ScottMap.evalMap.comp innerPair
  scottLambda inner

/-- Call-by-value application, remaining entirely in `Q(D∞)`. -/
noncomputable def applyComp
    (mf ma : ScottMap (Env (SemanticValue Q D₀ j₀))
      (SemanticComp Q D₀ j₀)) :
    ScottMap (Env (SemanticValue Q D₀ j₀))
      (SemanticComp Q D₀ j₀) :=
  ScottMap.evalMap.comp <|
    ScottMap.pairMap
      ((semanticBind (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp
        (applyContinuation (Q := Q) (D₀ := D₀) (j₀ := j₀) ma))
      mf

@[simp]
theorem applyContinuation_apply
    (ma : ScottMap (Env (SemanticValue Q D₀ j₀))
      (SemanticComp Q D₀ j₀))
    (ρ : Env (SemanticValue Q D₀ j₀)) (f : SemanticValue Q D₀ j₀) :
    applyContinuation (Q := Q) (D₀ := D₀) (j₀ := j₀) ma ρ f =
      semanticBind (Q := Q) (D₀ := D₀) (j₀ := j₀)
        (semanticUnfold (Q := Q) (D₀ := D₀) (j₀ := j₀) f) (ma ρ) :=
  rfl

@[simp]
theorem applyComp_apply
    (mf ma : ScottMap (Env (SemanticValue Q D₀ j₀))
      (SemanticComp Q D₀ j₀))
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    applyComp (Q := Q) (D₀ := D₀) (j₀ := j₀) mf ma ρ =
      semanticBind (Q := Q) (D₀ := D₀) (j₀ := j₀)
        (applyContinuation (Q := Q) (D₀ := D₀) (j₀ := j₀) ma ρ)
        (mf ρ) :=
  rfl

/-- Applying a pure abstraction to a pure argument evaluates its body in
the updated environment. This is the semantic β-equation before relating
environment update to syntactic substitution. -/
theorem applyComp_pure_lambda
    (x : Name)
    (body : ScottMap (Env (SemanticValue Q D₀ j₀))
      (SemanticComp Q D₀ j₀))
    (arg : ScottMap (Env (SemanticValue Q D₀ j₀))
      (SemanticValue Q D₀ j₀))
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    applyComp (Q := Q) (D₀ := D₀) (j₀ := j₀)
        ((semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp
          (lambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀) x body))
        ((semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp arg) ρ =
      body (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀)
        x (ρ, arg ρ)) := by
  rw [applyComp_apply]
  change
    semanticBind (Q := Q) (D₀ := D₀) (j₀ := j₀)
        (applyContinuation (Q := Q) (D₀ := D₀) (j₀ := j₀)
          ((semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp arg) ρ)
        (semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)
          (lambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀) x body ρ)) =
      body (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀)
        x (ρ, arg ρ))
  have hOuter := congrArg
    (fun f : ScottMap (SemanticValue Q D₀ j₀) (SemanticComp Q D₀ j₀) =>
      f (lambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀) x body ρ))
    (IsQuantumMonad.unit_bind (Q := Q)
      (applyContinuation (Q := Q) (D₀ := D₀) (j₀ := j₀)
        ((semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp arg) ρ))
  rw [ScottMap.comp_apply] at hOuter
  rw [hOuter, applyContinuation_apply]
  change
    semanticBind (Q := Q) (D₀ := D₀) (j₀ := j₀)
        (semanticUnfold (Q := Q) (D₀ := D₀) (j₀ := j₀)
          (lambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀) x body ρ))
        (semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀) (arg ρ)) =
      body (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀)
        x (ρ, arg ρ))
  have hInner := congrArg
    (fun f : ScottMap (SemanticValue Q D₀ j₀) (SemanticComp Q D₀ j₀) =>
      f (arg ρ))
    (IsQuantumMonad.unit_bind (Q := Q)
      (semanticUnfold (Q := Q) (D₀ := D₀) (j₀ := j₀)
        (lambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀) x body ρ)))
  rw [ScottMap.comp_apply] at hInner
  rw [hInner]
  change
    qEmbInfInf (QModel Q) D₀ j₀
        (qProjInfInf (QModel Q) D₀ j₀
          (scottLambda
            (body.comp
              (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x)) ρ))
        (arg ρ) =
      body (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x (ρ, arg ρ))
  let f :
      ScottMap (SemanticValue Q D₀ j₀) (SemanticComp Q D₀ j₀) :=
    scottLambda
      (body.comp (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x)) ρ
  have hf := congrArg (fun g :
      ScottMap (SemanticValue Q D₀ j₀) (SemanticComp Q D₀ j₀) =>
        g (arg ρ))
    (qEmbInfInf_qProjInfInf (QModel Q) D₀ j₀ f)
  simpa only [f, scottLambda_apply, ScottMap.comp_apply] using hf

/-- The environment-indexed continuous functional whose least fixed point
interprets a recursive abstraction. -/
noncomputable def recFunctional (self arg : Name)
    (body : ScottMap (Env (SemanticValue Q D₀ j₀))
      (SemanticComp Q D₀ j₀)) :
    ScottMap (Env (SemanticValue Q D₀ j₀))
      (ScottMap (SemanticValue Q D₀ j₀) (SemanticValue Q D₀ j₀)) :=
  let firstUpdate :
      ScottMap
        ((Env (SemanticValue Q D₀ j₀) × SemanticValue Q D₀ j₀) ×
          SemanticValue Q D₀ j₀)
        (Env (SemanticValue Q D₀ j₀)) :=
    (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) self).comp
      ScottMap.fstMap
  let bothUpdates :
      ScottMap
        ((Env (SemanticValue Q D₀ j₀) × SemanticValue Q D₀ j₀) ×
          SemanticValue Q D₀ j₀)
        (Env (SemanticValue Q D₀ j₀)) :=
    (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) arg).comp <|
      ScottMap.pairMap firstUpdate ScottMap.sndMap
  let bodyBySelf :
      ScottMap
        (Env (SemanticValue Q D₀ j₀) × SemanticValue Q D₀ j₀)
        (ScottMap (SemanticValue Q D₀ j₀) (SemanticComp Q D₀ j₀)) :=
    scottLambda (body.comp bothUpdates)
  let selfFunctional :
      ScottMap
        (Env (SemanticValue Q D₀ j₀) × SemanticValue Q D₀ j₀)
        (SemanticValue Q D₀ j₀) :=
    (semanticFold (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp bodyBySelf
  scottLambda selfFunctional

/-- The pure value denoted by a recursive abstraction. -/
noncomputable def recLambdaValue (self arg : Name)
    (body : ScottMap (Env (SemanticValue Q D₀ j₀))
      (SemanticComp Q D₀ j₀)) :
    ScottMap (Env (SemanticValue Q D₀ j₀))
      (SemanticValue Q D₀ j₀) :=
  Proposition314.fixMap.comp <|
    recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀) self arg body

/-- Recursive abstractions satisfy their semantic unfolding equation. -/
theorem recLambdaValue_unfold (self arg : Name)
    (body : ScottMap (Env (SemanticValue Q D₀ j₀))
      (SemanticComp Q D₀ j₀))
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀) self arg body ρ =
      recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀) self arg body ρ
        (recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀)
          self arg body ρ) := by
  exact (Proposition314.fix_eq
    (recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀)
      self arg body ρ)).symm

variable [HasComputationChoice (SemanticComp Q D₀ j₀)]

/-- Compositional computation-valued interpretation. Every constructor,
including pure values, denotes an element of `Q(D∞)`. -/
noncomputable def interp {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀) :
    Term Prim →
      ScottMap (Env (SemanticValue Q D₀ j₀)) (SemanticComp Q D₀ j₀)
  | .var x =>
      (semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp
        (envLookup (Q := Q) (D₀ := D₀) (j₀ := j₀) x)
  | .lam x M =>
      (semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp
        (lambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀) x
          (interp primitive M))
  | .app M N =>
      applyComp (Q := Q) (D₀ := D₀) (j₀ := j₀)
        (interp primitive M) (interp primitive N)
  | .prim p => ScottMap.const (primitive p)
  | .recLam self arg M =>
      (semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp
        (recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀) self arg
          (interp primitive M))
  | .prob p M N =>
      (HasComputationChoice.prob p).comp <|
        ScottMap.pairMap (interp primitive M) (interp primitive N)
  | .intern M N =>
      HasComputationChoice.intern.comp <|
        ScottMap.pairMap (interp primitive M) (interp primitive N)
  | .extern M N =>
      HasComputationChoice.extern.comp <|
        ScottMap.pairMap (interp primitive M) (interp primitive N)

/-- A value denotes the pure recursive-domain element before `unit`
lifts it into `Q(D∞)`. -/
noncomputable def valueInterp {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (M : Term Prim) :
    ScottMap (Env (SemanticValue Q D₀ j₀)) (SemanticValue Q D₀ j₀) :=
  match M with
  | .lam x body =>
      lambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀) x
        (interp primitive body)
  | .recLam self arg body =>
      recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀) self arg
        (interp primitive body)
  | _ => ⊥

/-- Value terms are exactly the pure cases of the computation
interpretation. -/
theorem interp_value {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    {M : Term Prim} (hM : Value M) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M =
      (semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp
        (valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M) := by
  rcases hM with (_ | _)
  · rfl
  · rfl

/-- Compositional Scott continuity in the environment is carried by the
type of the interpretation itself. -/
theorem interp_continuous {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀) (M : Term Prim) :
    @Continuous
      (Env (SemanticValue Q D₀ j₀)) (SemanticComp Q D₀ j₀)
      scottTopologicalSpace scottTopologicalSpace
      (interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M) :=
  (interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M).continuous

@[simp]
theorem interp_var_apply {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀) (x : Name)
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive (.var x) ρ =
      semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀) (ρ x) :=
  rfl

@[simp]
theorem interp_prim_apply {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀) (p : Prim)
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive (.prim p) ρ =
      primitive p :=
  rfl

@[simp]
theorem interp_lam_apply {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀) (x : Name) (M : Term Prim)
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive (.lam x M) ρ =
      semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)
        (lambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀) x
          (interp primitive M) ρ) :=
  rfl

@[simp]
theorem interp_app_apply {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀) (M N : Term Prim)
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive (.app M N) ρ =
      applyComp (Q := Q) (D₀ := D₀) (j₀ := j₀)
        (interp primitive M) (interp primitive N) ρ :=
  rfl

@[simp]
theorem interp_recLam_apply {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (self arg : Name) (M : Term Prim)
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀)
        primitive (.recLam self arg M) ρ =
      semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)
        (recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀) self arg
          (interp primitive M) ρ) :=
  rfl

@[simp]
theorem interp_prob_apply {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (p : Prob) (M N : Term Prim)
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀)
        primitive (.prob p M N) ρ =
      HasComputationChoice.prob p
        (interp primitive M ρ, interp primitive N ρ) :=
  rfl

@[simp]
theorem interp_intern_apply {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (M N : Term Prim) (ρ : Env (SemanticValue Q D₀ j₀)) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀)
        primitive (.intern M N) ρ =
      HasComputationChoice.intern
        (interp primitive M ρ, interp primitive N ρ) :=
  rfl

/-- Either internal-choice branch refines the combined computation, matching
the direction used by internal-step soundness. -/
theorem interp_le_intern_left {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (M N : Term Prim) (ρ : Env (SemanticValue Q D₀ j₀)) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M ρ ≤
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀)
        primitive (.intern M N) ρ := by
  rw [interp_intern_apply]
  exact HasComputationChoice.left_le_intern _ _

theorem interp_le_intern_right {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (M N : Term Prim) (ρ : Env (SemanticValue Q D₀ j₀)) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive N ρ ≤
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀)
        primitive (.intern M N) ρ := by
  rw [interp_intern_apply]
  exact HasComputationChoice.right_le_intern _ _

@[simp]
theorem interp_extern_apply {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (M N : Term Prim) (ρ : Env (SemanticValue Q D₀ j₀)) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀)
        primitive (.extern M N) ρ =
      HasComputationChoice.extern
        (interp primitive M ρ, interp primitive N ρ) :=
  rfl

end Semantics

end QLambda
