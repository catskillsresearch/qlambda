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

/-- Application is monotone in the function computation. -/
theorem applyComp_mono_left
    {mf mf' ma : ScottMap (Env (SemanticValue Q D₀ j₀))
      (SemanticComp Q D₀ j₀)}
    (h : mf ≤ mf') :
    applyComp (Q := Q) (D₀ := D₀) (j₀ := j₀) mf ma ≤
      applyComp (Q := Q) (D₀ := D₀) (j₀ := j₀) mf' ma := by
  rw [ScottMap.le_def]
  intro ρ
  rw [applyComp_apply, applyComp_apply]
  exact
    (semanticBind (Q := Q) (D₀ := D₀) (j₀ := j₀)
      (applyContinuation (Q := Q) (D₀ := D₀) (j₀ := j₀) ma ρ)).monotone
      (ScottMap.le_def.mp h ρ)

/-- Application is monotone in the argument computation. -/
theorem applyComp_mono_right
    {mf ma ma' : ScottMap (Env (SemanticValue Q D₀ j₀))
      (SemanticComp Q D₀ j₀)}
    (h : ma ≤ ma') :
    applyComp (Q := Q) (D₀ := D₀) (j₀ := j₀) mf ma ≤
      applyComp (Q := Q) (D₀ := D₀) (j₀ := j₀) mf ma' := by
  rw [ScottMap.le_def]
  intro ρ
  rw [applyComp_apply, applyComp_apply]
  apply ScottMap.le_def.mp
    ((semanticBind (Q := Q) (D₀ := D₀) (j₀ := j₀)).monotone ?_)
  rw [ScottMap.le_def]
  intro f
  rw [applyContinuation_apply, applyContinuation_apply]
  exact
    (semanticBind (Q := Q) (D₀ := D₀) (j₀ := j₀)
      (semanticUnfold (Q := Q) (D₀ := D₀) (j₀ := j₀) f)).monotone
      (ScottMap.le_def.mp h ρ)

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

/-- Applying a pure recursive abstraction to a pure argument unfolds one
recursive call and evaluates the body with both binders installed. -/
theorem applyComp_pure_recLambda
    (self arg : Name)
    (body : ScottMap (Env (SemanticValue Q D₀ j₀))
      (SemanticComp Q D₀ j₀))
    (value : ScottMap (Env (SemanticValue Q D₀ j₀))
      (SemanticValue Q D₀ j₀))
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    applyComp (Q := Q) (D₀ := D₀) (j₀ := j₀)
        ((semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp
          (recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀)
            self arg body))
        ((semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp value) ρ =
      body
        (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) arg
          (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) self
            (ρ, recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀)
              self arg body ρ),
            value ρ)) := by
  rw [applyComp_apply]
  change
    semanticBind (Q := Q) (D₀ := D₀) (j₀ := j₀)
        (applyContinuation (Q := Q) (D₀ := D₀) (j₀ := j₀)
          ((semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp value) ρ)
        (semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)
          (recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀)
            self arg body ρ)) =
      body
        (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) arg
          (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) self
            (ρ, recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀)
              self arg body ρ),
            value ρ))
  have hOuter := congrArg
    (fun f : ScottMap (SemanticValue Q D₀ j₀) (SemanticComp Q D₀ j₀) =>
      f (recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀)
        self arg body ρ))
    (IsQuantumMonad.unit_bind (Q := Q)
      (applyContinuation (Q := Q) (D₀ := D₀) (j₀ := j₀)
        ((semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp value) ρ))
  rw [ScottMap.comp_apply] at hOuter
  rw [hOuter, applyContinuation_apply]
  have hInner := congrArg
    (fun f : ScottMap (SemanticValue Q D₀ j₀) (SemanticComp Q D₀ j₀) =>
      f (value ρ))
    (IsQuantumMonad.unit_bind (Q := Q)
      (semanticUnfold (Q := Q) (D₀ := D₀) (j₀ := j₀)
        (recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀)
          self arg body ρ)))
  rw [ScottMap.comp_apply] at hInner
  change
    semanticBind (Q := Q) (D₀ := D₀) (j₀ := j₀)
        (semanticUnfold (Q := Q) (D₀ := D₀) (j₀ := j₀)
          (recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀)
            self arg body ρ))
        (semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀) (value ρ)) =
      body
        (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) arg
          (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) self
            (ρ, recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀)
              self arg body ρ),
            value ρ))
  rw [hInner]
  conv_lhs =>
    rw [recLambdaValue_unfold]
  change
    qEmbInfInf (QModel Q) D₀ j₀
        (qProjInfInf (QModel Q) D₀ j₀
          (scottLambda
            (body.comp
              ((envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) arg).comp
                (ScottMap.pairMap
                  ((envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) self).comp
                    ScottMap.fstMap)
                  ScottMap.sndMap)))
            (ρ, recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀)
              self arg body ρ)))
        (value ρ) =
      body
        (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) arg
          (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) self
            (ρ, recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀)
              self arg body ρ),
            value ρ))
  let f : ScottMap (SemanticValue Q D₀ j₀) (SemanticComp Q D₀ j₀) :=
    scottLambda
      (body.comp
        ((envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) arg).comp
          (ScottMap.pairMap
            ((envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) self).comp
              ScottMap.fstMap)
            ScottMap.sndMap)))
      (ρ, recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀)
        self arg body ρ)
  have hf := congrArg
    (fun g : ScottMap (SemanticValue Q D₀ j₀) (SemanticComp Q D₀ j₀) =>
      g (value ρ))
    (qEmbInfInf_qProjInfInf (QModel Q) D₀ j₀ f)
  simpa only [f, scottLambda_apply, ScottMap.comp_apply,
    ScottMap.pairMap_apply, ScottMap.fstMap_apply,
    ScottMap.sndMap_apply] using hf

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

/-- A term depends only on the values assigned to its free variables. -/
theorem interp_congr_free {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀) :
    ∀ (M : Term Prim) (ρ σ : Env (SemanticValue Q D₀ j₀)),
      (∀ x, x ∈ free M → ρ x = σ x) →
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M ρ =
        interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M σ
  | .var x, ρ, σ, h => by
      rw [interp_var_apply, interp_var_apply, h x]
      simp [free]
  | .lam x M, ρ, σ, h => by
      rw [interp_lam_apply, interp_lam_apply]
      unfold lambdaValue
      simp only [ScottMap.comp_apply]
      have hf :
          scottLambda
              ((interp primitive M).comp
                (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x)) ρ =
            scottLambda
              ((interp primitive M).comp
                (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x)) σ := by
        apply ScottMap.ext
        intro d
        simp only [scottLambda_apply, ScottMap.comp_apply]
        apply interp_congr_free primitive M
        intro y hy
        by_cases hyx : y = x
        · subst y
          simp
        · rw [envUpdate_other hyx, envUpdate_other hyx]
          apply h y
          simp [free, hy, hyx]
      rw [hf]
  | .app M N, ρ, σ, h => by
      rw [interp_app_apply, interp_app_apply, applyComp_apply, applyComp_apply]
      have hM := interp_congr_free primitive M ρ σ
        (fun x hx => h x (by simp [free, hx]))
      have hN := interp_congr_free primitive N ρ σ
        (fun x hx => h x (by simp [free, hx]))
      have hCont :
          applyContinuation (Q := Q) (D₀ := D₀) (j₀ := j₀)
              (interp primitive N) ρ =
            applyContinuation (Q := Q) (D₀ := D₀) (j₀ := j₀)
              (interp primitive N) σ := by
        apply ScottMap.ext
        intro f
        rw [applyContinuation_apply, applyContinuation_apply, hN]
      rw [hM, hCont]
  | .prim p, ρ, σ, h => by
      rw [interp_prim_apply, interp_prim_apply]
  | .recLam self arg M, ρ, σ, h => by
      rw [interp_recLam_apply, interp_recLam_apply]
      unfold recLambdaValue
      simp only [ScottMap.comp_apply, Proposition314.fixMap_apply]
      have hf :
          recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀)
              self arg (interp primitive M) ρ =
            recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀)
              self arg (interp primitive M) σ := by
        unfold recFunctional
        apply ScottMap.ext
        intro dself
        simp only [scottLambda_apply, ScottMap.comp_apply]
        apply congrArg
        apply ScottMap.ext
        intro darg
        simp only [scottLambda_apply, ScottMap.comp_apply,
          ScottMap.pairMap_apply, ScottMap.fstMap_apply,
          ScottMap.sndMap_apply]
        apply interp_congr_free primitive M
        intro y hy
        by_cases hys : y = self
        · subst y
          by_cases hsa : self = arg
          · subst arg
            simp
          · simp [envUpdate_apply, hsa]
        · by_cases hya : y = arg
          · subst y
            simp
          · rw [envUpdate_other hya, envUpdate_other hya,
              envUpdate_other hys, envUpdate_other hys]
            apply h y
            simp [free, hy, hys, hya]
      rw [hf]
  | .prob p M N, ρ, σ, h => by
      rw [interp_prob_apply, interp_prob_apply]
      rw [interp_congr_free primitive M ρ σ (fun x hx => h x (by
        simp [free, hx])),
        interp_congr_free primitive N ρ σ (fun x hx => h x (by
          simp [free, hx]))]
  | .intern M N, ρ, σ, h => by
      rw [interp_intern_apply, interp_intern_apply]
      rw [interp_congr_free primitive M ρ σ (fun x hx => h x (by
        simp [free, hx])),
        interp_congr_free primitive N ρ σ (fun x hx => h x (by
          simp [free, hx]))]
  | .extern M N, ρ, σ, h => by
      rw [interp_extern_apply, interp_extern_apply]
      rw [interp_congr_free primitive M ρ σ (fun x hx => h x (by
        simp [free, hx])),
        interp_congr_free primitive N ρ σ (fun x hx => h x (by
          simp [free, hx]))]

/-- The pure value extracted from a value term also depends only on its free
variables. -/
theorem valueInterp_congr_free {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    {V : Term Prim} (hV : Value V)
    (ρ σ : Env (SemanticValue Q D₀ j₀))
    (h : ∀ x, x ∈ free V → ρ x = σ x) :
    valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive V ρ =
      valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive V σ := by
  cases hV with
  | lam x M =>
    unfold valueInterp lambdaValue
    simp only [ScottMap.comp_apply]
    apply congrArg
    apply ScottMap.ext
    intro d
    simp only [scottLambda_apply, ScottMap.comp_apply]
    apply interp_congr_free primitive _
    intro y hy
    by_cases hyx : y = x
    · subst y
      simp
    · rw [envUpdate_other hyx, envUpdate_other hyx]
      apply h y
      simp [free, hy, hyx]
  | recLam self arg M =>
    unfold valueInterp recLambdaValue
    simp only [ScottMap.comp_apply, Proposition314.fixMap_apply]
    congr 1
    unfold recFunctional
    apply ScottMap.ext
    intro dself
    simp only [scottLambda_apply, ScottMap.comp_apply]
    apply congrArg
    apply ScottMap.ext
    intro darg
    simp only [scottLambda_apply, ScottMap.comp_apply,
      ScottMap.pairMap_apply, ScottMap.fstMap_apply,
      ScottMap.sndMap_apply]
    apply interp_congr_free primitive _
    intro y hy
    by_cases hys : y = self
    · subst y
      by_cases hsa : self = arg
      · subst arg
        simp
      · simp [envUpdate_apply, hsa]
    · by_cases hya : y = arg
      · subst y
        simp
      · rw [envUpdate_other hya, envUpdate_other hya,
          envUpdate_other hys, envUpdate_other hys]
        apply h y
        simp [free, hy, hys, hya]

/-- Updating a variable absent from a term's free variables does not change
its denotation. -/
theorem interp_weakening {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (M : Term Prim) (ρ : Env (SemanticValue Q D₀ j₀))
    (x : Name) (d : SemanticValue Q D₀ j₀) (hx : x ∉ free M) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M
        (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x (ρ, d)) =
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M ρ := by
  apply interp_congr_free primitive M
  intro y hy
  apply envUpdate_other
  intro hyx
  subst y
  exact hx hy

/-- Renaming a free variable to a name fresh for the term is interpreted by
redirecting that variable's environment entry. -/
theorem interp_rename {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀) :
    ∀ (M : Term Prim) (x y : Name)
      (ρ : Env (SemanticValue Q D₀ j₀)), y ∉ names M →
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
          (rename x y M) ρ =
        interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M
          (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀)
            x (ρ, ρ y))
  | .var z, x, y, ρ, hy => by
      simp only [rename]
      by_cases hzx : z = x
      · subst z
        simp
      · simp [interp_var_apply, envUpdate_apply, hzx]
  | .lam z M, x, y, ρ, hy => by
      have hy' : y ≠ z ∧ y ∉ names M := by
        simpa [names] using hy
      rcases hy' with ⟨hyz, hyM⟩
      simp only [rename]
      by_cases hzx : z = x
      · subst z
        simp only [if_pos]
        apply interp_congr_free primitive (.lam x M)
        intro w hw
        have hw' : w ∈ free M ∧ w ≠ x := by
          simpa [free] using hw
        rw [envUpdate_other hw'.2]
      · simp only [if_neg hzx, interp_lam_apply]
        unfold lambdaValue
        simp only [ScottMap.comp_apply]
        have hf :
            scottLambda
                ((interp primitive (rename x y M)).comp
                  (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) z)) ρ =
              scottLambda
                ((interp primitive M).comp
                  (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) z))
                (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀)
                  x (ρ, ρ y)) := by
          apply ScottMap.ext
          intro d
          simp only [scottLambda_apply, ScottMap.comp_apply]
          rw [interp_rename primitive M x y
            (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) z (ρ, d)) hyM]
          apply interp_congr_free primitive M
          intro w hw
          by_cases hwx : w = x
          · subst w
            simp [envUpdate_apply, Ne.symm hzx, hyz]
          · by_cases hwz : w = z
            · subst w
              simp [envUpdate_apply, hzx]
            · simp [envUpdate_apply, hwx, hwz, hyz]
        rw [hf]
  | .app M N, x, y, ρ, hy => by
      have hy' : y ∉ names M ∧ y ∉ names N := by
        simpa [names] using hy
      rcases hy' with ⟨hyM, hyN⟩
      rw [show rename x y (.app M N) =
        .app (rename x y M) (rename x y N) from rfl,
        interp_app_apply, interp_app_apply, applyComp_apply, applyComp_apply]
      have hM := interp_rename primitive M x y ρ hyM
      have hN := interp_rename primitive N x y ρ hyN
      have hCont :
          applyContinuation (Q := Q) (D₀ := D₀) (j₀ := j₀)
              (interp primitive (rename x y N)) ρ =
            applyContinuation (Q := Q) (D₀ := D₀) (j₀ := j₀)
              (interp primitive N)
              (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀)
                x (ρ, ρ y)) := by
        apply ScottMap.ext
        intro f
        rw [applyContinuation_apply, applyContinuation_apply, hN]
      rw [hM, hCont]
  | .prim p, x, y, ρ, hy => by
      rw [show rename x y (.prim p) = .prim p from rfl,
        interp_prim_apply, interp_prim_apply]
  | .recLam self arg M, x, y, ρ, hy => by
      have hy' : y ≠ self ∧ y ≠ arg ∧ y ∉ names M := by
        simpa [names] using hy
      rcases hy' with ⟨hys, hya, hyM⟩
      simp only [rename]
      by_cases hbound : self = x ∨ arg = x
      · simp only [if_pos hbound]
        apply interp_congr_free primitive (.recLam self arg M)
        intro w hw
        have hw' : w ∈ free M ∧ w ≠ arg ∧ w ≠ self := by
          simpa [free] using hw
        rcases hbound with hsx | hax
        · subst x
          rw [envUpdate_other hw'.2.2]
        · subst x
          rw [envUpdate_other hw'.2.1]
      · simp only [if_neg hbound, interp_recLam_apply]
        unfold recLambdaValue
        simp only [ScottMap.comp_apply, Proposition314.fixMap_apply]
        have hf :
            recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀)
                self arg (interp primitive (rename x y M)) ρ =
              recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀)
                self arg (interp primitive M)
                (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀)
                  x (ρ, ρ y)) := by
          unfold recFunctional
          apply ScottMap.ext
          intro dself
          simp only [scottLambda_apply, ScottMap.comp_apply]
          apply congrArg
          apply ScottMap.ext
          intro darg
          simp only [scottLambda_apply, ScottMap.comp_apply,
            ScottMap.pairMap_apply, ScottMap.fstMap_apply,
            ScottMap.sndMap_apply]
          rw [interp_rename primitive M x y
            (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) arg
              (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) self
                (ρ, dself), darg)) hyM]
          apply interp_congr_free primitive M
          intro w hw
          rcases not_or.mp hbound with ⟨hsx, hax⟩
          by_cases hwx : w = x
          · subst w
            simp [envUpdate_apply, Ne.symm hsx, Ne.symm hax, hys, hya]
          · by_cases hws : w = self
            · subst w
              simp [envUpdate_apply, hsx]
            · by_cases hwa : w = arg
              · subst w
                simp [envUpdate_apply, hax]
              · simp [envUpdate_apply, hwx, hws, hwa, hys, hya]
        rw [hf]
  | .prob p M N, x, y, ρ, hy => by
      have hy' : y ∉ names M ∧ y ∉ names N := by simpa [names] using hy
      rcases hy' with ⟨hyM, hyN⟩
      rw [show rename x y (.prob p M N) =
        .prob p (rename x y M) (rename x y N) from rfl,
        interp_prob_apply, interp_prob_apply,
        interp_rename primitive M x y ρ hyM,
        interp_rename primitive N x y ρ hyN]
  | .intern M N, x, y, ρ, hy => by
      have hy' : y ∉ names M ∧ y ∉ names N := by simpa [names] using hy
      rcases hy' with ⟨hyM, hyN⟩
      rw [show rename x y (.intern M N) =
        .intern (rename x y M) (rename x y N) from rfl,
        interp_intern_apply, interp_intern_apply,
        interp_rename primitive M x y ρ hyM,
        interp_rename primitive N x y ρ hyN]
  | .extern M N, x, y, ρ, hy => by
      have hy' : y ∉ names M ∧ y ∉ names N := by simpa [names] using hy
      rcases hy' with ⟨hyM, hyN⟩
      rw [show rename x y (.extern M N) =
        .extern (rename x y M) (rename x y N) from rfl,
        interp_extern_apply, interp_extern_apply,
        interp_rename primitive M x y ρ hyM,
        interp_rename primitive N x y ρ hyN]

/-- Renaming a λ-binder and its formerly free body occurrences to a fresh
name is semantically α-invariant. -/
theorem interp_lam_alpha {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (M : Term Prim) (x y : Name)
    (ρ : Env (SemanticValue Q D₀ j₀)) (hy : y ∉ names M) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
        (.lam y (rename x y M)) ρ =
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive (.lam x M) ρ := by
  rw [interp_lam_apply, interp_lam_apply]
  unfold lambdaValue
  simp only [ScottMap.comp_apply]
  have hf :
      scottLambda
          ((interp primitive (rename x y M)).comp
            (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) y)) ρ =
        scottLambda
          ((interp primitive M).comp
            (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x)) ρ := by
    apply ScottMap.ext
    intro d
    simp only [scottLambda_apply, ScottMap.comp_apply]
    rw [interp_rename primitive M x y
      (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) y (ρ, d)) hy]
    apply interp_congr_free primitive M
    intro w hw
    have hwy : w ≠ y := by
      intro hwy
      subst w
      exact hy (mem_names_of_mem_free hw)
    by_cases hwx : w = x
    · subst w
      simp [envUpdate_apply]
    · simp [envUpdate_apply, hwx, hwy]
  rw [hf]

/-- Simultaneously renaming the coincident binders of a recursive
abstraction is semantically α-invariant. -/
theorem interp_recLam_alpha_same {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (M : Term Prim) (x y : Name)
    (ρ : Env (SemanticValue Q D₀ j₀)) (hy : y ∉ names M) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
        (.recLam y y (rename x y M)) ρ =
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
        (.recLam x x M) ρ := by
  rw [interp_recLam_apply, interp_recLam_apply]
  unfold recLambdaValue
  simp only [ScottMap.comp_apply, Proposition314.fixMap_apply]
  have hf :
      recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀) y y
          (interp primitive (rename x y M)) ρ =
        recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀) x x
          (interp primitive M) ρ := by
    unfold recFunctional
    apply ScottMap.ext
    intro dself
    simp only [scottLambda_apply, ScottMap.comp_apply]
    apply congrArg
    apply ScottMap.ext
    intro darg
    simp only [scottLambda_apply, ScottMap.comp_apply,
      ScottMap.pairMap_apply, ScottMap.fstMap_apply, ScottMap.sndMap_apply]
    rw [interp_rename primitive M x y
      (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) y
        (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) y
          (ρ, dself), darg)) hy]
    apply interp_congr_free primitive M
    intro z hz
    have hzy : z ≠ y := by
      intro h
      subst z
      exact hy (mem_names_of_mem_free hz)
    by_cases hzx : z = x
    · subst z
      simp [envUpdate_apply, hzy]
    · simp [envUpdate_apply, hzx, hzy]
  rw [hf]

/-- Renaming the self binder of a recursive abstraction to a fresh name is
semantically α-invariant when the two recursive binders are distinct. -/
theorem interp_recLam_alpha_self {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (M : Term Prim) (self arg self' : Name)
    (ρ : Env (SemanticValue Q D₀ j₀))
    (hsa : self ≠ arg) (hfresh : self' ∉ names M)
    (hne : self' ≠ arg) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
        (.recLam self' arg (rename self self' M)) ρ =
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
        (.recLam self arg M) ρ := by
  rw [interp_recLam_apply, interp_recLam_apply]
  unfold recLambdaValue
  simp only [ScottMap.comp_apply, Proposition314.fixMap_apply]
  have hf :
      recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀) self' arg
          (interp primitive (rename self self' M)) ρ =
        recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀) self arg
          (interp primitive M) ρ := by
    unfold recFunctional
    apply ScottMap.ext
    intro dself
    simp only [scottLambda_apply, ScottMap.comp_apply]
    apply congrArg
    apply ScottMap.ext
    intro darg
    simp only [scottLambda_apply, ScottMap.comp_apply,
      ScottMap.pairMap_apply, ScottMap.fstMap_apply, ScottMap.sndMap_apply]
    rw [interp_rename primitive M self self'
      (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) arg
        (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) self'
          (ρ, dself), darg)) hfresh]
    apply interp_congr_free primitive M
    intro z hz
    have hzf : z ≠ self' := by
      intro h
      subst z
      exact hfresh (mem_names_of_mem_free hz)
    by_cases hzs : z = self
    · subst z
      simp [envUpdate_apply, hsa, hne]
    · by_cases hza : z = arg
      · subst z
        simp [envUpdate_apply, hsa, Ne.symm hsa, hne]
      · simp [envUpdate_apply, hzs, hza, hzf, hne]
  rw [hf]

/-- Renaming the argument binder of a recursive abstraction to a fresh name
is semantically α-invariant when the two recursive binders are distinct. -/
theorem interp_recLam_alpha_arg {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (M : Term Prim) (self arg arg' : Name)
    (ρ : Env (SemanticValue Q D₀ j₀))
    (hsa : self ≠ arg) (hfresh : arg' ∉ names M)
    (hne : arg' ≠ self) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
        (.recLam self arg' (rename arg arg' M)) ρ =
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
        (.recLam self arg M) ρ := by
  rw [interp_recLam_apply, interp_recLam_apply]
  unfold recLambdaValue
  simp only [ScottMap.comp_apply, Proposition314.fixMap_apply]
  have hf :
      recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀) self arg'
          (interp primitive (rename arg arg' M)) ρ =
        recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀) self arg
          (interp primitive M) ρ := by
    unfold recFunctional
    apply ScottMap.ext
    intro dself
    simp only [scottLambda_apply, ScottMap.comp_apply]
    apply congrArg
    apply ScottMap.ext
    intro darg
    simp only [scottLambda_apply, ScottMap.comp_apply,
      ScottMap.pairMap_apply, ScottMap.fstMap_apply, ScottMap.sndMap_apply]
    rw [interp_rename primitive M arg arg'
      (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) arg'
        (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) self
          (ρ, dself), darg)) hfresh]
    apply interp_congr_free primitive M
    intro z hz
    have hzf : z ≠ arg' := by
      intro h
      subst z
      exact hfresh (mem_names_of_mem_free hz)
    by_cases hzs : z = self
    · subst z
      simp [envUpdate_apply, hsa, hne, Ne.symm hne]
    · by_cases hza : z = arg
      · subst z
        simp [envUpdate_apply, hsa, hne]
      · simp [envUpdate_apply, hzs, hza, hzf, hne]
  rw [hf]

/-- Value substitution is interpreted by an environment update when the
term's binders are fresh for the substituted value. This is the
capture-free core used by the general α-renaming proof. -/
theorem interp_subst_value_of_binders_fresh {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (x : Name) {V : Term Prim} (hV : Value V) :
    ∀ (M : Term Prim) (ρ : Env (SemanticValue Q D₀ j₀)),
      (∀ z, z ∈ names M → z ∉ free V) →
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive (subst x V M) ρ =
        interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M
          (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
            (ρ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
              primitive V ρ))
  | .var y, ρ, hfresh => by
      by_cases hyx : y = x
      · subst y
        simpa [subst, interp_var_apply, envUpdate_apply] using
          congrArg (fun f :
            ScottMap (Env (SemanticValue Q D₀ j₀)) (SemanticComp Q D₀ j₀) =>
              f ρ) (interp_value primitive hV)
      · simp [subst, interp_var_apply, envUpdate_apply, hyx]
  | .lam y M, ρ, hfresh => by
      have hyV : y ∉ free V := hfresh y (by simp [names])
      have hM : ∀ z, z ∈ names M → z ∉ free V := by
        intro z hz
        exact hfresh z (by simp [names, hz])
      by_cases hyx : y = x
      · subst y
        simp only [subst, if_pos]
        apply interp_congr_free primitive (.lam x M)
        intro z hz
        have hz' : z ∈ free M ∧ z ≠ x := by simpa [free] using hz
        rw [envUpdate_other hz'.2]
      · simp only [subst, if_neg hyx, hyV, if_false, interp_lam_apply]
        unfold lambdaValue
        simp only [ScottMap.comp_apply]
        have hfun :
            scottLambda
                ((interp primitive (subst x V M)).comp
                  (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) y)) ρ =
              scottLambda
                ((interp primitive M).comp
                  (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) y))
                (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
                  (ρ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
                    primitive V ρ)) := by
          apply ScottMap.ext
          intro d
          simp only [scottLambda_apply, ScottMap.comp_apply]
          rw [interp_subst_value_of_binders_fresh primitive x hV M
            (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) y (ρ, d)) hM]
          have hval :
              valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive V
                  (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) y (ρ, d)) =
                valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
                  primitive V ρ := by
            apply valueInterp_congr_free primitive hV
            intro z hz
            rw [envUpdate_other]
            intro hzy
            subst z
            exact hyV hz
          rw [hval]
          apply interp_congr_free primitive M
          intro z hz
          by_cases hzx : z = x
          · subst z
            simp [envUpdate_apply, Ne.symm hyx]
          · by_cases hzy : z = y
            · subst z
              simp [envUpdate_apply, hyx]
            · simp [envUpdate_apply, hzx, hzy]
        rw [hfun]
  | .app M N, ρ, hfresh => by
      have hM : ∀ z, z ∈ names M → z ∉ free V := by
        intro z hz
        exact hfresh z (by simp [names, hz])
      have hN : ∀ z, z ∈ names N → z ∉ free V := by
        intro z hz
        exact hfresh z (by simp [names, hz])
      rw [show subst x V (.app M N) = .app (subst x V M) (subst x V N)
        by simp [subst], interp_app_apply, interp_app_apply,
        applyComp_apply, applyComp_apply]
      have hiM := interp_subst_value_of_binders_fresh
        primitive x hV M ρ hM
      have hiN := interp_subst_value_of_binders_fresh
        primitive x hV N ρ hN
      have hCont :
          applyContinuation (Q := Q) (D₀ := D₀) (j₀ := j₀)
              (interp primitive (subst x V N)) ρ =
            applyContinuation (Q := Q) (D₀ := D₀) (j₀ := j₀)
              (interp primitive N)
              (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
                (ρ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
                  primitive V ρ)) := by
        apply ScottMap.ext
        intro f
        rw [applyContinuation_apply, applyContinuation_apply, hiN]
      rw [hiM, hCont]
  | .prim p, ρ, hfresh => by
      rw [show subst x V (.prim p) = .prim p by simp [subst],
        interp_prim_apply, interp_prim_apply]
  | .recLam self arg M, ρ, hfresh => by
      have hsV : self ∉ free V := hfresh self (by simp [names])
      have haV : arg ∉ free V := hfresh arg (by simp [names])
      have hM : ∀ z, z ∈ names M → z ∉ free V := by
        intro z hz
        exact hfresh z (by simp [names, hz])
      by_cases hbound : self = x ∨ arg = x
      · simp only [subst, if_pos hbound]
        apply interp_congr_free primitive (.recLam self arg M)
        intro z hz
        have hz' : z ∈ free M ∧ z ≠ arg ∧ z ≠ self := by
          simpa [free] using hz
        rcases hbound with hsx | hax
        · subst x
          rw [envUpdate_other hz'.2.2]
        · subst x
          rw [envUpdate_other hz'.2.1]
      · have hsx : self ≠ x := (not_or.mp hbound).1
        have hax : arg ≠ x := (not_or.mp hbound).2
        by_cases hsa : self = arg
        · have hsubst :
              subst x V (.recLam self arg M) =
                .recLam self arg (subst x V M) := by
            simp [subst, hax, hsa, haV]
          rw [hsubst, interp_recLam_apply, interp_recLam_apply]
          subst arg
          unfold recLambdaValue
          simp only [ScottMap.comp_apply, Proposition314.fixMap_apply]
          have hf :
              recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀) self self
                  (interp primitive (subst x V M)) ρ =
                recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀) self self
                  (interp primitive M)
                  (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
                    (ρ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
                      primitive V ρ)) := by
            unfold recFunctional
            apply ScottMap.ext
            intro dself
            simp only [scottLambda_apply, ScottMap.comp_apply]
            apply congrArg
            apply ScottMap.ext
            intro darg
            simp only [scottLambda_apply, ScottMap.comp_apply,
              ScottMap.pairMap_apply, ScottMap.fstMap_apply,
              ScottMap.sndMap_apply]
            rw [interp_subst_value_of_binders_fresh primitive x hV M
              (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) self
                (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) self
                  (ρ, dself), darg)) hM]
            have hval :
                valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive V
                    (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) self
                      (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) self
                        (ρ, dself), darg)) =
                  valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
                    primitive V ρ := by
              apply valueInterp_congr_free primitive hV
              intro z hz
              by_cases hzs : z = self
              · subst z
                exact (hsV hz).elim
              · simp [envUpdate_apply, hzs]
            rw [hval]
            apply interp_congr_free primitive M
            intro z hz
            rcases not_or.mp hbound with ⟨hsx, _⟩
            by_cases hzx : z = x
            · subst z
              simp [envUpdate_apply, Ne.symm hsx]
            · by_cases hzs : z = self
              · subst z
                simp [envUpdate_apply, hsx]
              · simp [envUpdate_apply, hzx, hzs]
          rw [hf]
        · have hsubst :
              subst x V (.recLam self arg M) =
                .recLam self arg (subst x V M) := by
            simp [subst, hsx, hax, hsa, hsV, haV]
          rw [hsubst, interp_recLam_apply, interp_recLam_apply]
          unfold recLambdaValue
          simp only [ScottMap.comp_apply, Proposition314.fixMap_apply]
          have hf :
              recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀) self arg
                  (interp primitive (subst x V M)) ρ =
                recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀) self arg
                  (interp primitive M)
                  (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
                    (ρ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
                      primitive V ρ)) := by
            unfold recFunctional
            apply ScottMap.ext
            intro dself
            simp only [scottLambda_apply, ScottMap.comp_apply]
            apply congrArg
            apply ScottMap.ext
            intro darg
            simp only [scottLambda_apply, ScottMap.comp_apply,
              ScottMap.pairMap_apply, ScottMap.fstMap_apply,
              ScottMap.sndMap_apply]
            rw [interp_subst_value_of_binders_fresh primitive x hV M
              (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) arg
                (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) self
                  (ρ, dself), darg)) hM]
            have hval :
                valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive V
                    (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) arg
                      (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) self
                        (ρ, dself), darg)) =
                  valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
                    primitive V ρ := by
              apply valueInterp_congr_free primitive hV
              intro z hz
              by_cases hza : z = arg
              · subst z
                exact (haV hz).elim
              · rw [envUpdate_other hza]
                by_cases hzs : z = self
                · subst z
                  exact (hsV hz).elim
                · rw [envUpdate_other hzs]
            rw [hval]
            rcases not_or.mp hbound with ⟨hsx, hax⟩
            rw [envUpdate_comm (Q := Q) (D₀ := D₀) (j₀ := j₀)
              (Ne.symm hsx) ρ
              (valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
                primitive V ρ) dself]
            rw [envUpdate_comm (Q := Q) (D₀ := D₀) (j₀ := j₀)
              (Ne.symm hax)
              (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀)
                self (ρ, dself))
              (valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
                primitive V ρ) darg]
          rw [hf]
  | .prob p M N, ρ, hfresh => by
      have hM : ∀ z, z ∈ names M → z ∉ free V := by
        intro z hz; exact hfresh z (by simp [names, hz])
      have hN : ∀ z, z ∈ names N → z ∉ free V := by
        intro z hz; exact hfresh z (by simp [names, hz])
      rw [show subst x V (.prob p M N) =
        .prob p (subst x V M) (subst x V N) by simp [subst],
        interp_prob_apply, interp_prob_apply,
        interp_subst_value_of_binders_fresh primitive x hV M ρ hM,
        interp_subst_value_of_binders_fresh primitive x hV N ρ hN]
  | .intern M N, ρ, hfresh => by
      have hM : ∀ z, z ∈ names M → z ∉ free V := by
        intro z hz; exact hfresh z (by simp [names, hz])
      have hN : ∀ z, z ∈ names N → z ∉ free V := by
        intro z hz; exact hfresh z (by simp [names, hz])
      rw [show subst x V (.intern M N) =
        .intern (subst x V M) (subst x V N) by simp [subst],
        interp_intern_apply, interp_intern_apply,
        interp_subst_value_of_binders_fresh primitive x hV M ρ hM,
        interp_subst_value_of_binders_fresh primitive x hV N ρ hN]
  | .extern M N, ρ, hfresh => by
      have hM : ∀ z, z ∈ names M → z ∉ free V := by
        intro z hz; exact hfresh z (by simp [names, hz])
      have hN : ∀ z, z ∈ names N → z ∉ free V := by
        intro z hz; exact hfresh z (by simp [names, hz])
      rw [show subst x V (.extern M N) =
        .extern (subst x V M) (subst x V N) by simp [subst],
        interp_extern_apply, interp_extern_apply,
        interp_subst_value_of_binders_fresh primitive x hV M ρ hM,
        interp_subst_value_of_binders_fresh primitive x hV N ρ hN]

/-- Lift the substitution equation through a non-capturing lambda binder. -/
private theorem interp_subst_value_lam {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (x y : Name) {V M : Term Prim} (hV : Value V)
    (hyx : y ≠ x) (hyV : y ∉ free V)
    (hbody : ∀ σ : Env (SemanticValue Q D₀ j₀),
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive (subst x V M) σ =
        interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M
          (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
            (σ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
              primitive V σ)))
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
        (.lam y (subst x V M)) ρ =
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive (.lam y M)
        (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
          (ρ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
            primitive V ρ)) := by
  rw [interp_lam_apply, interp_lam_apply]
  unfold lambdaValue
  simp only [ScottMap.comp_apply]
  have hf :
      scottLambda ((interp primitive (subst x V M)).comp
          (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) y)) ρ =
        scottLambda ((interp primitive M).comp
          (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) y))
          (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
            (ρ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
              primitive V ρ)) := by
    apply ScottMap.ext
    intro d
    simp only [scottLambda_apply, ScottMap.comp_apply]
    rw [hbody]
    have hval :
        valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive V
            (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) y (ρ, d)) =
          valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive V ρ := by
      apply valueInterp_congr_free primitive hV
      intro z hz
      rw [envUpdate_other]
      intro hzy
      subst z
      exact hyV hz
    rw [hval]
    apply interp_congr_free primitive M
    intro z hz
    by_cases hzx : z = x
    · subst z
      simp [envUpdate_apply, Ne.symm hyx]
    · by_cases hzy : z = y
      · subst z
        simp [envUpdate_apply, hyx]
      · simp [envUpdate_apply, hzx, hzy]
  rw [hf]

/-- Lift the substitution equation through recursive binders that do not
capture the substituted value. This includes coincident self/argument
binders. -/
private theorem interp_subst_value_recLam {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (x self arg : Name) {V M : Term Prim} (hV : Value V)
    (hsx : self ≠ x) (hax : arg ≠ x)
    (hsV : self ∉ free V) (haV : arg ∉ free V)
    (hbody : ∀ σ : Env (SemanticValue Q D₀ j₀),
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive (subst x V M) σ =
        interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M
          (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
            (σ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
              primitive V σ)))
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
        (.recLam self arg (subst x V M)) ρ =
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
        (.recLam self arg M)
        (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
          (ρ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
            primitive V ρ)) := by
  rw [interp_recLam_apply, interp_recLam_apply]
  unfold recLambdaValue
  simp only [ScottMap.comp_apply, Proposition314.fixMap_apply]
  have hf :
      recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀) self arg
          (interp primitive (subst x V M)) ρ =
        recFunctional (Q := Q) (D₀ := D₀) (j₀ := j₀) self arg
          (interp primitive M)
          (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
            (ρ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
              primitive V ρ)) := by
    unfold recFunctional
    apply ScottMap.ext
    intro dself
    simp only [scottLambda_apply, ScottMap.comp_apply]
    apply congrArg
    apply ScottMap.ext
    intro darg
    simp only [scottLambda_apply, ScottMap.comp_apply,
      ScottMap.pairMap_apply, ScottMap.fstMap_apply, ScottMap.sndMap_apply]
    rw [hbody]
    have hval :
        valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive V
            (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) arg
              (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) self
                (ρ, dself), darg)) =
          valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive V ρ := by
      apply valueInterp_congr_free primitive hV
      intro z hz
      by_cases hza : z = arg
      · subst z
        exact (haV hz).elim
      · rw [envUpdate_other hza]
        by_cases hzs : z = self
        · subst z
          exact (hsV hz).elim
        · rw [envUpdate_other hzs]
    rw [hval]
    apply interp_congr_free primitive M
    intro z hz
    by_cases hzx : z = x
    · subst z
      simp [envUpdate_apply, Ne.symm hsx, Ne.symm hax]
    · by_cases hza : z = arg
      · subst z
        simp [envUpdate_apply, hax]
      · by_cases hzs : z = self
        · subst z
          simp [envUpdate_apply, hsx, hza]
        · simp [envUpdate_apply, hzx, hza, hzs]
  rw [hf]

set_option maxHeartbeats 1000000 in
/-- Capture-avoiding substitution of a value is interpreted by updating the
environment. The alpha-renaming performed by `subst` is handled
semantically, so no binder-freshness hypothesis is required. -/
theorem interp_subst_value {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (x : Name) {V : Term Prim} (hV : Value V)
    (M : Term Prim) (ρ : Env (SemanticValue Q D₀ j₀)) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive (subst x V M) ρ =
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M
        (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
          (ρ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
            primitive V ρ)) := by
  cases M with
  | var y =>
      by_cases hyx : y = x
      · subst y
        simpa [subst, interp_var_apply, envUpdate_apply] using
          congrArg (fun f :
            ScottMap (Env (SemanticValue Q D₀ j₀)) (SemanticComp Q D₀ j₀) =>
              f ρ) (interp_value primitive hV)
      · simp [subst, interp_var_apply, envUpdate_apply, hyx]
  | lam y M =>
      by_cases hyx : y = x
      · subst y
        simp only [subst, if_pos]
        apply interp_congr_free primitive (.lam x M)
        intro z hz
        have hz' : z ∈ free M ∧ z ≠ x := by simpa [free] using hz
        rw [envUpdate_other hz'.2]
      · by_cases hyV : y ∈ free V
        · let avoid := y :: x :: free V ++ free M ++ names V ++ names M
          let y' := fresh avoid
          have hy' : y' ∉ avoid := by
            dsimp [y']
            exact fresh_not_mem avoid
          have hy'x : y' ≠ x := by
            dsimp [y']
            apply fresh_ne_of_mem
            simp [avoid]
          have hy'V : y' ∉ free V := by
            dsimp [y']
            apply fresh_not_mem_of_subset
            intro z hz
            simp [avoid, hz]
          have hy'M : y' ∉ names M := by
            dsimp [y']
            apply fresh_not_mem_of_subset
            intro z hz
            simp [avoid, hz]
          have hrec : ∀ σ : Env (SemanticValue Q D₀ j₀),
              interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
                  (subst x V (rename y y' M)) σ =
                interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
                  (rename y y' M)
                  (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
                    (σ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
                      primitive V σ)) := by
            intro σ
            apply interp_subst_value primitive x hV
          have hlift := interp_subst_value_lam
            (Q := Q) (D₀ := D₀) (j₀ := j₀)
            primitive x y' hV hy'x hy'V hrec ρ
          have halpha := interp_lam_alpha
            (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M y y'
            (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
              (ρ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
                primitive V ρ)) hy'M
          simpa only [subst, if_neg hyx, if_pos hyV, avoid, y'] using
            hlift.trans halpha
        · simpa only [subst, if_neg hyx, if_neg hyV] using
            interp_subst_value_lam
              (Q := Q) (D₀ := D₀) (j₀ := j₀)
              primitive x y hV hyx hyV
              (fun σ => interp_subst_value primitive x hV M σ) ρ
  | app M N =>
      rw [show subst x V (.app M N) = .app (subst x V M) (subst x V N)
        by simp [subst], interp_app_apply, interp_app_apply,
        applyComp_apply, applyComp_apply]
      have hiM := interp_subst_value primitive x hV M ρ
      have hiN := interp_subst_value primitive x hV N ρ
      have hCont :
          applyContinuation (Q := Q) (D₀ := D₀) (j₀ := j₀)
              (interp primitive (subst x V N)) ρ =
            applyContinuation (Q := Q) (D₀ := D₀) (j₀ := j₀)
              (interp primitive N)
              (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
                (ρ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
                  primitive V ρ)) := by
        apply ScottMap.ext
        intro f
        rw [applyContinuation_apply, applyContinuation_apply, hiN]
      rw [hiM, hCont]
  | prim p =>
      rw [show subst x V (.prim p) = .prim p by simp [subst],
        interp_prim_apply, interp_prim_apply]
  | recLam self arg M =>
      by_cases hbound : self = x ∨ arg = x
      · simp only [subst, if_pos hbound]
        apply interp_congr_free primitive (.recLam self arg M)
        intro z hz
        have hz' : z ∈ free M ∧ z ≠ arg ∧ z ≠ self := by
          simpa [free] using hz
        rcases hbound with hsx | hax
        · subst x
          rw [envUpdate_other hz'.2.2]
        · subst x
          rw [envUpdate_other hz'.2.1]
      · have hsx : self ≠ x := (not_or.mp hbound).1
        have hax : arg ≠ x := (not_or.mp hbound).2
        by_cases hsa : self = arg
        · subst arg
          by_cases hsV : self ∈ free V
          · let avoid := self :: x :: free V ++ free M ++ names V ++ names M
            let z := fresh avoid
            have hz : z ∉ avoid := by
              dsimp [z]
              exact fresh_not_mem avoid
            have hzx : z ≠ x := by
              dsimp [z]
              apply fresh_ne_of_mem
              simp [avoid]
            have hzV : z ∉ free V := by
              dsimp [z]
              apply fresh_not_mem_of_subset
              intro w hw
              simp [avoid, hw]
            have hzM : z ∉ names M := by
              dsimp [z]
              apply fresh_not_mem_of_subset
              intro w hw
              simp [avoid, hw]
            have hrec : ∀ σ : Env (SemanticValue Q D₀ j₀),
                interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
                    (subst x V (rename self z M)) σ =
                  interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
                    (rename self z M)
                    (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
                      (σ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
                        primitive V σ)) := by
              intro σ
              apply interp_subst_value primitive x hV
            have hlift := interp_subst_value_recLam
              (Q := Q) (D₀ := D₀) (j₀ := j₀)
              primitive x z z hV hzx hzx hzV hzV hrec ρ
            have halpha := interp_recLam_alpha_same
              (Q := Q) (D₀ := D₀) (j₀ := j₀)
              primitive M self z
              (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
                (ρ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
                  primitive V ρ)) hzM
            simpa only [subst, if_neg hbound, if_pos, if_pos hsV,
              avoid, z] using hlift.trans halpha
          · simpa only [subst, if_neg hbound, if_pos, if_neg hsV] using
              interp_subst_value_recLam
                (Q := Q) (D₀ := D₀) (j₀ := j₀)
                primitive x self self hV hsx hsx hsV hsV
                (fun σ => interp_subst_value primitive x hV M σ) ρ
        · let avoid :=
            self :: arg :: x :: free V ++ free M ++ names V ++ names M
          let self' := if self ∈ free V then fresh avoid else self
          let M' := if self' = self then M else rename self self' M
          let avoid' := self' :: avoid ++ names M'
          let arg' := if arg ∈ free V then fresh avoid' else arg
          let M'' := if arg' = arg then M' else rename arg arg' M'
          have hs'x : self' ≠ x := by
            dsimp [self']
            split
            · apply fresh_ne_of_mem
              simp [avoid]
            · exact hsx
          have hs'V : self' ∉ free V := by
            dsimp [self']
            split
            · apply fresh_not_mem_of_subset
              intro z hz
              simp [avoid, hz]
            · assumption
          have hs'a : self' ≠ arg := by
            dsimp [self']
            split
            · apply fresh_ne_of_mem
              simp [avoid]
            · exact hsa
          have ha'x : arg' ≠ x := by
            dsimp [arg']
            split
            · apply fresh_ne_of_mem
              simp [avoid', avoid]
            · exact hax
          have ha'V : arg' ∉ free V := by
            dsimp [arg']
            split
            · apply fresh_not_mem_of_subset
              intro z hz
              simp [avoid', avoid, hz]
            · assumption
          have ha's : arg' ≠ self' := by
            dsimp [arg']
            split
            · apply fresh_ne_of_mem
              simp [avoid']
            · exact Ne.symm hs'a
          have hsize : termSize M'' = termSize M := by
            exact recLam_subst_body_termSize self arg x V M
          have hdecr :
              termSize M'' < termSize (.recLam self arg M) := by
            rw [hsize]
            simp [termSize]
          have hrec : ∀ σ : Env (SemanticValue Q D₀ j₀),
              interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
                  (subst x V M'') σ =
                interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive M''
                  (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
                    (σ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
                      primitive V σ)) := by
            intro σ
            apply interp_subst_value primitive x hV
          have hlift := interp_subst_value_recLam
            (Q := Q) (D₀ := D₀) (j₀ := j₀)
            primitive x self' arg' hV hs'x ha'x hs'V ha'V hrec ρ
          have halphaSelf : ∀ σ,
              interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
                  (.recLam self' arg M') σ =
                interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
                  (.recLam self arg M) σ := by
            intro σ
            by_cases hsV : self ∈ free V
            · have hf : fresh avoid ∉ names M := by
                apply fresh_not_mem_of_subset
                intro z hz
                simp [avoid, hz]
              have hs'eq : self' = fresh avoid := by
                simp [self', hsV]
              have hne : fresh avoid ≠ self :=
                fresh_ne_of_mem (by simp [avoid])
              have hM'eq : M' = rename self (fresh avoid) M := by
                simp [M', hs'eq, hne]
              rw [hs'eq, hM'eq]
              exact interp_recLam_alpha_self
                  (Q := Q) (D₀ := D₀) (j₀ := j₀)
                  primitive M self arg (fresh avoid) σ hsa hf
                  (fresh_ne_of_mem (by simp [avoid]))
            · simp [self', M', hsV]
          have halphaArg : ∀ σ,
              interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
                  (.recLam self' arg' M'') σ =
                interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
                  (.recLam self' arg M') σ := by
            intro σ
            by_cases haV : arg ∈ free V
            · have hf : fresh avoid' ∉ names M' := by
                apply fresh_not_mem_of_subset
                intro z hz
                simp [avoid', hz]
              have ha'eq : arg' = fresh avoid' := by
                simp [arg', haV]
              have hne : fresh avoid' ≠ arg :=
                fresh_ne_of_mem (by simp [avoid', avoid])
              have hM''eq : M'' = rename arg (fresh avoid') M' := by
                simp [M'', ha'eq, hne]
              rw [ha'eq, hM''eq]
              exact interp_recLam_alpha_arg
                  (Q := Q) (D₀ := D₀) (j₀ := j₀)
                  primitive M' self' arg (fresh avoid') σ hs'a hf
                  (fresh_ne_of_mem (by simp [avoid']))
            · simp [arg', M'', haV]
          have halpha := (halphaArg
            (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
              (ρ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
                primitive V ρ))).trans
            (halphaSelf
              (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) x
                (ρ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
                  primitive V ρ)))
          have hsubst :
              subst x V (.recLam self arg M) =
                .recLam self' arg' (subst x V M'') := by
            simp only [subst, if_neg hbound, if_neg hsa]
            rfl
          rw [hsubst]
          exact hlift.trans halpha
  | prob p M N =>
      rw [show subst x V (.prob p M N) =
        .prob p (subst x V M) (subst x V N) by simp [subst],
        interp_prob_apply, interp_prob_apply,
        interp_subst_value primitive x hV M ρ,
        interp_subst_value primitive x hV N ρ]
  | intern M N =>
      rw [show subst x V (.intern M N) =
        .intern (subst x V M) (subst x V N) by simp [subst],
        interp_intern_apply, interp_intern_apply,
        interp_subst_value primitive x hV M ρ,
        interp_subst_value primitive x hV N ρ]
  | extern M N =>
      rw [show subst x V (.extern M N) =
        .extern (subst x V M) (subst x V N) by simp [subst],
        interp_extern_apply, interp_extern_apply,
        interp_subst_value primitive x hV M ρ,
        interp_subst_value primitive x hV N ρ]
termination_by termSize M
decreasing_by
  all_goals first | assumption | omega | simp_all [termSize, rename_termSize]

/-- β-soundness under the explicit binder-freshness condition required by
the capture-free substitution core. -/
theorem interp_beta_of_binders_fresh {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (x : Name) (M V : Term Prim) (hV : Value V)
    (ρ : Env (SemanticValue Q D₀ j₀))
    (hfresh : ∀ z, z ∈ names M → z ∉ free V) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
        (.app (.lam x M) V) ρ =
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
        (subst x V M) ρ := by
  rw [interp_app_apply,
    interp_value primitive (Value.lam x M),
    interp_value primitive hV]
  change
    applyComp (Q := Q) (D₀ := D₀) (j₀ := j₀)
        ((semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp
          (lambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀)
            x (interp primitive M)))
        ((semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp
          (valueInterp primitive V)) ρ =
      interp primitive (subst x V M) ρ
  rw [applyComp_pure_lambda]
  exact (interp_subst_value_of_binders_fresh
    primitive x hV M ρ hfresh).symm

/-- General semantic β-equation. Capture-avoiding substitution performs any
required alpha-renaming automatically. -/
theorem interp_beta {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (x : Name) (M V : Term Prim) (hV : Value V)
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
        (.app (.lam x M) V) ρ =
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
        (subst x V M) ρ := by
  rw [interp_app_apply,
    interp_value primitive (Value.lam x M),
    interp_value primitive hV]
  change
    applyComp (Q := Q) (D₀ := D₀) (j₀ := j₀)
        ((semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp
          (lambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀)
            x (interp primitive M)))
        ((semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp
          (valueInterp primitive V)) ρ =
      interp primitive (subst x V M) ρ
  rw [applyComp_pure_lambda]
  exact (interp_subst_value primitive x hV M ρ).symm

/-- General semantic recursive β-equation. The recursive abstraction is
installed at `self`, the pure argument at `arg`, and the distinct updates are
commuted to match the operational substitution order. -/
theorem interp_rec_beta {Prim : Type}
    (primitive : Prim → SemanticComp Q D₀ j₀)
    (self arg : Name) (M V : Term Prim)
    (hne : self ≠ arg) (hV : Value V)
    (ρ : Env (SemanticValue Q D₀ j₀)) :
    interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
        (.app (.recLam self arg M) V) ρ =
      interp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
        (subst arg V (subst self (.recLam self arg M) M)) ρ := by
  rw [interp_app_apply,
    interp_value primitive (Value.recLam self arg M),
    interp_value primitive hV]
  change
    applyComp (Q := Q) (D₀ := D₀) (j₀ := j₀)
        ((semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp
          (recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀)
            self arg (interp primitive M)))
        ((semanticUnit (Q := Q) (D₀ := D₀) (j₀ := j₀)).comp
          (valueInterp primitive V)) ρ =
      interp primitive
        (subst arg V (subst self (.recLam self arg M) M)) ρ
  rw [applyComp_pure_recLambda]
  rw [interp_subst_value primitive arg hV]
  rw [interp_subst_value primitive self (Value.recLam self arg M)]
  have hrec :
      valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive
          (.recLam self arg M)
          (envUpdate (Q := Q) (D₀ := D₀) (j₀ := j₀) arg
            (ρ, valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀)
              primitive V ρ)) =
        recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀)
          self arg (interp primitive M) ρ := by
    apply valueInterp_congr_free primitive (Value.recLam self arg M)
    intro x hx
    rw [envUpdate_other]
    intro hxa
    subst x
    simp [free] at hx
  rw [hrec]
  rw [envUpdate_comm (Q := Q) (D₀ := D₀) (j₀ := j₀)
    (Ne.symm hne) ρ
    (valueInterp (Q := Q) (D₀ := D₀) (j₀ := j₀) primitive V ρ)
    (recLambdaValue (Q := Q) (D₀ := D₀) (j₀ := j₀)
      self arg (interp primitive M) ρ)]

end Semantics

end QLambda
