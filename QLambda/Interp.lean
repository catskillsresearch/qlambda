/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Effects
import QLambda.Operational
import QLambda.Syntax
import QLambda.QuantumDomainEquation

/-!
# Denotational interpretation of `qλ`

Paper §2 and §7. A term is interpreted in the inverse limit
`D_∞ ≅ [D_∞ → Q(D_∞)]`:

* application uses the order iso;
* `⊕_p` uses convex combination in the computation object;
* `⊓` uses `NondetPower`;
* `□` uses `HasExternalChoice`.

The current declarations are a specification boundary: the concrete
interpretation is added only after the instrument powerdomain and its
choice operations have been constructed.
-/

namespace QLambda

open Scott1972.ContinuousLattice

universe u

/-- Environments: names to elements of `D_∞`. -/
abbrev Env (Dinf : Type u) : Type u := Name → Dinf

/-- Interpretation of a term in the quantum inverse limit. -/
noncomputable def interp (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier))
    (_ρ : Env (QDInf M D₀ j₀)) : Term → QDInf M D₀ j₀ := by
  sorry

/-- Soundness specification: an internal one-step reduct refines the
denotation of its redex. -/
theorem interp_step_sound (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier))
    (ρ : Env (QDInf M D₀ j₀)) {t t' : Term} (_h : Step t t') :
    interp M D₀ j₀ ρ t' ≤ interp M D₀ j₀ ρ t := by
  sorry

end QLambda
