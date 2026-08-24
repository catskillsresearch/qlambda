/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.QuantumPower

/-!
# Quantum computation as a lawful monad (LNL)

Paper §5. Selinger–Valiron treat quantum computation as a monad on a
linear-nonlinear layer. `IsQuantumPowerModel` is only an endofunctor
spec. This chapter records the additional operations and laws needed
for a computation-valued interpretation. Concrete instances are supplied
by later modules, notably `QLambda.TTContinuationMonad`.
-/

namespace QLambda

open Scott1972.ContinuousLattice

universe u

/-- A locally continuous quantum computation model with lawful Kleisli extension. -/
class IsQuantumMonad (Q : (D : Type u) → [CompleteLattice D] → Type u)
    extends IsQuantumPowerModel Q where
  unit : ∀ {D : Type u} [CompleteLattice D],
    letI := str D
    ScottMap D (Q D)
  bind : ∀ {D E : Type u} [CompleteLattice D] [CompleteLattice E],
    letI := str D
    letI := str E
    ScottMap (ScottMap D (Q E)) (ScottMap (Q D) (Q E))
  bind_unit : ∀ {D : Type u} [CompleteLattice D],
    letI := str D
    bind (unit (D := D)) = ScottMap.idMap
  unit_bind : ∀ {D E : Type u} [CompleteLattice D] [CompleteLattice E]
      (f : letI := str E; ScottMap D (Q E)),
    letI := str D
    letI := str E
    (bind f).comp unit = f
  bind_assoc : ∀ {D E F : Type u}
      [CompleteLattice D] [CompleteLattice E] [CompleteLattice F]
      (f : letI := str E; ScottMap D (Q E))
      (g : letI := str F; ScottMap E (Q F)),
    letI := str D
    letI := str E
    letI := str F
    (bind g).comp (bind f) = bind ((bind g).comp f)
  map_eq_bind_unit : ∀ {D E : Type u} [CompleteLattice D] [CompleteLattice E]
      (f : ScottMap D E),
    letI := str D
    letI := str E
    map f = bind (unit.comp f)

/-- Regard a quantum monad as its underlying bundled quantum power model.
Using this constructor keeps the power-model and monad structures
definitionally aligned in computation-valued semantics. -/
noncomputable abbrev quantumMonadModel
    (Q : (D : Type u) → [CompleteLattice D] → Type u)
    [m : IsQuantumMonad Q] : QuantumPowerModel where
  Power := Q
  spec := m.toIsQuantumPowerModel

end QLambda
