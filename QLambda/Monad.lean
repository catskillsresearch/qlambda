/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Quantum.QuantumPower

/-!
# Quantum powerdomain as a monad (LNL)

Paper §5. Selinger–Valiron treat `Q` as a monad on a linear-nonlinear
layer. `IsQuantumPowerModel` is only an endofunctor spec. This chapter
adds unit and bind (Kleisli extension) so `Q` can interpret
measurement and mixed states, not only the domain equation
`D ≅ [D → Q(D)]`.
-/

namespace QLambda

open Scott1972.ContinuousLattice

universe u

/-- A quantum powerdomain that is a monad on Scott maps. -/
class IsQuantumMonad (Q : (D : Type u) → [CompleteLattice D] → Type u)
    extends IsQuantumPowerModel Q where
  unit : ∀ {D : Type u} [CompleteLattice D],
    letI := str D
    ScottMap D (Q D)
  bind : ∀ {D E : Type u} [CompleteLattice D] [CompleteLattice E],
    letI := str D
    letI := str E
    ScottMap D (Q E) → ScottMap (Q D) (Q E)

/-- (V) as a monad. -/
noncomputable instance instIsQuantumMonadValuation :
    IsQuantumMonad QuantumValuationPower := by
  sorry

/-- (S) as a monad. -/
noncomputable instance instIsQuantumMonadSaturation :
    IsQuantumMonad QuantumSaturationPower := by
  sorry

end QLambda
