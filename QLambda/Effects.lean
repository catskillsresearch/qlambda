/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Order.UpperLower.CompleteLattice
import Scott1972.ContinuousLattice.FunctionSpaces

/-!
# Effect powerdomains besides `Q`

Paper §1–2. Internal choice `⊓` is interpreted by a nondeterministic
powerdomain `𝒫`. Here `𝒫(D)` is the complete lattice of upper sets
(a Smyth-style carrier; Scott-closed convex Plotkin is not yet built).
External choice `□` needs an environment / synchrony structure and is
only a class, with no global instance.
-/

namespace QLambda

open Scott1972.ContinuousLattice

universe u

/-- Upper-set powerdomain of `D` (Smyth carrier, inclusion order). -/
abbrev NondetPower (D : Type u) [Preorder D] : Type u :=
  UpperSet D

noncomputable instance instCompleteLatticeNondetPower (D : Type u)
    [CompleteLattice D] : CompleteLattice (NondetPower D) :=
  inferInstance

/-- Algebra of internal choice on a domain. -/
class HasInternalChoice (D : Type u) [CompleteLattice D] where
  intern : D → D → D

/-- Algebra of external / interactive choice. -/
class HasExternalChoice (D : Type u) [CompleteLattice D] where
  extern : D → D → D

/-- Internal choice on `𝒫(D)` is the join of upper sets. -/
instance instHasInternalChoiceNondet (D : Type u)
    [CompleteLattice D] : HasInternalChoice (NondetPower D) where
  intern := (· ⊔ ·)

end QLambda
