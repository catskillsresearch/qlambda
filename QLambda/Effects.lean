/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Scott1972.ContinuousLattice.FunctionSpaces

/-!
# Effect powerdomains besides `Q`

Paper §1–2. Internal choice `⊓` is interpreted by a nondeterministic
powerdomain `𝒫`. External choice `□` needs an environment / synchrony
structure. The classical slogan is `D ≅ [D → 𝒫(𝒱_{≤1}(D))]`; the
ωQVA capstone only solves the `Q` half.
-/

namespace QLambda

open Scott1972.ContinuousLattice

universe u

/-- Plotkin / Smyth / Hoare powerdomain of `D` (not yet constructed). -/
noncomputable def NondetPower (D : Type u) [CompleteLattice D] : Type u := by
  sorry

noncomputable instance instCompleteLatticeNondetPower (D : Type u)
    [CompleteLattice D] : CompleteLattice (NondetPower D) := by
  sorry

/-- Algebra of internal choice on a domain. -/
class HasInternalChoice (D : Type u) [CompleteLattice D] where
  intern : D → D → D

/-- Algebra of external / interactive choice. -/
class HasExternalChoice (D : Type u) [CompleteLattice D] where
  extern : D → D → D

/-- `𝒫(D)` carries internal choice. -/
noncomputable instance instHasInternalChoiceNondet (D : Type u)
    [CompleteLattice D] : HasInternalChoice (NondetPower D) := by
  sorry

/-- External choice on `D` (not yet constructed). -/
noncomputable instance instHasExternalChoice (D : Type u)
    [CompleteLattice D] : HasExternalChoice D := by
  sorry

end QLambda
