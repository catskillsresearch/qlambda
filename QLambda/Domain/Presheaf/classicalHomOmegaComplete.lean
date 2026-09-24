/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.OmegaEnriched
import QLambda.Domain.Presheaf.unitHomOmegaComplete
import QLambda.Domain.Presheaf.classicalHomPartialOrder
import QLambda.Domain.Presheaf.classicalHomOrderBot

/-!
# Instance `classicalHomOmegaComplete`
-/

set_option maxHeartbeats 800000
namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

theorem classicalHom_paired_mono {M : Module}
    {N : BiorthogonalObject}
    {c : ℕ → Hom M N.module} (hc : Monotone c) :
    Monotone (fun k => closedPairingEquiv M N (c k)) :=
  fun _ _ h n x => hc h n x

/-- ω-suprema of classical homs, transported from maps into the unit. -/
noncomputable def classicalHomOmegaSup (M : Module)
    (N : BiorthogonalObject)
    (c : ℕ → Hom M N.module) (hc : Monotone c) :
    Hom M N.module :=
  (closedPairingEquiv M N).symm
    (QLambda.Domain.OmegaComplete.ωSup
      (fun k => closedPairingEquiv M N (c k))
      (classicalHom_paired_mono hc))


noncomputable instance classicalHomOmegaComplete
    (M : Module) (N : BiorthogonalObject) :
    QLambda.Domain.OmegaComplete (Hom M N.module) where
  ωSup := classicalHomOmegaSup M N
  le_ωSup c hc k := by
    intro n x
    have h :=
      QLambda.Domain.OmegaComplete.le_ωSup
        (fun r => closedPairingEquiv M N (c r))
        (classicalHom_paired_mono hc) k
    change
      (show Superoperator n 1 from
        (closedPairingEquiv M N (c k)).app n x) ≤
        (show Superoperator n 1 from
          (closedPairingEquiv M N
            (classicalHomOmegaSup M N c hc)).app n x)
    simp only [classicalHomOmegaSup, Equiv.apply_symm_apply]
    exact h n x
  ωSup_le c hc f hf := by
    intro n x
    have h :=
      QLambda.Domain.OmegaComplete.ωSup_le
        (fun r => closedPairingEquiv M N (c r))
        (classicalHom_paired_mono hc)
        (closedPairingEquiv M N f)
        (fun k => show ClassicalHomLE M N (c k) f from hf k)
    change
      (show Superoperator n 1 from
        (closedPairingEquiv M N
          (classicalHomOmegaSup M N c hc)).app n x) ≤
        (show Superoperator n 1 from
          (closedPairingEquiv M N f).app n x)
    simp only [classicalHomOmegaSup, Equiv.apply_symm_apply]
    exact h n x

end SuperoperatorModule
end QLambda.Domain.Presheaf
