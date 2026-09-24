/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.OmegaEnriched
import QLambda.Domain.Presheaf.omegaComplete
import QLambda.Domain.Presheaf.unitHomPartialOrder
import QLambda.Domain.Presheaf.unitHomOrderBot

/-!
# Instance `unitHomOmegaComplete`
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-- Pointwise supremum of an increasing chain of maps into the tensor unit. -/
noncomputable def unitHomOmegaSup (P : Module)
    (c : ℕ → Hom P dayTensorUnit) (hc : Monotone c) :
    Hom P dayTensorUnit where
  app := fun n x =>
    Superoperator.omegaSup
      (fun k => (show Superoperator n 1 from (c k).app n x))
      (fun _ _ h => hc h n x)
  map_zero := by
    intro n
    let d : ℕ → Superoperator n 1 := fun k => (c k).app n 0
    have hd : ∀ k, d k = 0 := fun k => (c k).map_zero n
    change Superoperator.omegaSup d _ = 0
    apply le_antisymm
    · apply QLambda.Domain.OmegaComplete.ωSup_le
      intro k
      rw [hd]
    · exact bot_le
  map_sum := by
    intro ι _ n f s h
    exact SigmaMon.ChoiSum.hasSum_omegaSup
      (fun k i => (c k).app n (f i))
      (fun k => (c k).app n s)
      (fun i _ _ hk => hc hk n (f i))
      (fun _ _ hk => hc hk n s)
      (fun k => (c k).map_sum h)
  naturality := by
    intro m n x f
    dsimp [dayTensorUnit, representable]
    rw (config := { transparency := .default }) [Superoperator.comp_omegaSup_left]
    apply le_antisymm
    · apply Superoperator.omegaSup_le
      intro k
      have hk := (c k).naturality x f
      dsimp [dayTensorUnit, representable] at hk
      rw [hk]
      exact Superoperator.le_omegaSup
        (fun r => Superoperator.comp ((c r).app n x) f) _ k
    · apply Superoperator.omegaSup_le
      intro k
      have hk := (c k).naturality x f
      dsimp [dayTensorUnit, representable] at hk
      rw [← hk]
      exact Superoperator.le_omegaSup
        (fun r => (c r).app m (P.act x f)) _ k

/-- Precomposition is monotone for the pointwise Choi order. -/

noncomputable instance unitHomOmegaComplete (P : Module) :
    QLambda.Domain.OmegaComplete (Hom P dayTensorUnit) where
  ωSup := unitHomOmegaSup P
  le_ωSup c hc k n x :=
    QLambda.Domain.OmegaComplete.le_ωSup
      (fun r =>
        (show Superoperator n 1 from (c r).app n x))
      (fun _ _ h => hc h n x) k
  ωSup_le c hc f hf n x :=
    QLambda.Domain.OmegaComplete.ωSup_le
      (fun r =>
        (show Superoperator n 1 from (c r).app n x))
      (fun _ _ h => hc h n x)
      (show Superoperator n 1 from f.app n x)
      (fun k => hf k n x)

end SuperoperatorModule
end QLambda.Domain.Presheaf
