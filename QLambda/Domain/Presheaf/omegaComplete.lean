/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.OmegaEnriched
import QLambda.Domain.Presheaf.instPartialOrderSuperoperator
import QLambda.Domain.Presheaf.instOrderBotSuperoperator

/-!
# Instance `omegaComplete`
-/

namespace QLambda.Domain.Presheaf
namespace Superoperator

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable instance omegaComplete {n m : ℕ} :
    QLambda.Domain.OmegaComplete (Superoperator n m) where
  ωSup := omegaSup
  le_ωSup := le_omegaSup
  ωSup_le := omegaSup_le

theorem eq_omegaSup_of_tendsto {n m : ℕ}
    (c : ℕ → Superoperator n m) (hc : Monotone c)
    (y : Superoperator n m) (hy : ∀ N, c N ≤ y)
    (ht : Filter.Tendsto (fun N => (c N).cp.choi) Filter.atTop
      (nhds y.cp.choi)) :
    y = QLambda.Domain.OmegaComplete.ωSup c hc := by
  let s := QLambda.Domain.OmegaComplete.ωSup c hc
  apply le_antisymm
  · change y.cp.choi ≤ s.cp.choi
    rw [Matrix.le_iff]
    have hpos (N : ℕ) :
        (s.cp.choi - (c N).cp.choi).PosSemidef :=
      Matrix.le_iff.mp
        (QLambda.Domain.OmegaComplete.le_ωSup c hc N)
    exact posSemidef_of_tendsto
      (fun N => s.cp.choi - (c N).cp.choi)
      (s.cp.choi - y.cp.choi) hpos
      (tendsto_const_nhds.sub ht)
  · exact QLambda.Domain.OmegaComplete.ωSup_le c hc y hy

theorem comp_omegaSup_left {n m l : ℕ}
    (c : ℕ → Superoperator m l) (hc : Monotone c)
    (g : Superoperator n m) :
    comp (QLambda.Domain.OmegaComplete.ωSup c hc) g =
      QLambda.Domain.OmegaComplete.ωSup (fun N => comp (c N) g)
        ((comp_mono_left g).comp hc) := by
  apply eq_omegaSup_of_tendsto
  · intro N
    exact comp_mono_left g
      (QLambda.Domain.OmegaComplete.le_ωSup c hc N)
  · exact choi_comp_tendsto_left c hc g

theorem comp_omegaSup_right {n m l : ℕ}
    (f : Superoperator m l) (c : ℕ → Superoperator n m)
    (hc : Monotone c) :
    comp f (QLambda.Domain.OmegaComplete.ωSup c hc) =
      QLambda.Domain.OmegaComplete.ωSup (fun N => comp f (c N))
        ((comp_mono_right f).comp hc) := by
  apply eq_omegaSup_of_tendsto
  · intro N
    exact comp_mono_right f
      (QLambda.Domain.OmegaComplete.le_ωSup c hc N)
  · exact choi_comp_tendsto_right f c hc


end Superoperator
end QLambda.Domain.Presheaf
