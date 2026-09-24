/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Module

/-!
# Joint action at arbitrary fiber dimension (`HasActSumFromDim`)

Includes the ambient CPM module instance.
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SuperoperatorModule

universe u

/-- Joint action at an arbitrary fiber dimension.  Holds for ambient CP
modules; fails for TNI representables when `d ≥ 2`. -/
class HasActSumFromDim (M : Module.{u}) : Prop where
  act_sum_from_dim :
    ∀ {ι : Type} [Countable ι] {m d : ℕ}
      {x : ι → (M.obj d).Carrier} {s : (M.obj d).Carrier}
      (f : ι → Superoperator m d),
      (M.obj d).HasSum x s →
        ∃ z : (M.obj m).Carrier,
          (M.obj m).HasSum (fun i => M.act (x i) (f i)) z

/-- The ambient module `CPM(-, A)` of unrestricted completely positive maps.
It is distinct from the representable `Q(-, A)`, whose elements are TNI. -/
noncomputable def cpmModule (A : ℕ) : Module where
  obj n :=
    { Carrier := CPMap n A
      zero := 0
      summation := SigmaMon.cpMapPartialCountableSum }
  act := fun x f => CPMap.comp x f.cp
  act_zero_element := by
    intro m n f
    exact CPMap.comp_zero_left f.cp
  act_zero_map := by
    intro m n x
    exact CPMap.comp_zero_right x
  act_id := by
    intro n x
    change CPMap.comp x (Superoperator.identity n).cp = x
    rw [show (Superoperator.identity n).cp = CPMap.identity n from rfl]
    exact CPMap.comp_identity x
  act_comp := by
    intro ℓ m n x f g
    simpa using (CPMap.comp_assoc x f.cp g.cp).symm
  act_sum_element := by
    intro ι _ m n x s f h
    exact SigmaMon.CPMapSum.comp_right f.cp h
  act_sum_map := by
    intro ι _ m n x f s h
    exact SigmaMon.CPMapSum.comp_left x h
  act_sum_from_one := by
    intro ι _ m x s f h
    obtain ⟨Χ, hΧ⟩ := SigmaMon.CPMapSum.comp_from_one f h
    exact ⟨Χ, hΧ⟩
  act_sum_tensor_from_one := by
    intro ι _ m B x s f h
    have hmat :
        Summable fun k : ι =>
          (CPMap.comp (x k)
              (Superoperator.tensor (f k)
                (Superoperator.identity B)).cp).choi := by
      refine Pi.summable.mpr fun ai => Pi.summable.mpr fun bj => ?_
      rcases ai with ⟨a, i⟩; rcases bj with ⟨b, j⟩
      have ha :
          Summable fun k : ι =>
            ∑ u : Fin (1 * B), ∑ v : Fin (1 * B),
              ‖(x k).choi (a, u) (b, v)‖ * ((m * B : ℕ) : ℝ) := by
        apply summable_sum
        intro u _
        apply summable_sum
        intro v _
        exact
          ((((Pi.hasSum.mp (Pi.hasSum.mp h (a, u)) (b, v))).summable.norm).mul_right
            ((m * B : ℕ) : ℝ))
      refine Summable.of_norm_bounded ha fun k => ?_
      simp only [CPMap.choi_comp_apply]
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro u _
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro v _
      rw [norm_mul]
      have hb :=
        SigmaMon.ChoiSum.entry_norm_le_trace_re
          (Superoperator.tensor (f k)
            (Superoperator.identity B)).cp.choi_pos
          (u, i) (v, j)
      have htr :=
        SigmaMon.ChoiSum.trace_choi_re_le_input_dim
          (Superoperator.tensor (f k) (Superoperator.identity B))
      exact mul_le_mul_of_nonneg_left (hb.trans htr) (norm_nonneg _)
    exact
      ⟨⟨∑' k,
          (CPMap.comp (x k)
              (Superoperator.tensor (f k)
                (Superoperator.identity B)).cp).choi,
        SigmaMon.ChoiSum.hasSum_posSemidef hmat.hasSum fun k =>
          (CPMap.comp (x k)
              (Superoperator.tensor (f k)
                (Superoperator.identity B)).cp).choi_pos⟩,
        hmat.hasSum⟩

@[simp]
theorem cpmModule_obj (A n : ℕ) :
    ((cpmModule A).obj n).Carrier = CPMap n A :=
  rfl

@[simp]
theorem cpmModule_act {A m n : ℕ}
    (x : CPMap n A) (f : Superoperator m n) :
    (cpmModule A).act x f = CPMap.comp x f.cp :=
  rfl

/-- CPM fibers admit Bool-split sums (unrestricted CP addition). -/
theorem Fiber.HasSumAdd.cpmModule (A n : ℕ) :
    Fiber.HasSumAdd ((cpmModule A).obj n) := by
  intro a b
  change CPMap n A at a b
  exact ⟨a + b, SigmaMon.CPMapSum.hasSum_add a b⟩

end SuperoperatorModule

end QLambda.Domain.Presheaf
