/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Fiber

/-!
# Specialized right module over finite-dimensional superoperators
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SuperoperatorModule

universe u

/-- A specialized right module over finite-dimensional trace-nonincreasing
superoperators.  The two sum laws are exactly enriched functoriality in the
element and superoperator arguments. -/
structure Module where
  obj : ℕ → Fiber.{u}
  act : {m n : ℕ} → (obj n).Carrier → Superoperator m n → (obj m).Carrier
  act_zero_element :
    ∀ {m n} (f : Superoperator m n), act (0 : (obj n).Carrier) f = 0
  act_zero_map :
    ∀ {m n} (x : (obj n).Carrier), act x (0 : Superoperator m n) = 0
  act_id :
    ∀ {n} (x : (obj n).Carrier), act x (Superoperator.identity n) = x
  act_comp :
    ∀ {ℓ m n} (x : (obj n).Carrier)
      (f : Superoperator m n) (g : Superoperator ℓ m),
      act (act x f) g = act x (Superoperator.comp f g)
  act_sum_element :
    ∀ {ι : Type} [Countable ι] {m n} {x : ι → (obj n).Carrier}
      {s : (obj n).Carrier} (f : Superoperator m n),
      (obj n).HasSum x s →
        (obj m).HasSum (fun i => act (x i) f) (act s f)
  act_sum_map :
    ∀ {ι : Type} [Countable ι] {m n} (x : (obj n).Carrier)
      {f : ι → Superoperator m n} {s : Superoperator m n},
      SigmaMon.ChoiSum.HasSum f s →
        (obj m).HasSum (fun i => act x (f i)) (act x s)
  /-- Joint action of a summable family at the unit fiber against an
  arbitrary family of maps into the unit fiber. -/
  act_sum_from_one :
    ∀ {ι : Type} [Countable ι] {m} {x : ι → (obj 1).Carrier}
      {s : (obj 1).Carrier} (f : ι → Superoperator m 1),
      (obj 1).HasSum x s →
        ∃ z : (obj m).Carrier,
          (obj m).HasSum (fun i => act (x i) (f i)) z
  /-- Joint action of a summable family at fiber `1 * A` against maps
  `f i ⊗ id_A`. -/
  act_sum_tensor_from_one :
    ∀ {ι : Type} [Countable ι] {m A} {x : ι → (obj (1 * A)).Carrier}
      {s : (obj (1 * A)).Carrier} (f : ι → Superoperator m 1),
      (obj (1 * A)).HasSum x s →
        ∃ z : (obj (m * A)).Carrier,
          (obj (m * A)).HasSum
            (fun i =>
              act (x i)
                (Superoperator.tensor (f i) (Superoperator.identity A)))
            z
  /- NOTE (Gate 3 / Path 2): a proposed field

  ```
  act_sum_from_dim :
    ∀ {ι} [Countable ι] {m d} {x : ι → (obj d).Carrier} {s}
      (f : ι → Superoperator m d),
      (obj d).HasSum x s →
        ∃ z, (obj m).HasSum (fun i => act (x i) (f i)) z
  ```

  is **false** for TNI/representable modules when `d ≥ 2`; see
  `SigmaMon.ChoiSum.exists_fiber2_comp_without_superoperator_sum`
  (`e0`/`e1`/`p0`/`p1`, `not_exists_hasSum_gate3Composed`).
  It holds for unrestricted CP via `CPMapSum.comp_from_dim` /
  `HasActSumFromDim`.  Do not reintroduce it as a required `Module` field. -/

end SuperoperatorModule

end QLambda.Domain.Presheaf
