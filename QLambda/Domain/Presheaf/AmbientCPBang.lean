/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Comonoid

/-!
# Ambient-CP relative bang admissibility (L9)

L8 named `AmbientCPDayBangCategory` as scaffolding (`HasSumAdd` /
`HasActSumFromDim` on `cpmModule`).  This file rebuilds the Day comult
*gate* relative to that fiber class:

* `AmbientCPModule` — modules with Bool-additive fibers and joint action at
  every dimension;
* `BangComultAmbientCPAdmissible` — `BangComultComponentsAdmissible` with the
  bilinear target restricted to `AmbientCPModule`.

Absolute `BangComultComponentsAdmissible 2` is **not** claimed: ambient-CP
targets evade the Day-transfer Bool obstruction but do not remove nonadditive
TNI targets from the absolute quantifier.

**Status.**  Full relative admissibility is closed for `A ≤ 1` (inherits from
absolute).  For every `A`, each fixed total degree admits a finite ambient-CP
row sum via `HasSumAdd` + `HasActSumFromDim`
(`bangComultAmbientCP_degree_row_hasSum`).  Gluing those rows into a single
`ℕ × ℕ` sum for `A ≥ 2` is the common-fiber residual recorded as
`BangDegreeUnitRectangleHasSum` in `Comonoid.lean` (row intermediates live at
`A^k`).  L10–L12 still need relative Day/comonoid packaging for LNL.
-/

namespace QLambda.Domain.Presheaf.SuperoperatorModule

set_option maxHeartbeats 8000000

/-- Fiber class restored by the L8 ambient-CP replacement: Bool-additive
fibers and joint action at every dimension. -/
class AmbientCPModule (M : Module.{0}) : Prop where
  has_sum_add : ∀ n, Fiber.HasSumAdd (M.obj n)
  has_act_sum_from_dim : HasActSumFromDim M

instance cpmModule_ambientCP (B : ℕ) : AmbientCPModule (cpmModule B) where
  has_sum_add := fun n => Fiber.HasSumAdd.cpmModule B n
  has_act_sum_from_dim := HasActSumFromDim.cpmModule B

/-- Mixed-degree Day summability of homogeneous split components, relative to
ambient-CP bilinear targets only. -/
def BangComultAmbientCPAdmissible (A : ℕ) : Prop :=
  ∀ (n : ℕ) (x : ((bang A).obj n).Carrier)
    (L : Module) [AmbientCPModule L]
    (β : Bilinear (bang A) (bang A) L),
    ∃ z : (L.obj n).Carrier,
      (L.obj n).HasSum
        (fun pq : ℕ × ℕ =>
          DayCoend.evaluate L β
            (bangComultComponentFamily A n x pq))
        z

/-- Absolute Day admissibility implies the ambient-CP restriction. -/
theorem bangComultAmbientCPAdmissible_of_components (A : ℕ)
    (h : BangComultComponentsAdmissible A) :
    BangComultAmbientCPAdmissible A := by
  intro n x L _ β
  exact h n x L β

theorem bangComultAmbientCPAdmissible_zero :
    BangComultAmbientCPAdmissible 0 :=
  bangComultAmbientCPAdmissible_of_components 0
    bangComultComponentsAdmissible_zero

theorem bangComultAmbientCPAdmissible_one :
    BangComultAmbientCPAdmissible 1 :=
  bangComultAmbientCPAdmissible_of_components 1
    bangComultComponentsAdmissible_one

theorem bangComultAmbientCPAdmissible_of_le_one (A : ℕ) (hA : A ≤ 1) :
    BangComultAmbientCPAdmissible A := by
  interval_cases A
  · exact bangComultAmbientCPAdmissible_zero
  · exact bangComultAmbientCPAdmissible_one

/-- Per-degree ambient-CP row: finite partitions of a fixed total degree. -/
def BangComultAmbientCPDegreeRowAdmissible (A : ℕ) : Prop :=
  ∀ (n k : ℕ) (x : ((bang A).obj n).Carrier)
    (L : Module) [AmbientCPModule L]
    (β : Bilinear (bang A) (bang A) L),
    ∃ z : (L.obj n).Carrier,
      (L.obj n).HasSum
        (fun part : DegreePartition k =>
          DayCoend.evaluate L β
            (bangComultComponentFamily A n x
              (degreePartitionToPair k part)))
        z

/-- Product of Yoneda unit fibers equals the degree-`k` tensor-power dimension. -/
theorem tensorPowerDimension_mul_partition (A k : ℕ)
    (part : DegreePartition k) :
    tensorPowerDimension A part.val *
        tensorPowerDimension A (k - part.val) =
      tensorPowerDimension A k := by
  have hpq : part.val + (k - part.val) = k :=
    Nat.add_sub_of_le (Nat.le_of_lt_succ part.isLt)
  rw [tensorPowerDimension_eq_pow, tensorPowerDimension_eq_pow,
    tensorPowerDimension_eq_pow, ← pow_add, hpq]

/-- Cast a bilinear generator along `A^p * A^q = A^k`. -/
noncomputable def bangAmbientCPRowGenerator (A k n : ℕ)
    (part : DegreePartition k) (_x : ((bang A).obj n).Carrier)
    (L : Module) (β : Bilinear (bang A) (bang A) L) :
    (L.obj (tensorPowerDimension A k)).Carrier :=
  let p := part.val
  let q := k - part.val
  let hdim := tensorPowerDimension_mul_partition A k part
  (congrArg (fun m => (L.obj m).Carrier) hdim) ▸
    β.app (bangDegreeUnit A p) (bangDegreeUnit A q)

/-- Cast a bang split along `A^p * A^q = A^k`. -/
noncomputable def bangAmbientCPRowSplit (A k n : ℕ)
    (part : DegreePartition k) (x : ((bang A).obj n).Carrier) :
    Superoperator n (tensorPowerDimension A k) :=
  let p := part.val
  let q := k - part.val
  let hdim := tensorPowerDimension_mul_partition A k part
  (congrArg (Superoperator n) hdim) ▸
    (bangSplitComponent A p q).app n x

/-- Action is invariant under casting the intermediate fiber dimension. -/
theorem Module.act_congrArg_dim {L : Module} {n a b : ℕ} (h : a = b)
    (x : (L.obj a).Carrier) (f : Superoperator n a) :
    L.act ((congrArg (fun m => (L.obj m).Carrier) h) ▸ x)
        ((congrArg (Superoperator n) h) ▸ f) =
      L.act x f := by
  cases h
  rfl

theorem bangComultComponent_evaluate_partition (A k n : ℕ)
    (part : DegreePartition k) (x : ((bang A).obj n).Carrier)
    (L : Module) (β : Bilinear (bang A) (bang A) L) :
    DayCoend.evaluate L β
        ((bangComultComponent A part.val (k - part.val)).app n x) =
      L.act (bangAmbientCPRowGenerator A k n part x L β)
        (bangAmbientCPRowSplit A k n part x) := by
  have he :=
    bangComultComponent_evaluate A part.val (k - part.val) n x L β
  refine Eq.trans he ?_
  symm
  exact Module.act_congrArg_dim
    (tensorPowerDimension_mul_partition A k part)
    (β.app (bangDegreeUnit A part.val) (bangDegreeUnit A (k - part.val)))
    ((bangSplitComponent A part.val (k - part.val)).app n x)

/-- Ambient-CP modules admit every fixed-degree bang-comult row. -/
theorem bangComultAmbientCP_degree_row_hasSum (A : ℕ) :
    BangComultAmbientCPDegreeRowAdmissible A := by
  intro n k x L hL β
  let d := tensorPowerDimension A k
  let R : DegreePartition k → (L.obj d).Carrier := fun part =>
    bangAmbientCPRowGenerator A k n part x L β
  obtain ⟨Rsum, hR⟩ :=
    Fiber.hasSum_fintype (L.obj d) (hL.has_sum_add d) R
  let f : DegreePartition k → Superoperator n d := fun part =>
    bangAmbientCPRowSplit A k n part x
  obtain ⟨z, hz⟩ :=
    hL.has_act_sum_from_dim.act_sum_from_dim (m := n) (d := d) (x := R)
      (s := Rsum) f hR
  refine ⟨z, ?_⟩
  have hfam :
      (fun part : DegreePartition k =>
          DayCoend.evaluate L β
            (bangComultComponentFamily A n x
              (degreePartitionToPair k part))) =
        fun part => L.act (R part) (f part) := by
    funext part
    change
        DayCoend.evaluate L β
            ((bangComultComponent A part.val (k - part.val)).app n x) =
          L.act (R part) (f part)
    simpa [R, f] using
      bangComultComponent_evaluate_partition A k n part x L β
  exact hfam ▸ hz

theorem bangComultAmbientCP_degree_row_admissible_two :
    BangComultAmbientCPDegreeRowAdmissible 2 :=
  bangComultAmbientCP_degree_row_hasSum 2

/-- Absolute Day admissibility at `A = 2` is not obtained from ambient-CP
relative data: absolute quantifies over every module target, including
non-`HasSumAdd` fibers that can host a Day-transfer witness. -/
theorem day_bang_l9_absolute_bangComult_two_not_claimed :
    (BangComultDayTransferWitness →
      ¬ BangComultComponentsAdmissible 2) ∧
      (∀ A, BangComultComponentsAdmissible A →
        BangComultAmbientCPAdmissible A) :=
  ⟨bangComultDayTransferWitness_not_admissible,
    bangComultAmbientCPAdmissible_of_components⟩

/-- Low-dimensional absolute bang comonoids remain available. -/
theorem bangComonoid_nonempty_of_le_one (A : ℕ) (hA : A ≤ 1) :
    Nonempty Comonoid :=
  ⟨bangComonoid A hA⟩

end QLambda.Domain.Presheaf.SuperoperatorModule
