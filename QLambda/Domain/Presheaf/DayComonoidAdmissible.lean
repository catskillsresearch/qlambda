/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.DayComonoidRouteA

/-!
# Bang comult admissibility for `A ≤ 1`
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

set_option maxHeartbeats 8000000

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-- Yoneda unit at homogeneous degree `k`, injected into the series. -/
noncomputable def bangDegreeUnit (A k : ℕ) :
    ((bang A).obj (tensorPowerDimension A k)).Carrier :=
  (representableToBang A k).app (tensorPowerDimension A k)
    (Superoperator.identity (tensorPowerDimension A k))

/-- Unfolding of `bangSplitToRepDay` on a representable element. -/
theorem bangSplitToRepDay_app (A p q n : ℕ)
    (Φ : ((representable
        (tensorPowerDimension A p * tensorPowerDimension A q)).obj n).Carrier) :
    (bangSplitToRepDay A p q).app n Φ =
      (dayTensor
          (representable (tensorPowerDimension A p))
          (representable (tensorPowerDimension A q))).act
        ((DayCoend.intro
            (representable (tensorPowerDimension A p))
            (representable (tensorPowerDimension A q))).app
          (Superoperator.identity (tensorPowerDimension A p)
            : ((representable (tensorPowerDimension A p)).obj
                (tensorPowerDimension A p)).Carrier)
          (Superoperator.identity (tensorPowerDimension A q)
            : ((representable (tensorPowerDimension A q)).obj
                (tensorPowerDimension A q)).Carrier))
        Φ :=
  rfl

/-- Evaluation of a Day comultiplication component: the series Day map of the
Yoneda coend unit, acted by the contraction split. -/
theorem bangComultComponent_evaluate (A p q n : ℕ)
    (x : ((bang A).obj n).Carrier)
    (L : Module) (β : Bilinear (bang A) (bang A) L) :
    DayCoend.evaluate L β ((bangComultComponent A p q).app n x) =
      L.act
        (β.app (bangDegreeUnit A p) (bangDegreeUnit A q))
        ((bangSplitComponent A p q).app n x) := by
  let idp : ((representable (tensorPowerDimension A p)).obj
      (tensorPowerDimension A p)).Carrier :=
    Superoperator.identity (tensorPowerDimension A p)
  let idq : ((representable (tensorPowerDimension A q)).obj
      (tensorPowerDimension A q)).Carrier :=
    Superoperator.identity (tensorPowerDimension A q)
  let Φ : Superoperator n
      (tensorPowerDimension A p * tensorPowerDimension A q) :=
    (bangSplitComponent A p q).app n x
  let gen :=
    (DayCoend.intro
        (representable (tensorPowerDimension A p))
        (representable (tensorPowerDimension A q))).app idp idq
  -- `bangComultComponent = map ∘ splitToRepDay ∘ split`.
  change
      (DayCoend.lift β).app n
          ((DayTensor.map
              (representableToBang A p) (representableToBang A q)).app n
            ((bangSplitToRepDay A p q).app n Φ)) =
        L.act (β.app (bangDegreeUnit A p) (bangDegreeUnit A q)) Φ
  have hsplit :
      (bangSplitToRepDay A p q).app n Φ =
        (dayTensor
            (representable (tensorPowerDimension A p))
            (representable (tensorPowerDimension A q))).act gen Φ :=
    bangSplitToRepDay_app A p q n Φ
  rw [hsplit]
  -- Push the Day bifunctor through the Yoneda action.
  rw [(DayTensor.map (representableToBang A p)
      (representableToBang A q)).naturality gen Φ]
  -- Push `lift β` through the series Day action.
  rw [(DayCoend.lift β).naturality _ Φ]
  -- Reduce the mapped generator.
  have hintro :
      (DayTensor.map
          (representableToBang A p) (representableToBang A q)).app
          (tensorPowerDimension A p * tensorPowerDimension A q) gen =
        (DayCoend.intro (bang A) (bang A)).app
          (bangDegreeUnit A p) (bangDegreeUnit A q) := by
    unfold gen idp idq bangDegreeUnit representableToBang
    exact DayTensor.map_intro
      (representableToBang A p) (representableToBang A q)
      (Superoperator.identity (tensorPowerDimension A p))
      (Superoperator.identity (tensorPowerDimension A q))
  rw [hintro]
  -- `lift.app (intro x y) = β.app x y` after `act_id`.
  change
      L.act
          (DayCoend.evaluate L β
            ((DayCoend.intro (bang A) (bang A)).app
              (bangDegreeUnit A p) (bangDegreeUnit A q)))
          Φ =
        L.act (β.app (bangDegreeUnit A p) (bangDegreeUnit A q)) Φ
  rw [DayCoend.evaluate_intro]

/-- Off-degree injections are annihilated by a fixed split component. -/
theorem bangComultComponent_comp_injection_eq_zero (A p q k n : ℕ)
    (hk : k ≠ p + q)
    (y : ((symmetricPower A k).obj n).Carrier) :
    (bangComultComponent A p q).app n
        ((bangInjection A k).app n y) = 0 := by
  have hsplit :
      (bangSplitComponent A p q).app n
          ((bangInjection A k).app n y) = 0 := by
    change
        Superoperator.comp
          (Superoperator.ofEquivalence (tensorSplitEquiv A p q))
          ((((countableProductInjection
              (fun j => symmetricPower A j) k).app n y)
            (p + q)).val) =
          0
    have hz :
        ((countableProductInjection
            (fun j => symmetricPower A j) k).app n y) (p + q) =
          (0 : SymmetricElement A (p + q) n) := by
      change (if h : p + q = k then h.symm ▸ y else 0) =
        (0 : SymmetricElement A (p + q) n)
      simp [Ne.symm hk]
    rw [hz, SymmetricElement.zero_val, Superoperator.comp_zero_right]
  change
      (bangRepDayToSeriesDay A p q).app n
          ((bangSplitToRepDay A p q).app n
            ((bangSplitComponent A p q).app n
              ((bangInjection A k).app n y))) =
        0
  rw [hsplit, (bangSplitToRepDay A p q).map_zero,
    (bangRepDayToSeriesDay A p q).map_zero]

/-- A comultiplication component depends only on the homogeneous
coefficient of total degree `p + q`. -/
theorem bangComultComponent_eq_of_injection (A p q n : ℕ)
    (x : ((bang A).obj n).Carrier) :
    (bangComultComponent A p q).app n x =
      (bangComultComponent A p q).app n
        ((bangInjection A (p + q)).app n (x (p + q))) := by
  have hx :=
    (bangComultComponent A p q).map_sum
      (countableProduct_hasSum_coordinates
        (fun j => symmetricPower A j) n x)
  have hsupp :
      ∀ k, k ≠ p + q →
        (bangComultComponent A p q).app n
            ((bangInjection A k).app n (x k)) = 0 :=
    fun k hk => bangComultComponent_comp_injection_eq_zero A p q k n hk _
  have hfam :
      (fun k =>
          (bangComultComponent A p q).app n
            ((bangInjection A k).app n (x k))) =
        fun k =>
          if k = p + q then
            (bangComultComponent A p q).app n
              ((bangInjection A (p + q)).app n (x (p + q)))
          else 0 := by
    funext k
    by_cases hk : k = p + q
    · subst hk; simp
    · rw [hsupp k hk, if_neg hk]
  have hx' :
      ((dayTensor (bang A) (bang A)).obj n).HasSum
        (fun k =>
          if k = p + q then
            (bangComultComponent A p q).app n
              ((bangInjection A (p + q)).app n (x (p + q)))
          else 0)
        ((bangComultComponent A p q).app n x) := by
    convert hx using 1
    exact hfam.symm
  have hsingle :=
    Fiber.hasSum_singleCoordinate
      ((dayTensor (bang A) (bang A)).obj n) (p + q)
      ((bangComultComponent A p q).app n
        ((bangInjection A (p + q)).app n (x (p + q))))
  exact ((dayTensor (bang A) (bang A)).obj n).summation.unique
    hx' hsingle

/-- For `A = 1` every tensor-power dimension is `1`. -/
theorem tensorPowerDimension_one_eq (k : ℕ) :
    tensorPowerDimension 1 k = 1 := by
  simp [tensorPowerDimension_eq_pow, one_pow]

/-- Cast of an `A = 1` homogeneous coefficient to fiber dimension `1`. -/
noncomputable def bangOneCoeff (n k : ℕ)
    (x : SymmetricElement 1 k n) : Superoperator n 1 :=
  (tensorPowerDimension_one_eq k) ▸ x.val

/-- The `A = 1` series with identity in every homogeneous degree (fiber `1`). -/
noncomputable def bangOneDegreeUnits :
    ((bang 1).obj 1).Carrier :=
  fun k =>
    (symmetricPowerProjection 1 k).app 1 <|
      show Superoperator 1 (tensorPowerDimension 1 k) from
        cast (congrArg (Superoperator 1) (tensorPowerDimension_one_eq k).symm)
          (Superoperator.identity 1)

/-- Degree-`k` unit, injected into the common fiber `1`. -/
noncomputable def bangDegreeUnitOne (k : ℕ) :
    ((bang 1).obj 1).Carrier :=
  (bangInjection 1 k).app 1 (bangOneDegreeUnits k)

theorem bangDegreeUnitOne_hasSum :
    ((bang 1).obj 1).HasSum bangDegreeUnitOne bangOneDegreeUnits :=
  countableProduct_hasSum_coordinates
    (fun j => symmetricPower 1 j) 1 bangOneDegreeUnits

/-- Rectangle summability of `β` on the `A = 1` degree-unit series. -/
theorem bangOne_degreeUnit_rectangle_hasSum
    (L : Module.{0}) (β : Bilinear (bang 1) (bang 1) L) :
    (L.obj (1 * 1)).HasSum
      (fun pq : ℕ × ℕ =>
        β.app (bangDegreeUnitOne pq.1) (bangDegreeUnitOne pq.2))
      (β.app bangOneDegreeUnits bangOneDegreeUnits) := by
  have hU := bangDegreeUnitOne_hasSum
  have hrows (p : ℕ) :
      (L.obj (1 * 1)).HasSum
        (fun q : ℕ => β.app (bangDegreeUnitOne p) (bangDegreeUnitOne q))
        (β.app (bangDegreeUnitOne p) bangOneDegreeUnits) :=
    β.map_sum_right (bangDegreeUnitOne p) hU
  have hcol :
      (L.obj (1 * 1)).HasSum
        (fun p : ℕ => β.app (bangDegreeUnitOne p) bangOneDegreeUnits)
        (β.app bangOneDegreeUnits bangOneDegreeUnits) :=
    β.map_sum_left bangOneDegreeUnits hU
  have hflat :=
    ((L.obj (1 * 1)).summation.flatten
      (fun p q => β.app (bangDegreeUnitOne p) (bangDegreeUnitOne q))
      (β.app bangOneDegreeUnits bangOneDegreeUnits)).mpr
        ⟨fun p => β.app (bangDegreeUnitOne p) bangOneDegreeUnits,
          hrows, hcol⟩
  exact
    ((L.obj (1 * 1)).summation.reindex (Equiv.sigmaEquivProd ℕ ℕ)
      (fun pq : ℕ × ℕ =>
        β.app (bangDegreeUnitOne pq.1) (bangDegreeUnitOne pq.2))
      (β.app bangOneDegreeUnits bangOneDegreeUnits)).mp hflat

/-- Outer series gate for assembling `A = 1` admissibility from homogeneous
diagonal rows: joint `L.act d_k Φ_k` with summable `(d_k)`. -/
def BangComultSeriesActHasSum : Prop :=
  ∀ (n : ℕ) (x : ((bang 1).obj n).Carrier)
    (L : Module.{0}) (d : ℕ → (L.obj 1).Carrier) (D : (L.obj 1).Carrier),
    (L.obj 1).HasSum d D →
      ∃ z : (L.obj n).Carrier,
        (L.obj n).HasSum (fun k => L.act (d k) (bangOneCoeff n k (x k))) z

/-- The outer series gate is `Module.act_sum_from_one` (fiber `1 = 1 * 1`). -/
theorem bangComultSeriesActHasSum_holds : BangComultSeriesActHasSum := by
  intro n x L d D hD
  exact L.act_sum_from_one (fun k => bangOneCoeff n k (x k)) hD

/-- Identity cast along a dimension equality as a basis equivalence. -/
theorem cast_identity_eq_ofEquivalence {a b : ℕ} (h : a = b) :
    cast (congrArg (Superoperator a) h) (Superoperator.identity a) =
      Superoperator.ofEquivalence (finCongr h) := by
  cases h
  exact (Superoperator.ofEquivalence_refl a).symm

/-- `A = 1` Yoneda degree unit is the fiber-`1` unit acted by the dimension cast. -/
theorem bangDegreeUnit_eq_act (k : ℕ) :
    bangDegreeUnit 1 k =
      (bang 1).act (bangDegreeUnitOne k)
        (Superoperator.ofEquivalence
          (finCongr (tensorPowerDimension_one_eq k))) := by
  let h := tensorPowerDimension_one_eq k
  change
    (bangInjection 1 k).app (tensorPowerDimension 1 k)
        ((symmetricPowerProjection 1 k).app (tensorPowerDimension 1 k)
          (Superoperator.identity (tensorPowerDimension 1 k))) =
      (bang 1).act
        ((bangInjection 1 k).app 1 (bangOneDegreeUnits k))
        (Superoperator.ofEquivalence (finCongr h))
  have hn :=
    (bangInjection 1 k).naturality (bangOneDegreeUnits k)
      (Superoperator.ofEquivalence (finCongr h))
  refine Eq.trans ?_ hn
  congr 1
  change
    (symmetricPowerProjection 1 k).app (tensorPowerDimension 1 k)
        (Superoperator.identity (tensorPowerDimension 1 k)) =
      (symmetricPower 1 k).act
        ((symmetricPowerProjection 1 k).app 1
          (cast (congrArg (Superoperator 1) h.symm)
            (Superoperator.identity 1)))
        (Superoperator.ofEquivalence (finCongr h))
  have hp :=
    (symmetricPowerProjection 1 k).naturality
      (cast (congrArg (Superoperator 1) h.symm)
        (Superoperator.identity 1))
      (Superoperator.ofEquivalence (finCongr h))
  refine Eq.trans ?_ hp
  congr 1
  show Superoperator.identity (tensorPowerDimension 1 k) =
    Superoperator.comp
      (cast (congrArg (Superoperator 1) h.symm) (Superoperator.identity 1))
      (Superoperator.ofEquivalence (finCongr h))
  rw [cast_identity_eq_ofEquivalence h.symm, Superoperator.ofEquivalence_comp]
  have : (finCongr h).trans (finCongr h.symm) = Equiv.refl _ := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    simp
  rw [this, Superoperator.ofEquivalence_refl]

/-- Split channel for `A = 1`, after tensoring dimension casts, equals `bangOneCoeff`. -/
theorem bangSplit_tensor_cast_eq_oneCoeff (p q n : ℕ)
    (x : ((bang 1).obj n).Carrier) :
    Superoperator.comp
      (Superoperator.tensor
        (Superoperator.ofEquivalence (finCongr (tensorPowerDimension_one_eq p)))
        (Superoperator.ofEquivalence (finCongr (tensorPowerDimension_one_eq q))))
      ((bangSplitComponent 1 p q).app n x) =
      bangOneCoeff n (p + q) (x (p + q)) := by
  simp only [bangSplitComponent, bangOneCoeff]
  rw [Superoperator.comp_assoc]
  let hp := tensorPowerDimension_one_eq p
  let hq := tensorPowerDimension_one_eq q
  let hk := tensorPowerDimension_one_eq (p + q)
  have htarget :
      Superoperator.comp
          (Superoperator.tensor
            (Superoperator.ofEquivalence (finCongr hp))
            (Superoperator.ofEquivalence (finCongr hq)))
          (Superoperator.ofEquivalence (tensorSplitEquiv 1 p q)) =
        Superoperator.ofEquivalence (finCongr hk) := by
    rw [Superoperator.tensor_ofEquivalence, Superoperator.ofEquivalence_comp]
    congr 1
    apply Equiv.ext
    intro i
    apply Fin.ext
    have hL :
        ((((tensorSplitEquiv 1 p q).trans
          (Superoperator.tensorEquiv (finCongr hp) (finCongr hq))) i :
            Fin (1 * 1)) : ℕ) = 0 :=
      fin_val_eq_zero_of_card_one (by rfl) _
    have hR : (((finCongr hk) i : Fin 1) : ℕ) = 0 :=
      fin_val_eq_zero_of_card_one rfl _
    exact hL.trans hR.symm
  have hΦ :=
    congrArg (fun Φ => Superoperator.comp Φ (x (p + q)).val) htarget
  exact hΦ.trans (Superoperator.comp_ofEquivalence_finCongr hk (x (p + q)).val)

/-- Equivalence between pairs and ordered partitions of their total degree. -/
def degreePartitionEquiv : ℕ × ℕ ≃ (Σ t : ℕ, DegreePartition t) where
  toFun := pairToDegreePartition
  invFun := fun p => degreePartitionToPair p.1 p.2
  left_inv := pairToDegreePartition_toPair
  right_inv := by
    rintro ⟨t, part⟩
    dsimp [pairToDegreePartition, degreePartitionToPair]
    have hs : part.val + (t - part.val) = t :=
      Nat.add_sub_of_le (Nat.le_of_lt_succ part.isLt)
    refine Sigma.ext hs ?_
    let lhs : Fin (part.val + (t - part.val) + 1) :=
      ⟨part.val, Nat.lt_succ_of_le (Nat.le_add_right _ _)⟩
    let hs' : part.val + (t - part.val) + 1 = t + 1 :=
      congrArg (· + 1) hs
    have hEq : Fin.cast hs' lhs = part := by
      apply Fin.ext
      exact Fin.val_cast hs' lhs
    refine HEq.trans (b := Fin.cast hs' lhs) ?_ (heq_of_eq hEq)
    have hfun : (Fin.cast hs' : Fin _ → Fin _) =
        cast (congrArg Fin hs') :=
      Fin.cast_eq_cast hs'
    show lhs ≍ Fin.cast hs' lhs
    rw [show Fin.cast hs' lhs = cast (congrArg Fin hs') lhs from
      congrFun hfun lhs]
    exact (cast_heq (congrArg Fin hs') lhs).symm

/-- Homogeneous `A = 1` family vanishes off the diagonal `p + q = k`. -/
theorem bangComultComponent_evaluate_injection_eq_zero
    (p q k n : ℕ) (hk : k ≠ p + q)
    (y : ((symmetricPower 1 k).obj n).Carrier)
    (L : Module) (β : Bilinear (bang 1) (bang 1) L) :
    DayCoend.evaluate L β
        ((bangComultComponent 1 p q).app n
          ((bangInjection 1 k).app n y)) =
      0 := by
  rw [bangComultComponent_comp_injection_eq_zero 1 p q k n hk y]
  exact DayCoend.evaluate_zero β

/-- Evaluation at `A = 1`: Day component equals rectangle coefficient acted by
the total-degree series channel. -/
theorem bangComultComponent_evaluate_one (p q n : ℕ)
    (x : ((bang 1).obj n).Carrier)
    (L : Module) (β : Bilinear (bang 1) (bang 1) L) :
    DayCoend.evaluate L β ((bangComultComponent 1 p q).app n x) =
      L.act (β.app (bangDegreeUnitOne p) (bangDegreeUnitOne q))
        (bangOneCoeff n (p + q) (x (p + q))) := by
  have he := bangComultComponent_evaluate 1 p q n x L β
  rw [he, bangDegreeUnit_eq_act p, bangDegreeUnit_eq_act q, β.naturality]
  have hact := L.act_comp
    (β.app (bangDegreeUnitOne p) (bangDegreeUnitOne q))
    (Superoperator.tensor
      (Superoperator.ofEquivalence (finCongr (tensorPowerDimension_one_eq p)))
      (Superoperator.ofEquivalence (finCongr (tensorPowerDimension_one_eq q))))
    ((bangSplitComponent 1 p q).app n x)
  rw [hact, bangSplit_tensor_cast_eq_oneCoeff]

/-- Mixed-partition admissibility for `A = 1`. -/
theorem bangComultComponentsAdmissible_one :
    BangComultComponentsAdmissible 1 := by
  intro n x L β
  have hrect := bangOne_degreeUnit_rectangle_hasSum L β
  have hre :
      (L.obj (1 * 1)).HasSum
        (fun p : Σ t : ℕ, DegreePartition t =>
          β.app (bangDegreeUnitOne (degreePartitionToPair p.1 p.2).1)
            (bangDegreeUnitOne (degreePartitionToPair p.1 p.2).2))
        (β.app bangOneDegreeUnits bangOneDegreeUnits) :=
    ((L.obj (1 * 1)).summation.reindex degreePartitionEquiv.symm
      (fun pq =>
        β.app (bangDegreeUnitOne pq.1) (bangDegreeUnitOne pq.2))
      (β.app bangOneDegreeUnits bangOneDegreeUnits)).mpr hrect
  obtain ⟨row, hrows, hrowSum⟩ :=
    ((L.obj (1 * 1)).summation.flatten
      (fun t (part : DegreePartition t) =>
        β.app (bangDegreeUnitOne (degreePartitionToPair t part).1)
          (bangDegreeUnitOne (degreePartitionToPair t part).2))
      (β.app bangOneDegreeUnits bangOneDegreeUnits)).mp hre
  obtain ⟨Z, hZ⟩ :=
    bangComultSeriesActHasSum_holds n x L
      (fun k => row k) (β.app bangOneDegreeUnits bangOneDegreeUnits) hrowSum
  refine ⟨Z, ?_⟩
  have hfam :
      (fun pq : ℕ × ℕ =>
          DayCoend.evaluate L β (bangComultComponentFamily 1 n x pq)) =
        fun pq : ℕ × ℕ =>
          L.act (β.app (bangDegreeUnitOne pq.1) (bangDegreeUnitOne pq.2))
            (bangOneCoeff n (pq.1 + pq.2) (x (pq.1 + pq.2))) := by
    funext pq
    simpa [bangComultComponentFamily] using
      bangComultComponent_evaluate_one pq.1 pq.2 n x L β
  rw [hfam]
  have hflat :
      (L.obj n).HasSum
        (fun p : Σ t : ℕ, DegreePartition t =>
          L.act
            (β.app (bangDegreeUnitOne (degreePartitionToPair p.1 p.2).1)
              (bangDegreeUnitOne (degreePartitionToPair p.1 p.2).2))
            (bangOneCoeff n p.1 (x p.1)))
        Z :=
    ((L.obj n).summation.flatten
        (fun t (part : DegreePartition t) =>
          L.act
            (β.app (bangDegreeUnitOne (degreePartitionToPair t part).1)
              (bangDegreeUnitOne (degreePartitionToPair t part).2))
            (bangOneCoeff n t (x t)))
        Z).mpr
      ⟨fun t => L.act (row t) (bangOneCoeff n t (x t)),
        fun t => L.act_sum_element (bangOneCoeff n t (x t)) (hrows t),
        hZ⟩
  have hflat' :
      (L.obj n).HasSum
        (fun p : Σ t : ℕ, DegreePartition t =>
          L.act
            (β.app (bangDegreeUnitOne (degreePartitionToPair p.1 p.2).1)
              (bangDegreeUnitOne (degreePartitionToPair p.1 p.2).2))
            (bangOneCoeff n
              ((degreePartitionToPair p.1 p.2).1 +
                (degreePartitionToPair p.1 p.2).2)
              (x
                ((degreePartitionToPair p.1 p.2).1 +
                  (degreePartitionToPair p.1 p.2).2))))
        Z := by
    convert hflat using 1
    funext p
    rw [degreePartitionToPair_snd_add]
  exact
    ((L.obj n).summation.reindex degreePartitionEquiv.symm
      (fun pq =>
        L.act (β.app (bangDegreeUnitOne pq.1) (bangDegreeUnitOne pq.2))
          (bangOneCoeff n (pq.1 + pq.2) (x (pq.1 + pq.2))))
      Z).mp hflat'

/-- Unconditional Day comultiplication for the one-dimensional exponential. -/
noncomputable def bangComult_one :
    Hom (bang 1) (dayTensor (bang 1) (bang 1)) :=
  bangComult 1 bangComultComponentsAdmissible_one

/-! ## Special case `A = 0`: only degree 0 survives -/

/-- There is a unique superoperator into the zero-dimensional system. -/
theorem superoperator_outDim_zero {n : ℕ} (Φ : Superoperator n 0) :
    Φ = 0 := by
  apply Superoperator.ext
  apply CPMap.ext
  ext a b
  exact isEmptyElim a.1

/-- For `A = 0`, every positive symmetric degree is the zero channel. -/
theorem bang_zero_high_degree (n k : ℕ) (hk : 0 < k)
    (x : ((bang 0).obj n).Carrier) :
    (x k).val = 0 := by
  cases k with
  | zero => exact (lt_irrefl _ hk).elim
  | succ k =>
    have hdim : tensorPowerDimension 0 (k + 1) = 0 := by
      simp [tensorPowerDimension]
    apply Superoperator.ext
    apply CPMap.ext
    ext a b
    have : IsEmpty (Fin (tensorPowerDimension 0 (k + 1))) := by
      rw [hdim]; infer_instance
    exact isEmptyElim a.1

/-- Homogeneous Day components vanish off the `(0,0)` slot when `A = 0`. -/
theorem bangComultComponentFamily_zero_of_pos_degree
    (n : ℕ) (x : ((bang 0).obj n).Carrier) (pq : ℕ × ℕ)
    (hpq : pq ≠ (0, 0)) :
    bangComultComponentFamily 0 n x pq = 0 := by
  have hpos : 0 < pq.1 + pq.2 := by
    rcases pq with ⟨p, q⟩
    change (p, q) ≠ (0, 0) at hpq
    cases p with
    | zero =>
      cases q with
      | zero => exact (hpq rfl).elim
      | succ q => exact Nat.succ_pos _
    | succ p => exact Nat.add_pos_left (Nat.succ_pos _) _
  have hsplit :
      (bangSplitComponent 0 pq.1 pq.2).app n x = 0 := by
    change
        Superoperator.comp
          (Superoperator.ofEquivalence
            (tensorSplitEquiv 0 pq.1 pq.2))
          (x (pq.1 + pq.2)).val =
          0
    rw [bang_zero_high_degree n (pq.1 + pq.2) hpos x]
    exact Superoperator.comp_zero_right _
  change
      (bangComultComponent 0 pq.1 pq.2).app n x = 0
  simp only [bangComultComponent, Hom.comp_app]
  rw [hsplit, (bangSplitToRepDay 0 pq.1 pq.2).map_zero,
    (bangRepDayToSeriesDay 0 pq.1 pq.2).map_zero]

/-- Mixed-partition admissibility holds for `A = 0`: only the `(0,0)`
component can be nonzero, so the Day family is a singleton sum. -/
theorem bangComultComponentsAdmissible_zero :
    BangComultComponentsAdmissible 0 := by
  intro n x L β
  refine
    ⟨DayCoend.evaluate L β (bangComultComponentFamily 0 n x (0, 0)), ?_⟩
  have hfam :
      (fun pq : ℕ × ℕ =>
          DayCoend.evaluate L β (bangComultComponentFamily 0 n x pq)) =
        fun pq : ℕ × ℕ =>
          if pq = (0, 0) then
            DayCoend.evaluate L β (bangComultComponentFamily 0 n x (0, 0))
          else 0 := by
    funext pq
    by_cases hpq : pq = (0, 0)
    · subst hpq; simp
    · rw [bangComultComponentFamily_zero_of_pos_degree n x pq hpq,
        if_neg hpq]
      exact DayCoend.evaluate_zero β
  rw [hfam]
  exact Fiber.hasSum_singleAt (L.obj n) (0, 0)
    (DayCoend.evaluate L β (bangComultComponentFamily 0 n x (0, 0)))

/-- Unconditional Day comultiplication for the zero-dimensional exponential. -/
noncomputable def bangComult_zero :
    Hom (bang 0) (dayTensor (bang 0) (bang 0)) :=
  bangComult 0 bangComultComponentsAdmissible_zero

/-- For `A = 0` the Day comultiplication is exactly the `(0,0)` homogeneous
component (singleton coend sum). -/
theorem bangComult_zero_eq_component (n : ℕ)
    (x : ((bang 0).obj n).Carrier) :
    bangComult_zero.app n x =
      (bangComultComponent 0 0 0).app n x := by
  have hsum :
      DayCoend.HasSum (bangComultComponentFamily 0 n x)
        ((bangComultComponent 0 0 0).app n x) := by
    intro L β
    have hfam :
        (fun pq : ℕ × ℕ =>
            DayCoend.evaluate L β (bangComultComponentFamily 0 n x pq)) =
          fun pq : ℕ × ℕ =>
            if pq = (0, 0) then
              DayCoend.evaluate L β
                ((bangComultComponent 0 0 0).app n x)
            else 0 := by
      funext pq
      by_cases hpq : pq = (0, 0)
      · subst hpq; rfl
      · rw [bangComultComponentFamily_zero_of_pos_degree n x pq hpq,
          if_neg hpq]
        exact DayCoend.evaluate_zero β
    rw [hfam]
    exact Fiber.hasSum_singleAt (L.obj n) (0, 0) _
  exact ((dayTensor (bang 0) (bang 0)).obj n).summation.unique
    (bangComultApp_hasSum 0 bangComultComponentsAdmissible_zero n x) hsum


/-- Admissibility for the two fibers where the acted outer series lands in
fiber `1` (so `Module.act_sum_from_one` applies). -/
theorem bangComultComponentsAdmissible_of_le_one (A : ℕ) (hA : A ≤ 1) :
    BangComultComponentsAdmissible A := by
  interval_cases A
  · exact bangComultComponentsAdmissible_zero
  · exact bangComultComponentsAdmissible_one

/-- Unconditional Day comultiplication when `A ≤ 1`. -/
noncomputable def bangComult_of_le_one (A : ℕ) (hA : A ≤ 1) :
    Hom (bang A) (dayTensor (bang A) (bang A)) :=
  bangComult A (bangComultComponentsAdmissible_of_le_one A hA)

/-! ## Day factorization of contraction for `A ≤ 1` -/

/-- For `A = 1`, every tensor-factor permutation is the identity equivalence. -/
theorem factorPermutationEquiv_one (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    factorPermutationEquiv 1 k σ = Equiv.refl _ := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  have hd := tensorPowerDimension_one_eq k
  exact (fin_val_eq_zero_of_card_one hd _).trans
    (fin_val_eq_zero_of_card_one hd _).symm

/-- For `A = 1`, every tensor-factor permutation channel is the identity. -/
theorem factorPermutation_one (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    factorPermutation 1 k σ =
      Superoperator.identity (tensorPowerDimension 1 k) := by
  change Superoperator.ofEquivalence (factorPermutationEquiv 1 k σ) = _
  rw [factorPermutationEquiv_one, Superoperator.ofEquivalence_refl]

/-- Symmetric averaging is trivial on one-dimensional tensor powers. -/
theorem symmetricAverage_one (k : ℕ) :
    symmetricAverage 1 k =
      Superoperator.identity (tensorPowerDimension 1 k) := by
  apply Superoperator.ext
  apply CPMap.ext_apply
  intro ρ
  rw [symmetricAverage_applyMat]
  simp_rw [factorPermutation_one]
  have hid :
      (Superoperator.identity (tensorPowerDimension 1 k)).cp.applyMat ρ = ρ := by
    change (CPMap.identity _).applyMat ρ = ρ
    exact CPMap.applyMat_identity ρ
  simp_rw [hid]
  rw [Finset.sum_const]
  have hcard :
      (Finset.univ : Finset (Equiv.Perm (Fin k))).card = Nat.factorial k := by
    simp [Fintype.card_perm]
  rw [hcard, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hk : ((Nat.factorial k : ℝ)⁻¹ : ℂ) * (Nat.factorial k : ℂ) = 1 := by
    rw [← Complex.ofReal_natCast (Nat.factorial k), ← Complex.ofReal_inv,
      ← Complex.ofReal_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)),
      Complex.ofReal_one]
  rw [hk, one_smul]

/-- Symmetric averaging is trivial on the unique degree-zero zero-dimensional
fiber. -/
theorem symmetricAverage_zero_zero :
    symmetricAverage 0 0 = Superoperator.identity (tensorPowerDimension 0 0) := by
  have hdim : tensorPowerDimension 0 0 = 1 := by simp [tensorPowerDimension]
  apply Superoperator.ext
  apply CPMap.ext_apply
  intro ρ
  rw [symmetricAverage_applyMat]
  have hperm (σ : Equiv.Perm (Fin 0)) :
      factorPermutation 0 0 σ =
        Superoperator.identity (tensorPowerDimension 0 0) := by
    change Superoperator.ofEquivalence (factorPermutationEquiv 0 0 σ) = _
    have : factorPermutationEquiv 0 0 σ = Equiv.refl _ := by
      apply Equiv.ext
      intro i
      apply Fin.ext
      exact (fin_val_eq_zero_of_card_one hdim _).trans
        (fin_val_eq_zero_of_card_one hdim _).symm
    rw [this, Superoperator.ofEquivalence_refl]
  simp_rw [hperm]
  have hid :
      (Superoperator.identity (tensorPowerDimension 0 0)).cp.applyMat ρ = ρ := by
    change (CPMap.identity _).applyMat ρ = ρ
    exact CPMap.applyMat_identity ρ
  simp_rw [hid]
  rw [Finset.sum_const]
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin 0))).card = 1 := by decide
  rw [hcard, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num

/-- For `A ≤ 1`, symmetric averaging coincides with the identity channel. -/
theorem symmetricAverage_of_le_one (A k : ℕ) (hA : A ≤ 1) :
    symmetricAverage A k =
      Superoperator.identity (tensorPowerDimension A k) := by
  interval_cases A
  · cases k with
    | zero => exact symmetricAverage_zero_zero
    | succ k =>
      apply Superoperator.ext
      apply CPMap.ext
      ext a b
      have : IsEmpty (Fin (tensorPowerDimension 0 (k + 1))) := by
        simp [tensorPowerDimension]; infer_instance
      exact isEmptyElim a.1
  · exact symmetricAverage_one k

/-- Coordinate form of the Yoneda degree unit in the series. -/
theorem bangDegreeUnit_apply (A k j : ℕ) :
    bangDegreeUnit A k j =
      if h : j = k then
        h.symm ▸
          (symmetricPowerProjection A k).app
            (tensorPowerDimension A k)
            (Superoperator.identity (tensorPowerDimension A k))
      else 0 :=
  rfl

/-- Diagonal slot of a square injection recovers the injected channel. -/
theorem injection_square_eq_slot (A p q n : ℕ)
    (Φ : Superoperator n
      (tensorPowerDimension A p * tensorPowerDimension A q)) :
    (countableRepresentableDayTensorInjection
        (tensorPowerDimension A) (tensorPowerDimension A) p q).app n Φ p q =
      Φ := by
  dsimp [countableRepresentableDayTensorInjection, Hom.comp,
    countableProductInjection]
  simp only [↓reduceDIte]

/-- Off-row slots of a square injection vanish. -/
theorem injection_square_eq_zero_left (A p q n i j : ℕ) (hi : i ≠ p)
    (Φ : Superoperator n
      (tensorPowerDimension A p * tensorPowerDimension A q)) :
    (countableRepresentableDayTensorInjection
        (tensorPowerDimension A) (tensorPowerDimension A) p q).app n Φ i j =
      0 := by
  dsimp [countableRepresentableDayTensorInjection, Hom.comp,
    countableProductInjection]
  simp only [hi, ↓reduceDIte]
  rfl

/-- Off-column slots of a square injection vanish. -/
theorem injection_square_eq_zero_right (A p q n j : ℕ) (hj : j ≠ q)
    (Φ : Superoperator n
      (tensorPowerDimension A p * tensorPowerDimension A q)) :
    (countableRepresentableDayTensorInjection
        (tensorPowerDimension A) (tensorPowerDimension A) p q).app n Φ p j =
      0 := by
  dsimp [countableRepresentableDayTensorInjection, Hom.comp,
    countableProductInjection]
  simp only [↓reduceDIte, hj]
  rfl

/-- For `A ≤ 1`, Day compare on a homogeneous comult component is the
corresponding square injection of the contraction slot. -/
theorem compare_bangComultComponent_of_le_one (A : ℕ) (hA : A ≤ 1)
    (p q n : ℕ) (x : ((bang A).obj n).Carrier) :
    (symmetricSeriesDayCompare A).app n
        ((bangComultComponent A p q).app n x) =
      (countableRepresentableDayTensorInjection
          (tensorPowerDimension A) (tensorPowerDimension A) p q).app n
        ((bangSplitComponent A p q).app n x) := by
  have he :=
    bangComultComponent_evaluate A p q n x
      (symmetricFormalTensorSquare A) (symmetricSeriesDayBilinear A)
  have he' :
      (symmetricSeriesDayCompare A).app n
          ((bangComultComponent A p q).app n x) =
        (symmetricFormalTensorSquare A).act
          ((symmetricSeriesDayBilinear A).app
            (bangDegreeUnit A p) (bangDegreeUnit A q))
          ((bangSplitComponent A p q).app n x) := by
    simpa [symmetricSeriesDayCompare, DayCoend.lift] using he
  rw [he']
  funext i j
  change
      Superoperator.comp
          (Superoperator.tensor
            (bangDegreeUnit A p i).val
            (bangDegreeUnit A q j).val)
          ((bangSplitComponent A p q).app n x) =
        (countableRepresentableDayTensorInjection
            (tensorPowerDimension A) (tensorPowerDimension A) p q).app n
          ((bangSplitComponent A p q).app n x) i j
  let Φ : Superoperator n
      (tensorPowerDimension A p * tensorPowerDimension A q) :=
    (bangSplitComponent A p q).app n x
  by_cases hi : i = p
  · subst i
    by_cases hj : j = q
    · subst j
      have hup :
          bangDegreeUnit A p p =
            (symmetricPowerProjection A p).app
              (tensorPowerDimension A p)
              (Superoperator.identity (tensorPowerDimension A p)) := by
        simp [bangDegreeUnit_apply]
      have huq :
          bangDegreeUnit A q q =
            (symmetricPowerProjection A q).app
              (tensorPowerDimension A q)
              (Superoperator.identity (tensorPowerDimension A q)) := by
        simp [bangDegreeUnit_apply]
      rw [hup, huq]
      change Superoperator.comp
          (Superoperator.tensor
            (Superoperator.comp (symmetricAverage A p)
              (Superoperator.identity _))
            (Superoperator.comp (symmetricAverage A q)
              (Superoperator.identity _)))
          Φ =
        (countableRepresentableDayTensorInjection
            (tensorPowerDimension A) (tensorPowerDimension A) p q).app n Φ p q
      rw [Superoperator.comp_identity, Superoperator.comp_identity,
        symmetricAverage_of_le_one A p hA,
        symmetricAverage_of_le_one A q hA,
        Superoperator.tensor_identity, Superoperator.identity_comp,
        injection_square_eq_slot]
    · have huq : bangDegreeUnit A q j =
          (0 : SymmetricElement A j (tensorPowerDimension A q)) := by
        simp [bangDegreeUnit_apply, hj]; rfl
      have hten :
          Superoperator.tensor (bangDegreeUnit A p p).val
              (bangDegreeUnit A q j).val =
            (0 : Superoperator
              (tensorPowerDimension A p * tensorPowerDimension A q)
              (tensorPowerDimension A p * tensorPowerDimension A j)) := by
        have hz : (bangDegreeUnit A q j).val =
            (0 : Superoperator (tensorPowerDimension A q)
              (tensorPowerDimension A j)) := by
          rw [huq, SymmetricElement.zero_val]
        rw [hz]
        exact Superoperator.tensor_zero_right _
      have hL :
          Superoperator.comp
            (Superoperator.tensor (bangDegreeUnit A p p).val
              (bangDegreeUnit A q j).val) Φ =
          (0 : Superoperator n
            (tensorPowerDimension A p * tensorPowerDimension A j)) := by
        rw [hten]
        exact Superoperator.comp_zero_left
          (ℓ := tensorPowerDimension A p * tensorPowerDimension A j) Φ
      have hR :
          (countableRepresentableDayTensorInjection
              (tensorPowerDimension A) (tensorPowerDimension A) p q).app n Φ p j =
          (0 : Superoperator n
            (tensorPowerDimension A p * tensorPowerDimension A j)) :=
        injection_square_eq_zero_right A p q n j hj Φ
      exact hL.trans hR.symm
  · have hup : bangDegreeUnit A p i =
        (0 : SymmetricElement A i (tensorPowerDimension A p)) := by
      simp [bangDegreeUnit_apply, hi]; rfl
    have hten :
        Superoperator.tensor (bangDegreeUnit A p i).val
            (bangDegreeUnit A q j).val =
          (0 : Superoperator
            (tensorPowerDimension A p * tensorPowerDimension A q)
            (tensorPowerDimension A i * tensorPowerDimension A j)) := by
      have hz : (bangDegreeUnit A p i).val =
          (0 : Superoperator (tensorPowerDimension A p)
            (tensorPowerDimension A i)) := by
        rw [hup, SymmetricElement.zero_val]
      rw [hz]
      exact Superoperator.tensor_zero_left _
    have hL :
        Superoperator.comp
          (Superoperator.tensor (bangDegreeUnit A p i).val
            (bangDegreeUnit A q j).val) Φ =
        (0 : Superoperator n
          (tensorPowerDimension A i * tensorPowerDimension A j)) := by
      rw [hten]
      exact Superoperator.comp_zero_left
        (ℓ := tensorPowerDimension A i * tensorPowerDimension A j) Φ
    have hR :
        (countableRepresentableDayTensorInjection
            (tensorPowerDimension A) (tensorPowerDimension A) p q).app n Φ i j =
        (0 : Superoperator n
          (tensorPowerDimension A i * tensorPowerDimension A j)) :=
      injection_square_eq_zero_left A p q n i j hi Φ
    exact hL.trans hR.symm

/-- For `A ≤ 1`, Day comultiplication factors coefficientwise contraction
through the Day comparison. -/
theorem bangComult_factors_contraction_of_le_one (A : ℕ) (hA : A ≤ 1)
    (h : BangComultComponentsAdmissible A) :
    Hom.comp (symmetricSeriesDayCompare A) (bangComult A h) =
      symmetricContraction A := by
  ext n x
  have hsum :
      (symmetricFormalTensorSquare A).obj n |>.HasSum
        (fun pq : ℕ × ℕ =>
          (countableRepresentableDayTensorInjection
              (tensorPowerDimension A) (tensorPowerDimension A)
              pq.1 pq.2).app n
            ((symmetricContraction A).app n x pq.1 pq.2))
        ((symmetricContraction A).app n x) :=
    countableRepresentableDayTensor_hasSum_coordinates
      (tensorPowerDimension A) (tensorPowerDimension A) n
      ((symmetricContraction A).app n x)
  have hfam :
      (fun pq : ℕ × ℕ =>
          (symmetricSeriesDayCompare A).app n
            (bangComultComponentFamily A n x pq)) =
        fun pq : ℕ × ℕ =>
          (countableRepresentableDayTensorInjection
              (tensorPowerDimension A) (tensorPowerDimension A)
              pq.1 pq.2).app n
            ((symmetricContraction A).app n x pq.1 pq.2) := by
    funext pq
    simpa [bangComultComponentFamily, bangSplitComponent_eq_contraction_slot]
      using compare_bangComultComponent_of_le_one A hA pq.1 pq.2 n x
  have hcmp :
      (symmetricFormalTensorSquare A).obj n |>.HasSum
        (fun pq : ℕ × ℕ =>
          (symmetricSeriesDayCompare A).app n
            (bangComultComponentFamily A n x pq))
        ((symmetricSeriesDayCompare A).app n (bangComultApp A h n x)) := by
    simpa [symmetricSeriesDayCompare, DayCoend.lift] using
      bangComultApp_hasSum A h n x
        (symmetricFormalTensorSquare A) (symmetricSeriesDayBilinear A)
  rw [hfam] at hcmp
  exact
    ((symmetricFormalTensorSquare A).obj n).summation.unique hcmp hsum

/-- Unconditional Day factorization of contraction when `A ≤ 1`. -/
theorem bangComult_factors_contraction_le_one (A : ℕ) (hA : A ≤ 1) :
    Hom.comp (symmetricSeriesDayCompare A) (bangComult_of_le_one A hA) =
      symmetricContraction A :=
  bangComult_factors_contraction_of_le_one A hA
    (bangComultComponentsAdmissible_of_le_one A hA)

/-- Day factorization residual closed for `A ≤ 1`. -/
theorem symmetricContractionDayFactorization_of_le_one (A : ℕ) (hA : A ≤ 1) :
    SymmetricContractionDayFactorization A :=
  ⟨bangComult_of_le_one A hA, bangComult_factors_contraction_le_one A hA⟩

/-- Day comonoid package for `A ≤ 1`: admissibility plus factorization. -/
theorem bangDayComonoid_of_le_one (A : ℕ) (hA : A ≤ 1) :
    BangDayComonoid A :=
  ⟨bangComultComponentsAdmissible_of_le_one A hA,
    symmetricContractionDayFactorization_of_le_one A hA⟩


end SuperoperatorModule

end QLambda.Domain.Presheaf
