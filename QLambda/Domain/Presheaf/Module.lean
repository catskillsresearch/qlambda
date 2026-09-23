/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.SigmaMon

/-!
# Specialized modules over finite-dimensional superoperators

This is the elementary presentation of a `ΣMon`-enriched presheaf over the
finite-dimensional superoperator category.  It deliberately does not assert
Day closure or a cofree exponential; those require additional constructions.
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SigmaMon.ChoiSum

variable {n m ℓ : ℕ}

/-- Postcomposition by a fixed superoperator preserves every defined Choi
sum. -/
theorem comp_left {ι : Type} [Countable ι]
    (Ψ : Superoperator m ℓ) {f : ι → Superoperator n m}
    {Φ : Superoperator n m} (h : HasSum f Φ) :
    HasSum (fun i => Superoperator.comp Ψ (f i))
      (Superoperator.comp Ψ Φ) := by
  change _root_.HasSum
      (fun k => (CPMap.comp Ψ.cp (f k).cp).choi)
      (CPMap.comp Ψ.cp Φ.cp).choi
  apply Pi.hasSum.mpr
  rintro ⟨a, i⟩
  apply Pi.hasSum.mpr
  rintro ⟨b, j⟩
  simp_rw [CPMap.choi_comp_apply]
  apply hasSum_sum
  intro x _
  apply hasSum_sum
  intro y _
  exact
    ((Pi.hasSum.mp (Pi.hasSum.mp h (x, i)) (y, j)).mul_left
      (Ψ.cp.choi (a, x) (b, y)))

/-- Precomposition by a fixed superoperator preserves every defined Choi
sum. -/
theorem comp_right {ι : Type} [Countable ι]
    {f : ι → Superoperator m ℓ} {Ψ : Superoperator m ℓ}
    (Φ : Superoperator n m) (h : HasSum f Ψ) :
    HasSum (fun i => Superoperator.comp (f i) Φ)
      (Superoperator.comp Ψ Φ) := by
  change _root_.HasSum
      (fun k => (CPMap.comp (f k).cp Φ.cp).choi)
      (CPMap.comp Ψ.cp Φ.cp).choi
  apply Pi.hasSum.mpr
  rintro ⟨a, i⟩
  apply Pi.hasSum.mpr
  rintro ⟨b, j⟩
  simp_rw [CPMap.choi_comp_apply]
  apply hasSum_sum
  intro x _
  apply hasSum_sum
  intro y _
  exact
    ((Pi.hasSum.mp (Pi.hasSum.mp h (a, x)) (b, y)).mul_right
      (Φ.cp.choi (x, i) (y, j)))

/-- Effect of composing a map out of the unit fiber with a map into it. -/
theorem effect_comp_from_one (f : CPMap 1 ℓ) (g : CPMap m 1) :
    (CPMap.comp f g).effect = (f.effect 0 0) • g.effect := by
  ext i j
  change
      (∑ a : Fin ℓ, (CPMap.comp f g).choi (a, j) (a, i)) =
        (f.effect 0 0) * g.effect i j
  simp only [CPMap.choi_comp_apply, Fin.default_eq_zero, CPMap.effect]
  have hfactor :
      (∑ a : Fin ℓ, f.choi (a, 0) (a, 0) * g.choi (0, j) (0, i)) =
        (∑ a : Fin ℓ, f.choi (a, 0) (a, 0)) * g.choi (0, j) (0, i) := by
    rw [← Finset.sum_mul]
  simpa [Fintype.sum_unique] using hfactor

/-- Trace bound: `Trace(choi).re ≤ input dimension` for TNI maps. -/
theorem trace_choi_re_le_input_dim {n m : ℕ} (Φ : Superoperator n m) :
    (Matrix.trace Φ.cp.choi).re ≤ n := by
  have he :=
    CPMap.effect_le_one_of_trace_nonincreasing Φ.cp Φ.trace_nonincreasing
  have hp : (1 - Φ.cp.effect).PosSemidef := Matrix.le_iff.mp he
  have ht := hp.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_one] at ht
  have htre := (RCLike.nonneg_iff.mp ht).1
  have hte :
      Matrix.trace Φ.cp.choi = Matrix.trace Φ.cp.effect := by
    change (∑ p : Fin m × Fin n, Φ.cp.choi p p) =
      ∑ i : Fin n, ∑ a : Fin m, Φ.cp.choi (a, i) (a, i)
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hte]
  simpa using htre

/-- Choi → effect as a continuous linear map. -/
noncomputable def effectCLM (n m : ℕ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →L[ℂ]
      Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A i j => ∑ a : Fin m, A (a, j) (a, i)
      map_add' := by
        intro A B; ext i j
        exact Finset.sum_add_distrib
      map_smul' := by
        intro c A; ext i j
        change (∑ a : Fin m, c * A (a, j) (a, i)) = c * ∑ a : Fin m, A (a, j) (a, i)
        rw [← Finset.mul_sum] }

/-- Joint precomposition against maps into the unit fiber. -/
theorem comp_from_one {ι : Type} [Countable ι] {m ℓ : ℕ}
    {f : ι → Superoperator 1 ℓ} {Ψ : Superoperator 1 ℓ}
    (g : ι → Superoperator m 1) (hf : HasSum f Ψ) :
    ∃ Χ : Superoperator m ℓ,
      HasSum (fun i => Superoperator.comp (f i) (g i)) Χ := by
  classical
  have hfin (k : ι) (a b : Fin ℓ) (i j : Fin m) :
      (CPMap.comp (f k).cp (g k).cp).choi (a, i) (b, j) =
        (f k).cp.choi (a, 0) (b, 0) *
          (g k).cp.choi (0, i) (0, j) := by
    simp [CPMap.choi_comp_apply, Fin.default_eq_zero]
  have hentries (a b : Fin ℓ) (i j : Fin m) :
      Summable fun k : ι =>
        (CPMap.comp (f k).cp (g k).cp).choi (a, i) (b, j) := by
    simp_rw [hfin]
    have ha :
        Summable fun k : ι => (f k).cp.choi (a, 0) (b, 0) :=
      (Pi.hasSum.mp
        (Pi.hasSum.mp hf (a, (0 : Fin 1)))
        (b, (0 : Fin 1))).summable
    have haN : Summable fun k : ι =>
        ‖(f k).cp.choi (a, 0) (b, 0)‖ * (m : ℝ) :=
      (ha.norm.mul_right (m : ℝ))
    refine Summable.of_norm_bounded haN fun k => ?_
    rw [norm_mul]
    have hb :=
      entry_norm_le_trace_re (g k).cp.choi_pos (0, i) (0, j)
    have htr := trace_choi_re_le_input_dim (g k)
    exact
      (mul_le_mul_of_nonneg_left (hb.trans htr) (norm_nonneg _)).trans_eq
        (by ring)
  have hmat :
      Summable fun k : ι =>
        (CPMap.comp (f k).cp (g k).cp).choi := by
    refine Pi.summable.mpr fun ai => Pi.summable.mpr fun bj => ?_
    rcases ai with ⟨a, i⟩; rcases bj with ⟨b, j⟩
    exact hentries a b i j
  let Ψcp : CPMap m ℓ :=
    { choi := ∑' k : ι, (CPMap.comp (f k).cp (g k).cp).choi
      choi_pos :=
        hasSum_posSemidef hmat.hasSum fun k =>
          (CPMap.comp (f k).cp (g k).cp).choi_pos }
  have hcp :
      _root_.HasSum
        (fun i => (CPMap.comp (f i).cp (g i).cp).choi) Ψcp.choi :=
    hmat.hasSum
  refine ⟨⟨Ψcp, ?_⟩, hcp⟩
  -- TNI via `effect ≤ 1`.
  rw [traceNonincreasing_iff_effect_le_one]
  have heffect_term (k : ι) :
      (CPMap.comp (f k).cp (g k).cp).effect =
        ((f k).cp.effect 0 0) • (g k).cp.effect :=
    effect_comp_from_one (f k).cp (g k).cp
  have heff_sum :
      _root_.HasSum
        (fun k => (CPMap.comp (f k).cp (g k).cp).effect) Ψcp.effect :=
    hcp.map (effectCLM m ℓ) (effectCLM m ℓ).cont
  have heff_sum' :
      _root_.HasSum
        (fun k => ((f k).cp.effect 0 0) • (g k).cp.effect) Ψcp.effect :=
    heff_sum.congr_fun fun k => (heffect_term k).symm
  have hα_re (k : ι) : 0 ≤ ((f k).cp.effect 0 0).re :=
    diag_re_nonneg (f k).cp.effect_posSemidef 0
  have hα_im (k : ι) : ((f k).cp.effect 0 0).im = 0 :=
    diag_im_eq_zero (f k).cp.effect_posSemidef 0
  have hα_nn (k : ι) : 0 ≤ (f k).cp.effect 0 0 :=
    RCLike.nonneg_iff.mpr ⟨hα_re k, hα_im k⟩
  have hα_sum :
      _root_.HasSum (fun k => (f k).cp.effect 0 0) (Ψ.cp.effect 0 0) := by
    have hE :
        _root_.HasSum (fun k => (f k).cp.effect) Ψ.cp.effect :=
      hf.map (effectCLM 1 ℓ) (effectCLM 1 ℓ).cont
    exact Pi.hasSum.mp (Pi.hasSum.mp hE 0) 0
  have hα_le : (Ψ.cp.effect 0 0).re ≤ 1 := by
    have hΨe :=
      CPMap.effect_le_one_of_trace_nonincreasing Ψ.cp
        Ψ.trace_nonincreasing
    have hpsd : (1 - Ψ.cp.effect).PosSemidef := Matrix.le_iff.mp hΨe
    have hre := diag_re_nonneg hpsd (0 : Fin 1)
    change 0 ≤ (1 - Ψ.cp.effect 0 0).re at hre
    rw [Complex.sub_re, Complex.one_re] at hre
    linarith
  -- Entrywise: `∑ α_k • I = (∑ α_k) • I`.
  have hI_sum :
      _root_.HasSum
        (fun k =>
          ((f k).cp.effect 0 0) • (1 : Matrix (Fin m) (Fin m) ℂ))
        ((Ψ.cp.effect 0 0) • (1 : Matrix (Fin m) (Fin m) ℂ)) := by
    apply Pi.hasSum.mpr
    intro i
    apply Pi.hasSum.mpr
    intro j
    simp only [Matrix.smul_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simpa using hα_sum
    · simpa [hij] using hasSum_zero
  -- Difference family `α_k • (I - E_k)` sums to `(∑ α)•I - Ψcp.effect`.
  have hdiff :
      _root_.HasSum
        (fun k =>
          ((f k).cp.effect 0 0) •
            ((1 : Matrix (Fin m) (Fin m) ℂ) - (g k).cp.effect))
        ((Ψ.cp.effect 0 0) • (1 : Matrix (Fin m) (Fin m) ℂ) -
          Ψcp.effect) := by
    have hsub := hI_sum.sub heff_sum'
    refine hsub.congr_fun fun k => ?_
    simp [smul_sub]
  have hpsd_term (k : ι) :
      (((f k).cp.effect 0 0) •
          ((1 : Matrix (Fin m) (Fin m) ℂ) -
            (g k).cp.effect)).PosSemidef := by
    have hg :=
      CPMap.effect_le_one_of_trace_nonincreasing (g k).cp
        (g k).trace_nonincreasing
    exact (Matrix.le_iff.mp hg).smul (hα_nn k)
  have hsum_le :
      Ψcp.effect ≤
        (Ψ.cp.effect 0 0) • (1 : Matrix (Fin m) (Fin m) ℂ) :=
    Matrix.le_iff.mpr (hasSum_posSemidef hdiff hpsd_term)
  have hscale :
      (Ψ.cp.effect 0 0) • (1 : Matrix (Fin m) (Fin m) ℂ) ≤
        (1 : Matrix (Fin m) (Fin m) ℂ) := by
    have hα1 : Ψ.cp.effect 0 0 ≤ (1 : ℂ) := by
      rw [← sub_nonneg]
      refine RCLike.nonneg_iff.mpr ⟨?_, ?_⟩
      · simpa [Complex.sub_re, Complex.one_re] using sub_nonneg.mpr hα_le
      · simp [Complex.sub_im, diag_im_eq_zero Ψ.cp.effect_posSemidef 0]
    have : (1 : Matrix (Fin m) (Fin m) ℂ) -
        (Ψ.cp.effect 0 0) • 1 =
          (1 - Ψ.cp.effect 0 0) • 1 := by
      simp [sub_smul, one_smul]
    rw [Matrix.le_iff, this]
    exact (Matrix.PosSemidef.one (n := Fin m)).smul (sub_nonneg.mpr hα1)
  exact hsum_le.trans hscale

end SigmaMon.ChoiSum

namespace SigmaMon.CPMapSum

variable {n m ℓ : ℕ}

/-- Postcomposition by a fixed CP map preserves ambient CP sums. -/
theorem comp_left {ι : Type} [Countable ι]
    (Ψ : CPMap m ℓ) {f : ι → CPMap n m}
    {Φ : CPMap n m} (h : HasSum f Φ) :
    HasSum (fun i => CPMap.comp Ψ (f i)) (CPMap.comp Ψ Φ) := by
  change _root_.HasSum
    (fun k => (CPMap.comp Ψ (f k)).choi) (CPMap.comp Ψ Φ).choi
  apply Pi.hasSum.mpr
  rintro ⟨a, i⟩
  apply Pi.hasSum.mpr
  rintro ⟨b, j⟩
  simp_rw [CPMap.choi_comp_apply]
  apply hasSum_sum
  intro x _
  apply hasSum_sum
  intro y _
  exact
    ((Pi.hasSum.mp (Pi.hasSum.mp h (x, i)) (y, j)).mul_left
      (Ψ.choi (a, x) (b, y)))

/-- Precomposition by a fixed CP map preserves ambient CP sums. -/
theorem comp_right {ι : Type} [Countable ι]
    {f : ι → CPMap m ℓ} {Ψ : CPMap m ℓ}
    (Φ : CPMap n m) (h : HasSum f Ψ) :
    HasSum (fun i => CPMap.comp (f i) Φ) (CPMap.comp Ψ Φ) := by
  change _root_.HasSum
    (fun k => (CPMap.comp (f k) Φ).choi) (CPMap.comp Ψ Φ).choi
  apply Pi.hasSum.mpr
  rintro ⟨a, i⟩
  apply Pi.hasSum.mpr
  rintro ⟨b, j⟩
  simp_rw [CPMap.choi_comp_apply]
  apply hasSum_sum
  intro x _
  apply hasSum_sum
  intro y _
  exact
    ((Pi.hasSum.mp (Pi.hasSum.mp h (a, x)) (b, y)).mul_right
      (Φ.choi (x, i) (y, j)))


/-- Joint precomposition of ambient CP maps against TNI maps into the unit
fiber.  No TNI obligation is placed on the result. -/
theorem comp_from_one {ι : Type} [Countable ι] {m ℓ : ℕ}
    {f : ι → CPMap 1 ℓ} {Ψ : CPMap 1 ℓ}
    (g : ι → Superoperator m 1) (hf : HasSum f Ψ) :
    ∃ Χ : CPMap m ℓ,
      HasSum (fun i => CPMap.comp (f i) (g i).cp) Χ := by
  classical
  have hfin (k : ι) (a b : Fin ℓ) (i j : Fin m) :
      (CPMap.comp (f k) (g k).cp).choi (a, i) (b, j) =
        (f k).choi (a, 0) (b, 0) * (g k).cp.choi (0, i) (0, j) := by
    simp [CPMap.choi_comp_apply, Fin.default_eq_zero]
  have hentries (a b : Fin ℓ) (i j : Fin m) :
      Summable fun k : ι =>
        (CPMap.comp (f k) (g k).cp).choi (a, i) (b, j) := by
    simp_rw [hfin]
    have ha : Summable fun k : ι => (f k).choi (a, 0) (b, 0) :=
      (Pi.hasSum.mp (Pi.hasSum.mp hf (a, (0 : Fin 1)))
        (b, (0 : Fin 1))).summable
    have haN : Summable fun k : ι =>
        ‖(f k).choi (a, 0) (b, 0)‖ * (m : ℝ) :=
      ha.norm.mul_right (m : ℝ)
    refine Summable.of_norm_bounded haN fun k => ?_
    rw [norm_mul]
    have hb :=
      ChoiSum.entry_norm_le_trace_re (g k).cp.choi_pos (0, i) (0, j)
    have htr := ChoiSum.trace_choi_re_le_input_dim (g k)
    exact
      (mul_le_mul_of_nonneg_left (hb.trans htr) (norm_nonneg _)).trans_eq
        (by ring)
  have hmat :
      Summable fun k : ι => (CPMap.comp (f k) (g k).cp).choi := by
    refine Pi.summable.mpr fun ai => Pi.summable.mpr fun bj => ?_
    rcases ai with ⟨a, i⟩; rcases bj with ⟨b, j⟩
    exact hentries a b i j
  exact ⟨⟨∑' k, (CPMap.comp (f k) (g k).cp).choi,
    ChoiSum.hasSum_posSemidef hmat.hasSum fun k =>
      (CPMap.comp (f k) (g k).cp).choi_pos⟩, hmat.hasSum⟩

end SigmaMon.CPMapSum

namespace SuperoperatorModule

universe u v w x

/-- A carrier equipped with a relational partial countable sum. -/
structure Fiber where
  Carrier : Type u
  zero : Carrier
  summation : @SigmaMon.PartialCountableSum Carrier ⟨zero⟩

instance (X : Fiber) : Zero X.Carrier := ⟨X.zero⟩

/-- The relation saying that a family has the indicated partial sum in a
fiber. -/
abbrev Fiber.HasSum (X : Fiber) {ι : Type} [Countable ι]
    (f : ι → X.Carrier) (x : X.Carrier) : Prop :=
  X.summation.HasSum f x

/-- The constantly-zero family has a sum over every countable index type. -/
theorem Fiber.hasSum_zero (X : Fiber.{u}) {ι : Type} [Countable ι] :
    X.HasSum (fun _ : ι => 0) 0 := by
  have hEmpty :
      X.HasSum (fun i : (∅ : Set ι) => 0) 0 := by
    convert ((X.summation.reindex (Equiv.Set.empty ι)
      (fun i : Empty => nomatch i) 0).mpr
        X.summation.empty) using 1
    funext i
    exact i.property.elim
  exact (X.summation.remove_zero
    (fun _ : ι => 0) ∅ 0 (by simp)).mp hEmpty

theorem Fiber.hasSum_congr (X : Fiber.{u}) {ι : Type} [Countable ι]
    {f g : ι → X.Carrier} {x : X.Carrier}
    (h : ∀ i, f i = g i) :
    X.HasSum f x ↔ X.HasSum g x := by
  have hfg : f = g := funext h
  subst g
  rfl

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

/-- A sum-preserving natural transformation of specialized modules. -/
structure Hom (M : Module.{u}) (N : Module.{v}) where
  app : ∀ n, (M.obj n).Carrier → (N.obj n).Carrier
  map_zero : ∀ n, app n 0 = 0
  map_sum :
    ∀ {ι : Type} [Countable ι] {n} {f : ι → (M.obj n).Carrier}
      {x : (M.obj n).Carrier},
      (M.obj n).HasSum f x →
        (N.obj n).HasSum (fun i => app n (f i)) (app n x)
  naturality :
    ∀ {m n} (x : (M.obj n).Carrier) (f : Superoperator m n),
      app m (M.act x f) = N.act (app n x) f

namespace Hom

@[ext]
theorem ext {M : Module.{u}} {N : Module.{v}} {f g : Hom M N}
    (h : ∀ n x, f.app n x = g.app n x) : f = g := by
  cases f
  cases g
  congr
  funext n x
  exact h n x

def id (M : Module.{u}) : Hom M M where
  app := fun _ x => x
  map_zero := fun _ => rfl
  map_sum := fun h => h
  naturality := fun _ _ => rfl

def comp {L : Module.{u}} {M : Module.{v}} {N : Module.{w}}
    (g : Hom M N) (f : Hom L M) : Hom L N where
  app := fun n x => g.app n (f.app n x)
  map_zero := by
    intro n
    rw [f.map_zero, g.map_zero]
  map_sum := fun h => g.map_sum (f.map_sum h)
  naturality := by
    intro m n x h
    rw [f.naturality, g.naturality]

@[simp]
theorem id_app (M : Module.{u}) (n : ℕ) (x : (M.obj n).Carrier) :
    (id M).app n x = x :=
  rfl

@[simp]
theorem comp_app {L : Module.{u}} {M : Module.{v}} {N : Module.{w}}
    (g : Hom M N) (f : Hom L M)
    (n : ℕ) (x : (L.obj n).Carrier) :
    (comp g f).app n x = g.app n (f.app n x) :=
  rfl

@[simp]
theorem id_comp {M : Module.{u}} {N : Module.{v}} (f : Hom M N) :
    comp (id N) f = f := by
  ext
  rfl

@[simp]
theorem comp_id {M : Module.{u}} {N : Module.{v}} (f : Hom M N) :
    comp f (id M) = f := by
  ext
  rfl

theorem comp_assoc {K : Module.{u}} {L : Module.{v}}
    {M : Module.{w}} {N : Module.{x}}
    (h : Hom M N) (g : Hom L M) (f : Hom K L) :
    comp h (comp g f) = comp (comp h g) f := by
  ext
  rfl

/-- The zero natural transformation. -/
def zero (M : Module.{u}) (N : Module.{v}) : Hom M N where
  app := fun n _ => 0
  map_zero := fun _ => rfl
  map_sum := by
    intro ι _ n f x h
    have hz :
        (N.obj n).HasSum (fun _ : (∅ : Set ι) => 0) 0 := by
      convert ((N.obj n).summation.reindex (Equiv.Set.empty ι)
        (fun i : Empty => nomatch i) 0).mpr
          (N.obj n).summation.empty using 1
      funext i
      exact i.property.elim
    exact (N.obj n).summation.remove_zero
      (fun _ : ι => (0 : (N.obj n).Carrier)) ∅ 0
      (by simp) |>.mp hz
  naturality := by
    intro m n x f
    exact (N.act_zero_element f).symm

instance (M : Module.{u}) (N : Module.{v}) : Zero (Hom M N) :=
  ⟨zero M N⟩

@[simp]
theorem zero_app (M : Module.{u}) (N : Module.{v})
    (n : ℕ) (x : (M.obj n).Carrier) :
    (0 : Hom M N).app n x = 0 :=
  rfl

/-- Pointwise partial sums of natural transformations.  Naturality belongs to
the proposed result `s`, so no choice of a pointwise sum is hidden here. -/
def HasSum {M : Module.{u}} {N : Module.{v}} {ι : Type} [Countable ι]
    (f : ι → Hom M N) (s : Hom M N) : Prop :=
  ∀ n x, (N.obj n).HasSum (fun i => (f i).app n x) (s.app n x)

theorem hasSum_unique {M : Module.{u}} {N : Module.{v}}
    {ι : Type} [Countable ι] {f : ι → Hom M N} {s t : Hom M N}
    (hs : HasSum f s) (ht : HasSum f t) : s = t := by
  ext n x
  exact (N.obj n).summation.unique (hs n x) (ht n x)

theorem hasSum_empty (M : Module.{u}) (N : Module.{v}) :
    HasSum (fun i : Empty => nomatch i) (0 : Hom M N) := by
  intro n x
  convert (N.obj n).summation.empty using 1
  change (zero M N).app n x = 0
  rfl

theorem hasSum_singleton {M : Module.{u}} {N : Module.{v}} (f : Hom M N) :
    HasSum (fun _ : PUnit => f) f := by
  intro n x
  exact (N.obj n).summation.singleton _

theorem hasSum_remove_zero {M : Module.{u}} {N : Module.{v}}
    {ι : Type} [Countable ι] (f : ι → Hom M N) (s : Set ι)
    (g : Hom M N) (hzero : ∀ i, i ∉ s → f i = 0) :
    HasSum (fun i : s => f i) g ↔ HasSum f g := by
  constructor <;> intro h n x
  · apply ((N.obj n).summation.remove_zero
      (fun i => (f i).app n x) s (g.app n x) ?_).mp
    · exact h n x
    · intro i hi
      rw [hzero i hi]
      rfl
  · apply ((N.obj n).summation.remove_zero
      (fun i => (f i).app n x) s (g.app n x) ?_).mpr
    · exact h n x
    · intro i hi
      rw [hzero i hi]
      rfl

theorem hasSum_reindex {M : Module.{u}} {N : Module.{v}}
    {ι κ : Type} [Countable ι] [Countable κ]
    (e : κ ≃ ι) (f : ι → Hom M N) (s : Hom M N) :
    HasSum (f ∘ e) s ↔ HasSum f s := by
  constructor <;> intro h n x
  · exact ((N.obj n).summation.reindex e
      (fun i => (f i).app n x) (s.app n x)).mp (h n x)
  · exact ((N.obj n).summation.reindex e
      (fun i => (f i).app n x) (s.app n x)).mpr (h n x)

/-- Postcomposition preserves every defined pointwise sum of module maps. -/
theorem hasSum_comp_left {L : Module.{u}} {M : Module.{v}}
    {N : Module.{w}} {ι : Type} [Countable ι]
    (g : Hom M N) {f : ι → Hom L M} {s : Hom L M}
    (h : HasSum f s) :
    HasSum (fun i => comp g (f i)) (comp g s) := by
  intro n x
  exact g.map_sum (h n x)

/-- Precomposition preserves every defined pointwise sum of module maps. -/
theorem hasSum_comp_right {L : Module.{u}} {M : Module.{v}}
    {N : Module.{w}} {ι : Type} [Countable ι]
    {f : ι → Hom M N} {s : Hom M N} (g : Hom L M)
    (h : HasSum f s) :
    HasSum (fun i => comp (f i) g) (comp s g) := by
  intro n x
  exact h n (g.app n x)

end Hom

/-- A module isomorphism, used without importing a second categorical
interface. -/
structure Iso (M : Module.{u}) (N : Module.{v}) where
  hom : Hom M N
  inv : Hom N M
  hom_inv : Hom.comp hom inv = Hom.id N
  inv_hom : Hom.comp inv hom = Hom.id M

end SuperoperatorModule

end QLambda.Domain.Presheaf
