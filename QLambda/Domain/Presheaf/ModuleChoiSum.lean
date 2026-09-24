/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.SigmaMon

/-!
# Choi / CPMap sum lemmas used by specialized modules

Support material previously living at the top of `Module.lean`.
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

/-! ## Gate 3 / Path 2 obstruction (kernel-checked)

A proposed `ChoiSum.comp_from_dim` / `Module.act_sum_from_dim` (joint TNI
precomposition at fiber `d ≥ 2`) is false.  The counterexample below
constructs complementary basis effects `e0, e1 : 2 → 1` summing to discard
and isometric preparations `p0, p1 : 1 → 2`, so that
`eᵢ ∘ pᵢ = id₁` and the composed Bool-family has no TNI/`Superoperator`
Choi sum (`not_exists_hasSum_gate3Composed`,
`exists_fiber2_comp_without_superoperator_sum`).  Ambient CP still admits
`CPMapSum.comp_from_dim` below; do not add the false statement as a
required `Module` field. -/

/-- Computational-basis bra `⟨i|` as a Kraus operator `2 → 1`. -/
def basisBra (i : Fin 2) : KrausOperator 2 1 :=
  fun _ j => if j = i then (1 : ℂ) else 0

/-- Computational-basis ket `|i⟩` as a Kraus operator `1 → 2`. -/
def basisKet (i : Fin 2) : KrausOperator 1 2 :=
  fun j _ => if j = i then (1 : ℂ) else 0

theorem basisBra_effect (i : Fin 2) :
    KrausFamily.effect [basisBra i] =
      fun j k => if j = i ∧ k = i then (1 : ℂ) else 0 := by
  ext j k
  simp only [KrausFamily.effect, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, basisBra, Matrix.mul_apply, conjTranspose_apply,
    Fintype.sum_unique]
  split_ifs <;> simp_all

theorem basisBra_effect_add :
    KrausFamily.effect [basisBra 0] + KrausFamily.effect [basisBra 1] =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext j k
  rw [Matrix.add_apply, basisBra_effect, basisBra_effect, Matrix.one_apply]
  fin_cases j <;> fin_cases k <;> simp

theorem basisBra_effect_le_one (i : Fin 2) :
    KrausFamily.effect [basisBra i] ≤ 1 := by
  have hsum := basisBra_effect_add
  have hother :
      KrausFamily.effect [basisBra (1 - i)] =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) - KrausFamily.effect [basisBra i] := by
    fin_cases i
    · exact eq_sub_of_add_eq (by simpa [add_comm] using hsum)
    · exact eq_sub_of_add_eq hsum
  rw [Matrix.le_iff, ← hother]
  exact KrausFamily.effect_posSemidef _

theorem basisKet_effect (i : Fin 2) :
    KrausFamily.effect [basisKet i] = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext a b
  fin_cases a; fin_cases b
  simp only [KrausFamily.effect, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, basisKet, Matrix.mul_apply, conjTranspose_apply,
    Matrix.one_apply]
  classical
  calc
    (∑ j : Fin 2, star (if j = i then (1 : ℂ) else 0) *
        (if j = i then (1 : ℂ) else 0)) =
        ∑ j : Fin 2, if j = i then (1 : ℂ) else 0 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    _ = 1 := by simp

theorem basisBra_mul_basisKet (i : Fin 2) :
    basisBra i * basisKet i = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext a b
  fin_cases a; fin_cases b
  simp only [basisBra, basisKet, Matrix.mul_apply, Matrix.one_apply]
  classical
  calc
    (∑ j : Fin 2, (if j = i then (1 : ℂ) else 0) *
        (if j = i then (1 : ℂ) else 0)) =
        ∑ j : Fin 2, if j = i then (1 : ℂ) else 0 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    _ = 1 := by simp

theorem basisBra_mul_basisKet_of_ne {i j : Fin 2} (h : i ≠ j) :
    basisBra i * basisKet j = (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext a b
  fin_cases a; fin_cases b
  simp only [basisBra, basisKet, Matrix.mul_apply, Matrix.zero_apply]
  classical
  calc
    (∑ k : Fin 2, (if k = i then (1 : ℂ) else 0) *
        (if k = j then (1 : ℂ) else 0)) =
        ∑ k : Fin 2, (0 : ℂ) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs with hki hkj
      · exact False.elim (h (hki.symm.trans hkj))
      · simp
      · simp
      · simp
    _ = 0 := by simp

/-- Complementary computational-basis effect `⟨i|−|i⟩ : 2 → 1`. -/
noncomputable def complementaryBasisEffect (i : Fin 2) : Superoperator 2 1 where
  cp := CPMap.ofKraus [basisBra i]
  trace_nonincreasing :=
    (traceNonincreasing_iff_effect_le_one _).mpr <| by
      simpa [CPMap.effect_ofKraus] using basisBra_effect_le_one i

/-- Isometric preparation of computational-basis state `|i⟩` as `1 → 2`. -/
noncomputable def isometricBasisPrep (i : Fin 2) : Superoperator 1 2 where
  cp := CPMap.ofKraus [basisKet i]
  trace_nonincreasing :=
    (traceNonincreasing_iff_effect_le_one _).mpr <| by
      simp [CPMap.effect_ofKraus, basisKet_effect]

/-- Discard / partial trace `2 → 1` (effect `I₂`). -/
noncomputable def discardTwo : Superoperator 2 1 where
  cp := CPMap.ofKraus [basisBra 0, basisBra 1]
  trace_nonincreasing :=
    (traceNonincreasing_iff_effect_le_one _).mpr <| by
      rw [CPMap.effect_ofKraus]
      have heff :
          KrausFamily.effect [basisBra 0, basisBra 1] =
            KrausFamily.effect [basisBra 0] + KrausFamily.effect [basisBra 1] := by
        simp [KrausFamily.effect]
      rw [heff, basisBra_effect_add]

noncomputable abbrev e0 : Superoperator 2 1 := complementaryBasisEffect 0
noncomputable abbrev e1 : Superoperator 2 1 := complementaryBasisEffect 1
noncomputable abbrev p0 : Superoperator 1 2 := isometricBasisPrep 0
noncomputable abbrev p1 : Superoperator 1 2 := isometricBasisPrep 1

theorem e0_add_e1_cp_eq_discardTwo :
    e0.cp + e1.cp = discardTwo.cp := by
  change CPMap.ofKraus [basisBra 0] + CPMap.ofKraus [basisBra 1] =
    CPMap.ofKraus [basisBra 0, basisBra 1]
  simpa using (CPMap.ofKraus_append [basisBra 0] [basisBra 1]).symm

theorem complementaryBasisEffect_comp_isometricBasisPrep (i : Fin 2) :
    Superoperator.comp (complementaryBasisEffect i) (isometricBasisPrep i) =
      Superoperator.identity 1 := by
  apply Superoperator.ext
  apply CPMap.ext_apply
  intro ρ
  simp only [Superoperator.cp_comp, complementaryBasisEffect, isometricBasisPrep,
    Superoperator.identity, CPMap.applyMat_comp, CPMap.applyMat_ofKraus,
    CPMap.applyMat_identity, KrausFamily.applyMat_single]
  calc
    basisBra i * (basisKet i * ρ * (basisKet i)ᴴ) * (basisBra i)ᴴ
        = (basisBra i * basisKet i) * ρ *
            ((basisBra i * basisKet i)ᴴ) := by
          simp [Matrix.mul_assoc]
    _ = (1 : Matrix (Fin 1) (Fin 1) ℂ) * ρ * (1 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ := by
          simp [basisBra_mul_basisKet]
    _ = ρ := by simp

theorem complementaryBasisEffect_comp_isometricBasisPrep_of_ne
    {i j : Fin 2} (h : i ≠ j) :
    Superoperator.comp (complementaryBasisEffect i) (isometricBasisPrep j) = 0 := by
  apply Superoperator.ext
  apply CPMap.ext_apply
  intro ρ
  simp only [Superoperator.cp_comp, complementaryBasisEffect, isometricBasisPrep,
    Superoperator.cp_zero, CPMap.applyMat_comp, CPMap.applyMat_ofKraus,
    CPMap.applyMat_zero, KrausFamily.applyMat_single]
  calc
    basisBra i * (basisKet j * ρ * (basisKet j)ᴴ) * (basisBra i)ᴴ
        = (basisBra i * basisKet j) * ρ *
            ((basisBra i * basisKet j)ᴴ) := by
          -- `(basisKet j)ᴴ * (basisBra i)ᴴ = (basisBra i * basisKet j)ᴴ`
          simp [Matrix.mul_assoc, ← Matrix.conjTranspose_mul]
    _ = (0 : Matrix (Fin 1) (Fin 1) ℂ) * ρ *
            ((0 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ) := by
          simp [basisBra_mul_basisKet_of_ne h]
    _ = 0 := by simp

theorem e0_comp_p0 :
    Superoperator.comp e0 p0 = Superoperator.identity 1 :=
  complementaryBasisEffect_comp_isometricBasisPrep 0

theorem e1_comp_p1 :
    Superoperator.comp e1 p1 = Superoperator.identity 1 :=
  complementaryBasisEffect_comp_isometricBasisPrep 1

/-- The complementary basis effects are Choi-summable to discard. -/
theorem complementaryBasisEffects_hasSum_discard :
    HasSum (fun i : Bool => bif i then e0 else e1) discardTwo := by
  have hTNI : TraceNonincreasing (e0.cp + e1.cp) := by
    rw [e0_add_e1_cp_eq_discardTwo]
    exact discardTwo.trace_nonincreasing
  have hsum := hasSum_add_of_addable e0 e1 hTNI
  have heq : (⟨e0.cp + e1.cp, hTNI⟩ : Superoperator 2 1) = discardTwo :=
    Superoperator.ext e0_add_e1_cp_eq_discardTwo
  rwa [heq] at hsum

/-- Joint composition of the Gate-3 complementary effects against the matching
preparations: two copies of `id₁`. -/
noncomputable def gate3ComposedFamily : Bool → Superoperator 1 1 :=
  fun i =>
    Superoperator.comp (bif i then e0 else e1) (bif i then p0 else p1)

theorem gate3ComposedFamily_eq_identity (i : Bool) :
    gate3ComposedFamily i = Superoperator.identity 1 := by
  cases i <;> simp [gate3ComposedFamily, e0_comp_p0, e1_comp_p1]

theorem identity_effect (n : ℕ) :
    (CPMap.identity n).effect = 1 := by
  rw [CPMap.identity, CPMap.effect_ofKraus]
  simp [KrausFamily.effect, KrausFamily.identity]

theorem effect_add (Φ Ψ : CPMap n m) :
    (Φ + Ψ).effect = Φ.effect + Ψ.effect := by
  ext i j
  simp only [CPMap.effect, CPMap.choi_add, Matrix.add_apply, Finset.sum_add_distrib]

/-- The CP sum of two copies of `id₁` has effect `2 · I₁`. -/
theorem two_identity_effect :
    (CPMap.identity 1 + CPMap.identity 1).effect =
      (2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  rw [effect_add, identity_effect]
  ext i j
  fin_cases i; fin_cases j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  norm_num

/-- Hence `id₁ + id₁` is not trace-nonincreasing. -/
theorem two_identity_not_traceNonincreasing :
    ¬ TraceNonincreasing (CPMap.identity 1 + CPMap.identity 1) := by
  rw [traceNonincreasing_iff_effect_le_one, two_identity_effect]
  intro h
  have hp : ((1 : Matrix (Fin 1) (Fin 1) ℂ) - (2 : ℂ) • 1).PosSemidef :=
    Matrix.le_iff.mp h
  have hdiag := diag_re_nonneg hp (0 : Fin 1)
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Complex.sub_re] at hdiag
  norm_num at hdiag

/-- The composed Gate-3 family has no Superoperator (TNI) Choi sum. -/
theorem not_exists_hasSum_gate3Composed :
    ¬ ∃ Φ : Superoperator 1 1, HasSum gate3ComposedFamily Φ := by
  rintro ⟨Φ, hΦ⟩
  have hΦ' :
      _root_.HasSum
        (fun _ : Bool => (CPMap.identity 1).choi) Φ.cp.choi := by
    refine
      (show _root_.HasSum (fun i => (gate3ComposedFamily i).cp.choi) Φ.cp.choi
        from hΦ).congr_fun ?_
    intro i
    rw [gate3ComposedFamily_eq_identity i]
    rfl
  have hfin :
      _root_.HasSum
        (fun _ : Bool => (CPMap.identity 1).choi)
        (∑ _ : Bool, (CPMap.identity 1).choi) :=
    hasSum_fintype fun _ : Bool => (CPMap.identity 1).choi
  have hchoi : Φ.cp.choi = ∑ _ : Bool, (CPMap.identity 1).choi :=
    hΦ'.unique hfin
  have hsum :
      ∑ _ : Bool, (CPMap.identity 1).choi =
        (CPMap.identity 1 + CPMap.identity 1).choi := by
    simp only [Fintype.sum_bool, CPMap.choi_add]
  have hcp : Φ.cp = CPMap.identity 1 + CPMap.identity 1 :=
    CPMap.ext (hchoi.trans hsum)
  exact two_identity_not_traceNonincreasing (hcp ▸ Φ.trace_nonincreasing)

/-- Precise Gate-3 negation: there is a Choi-summable TNI family at fiber `2`
and a TNI family into fiber `2` whose joint compositions admit no
`Superoperator` Choi sum. -/
theorem exists_fiber2_comp_without_superoperator_sum :
    ∃ (f : Bool → Superoperator 2 1) (Ψ : Superoperator 2 1)
      (g : Bool → Superoperator 1 2),
      HasSum f Ψ ∧
        ¬ ∃ Φ : Superoperator 1 1,
            HasSum (fun i => Superoperator.comp (f i) (g i)) Φ := by
  refine
    ⟨fun i => bif i then e0 else e1, discardTwo,
      fun i => bif i then p0 else p1,
      complementaryBasisEffects_hasSum_discard, ?_⟩
  exact not_exists_hasSum_gate3Composed

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

/-- Joint precomposition of ambient CP maps against TNI maps into an
arbitrary fiber dimension `d`.  No TNI obligation is placed on the result
(unlike `ChoiSum.comp_from_one`, which is fiber-`1` only). -/
theorem comp_from_dim {ι : Type} [Countable ι] {m d ℓ : ℕ}
    {f : ι → CPMap d ℓ} {Ψ : CPMap d ℓ}
    (g : ι → Superoperator m d) (hf : HasSum f Ψ) :
    ∃ Χ : CPMap m ℓ,
      HasSum (fun i => CPMap.comp (f i) (g i).cp) Χ := by
  classical
  have hentries (a b : Fin ℓ) (i j : Fin m) :
      Summable fun k : ι =>
        (CPMap.comp (f k) (g k).cp).choi (a, i) (b, j) := by
    have hsum :
        Summable fun k : ι =>
          ∑ x : Fin d, ∑ y : Fin d,
            ‖(f k).choi (a, x) (b, y)‖ * ((m : ℕ) : ℝ) := by
      apply summable_sum
      intro x _
      apply summable_sum
      intro y _
      exact
        ((((Pi.hasSum.mp (Pi.hasSum.mp hf (a, x)) (b, y))).summable.norm).mul_right
          ((m : ℕ) : ℝ))
    refine Summable.of_norm_bounded hsum fun k => ?_
    simp only [CPMap.choi_comp_apply]
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro x _
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro y _
    rw [norm_mul]
    have hb :=
      ChoiSum.entry_norm_le_trace_re (g k).cp.choi_pos (x, i) (y, j)
    have htr := ChoiSum.trace_choi_re_le_input_dim (g k)
    exact mul_le_mul_of_nonneg_left (hb.trans htr) (norm_nonneg _)
  have hmat :
      Summable fun k : ι => (CPMap.comp (f k) (g k).cp).choi := by
    refine Pi.summable.mpr fun ai => Pi.summable.mpr fun bj => ?_
    rcases ai with ⟨a, i⟩; rcases bj with ⟨b, j⟩
    exact hentries a b i j
  exact ⟨⟨∑' k, (CPMap.comp (f k) (g k).cp).choi,
    ChoiSum.hasSum_posSemidef hmat.hasSum fun k =>
      (CPMap.comp (f k) (g k).cp).choi_pos⟩, hmat.hasSum⟩

end SigmaMon.CPMapSum

end QLambda.Domain.Presheaf
