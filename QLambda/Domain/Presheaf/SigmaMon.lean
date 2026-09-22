/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Superoperator

/-!
# Partial countable sums of superoperators

`PartialCountableSum` records the actual Tsukada--Asada laws for relational
partial countable sums: uniqueness, empty and singleton sums, zero removal,
reindexing, and the Kleene-equality form of countable associativity.

For finite-dimensional superoperators, `ChoiSum.HasSum` is the mathematically
natural candidate: unconditional convergence of the intrinsic positive Choi
matrices to the Choi matrix of the result.  This file proves uniqueness,
empty/singleton, zero-removal, reindexing, and both directions of regrouping
using finite-dimensional absolute summability and positivity.  The crucial
analytic step bounds the norm of every entry of a positive Choi matrix by its
trace, reducing countable regrouping to Tonelli's theorem for nonnegative real
series.

The old eventually-zero construction remains under `FiniteSupport`; it is a
helper, not the full Σ-monoid structure.
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder

namespace SigmaMon

universe u

/-- A genuine relational partial countable-sum algebra.  The associativity
field is an `Iff`, corresponding to Kleene equality of the nested and
flattened partial expressions. -/
structure PartialCountableSum (α : Type u) [Zero α] where
  HasSum : {ι : Type} → [Countable ι] → (ι → α) → α → Prop
  unique : ∀ {ι : Type} [Countable ι] {f : ι → α} {a b : α},
    HasSum f a → HasSum f b → a = b
  empty : HasSum (fun i : Empty => nomatch i) 0
  singleton : ∀ (a : α), HasSum (fun _ : PUnit => a) a
  remove_zero : ∀ {ι : Type} [Countable ι] (f : ι → α)
    (s : Set ι) (a : α), (∀ i, i ∉ s → f i = 0) →
      (HasSum (fun i : s => f i) a ↔ HasSum f a)
  reindex : ∀ {ι κ : Type} [Countable ι] [Countable κ]
    (e : κ ≃ ι) (f : ι → α) (a : α),
      HasSum (f ∘ e) a ↔ HasSum f a
  flatten : ∀ {ι : Type} [Countable ι] {κ : ι → Type}
    [∀ i, Countable (κ i)] (f : (i : ι) → κ i → α) (a : α),
      (HasSum (fun p : Σ i, κ i => f p.1 p.2) a ↔
        ∃ g : ι → α, (∀ i, HasSum (f i) (g i)) ∧ HasSum g a)

namespace ChoiSum

variable {n m : ℕ}

/-- A family of TNI superoperators has sum `Φ` when its intrinsic Choi
matrices converge unconditionally to `Φ`'s Choi matrix. -/
def HasSum {ι : Type} [Countable ι]
    (f : ι → Superoperator n m) (Φ : Superoperator n m) : Prop :=
  _root_.HasSum (fun i => (f i).cp.choi) Φ.cp.choi

theorem unique {ι : Type} [Countable ι] {f : ι → Superoperator n m}
    {Φ Ψ : Superoperator n m} (hΦ : HasSum f Φ) (hΨ : HasSum f Ψ) :
    Φ = Ψ := by
  apply Superoperator.ext
  apply CPMap.ext
  exact hΦ.unique hΨ

theorem empty :
    HasSum (fun i : Empty => nomatch i) (0 : Superoperator n m) := by
  exact hasSum_empty

theorem singleton (Φ : Superoperator n m) :
    HasSum (fun _ : PUnit => Φ) Φ := by
  exact hasSum_single PUnit.unit
    (fun i hi => (hi (Subsingleton.elim i PUnit.unit)).elim)

theorem remove_zero {ι : Type} [Countable ι]
    (f : ι → Superoperator n m) (s : Set ι) (Φ : Superoperator n m)
    (hzero : ∀ i, i ∉ s → f i = 0) :
    HasSum (fun i : s => f i) Φ ↔ HasSum f Φ := by
  change
    _root_.HasSum
        ((fun i => (f i).cp.choi) ∘ (fun i : s => (i : ι))) Φ.cp.choi ↔
      _root_.HasSum (fun i => (f i).cp.choi) Φ.cp.choi
  apply Subtype.val_injective.hasSum_iff
  intro i hi
  have his : i ∉ s := by
    simpa using hi
  rw [hzero i his]
  rfl

theorem reindex {ι κ : Type} [Countable ι] [Countable κ]
    (e : κ ≃ ι) (f : ι → Superoperator n m) (Φ : Superoperator n m) :
    HasSum (f ∘ e) Φ ↔ HasSum f Φ := by
  change
    _root_.HasSum ((fun i => (f i).cp.choi) ∘ e) Φ.cp.choi ↔
      _root_.HasSum (fun i => (f i).cp.choi) Φ.cp.choi
  exact e.hasSum_iff

/-- Tensoring on the right preserves every defined Choi sum. -/
theorem tensor_hasSum_left {ι : Type} [Countable ι]
    {f : ι → Superoperator n m} {Φ : Superoperator n m}
    (h : HasSum f Φ) (Ψ : Superoperator ℓ r) :
    HasSum (fun i => Superoperator.tensor (f i) Ψ)
      (Superoperator.tensor Φ Ψ) := by
  let T : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin (m * r) × Fin (n * ℓ))
        (Fin (m * r) × Fin (n * ℓ)) ℂ :=
    { toFun := fun A =>
        Matrix.reindex (CPMap.choiTensorEquiv n m ℓ r)
          (CPMap.choiTensorEquiv n m ℓ r) (A ⊗ₖ Ψ.cp.choi)
      map_add' := by
        intro A B
        ext i j
        simp [Matrix.reindex_apply, Matrix.add_kronecker]
      map_smul' := by
        intro c A
        ext i j
        simp [Matrix.reindex_apply, Matrix.smul_kronecker] }
  change _root_.HasSum (fun i => T (f i).cp.choi) (T Φ.cp.choi)
  exact h.map T (LinearMap.continuous_of_finiteDimensional T)

/-- Tensoring on the left preserves every defined Choi sum. -/
theorem tensor_hasSum_right {ι : Type} [Countable ι]
    (Φ : Superoperator n m) {f : ι → Superoperator ℓ r}
    {Ψ : Superoperator ℓ r} (h : HasSum f Ψ) :
    HasSum (fun i => Superoperator.tensor Φ (f i))
      (Superoperator.tensor Φ Ψ) := by
  let T : Matrix (Fin r × Fin ℓ) (Fin r × Fin ℓ) ℂ →ₗ[ℂ]
      Matrix (Fin (m * r) × Fin (n * ℓ))
        (Fin (m * r) × Fin (n * ℓ)) ℂ :=
    { toFun := fun A =>
        Matrix.reindex (CPMap.choiTensorEquiv n m ℓ r)
          (CPMap.choiTensorEquiv n m ℓ r) (Φ.cp.choi ⊗ₖ A)
      map_add' := by
        intro A B
        ext i j
        simp [Matrix.reindex_apply, Matrix.kronecker_add]
      map_smul' := by
        intro c A
        ext i j
        simp [Matrix.reindex_apply, Matrix.kronecker_smul] }
  change _root_.HasSum (fun i => T (f i).cp.choi) (T Ψ.cp.choi)
  exact h.map T (LinearMap.continuous_of_finiteDimensional T)

/-- The unconditional sum of a flattened positive family can be regrouped
into any countable family of already-defined row sums. -/
theorem group {ι : Type} [Countable ι] {κ : ι → Type}
    [∀ i, Countable (κ i)] (f : (i : ι) → κ i → Superoperator n m)
    (g : ι → Superoperator n m) (Φ : Superoperator n m)
    (hflat : HasSum (fun p : Σ i, κ i => f p.1 p.2) Φ)
    (hrows : ∀ i, HasSum (f i) (g i)) :
    HasSum g Φ :=
  _root_.HasSum.sigma hflat hrows

/-- Conversely, row sums can be flattened when absolute/unconditional
summability of the flattened Choi family has been established. -/
theorem flatten_of_summable {ι : Type} [Countable ι] {κ : ι → Type}
    [∀ i, Countable (κ i)] (f : (i : ι) → κ i → Superoperator n m)
    (g : ι → Superoperator n m) (Φ : Superoperator n m)
    (hrows : ∀ i, HasSum (f i) (g i)) (hg : HasSum g Φ)
    (hflat : Summable (fun p : Σ i, κ i => (f p.1 p.2).cp.choi)) :
    HasSum (fun p : Σ i, κ i => f p.1 p.2) Φ :=
  _root_.HasSum.sigma_of_hasSum hg hrows hflat

theorem diag_re_nonneg {q : Type} [Fintype q]
    {A : Matrix q q ℂ} (hA : A.PosSemidef) (i : q) :
    0 ≤ (A i i).re :=
  (RCLike.nonneg_iff.mp hA.diag_nonneg).1

theorem diag_im_eq_zero {q : Type} [Fintype q]
    {A : Matrix q q ℂ} (hA : A.PosSemidef) (i : q) :
    (A i i).im = 0 :=
  (RCLike.nonneg_iff.mp hA.diag_nonneg).2

theorem diag_re_le_trace_re {q : Type} [Fintype q]
    {A : Matrix q q ℂ} (hA : A.PosSemidef) (i : q) :
    (A i i).re ≤ A.trace.re := by
  rw [show A.trace.re = ∑ j, (A j j).re by simp [Matrix.trace]]
  exact Finset.single_le_sum
    (fun j _ => diag_re_nonneg hA j) (Finset.mem_univ i)

theorem trace_re_nonneg {q : Type} [Fintype q]
    {A : Matrix q q ℂ} (hA : A.PosSemidef) :
    0 ≤ A.trace.re :=
  (RCLike.nonneg_iff.mp hA.trace_nonneg).1

/-- Every entry of a positive semidefinite matrix is bounded by its trace.
This is the finite-dimensional order-unit estimate used below to turn
trace summability into norm summability. -/
theorem entry_norm_le_trace_re {q : Type} [Fintype q] [DecidableEq q]
    {A : Matrix q q ℂ} (hA : A.PosSemidef) (i j : q) :
    ‖A i j‖ ≤ A.trace.re := by
  let e : Fin 2 → q := ![i, j]
  have hdet_re := (RCLike.nonneg_iff.mp (hA.submatrix e).det_nonneg).1
  rw [Matrix.det_fin_two] at hdet_re
  simp only [Matrix.submatrix_apply, e, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hdet_re
  have hherm : A j i = star (A i j) := by
    rw [← hA.isHermitian.apply]
  rw [hherm] at hdet_re
  change 0 ≤ (A i i * A j j - A i j * star (A i j)).re at hdet_re
  rw [Complex.sub_re] at hdet_re
  have hmul :
      (A i j * star (A i j)).re = Complex.normSq (A i j) := by
    change (A i j * (starRingEnd ℂ) (A i j)).re = _
    rw [Complex.mul_conj]
    simp
  rw [hmul, Complex.mul_re, diag_im_eq_zero hA i,
    diag_im_eq_zero hA j, Complex.normSq_apply] at hdet_re
  simp only [mul_zero, sub_zero] at hdet_re
  have hii := diag_re_nonneg hA i
  have hjj := diag_re_nonneg hA j
  have hit := diag_re_le_trace_re hA i
  have hjt := diag_re_le_trace_re hA j
  have htr := trace_re_nonneg hA
  have hsq := Complex.sq_norm (A i j)
  rw [Complex.normSq_apply] at hsq
  have hprod :
      (A i i).re * (A j j).re ≤ A.trace.re ^ 2 := by
    nlinarith
  have hnormsq : ‖A i j‖ ^ 2 ≤ A.trace.re ^ 2 := by
    nlinarith
  nlinarith [norm_nonneg (A i j)]

theorem hasSum_trace_re {ι q : Type} [Fintype q]
    {f : ι → Matrix q q ℂ} {A : Matrix q q ℂ}
    (hf : _root_.HasSum f A) :
    _root_.HasSum (fun i => (f i).trace.re) A.trace.re := by
  have hc : _root_.HasSum (fun i => (f i).trace) A.trace := by
    convert hf.map (Matrix.traceLinearMap q ℂ ℂ)
      (LinearMap.continuous_of_finiteDimensional _) using 1 <;> rfl
  convert hc.map Complex.reCLM Complex.reCLM.continuous using 1 <;> rfl

/-- The positive semidefinite cone of finite complex matrices is closed under
unconditional sums. -/
theorem hasSum_posSemidef {ι q : Type} [Fintype q]
    {f : ι → Matrix q q ℂ} {A : Matrix q q ℂ}
    (hf : _root_.HasSum f A) (hp : ∀ i, (f i).PosSemidef) :
    A.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    have hij : _root_.HasSum (fun k => f k i j) (A i j) :=
      Pi.hasSum.mp (Pi.hasSum.mp hf i) j
    have hji : _root_.HasSum (fun k => f k j i) (A j i) :=
      Pi.hasSum.mp (Pi.hasSum.mp hf j) i
    have hs : _root_.HasSum (fun k => f k i j) (star (A j i)) :=
      hji.star.congr_fun fun k => (hp k).isHermitian.apply i j |>.symm
    exact hs.unique hij
  · intro x
    have hentry (i j : q) :
        _root_.HasSum (fun k => f k i j) (A i j) :=
      Pi.hasSum.mp (Pi.hasSum.mp hf i) j
    have hterm (i j : q) :
        _root_.HasSum (fun k => star (x i) * f k i j * x j)
          (star (x i) * A i j * x j) :=
      ((hentry i j).mul_left (star (x i))).mul_right (x j)
    have hsraw :
        _root_.HasSum
          (fun k => ∑ i, ∑ j, star (x i) * f k i j * x j)
          (∑ i, ∑ j, star (x i) * A i j * x j) :=
      hasSum_sum fun i _ => hasSum_sum fun j _ => hterm i j
    have hs :
        _root_.HasSum (fun k => star x ⬝ᵥ (f k *ᵥ x))
          (star x ⬝ᵥ (A *ᵥ x)) := by
      simpa only [dotProduct, mulVec, Finset.mul_sum, mul_assoc,
        Pi.star_apply] using hsraw
    apply RCLike.nonneg_iff.mpr
    constructor
    · exact HasSum.nonneg (fun k => (hp k).re_dotProduct_nonneg x)
        ((Complex.hasSum_iff _ _).mp hs).1
    · have him := ((Complex.hasSum_iff _ _).mp hs).2
      apply him.unique
      exact hasSum_zero.congr_fun fun k =>
        (RCLike.nonneg_iff.mp ((hp k).dotProduct_mulVec_nonneg x)).2

private noncomputable def rowEquiv {ι : Type} {κ : ι → Type} (i : ι) :
    κ i ≃ {p : Σ i, κ i // p.1 = i} where
  toFun j := ⟨⟨i, j⟩, rfl⟩
  invFun p := by
    rcases p with ⟨⟨i', j⟩, h⟩
    change i' = i at h
    cases h
    exact j
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨i', j⟩, h⟩
    change i' = i at h
    cases h
    rfl

/-- Closure under countable subfamilies is one of the two finite-dimensional
positivity facts needed for full countable associativity. -/
def SubfamilyClosed : Prop :=
  ∀ {ι : Type} [Countable ι] {κ : ι → Type}
    [∀ i, Countable (κ i)] (f : (i : ι) → κ i → Superoperator n m)
    (Φ : Superoperator n m),
      HasSum (fun p : Σ i, κ i => f p.1 p.2) Φ →
        ∀ i, ∃ Ψ, HasSum (f i) Ψ

/-- Regrouping completeness is the second positivity fact: summable
positive rows with a summable family of row sums have a summable flattening. -/
def RegroupingComplete : Prop :=
  ∀ {ι : Type} [Countable ι] {κ : ι → Type}
    [∀ i, Countable (κ i)] (f : (i : ι) → κ i → Superoperator n m)
    (g : ι → Superoperator n m),
      (∀ i, HasSum (f i) (g i)) →
        Summable (fun i => (g i).cp.choi) →
        Summable (fun p : Σ i, κ i => (f p.1 p.2).cp.choi)

/-- Countable subfamilies of a convergent family of positive Choi matrices
again converge to a trace-nonincreasing completely positive map. -/
theorem subfamilyClosed : SubfamilyClosed (n := n) (m := m) := by
  classical
  intro ι _ κ _ f Φ hflat i
  let F : (Σ i, κ i) → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
    fun p => (f p.1 p.2).cp.choi
  have hF : _root_.HasSum F Φ.cp.choi := hflat
  have hFs : Summable F := hF.summable
  have hinj : Function.Injective (fun j : κ i => Sigma.mk i j) := by
    intro a b h
    exact eq_of_heq (Sigma.mk.inj h).2
  have hrow : Summable (fun j : κ i => (f i j).cp.choi) := by
    simpa [F, Function.comp_def] using hFs.comp_injective hinj
  let A := ∑' j : κ i, (f i j).cp.choi
  have hA : _root_.HasSum (fun j : κ i => (f i j).cp.choi) A :=
    hrow.hasSum
  have hApos : A.PosSemidef :=
    hasSum_posSemidef hA (fun j => (f i j).cp.choi_pos)
  let B := ∑' p : Set.compl {p : Σ i, κ i | p.1 = i}, F p
  have hcomp :
      Summable
        (fun p : Set.compl {p : Σ i, κ i | p.1 = i} => F p) :=
    hFs.subtype _
  have hBpos : B.PosSemidef :=
    hasSum_posSemidef hcomp.hasSum (fun p => (f p.1.1 p.1.2).cp.choi_pos)
  have hrow_subtype :
      A = ∑' p : {p : Σ i, κ i // p.1 = i}, F p := by
    simpa [A, F, rowEquiv] using
      (rowEquiv i).tsum_eq
        (fun p : {p : Σ i, κ i // p.1 = i} => F p)
  have hAB : A + B = Φ.cp.choi := by
    rw [hrow_subtype]
    have hdecomp :=
      hFs.tsum_subtype_add_tsum_subtype_compl
        {p : Σ i, κ i | p.1 = i}
    change
      (∑' p : {p : Σ i, κ i // p.1 = i}, F p) + B =
        ∑' p, F p at hdecomp
    exact hdecomp.trans hF.tsum_eq
  let Ψcp : CPMap n m := ⟨A, hApos⟩
  let Χcp : CPMap n m := ⟨B, hBpos⟩
  have hcp : Ψcp + Χcp = Φ.cp := by
    apply CPMap.ext
    exact hAB
  let Ψ : Superoperator n m :=
    { cp := Ψcp
      trace_nonincreasing := by
        intro ρ hρ
        have hΧpos := CPMap.applyMat_posSemidef Χcp hρ
        have hΧtr := (RCLike.nonneg_iff.mp hΧpos.trace_nonneg).1
        have happly :
            Φ.cp.applyMat ρ = Ψcp.applyMat ρ + Χcp.applyMat ρ := by
          rw [← hcp, CPMap.applyMat_add_map]
        calc
          (Matrix.trace (Ψcp.applyMat ρ)).re
              ≤ (Matrix.trace
                  (Ψcp.applyMat ρ + Χcp.applyMat ρ)).re := by
                rw [Matrix.trace_add, Complex.add_re]
                exact le_add_of_nonneg_right hΧtr
          _ = (Matrix.trace (Φ.cp.applyMat ρ)).re := by
                rw [← happly]
          _ ≤ (Matrix.trace ρ).re :=
                Φ.trace_nonincreasing ρ hρ }
  exact ⟨Ψ, hA⟩

/-- Every countable subfamily of a defined Choi sum has a defined TNI sum.
This direct form is convenient for finite approximants and branch
selection. -/
theorem subfamily_hasSum {ι : Type} [Countable ι]
    {f : ι → Superoperator n m} {Φ : Superoperator n m}
    (hΦ : HasSum f Φ) (s : Set ι) :
    ∃ Ψ : Superoperator n m, HasSum (fun i : s => f i) Ψ := by
  classical
  let F : ι → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
    fun i => (f i).cp.choi
  have hF : _root_.HasSum F Φ.cp.choi := hΦ
  have hFs : Summable F := hF.summable
  let A := ∑' i : s, F i
  let B := ∑' i : (sᶜ : Set ι), F i
  have hAs : Summable (fun i : s => F i) := hFs.subtype s
  have hBs : Summable (fun i : (sᶜ : Set ι) => F i) :=
    hFs.subtype sᶜ
  have hA : _root_.HasSum (fun i : s => F i) A := hAs.hasSum
  have hB : _root_.HasSum (fun i : (sᶜ : Set ι) => F i) B :=
    hBs.hasSum
  have hApos : A.PosSemidef :=
    hasSum_posSemidef hA (fun i => (f i).cp.choi_pos)
  have hBpos : B.PosSemidef :=
    hasSum_posSemidef hB (fun i => (f i).cp.choi_pos)
  have hAB : A + B = Φ.cp.choi := by
    have hdecomp := hFs.tsum_subtype_add_tsum_subtype_compl s
    calc
      A + B = ∑' i, F i := by simpa [A, B] using hdecomp
      _ = Φ.cp.choi := hF.tsum_eq
  let Ψcp : CPMap n m := ⟨A, hApos⟩
  let Χcp : CPMap n m := ⟨B, hBpos⟩
  have hcp : Ψcp + Χcp = Φ.cp := by
    apply CPMap.ext
    exact hAB
  let Ψ : Superoperator n m :=
    { cp := Ψcp
      trace_nonincreasing := by
        intro ρ hρ
        have hΧpos := CPMap.applyMat_posSemidef Χcp hρ
        have hΧtr := (RCLike.nonneg_iff.mp hΧpos.trace_nonneg).1
        have happly :
            Φ.cp.applyMat ρ =
              Ψcp.applyMat ρ + Χcp.applyMat ρ := by
          rw [← hcp, CPMap.applyMat_add_map]
        calc
          (Matrix.trace (Ψcp.applyMat ρ)).re
              ≤ (Matrix.trace
                  (Ψcp.applyMat ρ + Χcp.applyMat ρ)).re := by
                rw [Matrix.trace_add, Complex.add_re]
                exact le_add_of_nonneg_right hΧtr
          _ = (Matrix.trace (Φ.cp.applyMat ρ)).re := by
                rw [← happly]
          _ ≤ (Matrix.trace ρ).re :=
                Φ.trace_nonincreasing ρ hρ }
  refine ⟨Ψ, ?_⟩
  exact hA

/-- Every finite approximant of a defined countable Choi sum is itself a
defined TNI sum. -/
theorem finite_subfamily_hasSum {ι : Type} [Countable ι]
    {f : ι → Superoperator n m} {Φ : Superoperator n m}
    (hΦ : HasSum f Φ) (s : Finset ι) :
    ∃ Ψ : Superoperator n m,
      HasSum (fun i : {i // i ∈ s} => f i) Ψ :=
  subfamily_hasSum hΦ {i | i ∈ s}

private theorem choi_finset_sum {ι : Type} [DecidableEq ι]
    (s : Finset ι) (f : ι → CPMap n m) :
    (∑ i ∈ s, f i).choi = ∑ i ∈ s, (f i).choi := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

/-- The intrinsic CP map of a finite approximant is the ordinary finite sum
of the selected branch CP maps. -/
theorem finite_subfamily_cp_sum {ι : Type} [Countable ι]
    {f : ι → Superoperator n m} {Φ : Superoperator n m}
    (hΦ : HasSum f Φ) (s : Finset ι) :
    ∃ Ψ : Superoperator n m,
      Ψ.cp = ∑ i ∈ s, (f i).cp := by
  classical
  obtain ⟨Ψ, hΨ⟩ := finite_subfamily_hasSum hΦ s
  refine ⟨Ψ, ?_⟩
  apply CPMap.ext
  have ht :
      (∑' i : {i // i ∈ s}, (f i).cp.choi) = Ψ.cp.choi :=
    hΨ.tsum_eq
  calc
    Ψ.cp.choi =
        ∑ i : {i // i ∈ s}, (f i).cp.choi := by
          rw [← ht, tsum_fintype]
    _ = (∑ i : {i // i ∈ s}, (f i).cp).choi := by
          exact (choi_finset_sum Finset.univ
            (fun i : {i // i ∈ s} => (f i).cp)).symm
    _ = (∑ i ∈ s, (f i).cp).choi := by
          rw [Finset.sum_subtype (p := fun i => i ∈ s)]
          simp

/-- Positive row sums cannot hide conditional cancellation: scalar Tonelli
for their nonnegative traces, together with the PSD trace bound, makes the
flattened Choi family summable. -/
theorem regroupingComplete :
    RegroupingComplete (n := n) (m := m) := by
  intro ι _ κ _ f g hrows hg
  let T : (p : Σ i, κ i) → ℝ :=
    fun p => (Matrix.trace (f p.1 p.2).cp.choi).re
  have hTnonneg : ∀ p, 0 ≤ T p :=
    fun p => trace_re_nonneg (f p.1 p.2).cp.choi_pos
  have hrowTrace (i : ι) :
      _root_.HasSum (fun j => T ⟨i, j⟩)
        (Matrix.trace (g i).cp.choi).re :=
    hasSum_trace_re (hrows i)
  have hgTrace :
      Summable (fun i => (Matrix.trace (g i).cp.choi).re) := by
    rcases hg with ⟨G, hG⟩
    exact (hasSum_trace_re hG).summable
  have hT : Summable T := by
    apply (summable_sigma_of_nonneg hTnonneg).2
    refine ⟨fun i => (hrowTrace i).summable, ?_⟩
    exact hgTrace.congr fun i => (hrowTrace i).tsum_eq.symm
  apply Pi.summable.mpr
  intro a
  apply Pi.summable.mpr
  intro b
  apply Summable.of_norm_bounded hT
  intro p
  exact entry_norm_le_trace_re (f p.1 p.2).cp.choi_pos a b

/-- Package the Choi relation once subfamily closure and regrouping
completeness have been proved. -/
def partialCountableSum (hsub : SubfamilyClosed (n := n) (m := m))
    (hregroup : RegroupingComplete (n := n) (m := m)) :
    PartialCountableSum (Superoperator n m) where
  HasSum := HasSum
  unique := unique
  empty := empty
  singleton := singleton
  remove_zero := remove_zero
  reindex := reindex
  flatten := by
    intro ι _ κ _ f Φ
    constructor
    · intro hflat
      choose g hg using fun i => hsub f Φ hflat i
      exact ⟨g, hg, group f g Φ hflat hg⟩
    · rintro ⟨g, hrows, hg⟩
      exact flatten_of_summable f g Φ hrows hg
        (hregroup f g hrows hg.summable)

end ChoiSum

/-! Partial countable sums in the ambient cone of all completely positive
maps.  Unlike `ChoiSum`, this relation carries no trace-nonincreasing bound. -/
namespace CPMapSum

variable {n m : ℕ}

def HasSum {ι : Type} [Countable ι]
    (f : ι → CPMap n m) (Φ : CPMap n m) : Prop :=
  _root_.HasSum (fun i => (f i).choi) Φ.choi

theorem unique {ι : Type} [Countable ι] {f : ι → CPMap n m}
    {Φ Ψ : CPMap n m} (hΦ : HasSum f Φ) (hΨ : HasSum f Ψ) :
    Φ = Ψ :=
  CPMap.ext (hΦ.unique hΨ)

theorem empty :
    HasSum (fun i : Empty => nomatch i) (0 : CPMap n m) :=
  hasSum_empty

theorem singleton (Φ : CPMap n m) :
    HasSum (fun _ : PUnit => Φ) Φ :=
  hasSum_single PUnit.unit
    (fun i hi => (hi (Subsingleton.elim i PUnit.unit)).elim)

theorem remove_zero {ι : Type} [Countable ι]
    (f : ι → CPMap n m) (s : Set ι) (Φ : CPMap n m)
    (hzero : ∀ i, i ∉ s → f i = 0) :
    HasSum (fun i : s => f i) Φ ↔ HasSum f Φ := by
  change
    _root_.HasSum
        ((fun i => (f i).choi) ∘ (fun i : s => (i : ι))) Φ.choi ↔
      _root_.HasSum (fun i => (f i).choi) Φ.choi
  apply Subtype.val_injective.hasSum_iff
  intro i hi
  rw [hzero i (by simpa using hi)]
  rfl

theorem reindex {ι κ : Type} [Countable ι] [Countable κ]
    (e : κ ≃ ι) (f : ι → CPMap n m) (Φ : CPMap n m) :
    HasSum (f ∘ e) Φ ↔ HasSum f Φ := by
  change
    _root_.HasSum ((fun i => (f i).choi) ∘ e) Φ.choi ↔
      _root_.HasSum (fun i => (f i).choi) Φ.choi
  exact e.hasSum_iff

theorem group {ι : Type} [Countable ι] {κ : ι → Type}
    [∀ i, Countable (κ i)] (f : (i : ι) → κ i → CPMap n m)
    (g : ι → CPMap n m) (Φ : CPMap n m)
    (hflat : HasSum (fun p : Σ i, κ i => f p.1 p.2) Φ)
    (hrows : ∀ i, HasSum (f i) (g i)) :
    HasSum g Φ :=
  _root_.HasSum.sigma hflat hrows

theorem flatten_of_summable {ι : Type} [Countable ι] {κ : ι → Type}
    [∀ i, Countable (κ i)] (f : (i : ι) → κ i → CPMap n m)
    (g : ι → CPMap n m) (Φ : CPMap n m)
    (hrows : ∀ i, HasSum (f i) (g i)) (hg : HasSum g Φ)
    (hflat : Summable (fun p : Σ i, κ i => (f p.1 p.2).choi)) :
    HasSum (fun p : Σ i, κ i => f p.1 p.2) Φ :=
  _root_.HasSum.sigma_of_hasSum hg hrows hflat

def SubfamilyClosed : Prop :=
  ∀ {ι : Type} [Countable ι] {κ : ι → Type}
    [∀ i, Countable (κ i)] (f : (i : ι) → κ i → CPMap n m)
    (Φ : CPMap n m),
      HasSum (fun p : Σ i, κ i => f p.1 p.2) Φ →
        ∀ i, ∃ Ψ, HasSum (f i) Ψ

def RegroupingComplete : Prop :=
  ∀ {ι : Type} [Countable ι] {κ : ι → Type}
    [∀ i, Countable (κ i)] (f : (i : ι) → κ i → CPMap n m)
    (g : ι → CPMap n m),
      (∀ i, HasSum (f i) (g i)) →
        Summable (fun i => (g i).choi) →
        Summable (fun p : Σ i, κ i => (f p.1 p.2).choi)

theorem subfamilyClosed : SubfamilyClosed (n := n) (m := m) := by
  classical
  intro ι _ κ _ f Φ hflat i
  let F : (Σ i, κ i) → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
    fun p => (f p.1 p.2).choi
  have hF : _root_.HasSum F Φ.choi := hflat
  have hFs : Summable F := hF.summable
  have hinj : Function.Injective (fun j : κ i => Sigma.mk i j) := by
    intro a b h
    exact eq_of_heq (Sigma.mk.inj h).2
  have hrow : Summable (fun j : κ i => (f i j).choi) := by
    simpa [F, Function.comp_def] using hFs.comp_injective hinj
  let A := ∑' j : κ i, (f i j).choi
  have hA : _root_.HasSum (fun j : κ i => (f i j).choi) A :=
    hrow.hasSum
  have hApos : A.PosSemidef :=
    ChoiSum.hasSum_posSemidef hA (fun j => (f i j).choi_pos)
  exact ⟨⟨A, hApos⟩, hA⟩

theorem regroupingComplete :
    RegroupingComplete (n := n) (m := m) := by
  intro ι _ κ _ f g hrows hg
  let T : (p : Σ i, κ i) → ℝ :=
    fun p => (Matrix.trace (f p.1 p.2).choi).re
  have hTnonneg : ∀ p, 0 ≤ T p :=
    fun p => ChoiSum.trace_re_nonneg (f p.1 p.2).choi_pos
  have hrowTrace (i : ι) :
      _root_.HasSum (fun j => T ⟨i, j⟩)
        (Matrix.trace (g i).choi).re :=
    ChoiSum.hasSum_trace_re (hrows i)
  have hgTrace :
      Summable (fun i => (Matrix.trace (g i).choi).re) := by
    rcases hg with ⟨G, hG⟩
    exact (ChoiSum.hasSum_trace_re hG).summable
  have hT : Summable T := by
    apply (summable_sigma_of_nonneg hTnonneg).2
    refine ⟨fun i => (hrowTrace i).summable, ?_⟩
    exact hgTrace.congr fun i => (hrowTrace i).tsum_eq.symm
  apply Pi.summable.mpr
  intro a
  apply Pi.summable.mpr
  intro b
  apply Summable.of_norm_bounded hT
  intro p
  exact ChoiSum.entry_norm_le_trace_re
    (f p.1 p.2).choi_pos a b

def partialCountableSum
    (hsub : SubfamilyClosed (n := n) (m := m))
    (hregroup : RegroupingComplete (n := n) (m := m)) :
    PartialCountableSum (CPMap n m) where
  HasSum := HasSum
  unique := unique
  empty := empty
  singleton := singleton
  remove_zero := remove_zero
  reindex := reindex
  flatten := by
    intro ι _ κ _ f Φ
    constructor
    · intro hflat
      choose g hg using fun i => hsub f Φ hflat i
      exact ⟨g, hg, group f g Φ hflat hg⟩
    · rintro ⟨g, hrows, hg⟩
      exact flatten_of_summable f g Φ hrows hg
        (hregroup f g hrows hg.summable)

end CPMapSum

/-- The premise-free partial countable sums of unrestricted intrinsic CP
maps, used as the ambient module for pseudo-representable coefficients. -/
noncomputable def cpMapPartialCountableSum :
    PartialCountableSum (CPMap n m) :=
  CPMapSum.partialCountableSum CPMapSum.subfamilyClosed
    CPMapSum.regroupingComplete

/-- The premise-free partial countable-sum structure on finite-dimensional
trace-nonincreasing superoperators. -/
noncomputable def superoperatorPartialCountableSum :
    PartialCountableSum (Superoperator n m) :=
  ChoiSum.partialCountableSum ChoiSum.subfamilyClosed
    ChoiSum.regroupingComplete

namespace ChoiSum

/-- The tensor product of two jointly TNI countable branch families is again
a jointly TNI countable family.  The result includes entangled ancillary
inputs because `Superoperator.tensor` is intrinsically TNI and the proof uses
the full Choi sums, not pointwise state factorization. -/
theorem tensor_hasSum {ι κ : Type} [Countable ι] [Countable κ]
    {f : ι → Superoperator n m} {Φ : Superoperator n m}
    {g : κ → Superoperator ℓ r} {Ψ : Superoperator ℓ r}
    (hf : HasSum f Φ) (hg : HasSum g Ψ) :
    HasSum
      (fun p : Σ _ : ι, κ => Superoperator.tensor (f p.1) (g p.2))
      (Superoperator.tensor Φ Ψ) := by
  exact
    (superoperatorPartialCountableSum.flatten
      (fun i j => Superoperator.tensor (f i) (g j))
      (Superoperator.tensor Φ Ψ)).mpr
        ⟨fun i => Superoperator.tensor (f i) Ψ,
          fun i => tensor_hasSum_right (f i) hg,
          tensor_hasSum_left hf Ψ⟩

/-- Every finite mixed tensor partition has exactly the ordinary CP sum as
its jointly TNI aggregate. -/
theorem tensor_finite_subfamily_cp_sum
    {ι κ : Type} [Countable ι] [Countable κ]
    {f : ι → Superoperator n m} {Φ : Superoperator n m}
    {g : κ → Superoperator ℓ r} {Ψ : Superoperator ℓ r}
    (hf : HasSum f Φ) (hg : HasSum g Ψ)
    (s : Finset (Σ _ : ι, κ)) :
    ∃ Χ : Superoperator (n * ℓ) (m * r),
      Χ.cp =
        ∑ p ∈ s,
          (Superoperator.tensor (f p.1) (g p.2)).cp :=
  finite_subfamily_cp_sum (tensor_hasSum hf hg) s

end ChoiSum

namespace FiniteSupport

variable {n m : ℕ}

/-- Two TNI maps are addable exactly when their CP sum remains TNI. -/
def Addable (Φ Ψ : Superoperator n m) : Prop :=
  TraceNonincreasing (Φ.cp + Ψ.cp)

/-- A defined binary sum. -/
def add (Φ Ψ : Superoperator n m) (h : Addable Φ Ψ) :
    Superoperator n m where
  cp := Φ.cp + Ψ.cp
  trace_nonincreasing := h

@[simp]
theorem cp_add (Φ Ψ : Superoperator n m) (h : Addable Φ Ψ) :
    (add Φ Ψ h).cp = Φ.cp + Ψ.cp :=
  rfl

theorem add_comm (Φ Ψ : Superoperator n m)
    (hΦΨ : Addable Φ Ψ) (hΨΦ : Addable Ψ Φ) :
    add Φ Ψ hΦΨ = add Ψ Φ hΨΦ := by
  apply Superoperator.ext
  exact _root_.add_comm Φ.cp Ψ.cp

theorem zero_addable (Φ : Superoperator n m) :
    Addable 0 Φ := by
  simpa [Addable] using Φ.trace_nonincreasing

theorem add_zeroable (Φ : Superoperator n m) :
    Addable Φ 0 := by
  simpa [Addable] using Φ.trace_nonincreasing

@[simp]
theorem add_zero (Φ : Superoperator n m) :
    add Φ 0 (add_zeroable Φ) = Φ := by
  apply Superoperator.ext
  simp

@[simp]
theorem zero_add (Φ : Superoperator n m) :
    add 0 Φ (zero_addable Φ) = Φ := by
  apply Superoperator.ext
  simp

theorem add_assoc (Φ Ψ Χ : Superoperator n m)
    (hΦΨ : Addable Φ Ψ)
    (hLeft : Addable (add Φ Ψ hΦΨ) Χ)
    (hΨΧ : Addable Ψ Χ)
    (hRight : Addable Φ (add Ψ Χ hΨΧ)) :
    add (add Φ Ψ hΦΨ) Χ hLeft =
      add Φ (add Ψ Χ hΨΧ) hRight := by
  apply Superoperator.ext
  exact _root_.add_assoc Φ.cp Ψ.cp Χ.cp

/-- The CP sum below a natural-number cutoff. -/
def cpSum (f : ℕ → Superoperator n m) (N : ℕ) : CPMap n m :=
  ∑ i ∈ Finset.range N, (f i).cp

/-- `N` supports `f` when every term at or above `N` is zero. -/
def SupportedAt (f : ℕ → Superoperator n m) (N : ℕ) : Prop :=
  ∀ i, N ≤ i → f i = 0

/-- Evidence that a countable family has a defined, finite-support TNI sum. -/
structure Summation (f : ℕ → Superoperator n m) where
  cutoff : ℕ
  supported : SupportedAt f cutoff
  trace_nonincreasing : TraceNonincreasing (cpSum f cutoff)

/-- The superoperator denoted by a supported summation witness. -/
def sum {f : ℕ → Superoperator n m} (h : Summation f) :
    Superoperator n m where
  cp := cpSum f h.cutoff
  trace_nonincreasing := h.trace_nonincreasing

@[simp]
theorem cp_sum {f : ℕ → Superoperator n m} (h : Summation f) :
    (sum h).cp = cpSum f h.cutoff :=
  rfl

private theorem cpSum_eq_of_supported {f : ℕ → Superoperator n m}
    {N M : ℕ} (hN : SupportedAt f N) (hM : SupportedAt f M) :
    cpSum f N = cpSum f M := by
  wlog hNM : N ≤ M generalizing N M
  · exact (this hM hN (le_of_not_ge hNM)).symm
  rw [cpSum, cpSum, ← Finset.sum_range_add_sum_Ico _ hNM]
  suffices (∑ i ∈ Finset.Ico N M, (f i).cp) = 0 by
    rw [this]
    exact (_root_.add_zero _).symm
  apply Finset.sum_eq_zero
  intro i hi
  rw [hN i (Finset.mem_Ico.mp hi).1]
  rfl

/-- Different valid support bounds produce the same sum. -/
theorem sum_eq {f : ℕ → Superoperator n m} (h k : Summation f) :
    sum h = sum k := by
  apply Superoperator.ext
  exact cpSum_eq_of_supported h.supported k.supported

/-- Pointwise-equal families transport summability evidence. -/
def congr {f g : ℕ → Superoperator n m} (h : Summation f)
    (hfg : ∀ i, f i = g i) : Summation g where
  cutoff := h.cutoff
  supported := by
    intro i hi
    rw [← hfg i]
    exact h.supported i hi
  trace_nonincreasing := by
    have hcp : cpSum g h.cutoff = cpSum f h.cutoff := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hfg i]
    rw [hcp]
    exact h.trace_nonincreasing

theorem sum_congr {f g : ℕ → Superoperator n m} (h : Summation f)
    (hfg : ∀ i, f i = g i) :
    sum (congr h hfg) = sum h := by
  apply Superoperator.ext
  change cpSum g h.cutoff = cpSum f h.cutoff
  unfold cpSum
  apply Finset.sum_congr rfl
  intro i _
  rw [← hfg i]

/-- The everywhere-zero family is summable. -/
def zeroSummation : Summation (fun _ : ℕ => (0 : Superoperator n m)) where
  cutoff := 0
  supported := by simp [SupportedAt]
  trace_nonincreasing := by
    simpa [cpSum] using (0 : Superoperator n m).trace_nonincreasing

@[simp]
theorem sum_zero : sum (zeroSummation : Summation
    (fun _ : ℕ => (0 : Superoperator n m))) = 0 := by
  apply Superoperator.ext
  rfl

/-- A countable family with one nonzero term. -/
def single (k : ℕ) (Φ : Superoperator n m) : ℕ → Superoperator n m :=
  fun i => if i = k then Φ else 0

@[simp]
theorem cpSum_single (k : ℕ) (Φ : Superoperator n m) :
    cpSum (single k Φ) (k + 1) = Φ.cp := by
  classical
  unfold cpSum
  rw [Finset.sum_eq_single k]
  · simp [single]
  · intro i hi hik
    simp [single, hik]
  · simp

/-- Every singleton family has a defined sum. -/
def singleSummation (k : ℕ) (Φ : Superoperator n m) :
    Summation (single k Φ) where
  cutoff := k + 1
  supported := by
    intro i hi
    simp only [single]
    split
    · rename_i hik
      subst i
      omega
    · rfl
  trace_nonincreasing := by
    rw [cpSum_single]
    exact Φ.trace_nonincreasing

@[simp]
theorem sum_single (k : ℕ) (Φ : Superoperator n m) :
    sum (singleSummation k Φ) = Φ := by
  apply Superoperator.ext
  exact cpSum_single k Φ

/-- Extend a finite family by zero to a countable family. -/
def extendFin (N : ℕ) (f : Fin N → Superoperator n m) :
    ℕ → Superoperator n m :=
  fun i => if h : i < N then f ⟨i, h⟩ else 0

theorem extendFin_supported (N : ℕ) (f : Fin N → Superoperator n m) :
    SupportedAt (extendFin N f) N := by
  intro i hi
  simp [extendFin, Nat.not_lt.mpr hi]

/-- A finite family has a defined σ-sum whenever its aggregate CP map is
trace-nonincreasing. -/
def finiteSummation (N : ℕ) (f : Fin N → Superoperator n m)
    (h : TraceNonincreasing (cpSum (extendFin N f) N)) :
    Summation (extendFin N f) where
  cutoff := N
  supported := extendFin_supported N f
  trace_nonincreasing := h

/-- A chain of finite prefixes that becomes stationary at `N` has the same
value at every later supported cutoff. -/
theorem stationary_cutoff {f : ℕ → Superoperator n m} {N M : ℕ}
    (hN : SupportedAt f N) (hNM : N ≤ M) :
    cpSum f M = cpSum f N := by
  apply cpSum_eq_of_supported
  · exact fun i hi => hN i (hNM.trans hi)
  · exact hN

end FiniteSupport

end SigmaMon

end QLambda.Domain.Presheaf
