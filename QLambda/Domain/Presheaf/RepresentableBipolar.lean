/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.ClassicalCategory
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# Bipolar gate for positive representables (`A > 0`)

`RepresentableReflexivity 0` and `1` are also in `ClassicalCategory.lean`.
This file closes the gate for every `0 < A`.

## Status: **CLOSED**

* Effect pairing / injectivity: `effectPrecompose_injective`.
* Unit reshape: `unit_fiber_eq` (`χ ∘ swap ∘ (Φ ⊗ id)`).
* Cup obstruction for raw Choi(`id`) when `A > 1`; normalized-cup fiber
  retraction `evaluation_comp_unit_fiber`.
* Surjectivity via effect-family Born–Riesz at `n = 1`, then column lift:
  `representable_unit_surjective_one`, `representable_unit_surjective`.
* Packaged: `representableDoubleDualEvaluation`, `representableReflexivity`,
  `representableClassicalObject`.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder InnerProductSpace Kronecker

universe u

/-! ## Effect pairing -/

/-- Precomposition of an effect `A → 1` against a map `n → A`. -/
noncomputable def effectPrecompose {n A : ℕ}
    (Φ : Superoperator n A) (e : Superoperator A 1) : Superoperator n 1 :=
  Superoperator.comp e Φ

@[simp]
theorem effectPrecompose_apply {n A : ℕ}
    (Φ : Superoperator n A) (e : Superoperator A 1) :
    effectPrecompose Φ e = Superoperator.comp e Φ :=
  rfl

/-- Build the TNI effect `A → 1` with prescribed input effect `E ≤ I`.

Choi indices are arranged so that `effect` recovers `E` exactly:
`effect i j = ∑_a choi (a,j) (a,i) = E i j`. -/
noncomputable def ofEffect {A : ℕ}
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hpsd : E.PosSemidef) (hle : E ≤ 1) : Superoperator A 1 := by
  let C : Matrix (Fin 1 × Fin A) (Fin 1 × Fin A) ℂ := fun p q => E q.2 p.2
  have hC : C.PosSemidef := by
    have hT : Eᵀ.PosSemidef := hpsd.transpose
    exact hT.submatrix (Prod.snd : Fin 1 × Fin A → Fin A)
  refine
    ⟨{ choi := C, choi_pos := hC },
      (traceNonincreasing_iff_effect_le_one _).mpr ?_⟩
  -- `effect i j = ∑_{a:Fin 1} E i j = E i j`.
  have hE : (⟨C, hC⟩ : CPMap A 1).effect = E := by
    ext i j
    simp only [CPMap.effect, C, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul, Nat.cast_one, one_mul]
  simpa [hE] using hle

theorem ofEffect_effect {A : ℕ}
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hpsd : E.PosSemidef) (hle : E ≤ 1) :
    (ofEffect E hpsd hle).cp.effect = E := by
  simp only [ofEffect]
  ext i j
  simp only [CPMap.effect, Finset.sum_const, Finset.card_fin,
    nsmul_eq_mul, Nat.cast_one, one_mul]

theorem ofEffect_applyMat_trace {A : ℕ}
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hpsd : E.PosSemidef) (hle : E ≤ 1)
    (ρ : Matrix (Fin A) (Fin A) ℂ) :
    Matrix.trace ((ofEffect E hpsd hle).cp.applyMat ρ) =
      Matrix.trace (E * ρ) := by
  rw [CPMap.trace_applyMat_eq_effect, ofEffect_effect]

/-- Effects separate applyMat/trace pairings: if `e ∘ Φ = e ∘ Ψ` for every
effect, then `Tr(E · Φ(ρ)) = Tr(E · Ψ(ρ))` for every Loewner effect `E ≤ I`. -/
theorem effectPrecompose_trace_eq {n A : ℕ}
    {Φ Ψ : Superoperator n A}
    (h : ∀ e : Superoperator A 1, effectPrecompose Φ e = effectPrecompose Ψ e)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hpsd : E.PosSemidef) (hle : E ≤ 1)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (E * Φ.cp.applyMat ρ) =
      Matrix.trace (E * Ψ.cp.applyMat ρ) := by
  have he :=
    congrArg
      (fun f : Superoperator n 1 => Matrix.trace (f.cp.applyMat ρ))
      (h (ofEffect E hpsd hle))
  have hΦ :
      Matrix.trace
          ((effectPrecompose Φ (ofEffect E hpsd hle)).cp.applyMat ρ) =
        Matrix.trace (E * Φ.cp.applyMat ρ) := by
    simp only [effectPrecompose, Superoperator.cp_comp, CPMap.applyMat_comp]
    exact ofEffect_applyMat_trace E hpsd hle _
  have hΨ :
      Matrix.trace
          ((effectPrecompose Ψ (ofEffect E hpsd hle)).cp.applyMat ρ) =
        Matrix.trace (E * Ψ.cp.applyMat ρ) := by
    simp only [effectPrecompose, Superoperator.cp_comp, CPMap.applyMat_comp]
    exact ofEffect_applyMat_trace E hpsd hle _
  exact (hΦ.symm.trans he).trans hΨ

/-! ## Effect-precompose injectivity -/

open WithLp

/-- Trace against a rank-one equals the quadratic form. -/
theorem trace_vecMulVec_mul {A : ℕ}
    (M : Matrix (Fin A) (Fin A) ℂ) (v : Fin A → ℂ) :
    Matrix.trace (Matrix.vecMulVec v (star v) * M) =
      star v ⬝ᵥ M *ᵥ v := by
  change (∑ i, ∑ j, (v i * star (v j)) * M j i) =
    ∑ i, star (v i) * ∑ j, M i j * v j
  have h1 :
      (∑ i, ∑ j, (v i * star (v j)) * M j i) =
        ∑ i, ∑ j, v i * star (v j) * M j i := by
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h2 :
      (∑ i, ∑ j, v i * star (v j) * M j i) =
        ∑ j, ∑ i, star (v j) * (M j i * v i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h3 :
      (∑ j, ∑ i, star (v j) * (M j i * v i)) =
        ∑ j, star (v j) * ∑ i, M j i * v i := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [← Finset.mul_sum]
  exact h1.trans (h2.trans h3)

/-- Unit rank-one is idempotent. -/
theorem vecMulVec_unit_mul_self {ι : Type*} [Fintype ι]
    (v : ι → ℂ) (hv : star v ⬝ᵥ v = 1) :
    Matrix.vecMulVec v (star v) * Matrix.vecMulVec v (star v) =
      Matrix.vecMulVec v (star v) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
  calc
    ∑ k, (v i * star (v k)) * (v k * star (v j))
        = ∑ k, (v i * star (v j)) * (star (v k) * v k) := by
          refine Finset.sum_congr rfl fun k _ => by ring
    _ = (v i * star (v j)) * ∑ k, star (v k) * v k := by
          rw [← Finset.mul_sum]
    _ = v i * star (v j) := by
          have hsum : (∑ k, star (v k) * v k) = (1 : ℂ) := by
            simpa [dotProduct] using hv
          rw [hsum, mul_one]

/-- Unit rank-one `|v⟩⟨v|` is an orthogonal projector, hence Loewner-below `I`. -/
theorem vecMulVec_unit_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℂ) (hv : star v ⬝ᵥ v = 1) :
    Matrix.vecMulVec v (star v) ≤ (1 : Matrix ι ι ℂ) := by
  set P := Matrix.vecMulVec v (star v)
  have hPherm : P.IsHermitian :=
    (Matrix.posSemidef_vecMulVec_self_star v).isHermitian
  have hPidem : P * P = P := vecMulVec_unit_mul_self v hv
  have hproj : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P - P + P := by rw [hPidem]
      _ = 1 - P := by abel
  have hhermIP : (1 - P).IsHermitian :=
    Matrix.IsHermitian.sub Matrix.isHermitian_one hPherm
  have hQQ : (1 - P)ᴴ * (1 - P) = 1 - P := by
    rw [hhermIP.eq, hproj]
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hhermIP fun x => ?_
  have key :
      star x ⬝ᵥ ((1 - P)ᴴ * (1 - P)) *ᵥ x =
        star ((1 - P) *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ x) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]
  have : star x ⬝ᵥ (1 - P) *ᵥ x =
      star ((1 - P) *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ x) := by
    convert key
    exact hQQ.symm
  rw [this]
  exact dotProduct_star_self_nonneg _

/-- Over `ℂ`, a matrix is zero iff every quadratic form vanishes.
Uses Mathlib's `inner_map_self_eq_zero` on `toEuclideanLin`. -/
theorem matrix_eq_zero_of_forall_quad {A : ℕ}
    (M : Matrix (Fin A) (Fin A) ℂ)
    (h : ∀ v : Fin A → ℂ, star v ⬝ᵥ M *ᵥ v = 0) : M = 0 := by
  classical
  have hT : ∀ x : EuclideanSpace ℂ (Fin A), ⟪M.toEuclideanLin x, x⟫_ℂ = 0 := by
    intro x
    set v := ofLp x
    have hq : star v ⬝ᵥ M *ᵥ v = 0 := h v
    have hinner :
        ⟪M.toEuclideanLin x, x⟫_ℂ = star (star v ⬝ᵥ M *ᵥ v) := by
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply, ofLp_toLpLin]
      change (∑ i, v i * star ((M *ᵥ v) i)) =
        star (∑ i, star (v i) * (M *ᵥ v) i)
      rw [star_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [star_mul, mul_comm]
    simp [hinner, hq]
  exact (LinearEquiv.map_eq_zero_iff Matrix.toEuclideanLin).1
    ((inner_map_self_eq_zero _).1 hT)

theorem star_dotProduct_smul_self {ι : Type*} [Fintype ι]
    (c : ℂ) (v : ι → ℂ) :
    star (c • v) ⬝ᵥ (c • v) = star c * c * (star v ⬝ᵥ v) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  calc
    ∑ i, star (c * v i) * (c * v i)
        = ∑ i, (star (v i) * star c) * (c * v i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [star_mul]
    _ = ∑ i, (star c * c) * (star (v i) * v i) := by
          refine Finset.sum_congr rfl fun i _ => by ring
    _ = (star c * c) * ∑ i, star (v i) * v i := by
          rw [← Finset.mul_sum]

/-- Quadratic form scales by `|c|²`. -/
theorem quad_smul {A : ℕ}
    (M : Matrix (Fin A) (Fin A) ℂ) (c : ℂ) (v : Fin A → ℂ) :
    star (c • v) ⬝ᵥ M *ᵥ (c • v) =
      star c * c * (star v ⬝ᵥ M *ᵥ v) := by
  have hmul : M *ᵥ (c • v) = c • (M *ᵥ v) := by
    ext i
    simp [mulVec, Pi.smul_apply]
  simp only [hmul, smul_eq_mul, dotProduct, Pi.smul_apply]
  calc
    ∑ i, star (c * v i) * (c * (M *ᵥ v) i)
        = ∑ i, (star (v i) * star c) * (c * (M *ᵥ v) i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [star_mul]
    _ = ∑ i, (star c * c) * (star (v i) * (M *ᵥ v) i) := by
          refine Finset.sum_congr rfl fun i _ => by ring
    _ = (star c * c) * ∑ i, star (v i) * (M *ᵥ v) i := by
          rw [← Finset.mul_sum]

/-- Loewner effects separate matrices via rank-one unit probes. -/
theorem matrix_eq_of_forall_effect_trace {A : ℕ}
    {X Y : Matrix (Fin A) (Fin A) ℂ}
    (h : ∀ E : Matrix (Fin A) (Fin A) ℂ,
      E.PosSemidef → E ≤ 1 → Matrix.trace (E * X) = Matrix.trace (E * Y)) :
    X = Y := by
  refine sub_eq_zero.mp (matrix_eq_zero_of_forall_quad (X - Y) fun v => ?_)
  by_cases hv0 : star v ⬝ᵥ v = 0
  · have : v = 0 := (dotProduct_star_self_eq_zero).1 hv0
    simp [this]
  · have hnn : (0 : ℂ) ≤ star v ⬝ᵥ v := dotProduct_star_self_nonneg v
    have hre_nonneg : 0 ≤ (star v ⬝ᵥ v).re := (Complex.nonneg_iff.mp hnn).1
    have him0 : (star v ⬝ᵥ v).im = 0 := by
      simpa using (Complex.nonneg_iff.mp hnn).2.symm
    have hre_pos : 0 < (star v ⬝ᵥ v).re := by
      refine lt_of_le_of_ne hre_nonneg fun hre0 => ?_
      exact hv0 (Complex.ext (Eq.symm hre0) him0)
    let s : ℝ := Real.sqrt (star v ⬝ᵥ v).re
    have hs_pos : 0 < s := Real.sqrt_pos.mpr hre_pos
    have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
    have hstar_s : star (s : ℂ) = (s : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    have hstar_inv : star ((s : ℂ)⁻¹) = (s : ℂ)⁻¹ := by
      rw [star_inv₀, hstar_s]
    have hv_norm : star v ⬝ᵥ v = (s : ℂ) * (s : ℂ) := by
      apply Complex.ext
      · have : (star v ⬝ᵥ v).re = s * s := by
          simpa [s] using (Real.mul_self_sqrt hre_nonneg).symm
        simpa [Complex.mul_re, Complex.ofReal_re] using this
      · simp [Complex.mul_im, him0]
    let w : Fin A → ℂ := ((s : ℂ)⁻¹) • v
    have hw1 : star w ⬝ᵥ w = 1 := by
      rw [star_dotProduct_smul_self, hv_norm, hstar_inv]
      field_simp [hs_ne]
    have htr :=
      h (Matrix.vecMulVec w (star w))
        (Matrix.posSemidef_vecMulVec_self_star w)
        (vecMulVec_unit_le_one w hw1)
    have hwquad : star w ⬝ᵥ (X - Y) *ᵥ w = 0 := by
      rw [← trace_vecMulVec_mul, Matrix.mul_sub, Matrix.trace_sub, htr, sub_self]
    have hvw : v = (s : ℂ) • w := by
      simp only [w]
      ext i
      change v i = (s : ℂ) * ((s : ℂ)⁻¹ * v i)
      rw [← mul_assoc, mul_inv_cancel₀ hs_ne, one_mul]
    calc
      star v ⬝ᵥ (X - Y) *ᵥ v =
          star ((s : ℂ) • w) ⬝ᵥ (X - Y) *ᵥ ((s : ℂ) • w) := by rw [hvw]
      _ = star (s : ℂ) * (s : ℂ) * (star w ⬝ᵥ (X - Y) *ᵥ w) :=
        quad_smul _ _ _
      _ = (s : ℂ) * (s : ℂ) * 0 := by rw [hstar_s, hwquad]
      _ = 0 := by ring

/-- Effects separate superoperators: `∀ e, e∘Φ = e∘Ψ` implies `Φ = Ψ`. -/
theorem effectPrecompose_injective {n A : ℕ}
    {Φ Ψ : Superoperator n A}
    (h : ∀ e : Superoperator A 1, effectPrecompose Φ e = effectPrecompose Ψ e) :
    Φ = Ψ := by
  apply Superoperator.ext
  apply CPMap.ext_apply
  intro ρ
  refine matrix_eq_of_forall_effect_trace ?_
  intro E hpsd hle
  exact effectPrecompose_trace_eq h E hpsd hle ρ

/-! ## Closed-adjunction transport of the first dual -/

/-- Closed-adjunction + Yoneda transport:
`Hom(y(n), ¬y(A)) ≃ Superoperator (n*A) 1`.

This is the fiber identification used when reconstructing maps out of
`¬¬y(A)` by evaluating against effects.  The carrier
`((¬¬y(A)).obj n).Carrier` itself is the bilinear module
`Bilinear(y(n), ¬y(A), I)`, not definitionally `Superoperator (n*A) 1`. -/
noncomputable def doubleDualFiberEquiv (A n : ℕ) :
    Hom (representable n) (DayNegation.neg (representable A)) ≃
      Superoperator (n * A) 1 :=
  ((DayInternalHom.curryEquiv
        (representable n) (representable A) dayTensorUnit).symm.trans
      (dayTensorRepresentableEquiv n A dayTensorUnit).symm).trans
    (yonedaEquiv dayTensorUnit (n * A))

@[simp]
theorem doubleDualFiberEquiv_apply (A n : ℕ)
    (η : Hom (representable n) (DayNegation.neg (representable A))) :
    doubleDualFiberEquiv A n η =
      yonedaEquiv dayTensorUnit (n * A)
        ((dayTensorRepresentableEquiv n A dayTensorUnit).symm
          (DayInternalHom.uncurry η)) :=
  rfl

/-- The same transport factors through the existing first-dual fiber
equivalence after Yoneda. -/
theorem doubleDualFiberEquiv_eq_fiberEquiv (A n : ℕ)
    (η : Hom (representable n) (DayNegation.neg (representable A))) :
    doubleDualFiberEquiv A n η =
      dayNegationRepresentableFiberEquiv A n
        (yonedaEquiv (DayNegation.neg (representable A)) n η) := by
  simp only [doubleDualFiberEquiv,
    dayNegationRepresentableFiberEquiv,
    dayInternalHomRepresentableFiberEquiv]
  rfl

/-! ## Concrete double-dual unit reshape -/

/-- Unfolded action of `DayNegation.unit` on a representable. -/
theorem representable_unit_app_app {A n p q : ℕ}
    (Φ : Superoperator n A) (r : Superoperator p n)
    (b : ((DayNegation.neg (representable A)).obj q).Carrier) :
    ((DayNegation.unit (representable A)).app n Φ).app r b =
      Superoperator.comp
        (b.app (Superoperator.identity q) (Superoperator.comp Φ r))
        (Superoperator.tensorSwap p q) := by
  simp only [DayNegation.unit, DayInternalHom.curry, DayNegation.unitBilinear]
  change
    Superoperator.comp
        (b.app (Superoperator.identity q)
          ((representable A).act Φ r))
        (Superoperator.tensorSwap p q) =
      Superoperator.comp
        (b.app (Superoperator.identity q) (Superoperator.comp Φ r))
        (Superoperator.tensorSwap p q)
  rw (config := { transparency := .default }) [representable_act]

/-- Transport a first-dual fiber element to its bilinear representative. -/
noncomputable def dualFiberBilinear (A q : ℕ)
    (χ : Superoperator (q * A) 1) :
    ((DayNegation.neg (representable A)).obj q).Carrier :=
  (dayInternalHomRepresentableIso A dayTensorUnit).inv.app q χ

@[simp]
theorem dualFiberBilinear_app {A q p q' : ℕ}
    (χ : Superoperator (q * A) 1)
    (r : Superoperator p q) (s : Superoperator q' A) :
    (dualFiberBilinear A q χ).app r s =
      Superoperator.comp χ (Superoperator.tensor r s) :=
  rfl

/-- **Unit fiber reshape.**  Evaluating the double-dual unit at `Φ` against a
dual-fiber probe `χ : Superoperator (q*A) 1` yields

`χ ∘ swap_{A,q} ∘ (Φ ⊗ id_q)`,

the Day form of `ε ∘ (Φ ⊗ id)` with tensor-swap braiding.  The result is always
a well-typed TNI map into `I` (effect `≤ I`), even when a raw cup reshape of
`Φ` itself would leave the TNI cone. -/
theorem unit_fiber_eq {A n q : ℕ}
    (Φ : Superoperator n A) (χ : Superoperator (q * A) 1) :
    ((DayNegation.unit (representable A)).app n Φ).app
        (Superoperator.identity n) (dualFiberBilinear A q χ) =
      Superoperator.comp χ
        (Superoperator.comp
          (Superoperator.tensorSwap A q)
          (Superoperator.tensor Φ (Superoperator.identity q))) := by
  rw [representable_unit_app_app, Superoperator.comp_identity,
    dualFiberBilinear_app]
  have hswap :=
    Superoperator.tensorSwap_naturality Φ (Superoperator.identity q)
  calc
    Superoperator.comp
        (Superoperator.comp χ
          (Superoperator.tensor (Superoperator.identity q) Φ))
        (Superoperator.tensorSwap n q) =
      Superoperator.comp χ
          (Superoperator.comp
            (Superoperator.tensor (Superoperator.identity q) Φ)
            (Superoperator.tensorSwap n q)) :=
              (Superoperator.comp_assoc _ _ _).symm
    _ = Superoperator.comp χ
          (Superoperator.comp
            (Superoperator.tensorSwap A q)
            (Superoperator.tensor Φ (Superoperator.identity q))) := by
              rw [← hswap]

/-- Right-associated form of `unit_fiber_eq`. -/
theorem unit_fiber_eq' {A n q : ℕ}
    (Φ : Superoperator n A) (χ : Superoperator (q * A) 1) :
    ((DayNegation.unit (representable A)).app n Φ).app
        (Superoperator.identity n) (dualFiberBilinear A q χ) =
      Superoperator.comp
        (Superoperator.comp χ (Superoperator.tensorSwap A q))
        (Superoperator.tensor Φ (Superoperator.identity q)) := by
  rw [unit_fiber_eq, Superoperator.comp_assoc]

/-- Evaluating the unit against an arbitrary dual bilinear recovers
`b(id, Φ)` after the Day braiding. -/
theorem unit_eval_bilinear {A n q : ℕ}
    (Φ : Superoperator n A)
    (b : ((DayNegation.neg (representable A)).obj q).Carrier) :
    ((DayNegation.unit (representable A)).app n Φ).app
        (Superoperator.identity n) b =
      Superoperator.comp
        (b.app (Superoperator.identity q) Φ)
        (Superoperator.tensorSwap n q) := by
  simpa [Superoperator.comp_identity] using
    representable_unit_app_app Φ (Superoperator.identity n) b

/-- Composition on the right by `tensorSwap` is injective. -/
theorem comp_tensorSwap_injective {p q : ℕ} :
    Function.Injective fun χ : Superoperator (p * q) 1 =>
      Superoperator.comp χ (Superoperator.tensorSwap q p) := by
  intro χ₁ χ₂ hcomp
  have h :=
    congrArg
      (fun ζ : Superoperator (q * p) 1 =>
        Superoperator.comp ζ (Superoperator.tensorSwap p q)) hcomp
  -- `χ ∘ swap ∘ swap = χ`.
  calc
    χ₁ = Superoperator.comp χ₁
          (Superoperator.comp (Superoperator.tensorSwap q p)
            (Superoperator.tensorSwap p q)) := by
              simp [Superoperator.tensorSwap_involutive]
    _ = Superoperator.comp
          (Superoperator.comp χ₁ (Superoperator.tensorSwap q p))
          (Superoperator.tensorSwap p q) := Superoperator.comp_assoc _ _ _
    _ = Superoperator.comp
          (Superoperator.comp χ₂ (Superoperator.tensorSwap q p))
          (Superoperator.tensorSwap p q) := h
    _ = Superoperator.comp χ₂
          (Superoperator.comp (Superoperator.tensorSwap q p)
            (Superoperator.tensorSwap p q)) :=
              (Superoperator.comp_assoc _ _ _).symm
    _ = χ₂ := by simp [Superoperator.tensorSwap_involutive]

/-! ## Fiberwise injectivity of the representable unit -/

/-- From equality of units, dual bilinears agree on `Φ` and `Ψ`. -/
theorem unit_eq_imp_bilinear_app {A n q : ℕ}
    {Φ Ψ : Superoperator n A}
    (h : (DayNegation.unit (representable A)).app n Φ =
      (DayNegation.unit (representable A)).app n Ψ)
    (b : ((DayNegation.neg (representable A)).obj q).Carrier) :
    b.app (Superoperator.identity q) Φ =
      b.app (Superoperator.identity q) Ψ := by
  have hval :=
    congrArg
      (fun F :
          ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier =>
        F.app (Superoperator.identity n) b) h
  rw [unit_eval_bilinear, unit_eval_bilinear] at hval
  exact comp_tensorSwap_injective hval

/-- Dual fiber at `q = 1` recovers ordinary effect precomposition (up to the
left unitor `1*A ≃ A`). -/
theorem dualFiberBilinear_one_app {A n : ℕ}
    (e : Superoperator A 1) (Φ : Superoperator n A) :
    (dualFiberBilinear A 1
        (Superoperator.comp e (Superoperator.tensorLeftUnitor A))).app
        (Superoperator.identity 1) Φ =
      Superoperator.comp (effectPrecompose Φ e)
        (Superoperator.tensorLeftUnitor n) := by
  simp only [dualFiberBilinear_app, effectPrecompose]
  calc
    Superoperator.comp
        (Superoperator.comp e (Superoperator.tensorLeftUnitor A))
        (Superoperator.tensor (Superoperator.identity 1) Φ) =
      Superoperator.comp e
          (Superoperator.comp (Superoperator.tensorLeftUnitor A)
            (Superoperator.tensor (Superoperator.identity 1) Φ)) := by
              rw [Superoperator.comp_assoc]
    _ = Superoperator.comp e
          (Superoperator.comp Φ (Superoperator.tensorLeftUnitor n)) := by
              rw [Superoperator.tensorLeftUnitor_naturality]
    _ = Superoperator.comp (Superoperator.comp e Φ)
          (Superoperator.tensorLeftUnitor n) := by
              rw [← Superoperator.comp_assoc]

/-- Composition on the right by `tensorLeftUnitor` is injective. -/
theorem comp_tensorLeftUnitor_injective {n : ℕ} :
    Function.Injective fun χ : Superoperator n 1 =>
      Superoperator.comp χ (Superoperator.tensorLeftUnitor n) := by
  intro χ₁ χ₂ hcomp
  have h :=
    congrArg
      (fun ζ : Superoperator (1 * n) 1 =>
        Superoperator.comp ζ (Superoperator.tensorLeftUnitorInv n)) hcomp
  calc
    χ₁ = Superoperator.comp χ₁
          (Superoperator.comp (Superoperator.tensorLeftUnitor n)
            (Superoperator.tensorLeftUnitorInv n)) := by
              simp [Superoperator.tensorLeftUnitor_hom_inv]
    _ = Superoperator.comp
          (Superoperator.comp χ₁ (Superoperator.tensorLeftUnitor n))
          (Superoperator.tensorLeftUnitorInv n) := Superoperator.comp_assoc _ _ _
    _ = Superoperator.comp
          (Superoperator.comp χ₂ (Superoperator.tensorLeftUnitor n))
          (Superoperator.tensorLeftUnitorInv n) := h
    _ = Superoperator.comp χ₂
          (Superoperator.comp (Superoperator.tensorLeftUnitor n)
            (Superoperator.tensorLeftUnitorInv n)) :=
              (Superoperator.comp_assoc _ _ _).symm
    _ = χ₂ := by simp [Superoperator.tensorLeftUnitor_hom_inv]

/-- Unit equality implies effect-precomposition equality. -/
theorem unit_eq_imp_effectPrecompose {A n : ℕ}
    {Φ Ψ : Superoperator n A}
    (h : (DayNegation.unit (representable A)).app n Φ =
      (DayNegation.unit (representable A)).app n Ψ)
    (e : Superoperator A 1) :
    effectPrecompose Φ e = effectPrecompose Ψ e := by
  have happ :=
    unit_eq_imp_bilinear_app h
      (dualFiberBilinear A 1
        (Superoperator.comp e (Superoperator.tensorLeftUnitor A)))
  rw [dualFiberBilinear_one_app, dualFiberBilinear_one_app] at happ
  exact comp_tensorLeftUnitor_injective happ

/-- Fiberwise injectivity of the representable unit, given effect separation. -/
theorem representable_unit_injective_of_effectPrecompose
    (A n : ℕ)
    (hEff : ∀ {Φ Ψ : Superoperator n A},
      (∀ e : Superoperator A 1, effectPrecompose Φ e = effectPrecompose Ψ e) →
        Φ = Ψ) :
    Function.Injective ((DayNegation.unit (representable A)).app n) := by
  intro Φ Ψ hΦΨ
  exact hEff (fun e => unit_eq_imp_effectPrecompose hΦΨ e)

/-- Unconditional fiberwise injectivity of the double-dual unit on representables. -/
theorem representable_unit_injective {A n : ℕ} (_hA : 0 < A)
    {Φ Ψ : Superoperator n A}
    (h : (DayNegation.unit (representable A)).app n Φ =
      (DayNegation.unit (representable A)).app n Ψ) :
    Φ = Ψ :=
  effectPrecompose_injective (fun e => unit_eq_imp_effectPrecompose h e)

/-- Same statement packaged as `Function.Injective`. -/
theorem representable_unit_injective' {A n : ℕ} (hA : 0 < A) :
    Function.Injective ((DayNegation.unit (representable A)).app n) :=
  fun _ _ h => representable_unit_injective hA h

/-- Specialization: for `A = 2`, `Φ = id`, every unit-fiber value
`χ ∘ swap ∘ (id ⊗ id)` is a genuine TNI effect (typed as `Superoperator`),
whereas the raw cup Choi(`id₂`) itself fails `≤ I`
(`choiIdentity_two_not_le_one`). -/
theorem unit_fiber_id_is_tni {q : ℕ} (χ : Superoperator (q * 2) 1) :
    TraceNonincreasing
      (((DayNegation.unit (representable 2)).app 2
          (Superoperator.identity 2)).app (Superoperator.identity 2)
        (dualFiberBilinear 2 q χ)).cp :=
  (((DayNegation.unit (representable 2)).app 2
      (Superoperator.identity 2)).app (Superoperator.identity 2)
    (dualFiberBilinear 2 q χ)).trace_nonincreasing

/-! ## Obstruction: raw cup / Choi(`id`) is not an effect for `A > 1` -/

/-- Choi matrix of the identity channel on `A`. -/
def choiIdentity (A : ℕ) :
    Matrix (Fin A × Fin A) (Fin A × Fin A) ℂ :=
  (CPMap.identity A).choi

/-- Unnormalized maximally-entangled vector `∑ᵢ |i,i⟩`. -/
def omegaVec (A : ℕ) : Fin A × Fin A → ℂ :=
  fun p => if p.1 = p.2 then 1 else 0

theorem choiIdentity_apply (A : ℕ) (p q : Fin A × Fin A) :
    choiIdentity A p q =
      (if p.1 = p.2 then (1 : ℂ) else 0) *
        (if q.1 = q.2 then 1 else 0) := by
  simp only [choiIdentity, CPMap.identity, CPMap.choi_ofKraus,
    KrausFamily.identity, KrausFamily.choi_single, KrausFamily.choiTerm]
  simp [Matrix.one_apply]

theorem omega_dot_omega (A : ℕ) :
    star (omegaVec A) ⬝ᵥ omegaVec A = (A : ℂ) := by
  simp only [dotProduct, omegaVec]
  rw [Fintype.sum_prod_type]
  change
    (∑ i : Fin A, ∑ j : Fin A,
        star (if i = j then (1 : ℂ) else 0) *
          (if i = j then 1 else 0)) =
      A
  simp

theorem sum_diagonal_indicator (A : ℕ) :
    (∑ q : Fin A × Fin A, (if q.1 = q.2 then (1 : ℂ) else 0)) =
      (A : ℂ) := by
  rw [Fintype.sum_prod_type]
  change (∑ i : Fin A, ∑ j : Fin A, (if i = j then (1 : ℂ) else 0)) = A
  simp

theorem choiIdentity_mulVec_omega (A : ℕ) :
    choiIdentity A *ᵥ omegaVec A = (A : ℂ) • omegaVec A := by
  ext p
  simp only [mulVec, Pi.smul_apply, smul_eq_mul, omegaVec, choiIdentity_apply]
  have hsum :
      (∑ q : Fin A × Fin A,
          (if p.1 = p.2 then (1 : ℂ) else 0) *
            (if q.1 = q.2 then 1 else 0)) =
        (A : ℂ) * (if p.1 = p.2 then 1 else 0) := by
    by_cases hp : p.1 = p.2
    · simp only [hp, ite_true, one_mul]
      simpa using sum_diagonal_indicator A
    · simp [hp]
  calc
    (∑ q : Fin A × Fin A,
          (if p.1 = p.2 then (1 : ℂ) else 0) *
            (if q.1 = q.2 then 1 else 0) *
            (if q.1 = q.2 then 1 else 0)) =
        ∑ q : Fin A × Fin A,
          (if p.1 = p.2 then (1 : ℂ) else 0) *
            (if q.1 = q.2 then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro q _
              by_cases hq : q.1 = q.2 <;> simp [hq]
    _ = (A : ℂ) * (if p.1 = p.2 then 1 else 0) := hsum

/-- For `A > 1`, Choi(`id_A`) is **not** Loewner-below `I`: it has eigenvalue
`A` on the maximally-entangled vector.  Consequently it cannot be the input
effect of any map `A² → 1` in the TNI cone, so the raw compact-closed cup is
not a dual element of `¬y(A)`. -/
theorem choiIdentity_not_le_one {A : ℕ} (hA : 1 < A) :
    ¬ choiIdentity A ≤
        (1 : Matrix (Fin A × Fin A) (Fin A × Fin A) ℂ) := by
  intro hle
  have hpsd : (1 - choiIdentity A).PosSemidef := Matrix.le_iff.mp hle
  have hquad := hpsd.dotProduct_mulVec_nonneg (omegaVec A)
  have hcalc :
      star (omegaVec A) ⬝ᵥ (1 - choiIdentity A) *ᵥ omegaVec A =
        (1 - A : ℂ) * A := by
    simp only [sub_mulVec, one_mulVec, dotProduct_sub, choiIdentity_mulVec_omega]
    have hAΩ :
        star (omegaVec A) ⬝ᵥ ((A : ℂ) • omegaVec A) = (A : ℂ) * A := by
      change
        (∑ i, star (omegaVec A i) * ((A : ℂ) * omegaVec A i)) =
          (A : ℂ) * A
      have h := omega_dot_omega A
      change (∑ i, star (omegaVec A i) * omegaVec A i) = (A : ℂ) at h
      calc
        (∑ i, star (omegaVec A i) * (↑A * omegaVec A i)) =
            ↑A * ∑ i, star (omegaVec A i) * omegaVec A i := by
              simp [mul_left_comm, Finset.mul_sum]
        _ = ↑A * ↑A := by rw [h]
    change
      star (omegaVec A) ⬝ᵥ omegaVec A -
          star (omegaVec A) ⬝ᵥ ((A : ℂ) • omegaVec A) =
        (1 - A : ℂ) * A
    rw [omega_dot_omega, hAΩ]
    ring
  have hre :
      (star (omegaVec A) ⬝ᵥ (1 - choiIdentity A) *ᵥ omegaVec A).re < 0 := by
    rw [hcalc]
    have : ((1 - A : ℂ) * A).re = (1 - (A : ℝ)) * A := by
      simp [Complex.mul_re, Complex.sub_re]
    rw [this]
    have hA0 : (0 : ℝ) < A := by exact_mod_cast (Nat.zero_lt_of_lt hA)
    have h1A : (1 - (A : ℝ)) < 0 := by
      have : (1 : ℝ) < A := by exact_mod_cast hA
      linarith
    exact mul_neg_of_neg_of_pos h1A hA0
  have hnonneg :
      0 ≤ (star (omegaVec A) ⬝ᵥ (1 - choiIdentity A) *ᵥ omegaVec A).re :=
    (Complex.nonneg_iff.mp hquad).1
  exact not_lt.mpr hnonneg hre

/-- Specialization: the `A = 2` cup obstruction (Choi(`id`) has eigenvalue 2). -/
theorem choiIdentity_two_not_le_one :
    ¬ choiIdentity 2 ≤
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :=
  choiIdentity_not_le_one (by decide)

/-! ## Discard counterexample refuted; normalized cup; surjectivity status -/

/-- Every `Superoperator _ 1` is TNI, so its output mass on a state of trace `t`
is at most `t`.  In particular, double-dual bilinear values (which land in
`Superoperator`) cannot exhibit the "mass `A`" reading of raw discard. -/
theorem effect_extract_mass_le_one {k : ℕ}
    (χ : Superoperator k 1)
    (ρ : Matrix (Fin k) (Fin k) ℂ) (hρ : ρ.PosSemidef) :
    (Matrix.trace (χ.cp.applyMat ρ)).re ≤ (Matrix.trace ρ).re :=
  χ.trace_nonincreasing ρ hρ

/-- Discard `ofEffect I_A` is a first-dual fiber element
`¬y(A)_1 ≃ Superoperator A 1`, via `dualFiberBilinear` / the closed-adjunction
fiber.  It is **not** an element of `((¬¬y(A)).obj n)`.  Transporting discard
into the double dual would require an additional embedding that the raw Day
negation does not supply; the mass-`A` pairing intuition cannot appear inside
`Superoperator`-valued double-dual outputs (`effect_extract_mass_le_one`). -/
noncomputable def discardEffect (A : ℕ) : Superoperator A 1 :=
  ofEffect (1 : Matrix (Fin A) (Fin A) ℂ)
    Matrix.PosSemidef.one (le_refl _)

/-- First-dual packaging of discard (closed-adjunction fiber at `q = 1`). -/
noncomputable def discardFirstDual (A : ℕ) :
    ((DayNegation.neg (representable A)).obj 1).Carrier :=
  dualFiberBilinear A 1
    (Superoperator.comp (discardEffect A)
      (Superoperator.tensorLeftUnitor A))

/-- For any preparation `Φ : 1 → A`, discard-precomposition has mass
`Tr(Φ(1)) ≤ 1`, so discard cannot obstruct the image of `unit.app 1` by a
mass-`A` mismatch. -/
theorem discard_precompose_mass_le_one {A : ℕ}
    (Φ : Superoperator 1 A)
    (hI : (1 : Matrix (Fin A) (Fin A) ℂ).PosSemidef := Matrix.PosSemidef.one)
    (hle : (1 : Matrix (Fin A) (Fin A) ℂ) ≤ 1 := le_refl _) :
    (Matrix.trace
        ((effectPrecompose Φ (ofEffect 1 hI hle)).cp.applyMat
          (1 : Matrix (Fin 1) (Fin 1) ℂ))).re ≤
      (1 : ℝ) := by
  have hρ : (1 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef := Matrix.PosSemidef.one
  have htr :=
    (effectPrecompose Φ (ofEffect 1 hI hle)).trace_nonincreasing _ hρ
  have : Matrix.trace (1 : Matrix (Fin 1) (Fin 1) ℂ) = (1 : ℂ) := by
    simp [Matrix.trace_one]
  simpa [this, Complex.one_re] using htr

/-- Choi(`id`) as an outer product `|Ω⟩⟨Ω|`. -/
theorem choiIdentity_eq_vecMulVec (A : ℕ) :
    choiIdentity A =
      Matrix.vecMulVec (omegaVec A) (star (omegaVec A)) := by
  ext p q
  simp only [choiIdentity_apply, Matrix.vecMulVec_apply, omegaVec, Pi.star_apply]
  split_ifs <;> simp

theorem choiIdentity_posSemidef (A : ℕ) :
    (choiIdentity A).PosSemidef := by
  rw [choiIdentity_eq_vecMulVec]
  exact Matrix.posSemidef_vecMulVec_self_star _

/-- Normalized maximally-entangled vector `Ω / √A`. -/
noncomputable def omegaUnitVec (A : ℕ) (_hA : 0 < A) :
    Fin A × Fin A → ℂ :=
  ((Real.sqrt (A : ℝ) : ℂ)⁻¹) • omegaVec A

theorem omegaUnitVec_norm {A : ℕ} (hA : 0 < A) :
    star (omegaUnitVec A hA) ⬝ᵥ omegaUnitVec A hA = 1 := by
  have hs_pos : 0 < Real.sqrt (A : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hA)
  have hs_ne : (Real.sqrt (A : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
  have hs2 : (Real.sqrt (A : ℝ) : ℂ) * (Real.sqrt (A : ℝ) : ℂ) = (A : ℂ) := by
    exact_mod_cast (Real.mul_self_sqrt (Nat.cast_nonneg A))
  have hstar : star (Real.sqrt (A : ℝ) : ℂ) = (Real.sqrt (A : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  simp only [omegaUnitVec]
  rw [star_dotProduct_smul_self, star_inv₀, hstar, omega_dot_omega]
  field_simp [hs_ne]
  calc
    (A : ℂ) = (Real.sqrt (A : ℝ) : ℂ) * (Real.sqrt (A : ℝ) : ℂ) := hs2.symm
    _ = (Real.sqrt (A : ℝ) : ℂ) ^ 2 := (pow_two _).symm


theorem choiIdentity_div_eq_unit_projector {A : ℕ} (hA : 0 < A) :
    ((A : ℝ)⁻¹ : ℂ) • choiIdentity A =
      Matrix.vecMulVec (omegaUnitVec A hA) (star (omegaUnitVec A hA)) := by
  have hs_pos : 0 < Real.sqrt (A : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hA)
  have hs_ne : (Real.sqrt (A : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
  have hs2 : (Real.sqrt (A : ℝ) : ℂ) * (Real.sqrt (A : ℝ) : ℂ) = (A : ℂ) := by
    exact_mod_cast (Real.mul_self_sqrt (Nat.cast_nonneg A))
  have hstar : star (Real.sqrt (A : ℝ) : ℂ) = (Real.sqrt (A : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [choiIdentity_eq_vecMulVec]
  ext p q
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, omegaUnitVec,
    Pi.smul_apply, smul_eq_mul, Pi.star_apply]
  rw [star_mul, star_inv₀, hstar]
  have hscale :
      ((A : ℝ)⁻¹ : ℂ) * (omegaVec A p * star (omegaVec A q)) =
        ((Real.sqrt (A : ℝ) : ℂ)⁻¹ * omegaVec A p) *
          (star (omegaVec A q) * (Real.sqrt (A : ℝ) : ℂ)⁻¹) := by
    field_simp [hs_ne]
    have hs2' : (Real.sqrt (A : ℝ) : ℂ) ^ 2 = (A : ℂ) := by
      rw [pow_two, hs2]
    simp [hs2', mul_assoc, mul_comm]
  exact hscale

/-- **Normalized cup.**  For `A > 0`, `(1/A) • Choi(id_A)` is a rank-one
orthogonal projector onto `Ω/√A`, hence Loewner-below `I`.  This is the
matrix-level content of weak dualizability (normalized cup/cap) for `y(A)`. -/
theorem choiIdentity_div_le_one {A : ℕ} (hA : 0 < A) :
    ((A : ℝ)⁻¹ : ℂ) • choiIdentity A ≤
      (1 : Matrix (Fin A × Fin A) (Fin A × Fin A) ℂ) := by
  rw [choiIdentity_div_eq_unit_projector hA]
  exact vecMulVec_unit_le_one (omegaUnitVec A hA) (omegaUnitVec_norm hA)

theorem choiIdentity_div_posSemidef {A : ℕ} (hA : 0 < A) :
    (((A : ℝ)⁻¹ : ℂ) • choiIdentity A).PosSemidef := by
  rw [choiIdentity_div_eq_unit_projector hA]
  exact Matrix.posSemidef_vecMulVec_self_star _

/-! ## Normalized cup as a dual probe; cup-name evaluation -/

/-- Reindex `(1/A)•Choi(id)` from `Fin A × Fin A` to `Fin (A*A)`. -/
noncomputable def normalizedCupMatrix (A : ℕ) (_hA : 0 < A) :
    Matrix (Fin (A * A)) (Fin (A * A)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (((A : ℝ)⁻¹ : ℂ) • choiIdentity A)

theorem normalizedCupMatrix_posSemidef {A : ℕ} (hA : 0 < A) :
    (normalizedCupMatrix A hA).PosSemidef := by
  -- `reindex e e M = M.submatrix e.symm e.symm`
  simpa [normalizedCupMatrix, Matrix.reindex] using
    (choiIdentity_div_posSemidef hA).submatrix (finProdFinEquiv.symm)

theorem reindex_one_eq_one {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) :
    Matrix.reindex e e (1 : Matrix ι ι ℂ) = (1 : Matrix κ κ ℂ) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.one_apply]

theorem reindex_sub {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M N : Matrix ι ι ℂ) :
    Matrix.reindex e e (M - N) =
      Matrix.reindex e e M - Matrix.reindex e e N := by
  ext; simp [Matrix.reindex_apply, Matrix.sub_apply]

theorem reindex_le_one {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    {M : Matrix ι ι ℂ} (h : M ≤ (1 : Matrix ι ι ℂ)) :
    Matrix.reindex e e M ≤ (1 : Matrix κ κ ℂ) := by
  rw [Matrix.le_iff] at h ⊢
  have h1 : (1 : Matrix κ κ ℂ) - Matrix.reindex e e M =
      Matrix.reindex e e (1 - M) := by
    rw [← reindex_one_eq_one e, ← reindex_sub]
  rw [h1]
  simpa [Matrix.reindex] using (h.submatrix e.symm)

theorem normalizedCupMatrix_le_one {A : ℕ} (hA : 0 < A) :
    normalizedCupMatrix A hA ≤
      (1 : Matrix (Fin (A * A)) (Fin (A * A)) ℂ) := by
  simpa [normalizedCupMatrix] using
    reindex_le_one finProdFinEquiv (choiIdentity_div_le_one hA)

/-- Normalized cup as a TNI effect `A² → 1`. -/
noncomputable def normalizedCup (A : ℕ) (hA : 0 < A) :
    Superoperator (A * A) 1 :=
  ofEffect (normalizedCupMatrix A hA)
    (normalizedCupMatrix_posSemidef hA)
    (normalizedCupMatrix_le_one hA)

@[simp]
theorem normalizedCup_effect {A : ℕ} (hA : 0 < A) :
    (normalizedCup A hA).cp.effect = normalizedCupMatrix A hA :=
  ofEffect_effect _ _ _

/-- Dual-fiber probe at `q = A` generated by the normalized cup. -/
noncomputable def normalizedCupProbe (A : ℕ) (hA : 0 < A) :
    ((DayNegation.neg (representable A)).obj A).Carrier :=
  dualFiberBilinear A A (normalizedCup A hA)

/-- Cup-name of a map `n → A`: `cup ∘ swap ∘ (Φ ⊗ id_A)`. -/
noncomputable def cupName {A : ℕ} (hA : 0 < A) {n : ℕ}
    (Φ : Superoperator n A) : Superoperator (n * A) 1 :=
  Superoperator.comp (normalizedCup A hA)
    (Superoperator.comp (Superoperator.tensorSwap A A)
      (Superoperator.tensor Φ (Superoperator.identity A)))

/-- Unit evaluation at the normalized-cup probe is the cup-name. -/
theorem unit_app_normalizedCupProbe {A n : ℕ} (hA : 0 < A)
    (Φ : Superoperator n A) :
    ((DayNegation.unit (representable A)).app n Φ).app
        (Superoperator.identity n) (normalizedCupProbe A hA) =
      cupName hA Φ := by
  simpa [normalizedCupProbe, cupName] using
    unit_fiber_eq Φ (normalizedCup A hA)

/-- Equivalence `(output, input) ≃ flat` for Choi ↔ effect-on-`n*A`. -/
noncomputable def choiFlatEquiv (A n : ℕ) :
    Fin A × Fin n ≃ Fin (n * A) :=
  (Equiv.prodComm (Fin A) (Fin n)).trans finProdFinEquiv

/-- Build a Choi matrix on `Fin A × Fin n` by reindexing the *transpose* of
an effect on `Fin (n*A)`.  The transpose matches the cup-name snake
(`χ ∘ swap ∘ (Φ ⊗ id)` recovers `Φ.choi` rather than its index-swap). -/
noncomputable def effectAsChoi {A n : ℕ}
    (E : Matrix (Fin (n * A)) (Fin (n * A)) ℂ) :
    Matrix (Fin A × Fin n) (Fin A × Fin n) ℂ :=
  Matrix.reindex (choiFlatEquiv A n).symm (choiFlatEquiv A n).symm Eᵀ

theorem effectAsChoi_apply {A n : ℕ}
    (E : Matrix (Fin (n * A)) (Fin (n * A)) ℂ)
    (p q : Fin A × Fin n) :
    effectAsChoi (A := A) (n := n) E p q =
      E (finProdFinEquiv (q.2, q.1)) (finProdFinEquiv (p.2, p.1)) := by
  -- `reindex e.symm e.symm Eᵀ p q = Eᵀ (e p) (e q) = E (e q) (e p)`.
  simp only [effectAsChoi, Matrix.reindex_apply, choiFlatEquiv]
  rfl

theorem effectAsChoi_posSemidef {A n : ℕ}
    {E : Matrix (Fin (n * A)) (Fin (n * A)) ℂ} (hE : E.PosSemidef) :
    (effectAsChoi (A := A) (n := n) E).PosSemidef := by
  have hT : Eᵀ.PosSemidef := hE.transpose
  simpa [effectAsChoi, Matrix.reindex] using
    hT.submatrix (choiFlatEquiv A n)

/-- Choi CP map recovered from a cup-name effect (scale `1`, no TNI). -/
noncomputable def cupNameCP {A n : ℕ}
    (χ : Superoperator (n * A) 1) : CPMap n A where
  choi := effectAsChoi (A := A) (n := n) χ.cp.effect
  choi_pos := effectAsChoi_posSemidef (CPMap.effect_posSemidef χ.cp)

/-- For `A = 1`, the normalized cup matrix is the `1×1` identity. -/
theorem normalizedCupMatrix_one :
    normalizedCupMatrix 1 (by decide) =
      (1 : Matrix (Fin (1 * 1)) (Fin (1 * 1)) ℂ) := by
  ext i j
  have hi : i = ⟨0, by decide⟩ := Fin.ext (by omega)
  have hj : j = ⟨0, by decide⟩ := Fin.ext (by omega)
  subst hi; subst hj
  have hfwd : finProdFinEquiv ((⟨0, by decide⟩ : Fin 1), (⟨0, by decide⟩ : Fin 1)) =
      (⟨0, by decide⟩ : Fin (1 * 1)) := by
    simp [finProdFinEquiv, Fin.divNat, Fin.modNat]
  have hpair : finProdFinEquiv.symm (⟨0, by decide⟩ : Fin (1 * 1)) =
      ((⟨0, by decide⟩ : Fin 1), (⟨0, by decide⟩ : Fin 1)) := by
    apply (finProdFinEquiv (m := 1) (n := 1)).injective
    exact hfwd.symm
  -- Goal reduces to `((1:ℝ)⁻¹ • choiIdentity 1) (0,0) (0,0) = 1`.
  change
      ((((1 : ℕ) : ℝ)⁻¹ : ℂ) • choiIdentity 1)
          (finProdFinEquiv.symm ⟨0, by decide⟩)
          (finProdFinEquiv.symm ⟨0, by decide⟩) =
        1
  rw [hpair]
  simp only [Matrix.smul_apply, choiIdentity_apply, ↓reduceIte, smul_eq_mul]
  -- `(1:ℝ)⁻¹ * 1 = 1`
  norm_num

/-! ### Cup-name snake / Choi recovery -/

/-- Effect of post-composing with a map into `1`. -/
theorem effect_comp_effect {n A : ℕ} (e : CPMap A 1) (Φ : CPMap n A) (i j : Fin n) :
    (CPMap.comp e Φ).effect i j =
      ∑ x : Fin A, ∑ y : Fin A, e.effect y x * Φ.choi (x, j) (y, i) := by
  simp [CPMap.effect, CPMap.choi_comp_apply, Fin.default_eq_zero]

/-- Effect of precomposing an effect with a basis equivalence. -/
theorem effect_comp_ofEquivalence {n m : ℕ} (e : Fin n ≃ Fin m)
    (Φ : Superoperator m 1) (i j : Fin n) :
    (Superoperator.comp Φ (Superoperator.ofEquivalence e)).cp.effect i j =
      Φ.cp.effect (e i) (e j) := by
  simp only [CPMap.effect, Superoperator.cp_comp, Fintype.sum_unique, Fin.default_eq_zero]
  have h := Superoperator.choi_comp_ofEquivalence_right e Φ (0 : Fin 1) 0 j i
  simpa [Superoperator.cp_comp] using h

theorem choi_identity_pair (A : ℕ) (c r d s : Fin A) :
    (CPMap.identity A).choi (c, r) (d, s) =
      (if c = r then (1 : ℂ) else 0) * (if d = s then 1 else 0) := by
  change choiIdentity A (c, r) (d, s) = _
  rw [choiIdentity_apply]

theorem choi_tensor_id_right {n A : ℕ} (Φ : CPMap n A)
    (a b : Fin A) (c d : Fin A) (p q : Fin n) (r s : Fin A) :
    (CPMap.tensor Φ (CPMap.identity A)).choi
        (finProdFinEquiv (a, c), finProdFinEquiv (p, r))
        (finProdFinEquiv (b, d), finProdFinEquiv (q, s)) =
      Φ.choi (a, p) (b, q) *
        (if c = r then (1 : ℂ) else 0) * (if d = s then 1 else 0) := by
  rw [CPMap.choi_tensor]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  have h1 : (CPMap.choiTensorEquiv n A A A).symm
      (finProdFinEquiv (a, c), finProdFinEquiv (p, r)) =
      ((a, p), (c, r)) := by
    dsimp [CPMap.choiTensorEquiv]; simp only [Equiv.symm_apply_apply]
  have h2 : (CPMap.choiTensorEquiv n A A A).symm
      (finProdFinEquiv (b, d), finProdFinEquiv (q, s)) =
      ((b, q), (d, s)) := by
    dsimp [CPMap.choiTensorEquiv]; simp only [Equiv.symm_apply_apply]
  rw [h1, h2]; simp only [Matrix.kronecker_apply]; rw [choi_identity_pair]; ring

theorem normalizedCup_effect_apply {A : ℕ} (hA : 0 < A) (u v : Fin (A * A)) :
    (normalizedCup A hA).cp.effect u v =
      ((A : ℝ)⁻¹ : ℂ) *
        (if (finProdFinEquiv.symm u).1 = (finProdFinEquiv.symm u).2 then (1 : ℂ) else 0) *
        (if (finProdFinEquiv.symm v).1 = (finProdFinEquiv.symm v).2 then 1 else 0) := by
  rw [normalizedCup_effect, normalizedCupMatrix]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply,
    choiIdentity_apply, smul_eq_mul]
  ring

theorem sum_me_indicators {n A : ℕ} (C : Matrix (Fin A × Fin n) (Fin A × Fin n) ℂ)
    (p q : Fin n) (r s : Fin A) :
    (∑ a : Fin A, ∑ c : Fin A, ∑ b : Fin A, ∑ d : Fin A,
        (if b = d then (1 : ℂ) else 0) * (if a = c then 1 else 0) *
          C (a, q) (b, p) * (if c = s then 1 else 0) * (if d = r then 1 else 0)) =
      C (s, q) (r, p) := by
  classical
  have hterm (a c b d : Fin A) :
      (if b = d then (1 : ℂ) else 0) * (if a = c then 1 else 0) *
          C (a, q) (b, p) * (if c = s then 1 else 0) * (if d = r then 1 else 0) =
        if a = s ∧ c = s ∧ b = r ∧ d = r then C (s, q) (r, p) else 0 := by
    by_cases hbd : b = d <;> by_cases hac : a = c <;>
      by_cases hcs : c = s <;> by_cases hdr : d = r <;>
        simp [hbd, hac, hcs, hdr] <;> (try subst_vars) <;> simp_all
  simp_rw [hterm]
  rw [Finset.sum_eq_single s]
  · rw [Finset.sum_eq_single s]
    · rw [Finset.sum_eq_single r]
      · rw [Finset.sum_eq_single r]
        · simp
        · intro d _ hd; simp [hd]
        · intro h; exact (h (Finset.mem_univ _)).elim
      · intro b _ hb; simp [hb]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · intro c _ hc; simp [hc]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · intro a _ ha; simp [ha]
  · intro h; exact (h (Finset.mem_univ _)).elim

/-- Maps into `1` are determined by their input effects. -/
theorem cpMap_one_ext_effect {n : ℕ} {Φ Ψ : CPMap n 1}
    (h : Φ.effect = Ψ.effect) : Φ = Ψ := by
  apply CPMap.ext_apply
  intro ρ
  have hΦ := CPMap.trace_applyMat_eq_effect Φ ρ
  have hΨ := CPMap.trace_applyMat_eq_effect Ψ ρ
  ext i j
  fin_cases i; fin_cases j
  have htΦ : Matrix.trace (Φ.applyMat ρ) = Φ.applyMat ρ 0 0 := by
    simp [Matrix.trace, Fin.default_eq_zero]
  have htΨ : Matrix.trace (Ψ.applyMat ρ) = Ψ.applyMat ρ 0 0 := by
    simp [Matrix.trace, Fin.default_eq_zero]
  calc
    Φ.applyMat ρ 0 0 = Matrix.trace (Φ.applyMat ρ) := htΦ.symm
    _ = Matrix.trace (Φ.effect * ρ) := hΦ
    _ = Matrix.trace (Ψ.effect * ρ) := by rw [h]
    _ = Matrix.trace (Ψ.applyMat ρ) := hΨ.symm
    _ = Ψ.applyMat ρ 0 0 := htΨ

/-- The normalized cup is invariant under the `A ↔ A` swap. -/
theorem normalizedCup_comp_swap {A : ℕ} (hA : 0 < A) :
    Superoperator.comp (normalizedCup A hA) (Superoperator.tensorSwap A A) =
      normalizedCup A hA := by
  apply Superoperator.ext
  apply cpMap_one_ext_effect
  ext i j
  simp only [Superoperator.tensorSwap]
  rw [effect_comp_ofEquivalence]
  simp only [normalizedCup_effect_apply hA, Superoperator.tensorSwapEquiv]
  simp [Equiv.trans_apply, Equiv.prodComm_apply, Equiv.symm_apply_apply]
  ring_nf
  congr 1 <;> simp [eq_comm]

theorem sum_finProd_sum_finProd {A : ℕ} (f : Fin (A * A) → Fin (A * A) → ℂ) :
    (∑ x : Fin (A * A), ∑ y : Fin (A * A), f x y) =
      ∑ a : Fin A, ∑ c : Fin A, ∑ b : Fin A, ∑ d : Fin A,
        f (finProdFinEquiv (a, c)) (finProdFinEquiv (b, d)) := by
  let e := finProdFinEquiv (m := A) (n := A)
  rw [← e.sum_comp (fun x => ∑ y : Fin (A * A), f x y)]
  have hin :
      (∑ x : Fin A × Fin A, ∑ y : Fin (A * A), f (e x) y) =
        ∑ x : Fin A × Fin A, ∑ y : Fin A × Fin A, f (e x) (e y) :=
    Finset.sum_congr rfl fun x _ =>
      (e.sum_comp (fun y : Fin (A * A) => f (e x) y)).symm
  refine hin.trans ?_
  rw [Fintype.sum_prod_type]
  conv_lhs =>
    enter [2, a, 2, c]
    rw [Fintype.sum_prod_type]

theorem cupName_comp_tensor_effect {A n : ℕ} (hA : 0 < A)
    (Φ : Superoperator n A) (p q : Fin n) (r s : Fin A) :
    (Superoperator.comp (normalizedCup A hA)
        (Superoperator.tensor Φ (Superoperator.identity A))).cp.effect
        (finProdFinEquiv (p, r)) (finProdFinEquiv (q, s)) =
      ((A : ℝ)⁻¹ : ℂ) * Φ.cp.choi (s, q) (r, p) := by
  classical
  rw [Superoperator.cp_comp, effect_comp_effect]
  have hid : (Superoperator.identity A).cp = CPMap.identity A := rfl
  simp only [Superoperator.cp_tensor, hid]
  rw [sum_finProd_sum_finProd (fun x y =>
      (normalizedCup A hA).cp.effect y x *
        (CPMap.tensor Φ.cp (CPMap.identity A)).choi
          (x, finProdFinEquiv (q, s)) (y, finProdFinEquiv (p, r)))]
  have hterm (a c b d : Fin A) :
      (normalizedCup A hA).cp.effect (finProdFinEquiv (b, d)) (finProdFinEquiv (a, c)) *
          (CPMap.tensor Φ.cp (CPMap.identity A)).choi
            (finProdFinEquiv (a, c), finProdFinEquiv (q, s))
            (finProdFinEquiv (b, d), finProdFinEquiv (p, r)) =
        (((A : ℝ)⁻¹ : ℂ) * (if b = d then (1 : ℂ) else 0) * (if a = c then 1 else 0)) *
          (Φ.cp.choi (a, q) (b, p) * (if c = s then 1 else 0) * (if d = r then 1 else 0)) := by
    rw [normalizedCup_effect_apply hA, choi_tensor_id_right]
    simp only [Equiv.symm_apply_apply]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => hterm a c b d]
  have hfac :
      (∑ a : Fin A, ∑ c : Fin A, ∑ b : Fin A, ∑ d : Fin A,
          (((A : ℝ)⁻¹ : ℂ) * (if b = d then (1 : ℂ) else 0) * (if a = c then 1 else 0)) *
            (Φ.cp.choi (a, q) (b, p) * (if c = s then 1 else 0) * (if d = r then 1 else 0))) =
        ((A : ℝ)⁻¹ : ℂ) *
          ∑ a : Fin A, ∑ c : Fin A, ∑ b : Fin A, ∑ d : Fin A,
            (if b = d then (1 : ℂ) else 0) * (if a = c then 1 else 0) *
              Φ.cp.choi (a, q) (b, p) * (if c = s then 1 else 0) *
                (if d = r then 1 else 0) := by
    simp only [mul_assoc, Finset.mul_sum]
  rw [hfac, sum_me_indicators]

/-- Cup-name effect at flat indices is `(1/A) • Φ.choi` (index-transposed). -/
theorem cupName_effect_apply {A n : ℕ} (hA : 0 < A)
    (Φ : Superoperator n A) (p q : Fin n) (r s : Fin A) :
    (cupName hA Φ).cp.effect
        (finProdFinEquiv (p, r)) (finProdFinEquiv (q, s)) =
      ((A : ℝ)⁻¹ : ℂ) * Φ.cp.choi (s, q) (r, p) := by
  simp only [cupName]
  rw [Superoperator.comp_assoc, normalizedCup_comp_swap hA,
    cupName_comp_tensor_effect]

/-- Snake at Choi level: reshape of the cup-name recovers `(1/A) • Φ.choi`. -/
theorem cupNameCP_cupName {A n : ℕ} (hA : 0 < A) (Φ : Superoperator n A) :
    (cupNameCP (cupName hA Φ)).choi =
      (A : ℝ)⁻¹ • Φ.cp.choi := by
  ext p q
  cases p with | mk a i =>
  cases q with | mk b j =>
  simp only [cupNameCP, effectAsChoi_apply]
  rw [cupName_effect_apply hA]
  -- `((A:ℝ)⁻¹ : ℂ) * z = (A:ℝ)⁻¹ • z` under the ℝ-action on ℂ.
  simp [Matrix.smul_apply, Algebra.smul_def]

/-- Recover a CP map by scaling the cup-name Choi reshape by `A`. -/
noncomputable def recoverCP {A : ℕ} (_hA : 0 < A) {n : ℕ}
    (χ : Superoperator (n * A) 1) : CPMap n A :=
  CPMap.scaleNonneg (A : ℝ) (Nat.cast_nonneg A) (cupNameCP χ)

@[simp]
theorem recoverCP_choi {A n : ℕ} (hA : 0 < A) (χ : Superoperator (n * A) 1) :
    (recoverCP hA χ).choi = (A : ℝ) • (cupNameCP χ).choi :=
  rfl

/-- Retraction of the cup-name reshape: `recoverCP (cupName Φ) = Φ.cp`. -/
theorem recoverCP_cupName {A n : ℕ} (hA : 0 < A) (Φ : Superoperator n A) :
    recoverCP hA (cupName hA Φ) = Φ.cp := by
  apply CPMap.ext
  change (A : ℝ) • (cupNameCP (cupName hA Φ)).choi = Φ.cp.choi
  rw [cupNameCP_cupName hA]
  have hA0 : (A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hA)
  -- `(A:ℝ) • ((A:ℝ)⁻¹ • M) = M`
  rw [smul_smul, mul_inv_cancel₀ hA0, one_smul]

/-- Fiberwise evaluation candidate: recover from the unit's cup-name probe. -/
noncomputable def evaluationFiber {A n : ℕ} (hA : 0 < A)
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier) :
    CPMap n A :=
  recoverCP hA (F.app (Superoperator.identity n) (normalizedCupProbe A hA))

/-- Retraction on the image of the unit (Choi level). -/
theorem evaluationFiber_unit {A n : ℕ} (hA : 0 < A) (Φ : Superoperator n A) :
    evaluationFiber hA ((DayNegation.unit (representable A)).app n Φ) = Φ.cp := by
  simp only [evaluationFiber]
  rw [unit_app_normalizedCupProbe, recoverCP_cupName]

/-- Package the recovered CP map as a superoperator on the unit image. -/
noncomputable def evaluationFiberSO {A n : ℕ} (hA : 0 < A)
    (Φ : Superoperator n A) : Superoperator n A where
  cp := evaluationFiber hA ((DayNegation.unit (representable A)).app n Φ)
  trace_nonincreasing := by
    rw [evaluationFiber_unit hA]
    exact Φ.trace_nonincreasing

/-- **Retraction** `evaluation ∘ unit = id` on fibers (via cup-name snake). -/
theorem evaluation_comp_unit_fiber {A n : ℕ} (hA : 0 < A)
    (Φ : Superoperator n A) :
    evaluationFiberSO hA Φ = Φ := by
  apply Superoperator.ext
  exact evaluationFiber_unit hA Φ

/-! ### Obstruction to naive total `Hom` via `recoverCP` -/

/-- Reshape of the identity effect is the identity Choi matrix. -/
theorem effectAsChoi_one {A n : ℕ} :
    effectAsChoi (A := A) (n := n) (1 : Matrix (Fin (n * A)) (Fin (n * A)) ℂ) =
      (1 : Matrix (Fin A × Fin n) (Fin A × Fin n) ℂ) := by
  ext p q
  simp only [effectAsChoi_apply, Matrix.one_apply]
  by_cases h : finProdFinEquiv (q.2, q.1) = finProdFinEquiv (p.2, p.1)
  · have hpq : p = q := by
      have := (finProdFinEquiv (m := n) (n := A)).injective h
      apply Prod.ext <;> simp_all [Prod.mk.injEq]
    simp [h, hpq]
  · have hpq : p ≠ q := by
      intro hpq; apply h; simp [hpq]
    simp [h, hpq]

/-- Matrix-level obstruction: `A² • I ≰ I` for `A > 1`. -/
theorem smul_one_not_le_one {A : ℕ} (hA : 1 < A) :
    ¬ (((A : ℝ) * A : ℂ) • (1 : Matrix (Fin A) (Fin A) ℂ) ≤
        (1 : Matrix (Fin A) (Fin A) ℂ)) := by
  intro hle
  have hpsd := Matrix.le_iff.mp hle
  let c : ℂ := (1 : ℂ) - ((A : ℝ) * A : ℂ)
  have hsub :
      (1 : Matrix (Fin A) (Fin A) ℂ) -
          ((A : ℝ) * A : ℂ) • (1 : Matrix (Fin A) (Fin A) ℂ) =
        c • (1 : Matrix (Fin A) (Fin A) ℂ) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, c, smul_eq_mul]
    split_ifs <;> ring
  rw [hsub] at hpsd
  let v : Fin A → ℂ := fun i => if i = ⟨0, Nat.zero_lt_of_lt hA⟩ then 1 else 0
  have hv := Matrix.PosSemidef.dotProduct_mulVec_nonneg hpsd v
  have hv' : star v ⬝ᵥ (c • (1 : Matrix (Fin A) (Fin A) ℂ)) *ᵥ v = c := by
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct, Pi.smul_apply,
      smul_eq_mul, v]
    rw [Finset.sum_eq_single ⟨0, Nat.zero_lt_of_lt hA⟩] <;> intros <;> simp_all
  have hre : c.re < 0 := by
    have : (1 : ℝ) < (A : ℝ) * A := by
      nlinarith [show (1 : ℝ) < A from Nat.one_lt_cast.mpr hA]
    simp only [c, Complex.sub_re, Complex.one_re]
    -- `(((A:ℝ)*A:ℂ)).re = A*A`
    have hr : (((A : ℝ) * A : ℂ)).re = (A : ℝ) * A := by
      simp
    rw [hr]
    linarith
  have hvre : 0 ≤ c.re := by
    rw [hv'] at hv
    exact (RCLike.nonneg_iff (K := ℂ)).mp hv |>.1
  exact not_le.mpr hre hvre

/-- `recoverCP` of the complete discard `I_{A²}` has Choi matrix `A • I`. -/
theorem recoverCP_discard_choi {A : ℕ} (hA : 0 < A) :
    (recoverCP hA
        (ofEffect (1 : Matrix (Fin (A * A)) (Fin (A * A)) ℂ)
          Matrix.PosSemidef.one le_rfl)).choi =
      (A : ℝ) • (1 : Matrix (Fin A × Fin A) (Fin A × Fin A) ℂ) := by
  simp only [recoverCP_choi, cupNameCP, ofEffect_effect, effectAsChoi_one]

/-- Input effect of `recoverCP I_{A²}` is `A² • I`. -/
theorem recoverCP_discard_effect {A : ℕ} (hA : 0 < A) :
    (recoverCP hA
        (ofEffect (1 : Matrix (Fin (A * A)) (Fin (A * A)) ℂ)
          Matrix.PosSemidef.one le_rfl)).effect =
      ((A : ℝ) * A : ℂ) • (1 : Matrix (Fin A) (Fin A) ℂ) := by
  have hC :
      cupNameCP (ofEffect (1 : Matrix (Fin (A * A)) (Fin (A * A)) ℂ)
          Matrix.PosSemidef.one le_rfl) =
        ⟨1, Matrix.PosSemidef.one⟩ := by
    apply CPMap.ext
    simp [cupNameCP, ofEffect_effect, effectAsChoi_one]
  simp only [recoverCP, hC]
  ext i j
  simp only [CPMap.effect, CPMap.choi_scaleNonneg, Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp [Finset.sum_const, nsmul_eq_mul, smul_eq_mul]
    try ring
  · have : ¬ j = i := Ne.symm hij
    simp [hij, this]

/-- **Obstruction:** `recoverCP` of discard `I_{A²}` is not TNI for `A > 1`
(effect `A² I ≰ I`).  So cup-name reshape cannot be a total `Hom` on *all*
effects — only on cup-names (`evaluation_comp_unit_fiber`). -/
theorem recoverCP_discard_not_tni {A : ℕ} (hA : 1 < A) :
    ¬ TraceNonincreasing
      (recoverCP (Nat.zero_lt_of_lt hA)
        (ofEffect (1 : Matrix (Fin (A * A)) (Fin (A * A)) ℂ)
          Matrix.PosSemidef.one le_rfl)) := by
  rw [traceNonincreasing_iff_effect_le_one]
  intro hle
  rw [recoverCP_discard_effect (Nat.zero_lt_of_lt hA)] at hle
  exact smul_one_not_le_one hA hle

/-! ### Cup-probe non-generation for `A > 1` -/

theorem dualFiberBilinear_app_id_id {A q : ℕ}
    (χ : Superoperator (q * A) 1) :
    (dualFiberBilinear A q χ).app
        (Superoperator.identity q) (Superoperator.identity A) = χ := by
  change Superoperator.comp χ
      (Superoperator.tensor (Superoperator.identity q) (Superoperator.identity A)) = χ
  rw [Superoperator.tensor_identity, Superoperator.comp_identity]

theorem dualFiberBilinear_injective {A q : ℕ} :
    Function.Injective (dualFiberBilinear A q) := by
  intro χ₁ χ₂ h
  have :=
    congrArg
      (fun b : ((DayNegation.neg (representable A)).obj q).Carrier =>
        b.app (Superoperator.identity q) (Superoperator.identity A)) h
  exact (dualFiberBilinear_app_id_id χ₁).symm.trans
    (this.trans (dualFiberBilinear_app_id_id χ₂))

/-- Day action on a dual-fiber effect is right tensor-precomposition. -/
theorem act_dualFiberBilinear {A m n : ℕ}
    (e : Superoperator (n * A) 1) (f : Superoperator m n) :
    (DayNegation.neg (representable A)).act (dualFiberBilinear A n e) f =
      dualFiberBilinear A m
        (Superoperator.comp e
          (Superoperator.tensor f (Superoperator.identity A))) := by
  apply Bilinear.ext
  intro p q r s
  change Superoperator p m at r
  change Superoperator q A at s
  change
      Superoperator.comp e
          (Superoperator.tensor (Superoperator.comp f r) s) =
        Superoperator.comp
          (Superoperator.comp e
            (Superoperator.tensor f (Superoperator.identity A)))
          (Superoperator.tensor r s)
  calc
    Superoperator.comp e (Superoperator.tensor (Superoperator.comp f r) s) =
      Superoperator.comp e
          (Superoperator.tensor (Superoperator.comp f r)
            (Superoperator.comp (Superoperator.identity A) s)) := by
              rw [Superoperator.identity_comp]
    _ = Superoperator.comp e
          (Superoperator.comp
            (Superoperator.tensor f (Superoperator.identity A))
            (Superoperator.tensor r s)) := by
              rw [← Superoperator.tensor_comp]
    _ = Superoperator.comp
          (Superoperator.comp e
            (Superoperator.tensor f (Superoperator.identity A)))
          (Superoperator.tensor r s) :=
            Superoperator.comp_assoc _ _ _

/-- Probe action is cup-precomposition: `act probe f = dualFiberBilinear(cup ∘ (f ⊗ id))`. -/
theorem normalizedCupProbe_act_eq {A q : ℕ} (hA : 0 < A)
    (f : Superoperator q A) :
    (DayNegation.neg (representable A)).act (normalizedCupProbe A hA) f =
      dualFiberBilinear A q
        (Superoperator.comp (normalizedCup A hA)
          (Superoperator.tensor f (Superoperator.identity A))) := by
  apply Bilinear.ext
  intro p q' r s
  change Superoperator p q at r
  change Superoperator q' A at s
  change
      Superoperator.comp (normalizedCup A hA)
          (Superoperator.tensor (Superoperator.comp f r) s) =
        Superoperator.comp
          (Superoperator.comp (normalizedCup A hA)
            (Superoperator.tensor f (Superoperator.identity A)))
          (Superoperator.tensor r s)
  calc
    Superoperator.comp (normalizedCup A hA)
        (Superoperator.tensor (Superoperator.comp f r) s) =
      Superoperator.comp (normalizedCup A hA)
          (Superoperator.tensor (Superoperator.comp f r)
            (Superoperator.comp (Superoperator.identity A) s)) := by
              rw [Superoperator.identity_comp]
    _ = Superoperator.comp (normalizedCup A hA)
          (Superoperator.comp
            (Superoperator.tensor f (Superoperator.identity A))
            (Superoperator.tensor r s)) := by
              rw [← Superoperator.tensor_comp]
    _ = Superoperator.comp
          (Superoperator.comp (normalizedCup A hA)
            (Superoperator.tensor f (Superoperator.identity A)))
          (Superoperator.tensor r s) :=
            Superoperator.comp_assoc _ _ _

/-- Swap-invariance of the cup collapses `cup ∘ (f ⊗ id)` to `cupName f`. -/
theorem cup_tensor_eq_cupName {A q : ℕ} (hA : 0 < A)
    (f : Superoperator q A) :
    Superoperator.comp (normalizedCup A hA)
        (Superoperator.tensor f (Superoperator.identity A)) =
      cupName hA f := by
  simp only [cupName]
  rw [Superoperator.comp_assoc, normalizedCup_comp_swap hA]

theorem normalizedCupProbe_act_eq_cupName {A q : ℕ} (hA : 0 < A)
    (f : Superoperator q A) :
    (DayNegation.neg (representable A)).act (normalizedCupProbe A hA) f =
      dualFiberBilinear A q (cupName hA f) := by
  rw [normalizedCupProbe_act_eq, cup_tensor_eq_cupName]

/-- Complete discard effect on `A²` as a dual-fiber witness. -/
noncomputable def discardEffectAA (A : ℕ) : Superoperator (A * A) 1 :=
  ofEffect (1 : Matrix (Fin (A * A)) (Fin (A * A)) ℂ)
    Matrix.PosSemidef.one le_rfl

theorem cupName_ne_discard {A : ℕ} (hA : 1 < A)
    (f : Superoperator A A) :
    cupName (Nat.zero_lt_of_lt hA) f ≠ discardEffectAA A := by
  intro hf
  have hrec := congrArg (recoverCP (Nat.zero_lt_of_lt hA)) hf
  rw [recoverCP_cupName] at hrec
  have hTNI : TraceNonincreasing (recoverCP (Nat.zero_lt_of_lt hA) (discardEffectAA A)) := by
    rw [← hrec]
    exact f.trace_nonincreasing
  exact recoverCP_discard_not_tni hA hTNI

/-- Cup-names do not exhaust `Superoperator(A²,1)` for `A > 1`. -/
theorem cupName_not_surjective {A : ℕ} (hA : 1 < A) :
    ¬ Function.Surjective (cupName (Nat.zero_lt_of_lt hA) (n := A)) := by
  intro hsurj
  obtain ⟨f, hf⟩ := hsurj (discardEffectAA A)
  exact cupName_ne_discard hA f hf

/-- **Non-generation:** the Day-action orbit of `normalizedCupProbe` is a proper
subset of `¬y(A)_A` for `A > 1`.  Witness: `dualFiberBilinear discardEffectAA`. -/
theorem normalizedCupProbe_not_generates {A : ℕ} (hA : 1 < A) :
    ∃ χ : ((DayNegation.neg (representable A)).obj A).Carrier,
      ∀ f : Superoperator A A,
        (DayNegation.neg (representable A)).act
            (normalizedCupProbe A (Nat.zero_lt_of_lt hA)) f ≠ χ := by
  refine ⟨dualFiberBilinear A A (discardEffectAA A), fun f hf => ?_⟩
  have hχ : cupName (Nat.zero_lt_of_lt hA) f = discardEffectAA A :=
    dualFiberBilinear_injective
      ((normalizedCupProbe_act_eq_cupName (Nat.zero_lt_of_lt hA) f).symm.trans hf)
  exact cupName_ne_discard hA f hχ

/-! ### Effect-family reconstruction (surjectivity strategy) -/

/-- Fiber-1 packaging of an effect `A → 1` into `¬y(A)_1`. -/
noncomputable def effectPack (A : ℕ) (e : Superoperator A 1) :
    ((DayNegation.neg (representable A)).obj 1).Carrier :=
  dualFiberBilinear A 1
    (Superoperator.comp e (Superoperator.tensorLeftUnitor A))

/-- Effect-family pairing of a double-dual element against fiber-1 effects.
Strips Day braiding / `1*n` unitor so the result matches `effectPrecompose`. -/
noncomputable def doubleDualEffectPairing {A n : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (e : Superoperator A 1) : Superoperator n 1 :=
  Superoperator.comp
    (Superoperator.comp
      (F.app (Superoperator.identity n) (effectPack A e))
      (Superoperator.tensorSwap 1 n))
    (Superoperator.tensorLeftUnitorInv n)

/-- On the unit image, the effect pairing recovers ordinary precomposition. -/
theorem doubleDualEffectPairing_unit {A n : ℕ}
    (Φ : Superoperator n A) (e : Superoperator A 1) :
    doubleDualEffectPairing
        ((DayNegation.unit (representable A)).app n Φ) e =
      effectPrecompose Φ e := by
  change Superoperator n A at Φ
  unfold doubleDualEffectPairing effectPack
  have hraw :
      ((DayNegation.unit (representable A)).app n Φ).app
          (Superoperator.identity n)
          (dualFiberBilinear A 1
            (Superoperator.comp e (Superoperator.tensorLeftUnitor A))) =
        Superoperator.comp
          (Superoperator.comp (effectPrecompose Φ e)
            (Superoperator.tensorLeftUnitor n))
          (Superoperator.tensorSwap n 1) := by
    rw [unit_eval_bilinear, dualFiberBilinear_one_app]
  rw [hraw]
  have h1 :
      Superoperator.comp
          (Superoperator.comp
            (Superoperator.comp (effectPrecompose Φ e)
              (Superoperator.tensorLeftUnitor n))
            (Superoperator.tensorSwap n 1))
          (Superoperator.tensorSwap 1 n) =
        Superoperator.comp (effectPrecompose Φ e)
          (Superoperator.tensorLeftUnitor n) := by
    rw [← Superoperator.comp_assoc,
      Superoperator.tensorSwap_involutive 1 n,
      Superoperator.comp_identity]
  rw [h1, ← Superoperator.comp_assoc, Superoperator.tensorLeftUnitor_hom_inv,
    Superoperator.comp_identity]

/-- Pairing agreement implies raw evaluation agrees on every `effectPack`. -/
theorem pairing_eq_imp_app_effectPack {A n : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (Φ : Superoperator n A)
    (hα : ∀ e : Superoperator A 1,
      doubleDualEffectPairing F e = effectPrecompose Φ e)
    (e : Superoperator A 1) :
    F.app (Superoperator.identity n) (effectPack A e) =
      ((DayNegation.unit (representable A)).app n Φ).app
        (Superoperator.identity n) (effectPack A e) := by
  have heq :
      doubleDualEffectPairing F e =
        doubleDualEffectPairing
          ((DayNegation.unit (representable A)).app n Φ) e :=
    (hα e).trans (doubleDualEffectPairing_unit Φ e).symm
  change
      Superoperator.comp
          (Superoperator.comp
            (F.app (Superoperator.identity n) (effectPack A e))
            (Superoperator.tensorSwap 1 n))
          (Superoperator.tensorLeftUnitorInv n) =
        Superoperator.comp
          (Superoperator.comp
            (((DayNegation.unit (representable A)).app n Φ).app
              (Superoperator.identity n) (effectPack A e))
            (Superoperator.tensorSwap 1 n))
          (Superoperator.tensorLeftUnitorInv n) at heq
  have heq2 :=
    congrArg
      (fun χ : Superoperator n 1 =>
        Superoperator.comp χ (Superoperator.tensorLeftUnitor n)) heq
  have hcancel (ζ : Superoperator (1 * n) 1) :
      Superoperator.comp
          (Superoperator.comp ζ (Superoperator.tensorLeftUnitorInv n))
          (Superoperator.tensorLeftUnitor n) =
        ζ := by
    rw [← Superoperator.comp_assoc, Superoperator.tensorLeftUnitor_inv_hom,
      Superoperator.comp_identity]
  rw [hcancel, hcancel] at heq2
  exact comp_tensorSwap_injective heq2

/-- Born scalar of a `1→1` map on the unit input. -/
noncomputable def bornScalar (χ : Superoperator 1 1) : ℂ :=
  χ.cp.applyMat (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0

theorem bornScalar_effectPrecompose {A : ℕ}
    (Φ : Superoperator 1 A) (e : Superoperator A 1) :
    bornScalar (effectPrecompose Φ e) =
      Matrix.trace
        (e.cp.effect * Φ.cp.applyMat (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  simp only [bornScalar, effectPrecompose, Superoperator.cp_comp,
    CPMap.applyMat_comp]
  have ht :
      Matrix.trace (e.cp.applyMat (Φ.cp.applyMat 1)) =
        e.cp.applyMat (Φ.cp.applyMat 1) 0 0 := by
    simp [Matrix.trace, Fin.default_eq_zero]
  exact ht.symm.trans (CPMap.trace_applyMat_eq_effect e.cp _)

/-- Effect expectation of a `1→1`-valued pairing on a Loewner matrix. -/
noncomputable def effectExpectation {A : ℕ}
    (α : Superoperator A 1 → Superoperator 1 1)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hpsd : E.PosSemidef) (hle : E ≤ 1) : ℂ :=
  bornScalar (α (ofEffect E hpsd hle))

theorem effectExpectation_unit {A : ℕ}
    (Φ : Superoperator 1 A)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hpsd : E.PosSemidef) (hle : E ≤ 1) :
    effectExpectation (effectPrecompose Φ) E hpsd hle =
      Matrix.trace (E * Φ.cp.applyMat (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  simp only [effectExpectation, bornScalar_effectPrecompose, ofEffect_effect]

/-- Uniqueness half of the analytic gate: an effect pairing determines at most
one `Φ` (`effectPrecompose_injective`). -/
theorem effect_pairing_unique {A n : ℕ}
    {Φ Ψ : Superoperator n A}
    (h : ∀ e : Superoperator A 1,
      effectPrecompose Φ e = effectPrecompose Ψ e) :
    Φ = Ψ :=
  effectPrecompose_injective h

/-! ## n=1 analytic reconstruction (preparations) -/

/-- A real scalar matrix `z·I₁` is Loewner-below `I₁` when `0 ≤ z ≤ 1`. -/
theorem scalar_matrix_le_one (z : ℂ) (_hre : 0 ≤ z.re) (hle : z.re ≤ 1)
    (him : z.im = 0) :
    (Matrix.of fun _ _ : Fin 1 => z) ≤ (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  have hz :
      Matrix.of (fun _ _ : Fin 1 => z) = diagonal (fun _ : Fin 1 => z) := by
    ext i j; fin_cases i; fin_cases j; simp [diagonal]
  have h1 :
      (1 : Matrix (Fin 1) (Fin 1) ℂ) =
        diagonal (fun _ : Fin 1 => (1 : ℂ)) := by
    ext i j; fin_cases i; fin_cases j; simp [diagonal]
  rw [hz, h1, Matrix.le_iff, diagonal_sub]
  refine PosSemidef.diagonal fun i => ?_
  fin_cases i
  refine Complex.nonneg_iff.mpr ⟨?_, ?_⟩
  · simp; linarith
  · simp [him]

/-- Package a subnormalized density `ρ` (`ρ ⪰ 0`, `Tr ρ ≤ 1`) as a
preparation `Superoperator 1 A` with Choi block equal to `ρ`. -/
noncomputable def preparationOfDensity {A : ℕ}
    (ρ : Matrix (Fin A) (Fin A) ℂ)
    (hpsd : ρ.PosSemidef)
    (hle : (Matrix.trace ρ).re ≤ 1) : Superoperator 1 A := by
  let C : Matrix (Fin A × Fin 1) (Fin A × Fin 1) ℂ := fun p q => ρ p.1 q.1
  have hC : C.PosSemidef := by
    have : C =
        ρ.submatrix (Prod.fst : Fin A × Fin 1 → Fin A)
          (Prod.fst : Fin A × Fin 1 → Fin A) := by
      ext; rfl
    rw [this]; exact hpsd.submatrix _
  refine ⟨⟨C, hC⟩, (traceNonincreasing_iff_effect_le_one _).mpr ?_⟩
  have heff :
      (⟨C, hC⟩ : CPMap 1 A).effect =
        Matrix.of fun _ _ : Fin 1 => Matrix.trace ρ := by
    ext i j
    fin_cases i; fin_cases j
    simp only [CPMap.effect, C, Matrix.trace, Matrix.of_apply, diag]
  have htr_nn : 0 ≤ (Matrix.trace ρ).re :=
    (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_nonneg hpsd)).1
  have him0 : (Matrix.trace ρ).im = 0 :=
    (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_nonneg hpsd)).2.symm
  rw [heff]
  exact scalar_matrix_le_one _ htr_nn hle him0

@[simp]
theorem preparationOfDensity_choi {A : ℕ}
    (ρ : Matrix (Fin A) (Fin A) ℂ)
    (hpsd : ρ.PosSemidef)
    (hle : (Matrix.trace ρ).re ≤ 1) (p q : Fin A × Fin 1) :
    (preparationOfDensity ρ hpsd hle).cp.choi p q = ρ p.1 q.1 :=
  rfl

/-- Applying a preparation to `I₁` recovers the packaged density. -/
theorem preparationOfDensity_applyMat_one {A : ℕ}
    (ρ : Matrix (Fin A) (Fin A) ℂ)
    (hpsd : ρ.PosSemidef)
    (hle : (Matrix.trace ρ).re ≤ 1) :
    (preparationOfDensity ρ hpsd hle).cp.applyMat
      (1 : Matrix (Fin 1) (Fin 1) ℂ) = ρ := by
  ext a b
  have h :=
    KrausFamily.applyMat_apply
      (CPMap.toKraus (preparationOfDensity ρ hpsd hle).cp) 1 a b
  change
      KrausFamily.applyMat
        (CPMap.toKraus (preparationOfDensity ρ hpsd hle).cp) 1 a b =
      ρ a b
  rw [h, CPMap.choi_toKraus]
  simp [Matrix.one_apply, preparationOfDensity_choi]

/-- `1→1` superoperators are determined by their Born scalar on `I₁`. -/
theorem superoperator_one_one_eq_of_bornScalar
    {χ ψ : Superoperator 1 1} (h : bornScalar χ = bornScalar ψ) :
    χ = ψ := by
  apply Superoperator.ext
  apply CPMap.ext_apply
  intro ρ
  have hρ : ρ = ρ 0 0 • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j; fin_cases i; fin_cases j; simp
  have h1 : χ.cp.applyMat 1 = ψ.cp.applyMat 1 := by
    ext i j; fin_cases i; fin_cases j
    simpa [bornScalar] using h
  rw [hρ, CPMap.applyMat_smul, CPMap.applyMat_smul, h1]

/-- Every effect `A → 1` equals `ofEffect` of its intrinsic effect matrix. -/
theorem ofEffect_effect_eq {A : ℕ} (e : Superoperator A 1) :
    ofEffect e.cp.effect (CPMap.effect_posSemidef e.cp)
      ((traceNonincreasing_iff_effect_le_one e.cp).1 e.trace_nonincreasing) =
      e := by
  apply Superoperator.ext
  apply CPMap.ext
  ext p q
  have hchoi :
      (ofEffect e.cp.effect (CPMap.effect_posSemidef e.cp)
          ((traceNonincreasing_iff_effect_le_one e.cp).1
            e.trace_nonincreasing)).cp.choi p q =
        e.cp.effect q.2 p.2 :=
    rfl
  rw [hchoi]
  simp only [CPMap.effect, Fin.sum_univ_one]
  congr 1
  · exact Prod.ext (Subsingleton.elim _ _) rfl
  · exact Prod.ext (Subsingleton.elim _ _) rfl

/-- Choi additivity of `ofEffect` on Loewner-summable effects. -/
theorem ofEffect_add_choi {A : ℕ}
    (E F : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hF : F.PosSemidef)
    (hEF : E + F ≤ 1) (hE1 : E ≤ 1) (hF1 : F ≤ 1) :
    (ofEffect (E + F) (hE.add hF) hEF).cp =
      (ofEffect E hE hE1).cp + (ofEffect F hF hF1).cp := by
  apply CPMap.ext
  ext p q
  change (E + F) q.2 p.2 = E q.2 p.2 + F q.2 p.2
  rw [Matrix.add_apply]

/-- Norm squared `star v ⬝ᵥ v` is a nonnegative real. -/
theorem star_dotProduct_self_nonneg_real {ι : Type*} [Fintype ι]
    (v : ι → ℂ) :
    0 ≤ (star v ⬝ᵥ v).re ∧ (star v ⬝ᵥ v).im = 0 := by
  have hnn : (0 : ℂ) ≤ star v ⬝ᵥ v := dotProduct_star_self_nonneg v
  exact ⟨(Complex.nonneg_iff.mp hnn).1, (Complex.nonneg_iff.mp hnn).2.symm⟩

/-- Normalize a nonzero vector to unit length using the real square root of
its squared norm. -/
noncomputable def normalizeVec {ι : Type*} [Fintype ι] (v : ι → ℂ)
    (_hv : star v ⬝ᵥ v ≠ 0) : ι → ℂ :=
  let nrm := star v ⬝ᵥ v
  let s : ℂ := (Real.sqrt nrm.re : ℂ)
  s⁻¹ • v

theorem normalizeVec_norm {ι : Type*} [Fintype ι] (v : ι → ℂ)
    (hv : star v ⬝ᵥ v ≠ 0) :
    star (normalizeVec v hv) ⬝ᵥ normalizeVec v hv = 1 := by
  let nrm := star v ⬝ᵥ v
  let s : ℂ := (Real.sqrt nrm.re : ℂ)
  have hre : 0 ≤ nrm.re := (star_dotProduct_self_nonneg_real v).1
  have him : nrm.im = 0 := (star_dotProduct_self_nonneg_real v).2
  have hs_ne : s ≠ 0 := by
    intro hs0
    have hre0 : nrm.re = 0 :=
      (Real.sqrt_eq_zero hre).1 (by
        have : (s : ℂ).re = 0 := by
          simpa [Complex.ofReal_re] using congrArg Complex.re hs0
        simpa [s, Complex.ofReal_re] using this)
    exact hv (Complex.ext hre0 him)
  have hstar_s : star s = s := by
    simp only [s, Complex.star_def, Complex.conj_ofReal]
  have hv_norm : nrm = s * s := by
    apply Complex.ext
    · have hims : s.im = 0 := by simp [s]
      have : nrm.re = s.re * s.re := by
        simpa [s, Complex.ofReal_re] using (Real.mul_self_sqrt hre).symm
      simpa [Complex.mul_re, hims] using this
    · simp [Complex.mul_im, him, s]
  change star (s⁻¹ • v) ⬝ᵥ (s⁻¹ • v) = 1
  rw [star_dotProduct_smul_self]
  change star s⁻¹ * s⁻¹ * nrm = 1
  rw [hv_norm, star_inv₀, hstar_s]
  field_simp [hs_ne]

/-- Homogeneous quadratic form of an effect pairing on vectors, via Born
reading of the normalized rank-one Loewner probe. -/
noncomputable def effectPairingQuad {A : ℕ}
    (α : Superoperator A 1 → Superoperator 1 1) (v : Fin A → ℂ) : ℂ :=
  let nrm := star v ⬝ᵥ v
  if h : nrm = 0 then 0
  else
    nrm *
      bornScalar
        (α (ofEffect
          (Matrix.vecMulVec (normalizeVec v h) (star (normalizeVec v h)))
          (Matrix.posSemidef_vecMulVec_self_star _)
          (vecMulVec_unit_le_one _ (normalizeVec_norm v h))))

/-- Polarization of a quadratic form into a candidate sesquilinear reading. -/
noncomputable def effectPairingPolar {A : ℕ}
    (α : Superoperator A 1 → Superoperator 1 1)
    (x y : Fin A → ℂ) : ℂ :=
  let q := effectPairingQuad α
  (q (x + y) - q (x - y) -
      Complex.I * q (x + Complex.I • y) +
        Complex.I * q (x - Complex.I • y)) / 4

/-- Density matrix recovered by polarization of the Born quadratic form on
the standard basis. -/
noncomputable def densityFromEffectPairing {A : ℕ}
    (α : Superoperator A 1 → Superoperator 1 1) :
    Matrix (Fin A) (Fin A) ℂ :=
  fun i j =>
    effectPairingPolar α (Pi.single i (1 : ℂ)) (Pi.single j (1 : ℂ))

/-- Existence half of the analytic gate at fiber `n = 1`: a Born pairing on
Loewner effects that is represented by a subnormalized density `ρ` yields a
preparation `Φ` with `e ∘ Φ = α e` for every effect `e`. -/
theorem exists_superoperator_of_effect_pairing {A : ℕ}
    (α : Superoperator A 1 → Superoperator 1 1)
    (ρ : Matrix (Fin A) (Fin A) ℂ)
    (hpsd : ρ.PosSemidef)
    (hle : (Matrix.trace ρ).re ≤ 1)
    (hα : ∀ (E : Matrix (Fin A) (Fin A) ℂ)
      (hE : E.PosSemidef) (hEle : E ≤ 1),
      bornScalar (α (ofEffect E hE hEle)) = Matrix.trace (E * ρ)) :
    ∃ Φ : Superoperator 1 A,
      ∀ e : Superoperator A 1, effectPrecompose Φ e = α e := by
  refine ⟨preparationOfDensity ρ hpsd hle, fun e => ?_⟩
  apply superoperator_one_one_eq_of_bornScalar
  have heff := ofEffect_effect_eq e
  have hEpsd : e.cp.effect.PosSemidef := CPMap.effect_posSemidef e.cp
  have hEle : e.cp.effect ≤ 1 :=
    (traceNonincreasing_iff_effect_le_one e.cp).1 e.trace_nonincreasing
  calc
    bornScalar (effectPrecompose (preparationOfDensity ρ hpsd hle) e) =
        Matrix.trace
          (e.cp.effect *
            (preparationOfDensity ρ hpsd hle).cp.applyMat
              (1 : Matrix (Fin 1) (Fin 1) ℂ)) :=
      bornScalar_effectPrecompose _ _
    _ = Matrix.trace (e.cp.effect * ρ) := by
          rw [preparationOfDensity_applyMat_one]
    _ = bornScalar (α (ofEffect e.cp.effect hEpsd hEle)) :=
          (hα e.cp.effect hEpsd hEle).symm
    _ = bornScalar (α e) := by rw [heff]

/-- On the unit image, the Born pairing is represented by `Φ(I₁)`. -/
theorem effectPrecompose_born_eq_trace {A : ℕ}
    (Φ : Superoperator 1 A)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hEle : E ≤ 1) :
    bornScalar (effectPrecompose Φ (ofEffect E hE hEle)) =
      Matrix.trace (E * Φ.cp.applyMat (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  simpa [effectExpectation] using effectExpectation_unit Φ E hE hEle

/-- Specialization: the existence gate applies to every unit-image pairing. -/
theorem exists_superoperator_of_effect_pairing_unit {A : ℕ}
    (Φ : Superoperator 1 A) :
    ∃ Ψ : Superoperator 1 A,
      ∀ e : Superoperator A 1, effectPrecompose Ψ e = effectPrecompose Φ e :=
  exists_superoperator_of_effect_pairing (effectPrecompose Φ)
    (Φ.cp.applyMat (1 : Matrix (Fin 1) (Fin 1) ℂ))
    (CPMap.applyMat_posSemidef Φ.cp Matrix.PosSemidef.one)
    (by
      have h :=
        Φ.trace_nonincreasing (1 : Matrix (Fin 1) (Fin 1) ℂ)
          Matrix.PosSemidef.one
      have : (Matrix.trace (1 : Matrix (Fin 1) (Fin 1) ℂ)).re = 1 := by
        simp [Matrix.trace_one]
      simpa [this] using h)
    (fun E hE hEle => effectPrecompose_born_eq_trace Φ E hE hEle)

/-- On the unit image, the Born quadratic form recovers the state quadratic
form `v ↦ ⟨v|Φ(I)|v⟩`. -/
theorem effectPairingQuad_unit {A : ℕ}
    (Φ : Superoperator 1 A) (v : Fin A → ℂ) :
    effectPairingQuad (effectPrecompose Φ) v =
      star v ⬝ᵥ (Φ.cp.applyMat (1 : Matrix (Fin 1) (Fin 1) ℂ)) *ᵥ v := by
  let ρ := Φ.cp.applyMat (1 : Matrix (Fin 1) (Fin 1) ℂ)
  let nrm := star v ⬝ᵥ v
  have him : nrm.im = 0 := (star_dotProduct_self_nonneg_real v).2
  simp only [effectPairingQuad]
  split_ifs with h
  · have : v = 0 := (dotProduct_star_self_eq_zero).1 h
    simp [this]
  · have hw := normalizeVec_norm v h
    have hborn :=
      effectPrecompose_born_eq_trace Φ
        (Matrix.vecMulVec (normalizeVec v h) (star (normalizeVec v h)))
        (Matrix.posSemidef_vecMulVec_self_star _)
        (vecMulVec_unit_le_one _ hw)
    rw [hborn, trace_vecMulVec_mul]
    set w := normalizeVec v h
    set s : ℂ := (Real.sqrt nrm.re : ℂ)
    have hvw : v = s • w := by
      simp only [w, normalizeVec]
      ext i
      change v i = s * (s⁻¹ * v i)
      have hs_ne : s ≠ 0 := by
        intro hs0
        have hre := (star_dotProduct_self_nonneg_real v).1
        have hre0 : nrm.re = 0 :=
          (Real.sqrt_eq_zero hre).1 (by
            simpa [s, Complex.ofReal_re] using congrArg Complex.re hs0)
        exact h (Complex.ext hre0 him)
      field_simp [hs_ne]
    have hstar_s : star s = s := by
      simp [s, Complex.conj_ofReal]
    have hnrm : nrm = s * s := by
      apply Complex.ext
      · have hims : s.im = 0 := by simp [s]
        have : nrm.re = s.re * s.re := by
          simpa [s, Complex.ofReal_re] using
            (Real.mul_self_sqrt (star_dotProduct_self_nonneg_real v).1).symm
        simpa [Complex.mul_re, hims] using this
      · simpa [Complex.mul_im, s] using him
    calc
      nrm * (star w ⬝ᵥ ρ *ᵥ w) =
          star s * s * (star w ⬝ᵥ ρ *ᵥ w) := by rw [hnrm, hstar_s]
      _ = star (s • w) ⬝ᵥ ρ *ᵥ (s • w) := (quad_smul ρ s w).symm
      _ = star v ⬝ᵥ ρ *ᵥ v := by rw [← hvw]


/-! ### Double-dual Born calculus (n=1) -/

/-- Born scalars of `1→1` maps are real and lie in `[0,1]`. -/
theorem bornScalar_nonneg (χ : Superoperator 1 1) :
    0 ≤ (bornScalar χ).re ∧ (bornScalar χ).im = 0 ∧ (bornScalar χ).re ≤ 1 := by
  have hpsd := CPMap.applyMat_posSemidef χ.cp Matrix.PosSemidef.one
  have htr :=
    χ.trace_nonincreasing (1 : Matrix (Fin 1) (Fin 1) ℂ) Matrix.PosSemidef.one
  have ht1 : (Matrix.trace (1 : Matrix (Fin 1) (Fin 1) ℂ)).re = 1 := by
    simp [Matrix.trace_one]
  have heq : bornScalar χ = Matrix.trace (χ.cp.applyMat 1) := by
    simp [bornScalar, Matrix.trace, Fin.default_eq_zero]
  have hnn := Matrix.PosSemidef.trace_nonneg hpsd
  rw [heq]
  exact ⟨(Complex.nonneg_iff.mp hnn).1, (Complex.nonneg_iff.mp hnn).2.symm,
    by simpa [ht1] using htr⟩

theorem bornScalar_eq_choi (ψ : Superoperator 1 1) :
    bornScalar ψ = ψ.cp.choi (0, 0) (0, 0) := by
  have h := KrausFamily.applyMat_apply (CPMap.toKraus ψ.cp) 1 0 0
  simp only [bornScalar]
  change KrausFamily.applyMat (CPMap.toKraus ψ.cp) 1 0 0 =
    ψ.cp.choi (0, 0) (0, 0)
  rw [h, CPMap.choi_toKraus]
  simp [Matrix.one_apply]

theorem bornScalar_hasSum {ι : Type} [Countable ι]
    {f : ι → Superoperator 1 1} {χ : Superoperator 1 1}
    (h : SigmaMon.ChoiSum.HasSum f χ) :
    HasSum (fun i => bornScalar (f i)) (bornScalar χ) := by
  simpa only [bornScalar_eq_choi] using
    (Pi.hasSum.mp (Pi.hasSum.mp h ⟨0, 0⟩) ⟨0, 0⟩)

theorem ofEffect_hasSum_add {A : ℕ}
    (E F : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hF : F.PosSemidef)
    (hE1 : E ≤ 1) (hF1 : F ≤ 1) (hEF : E + F ≤ 1) :
    SigmaMon.ChoiSum.HasSum
      (fun i : Bool => if i then ofEffect E hE hE1 else ofEffect F hF hF1)
      (ofEffect (E + F) (hE.add hF) hEF) := by
  let fChoi : Bool → Matrix (Fin 1 × Fin A) (Fin 1 × Fin A) ℂ :=
    fun i => (if i then ofEffect E hE hE1 else ofEffect F hF hF1).cp.choi
  have hsum : HasSum fChoi (∑ i : Bool, fChoi i) :=
    hasSum_sum_of_ne_finset_zero (s := Finset.univ)
      (fun i hi => (hi (Finset.mem_univ i)).elim)
  have hchoi := ofEffect_add_choi E F hE hF hEF hE1 hF1
  have htotal : ∑ i : Bool, fChoi i =
      (ofEffect (E + F) (hE.add hF) hEF).cp.choi := by
    simp only [fChoi, Fintype.sum_bool, ↓reduceIte]
    exact (congrArg CPMap.choi hchoi).symm
  change HasSum fChoi _
  rwa [← htotal]

theorem effectPack_hasSum_add {A : ℕ}
    (E F : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hF : F.PosSemidef)
    (hE1 : E ≤ 1) (hF1 : F ≤ 1) (hEF : E + F ≤ 1) :
    ((DayNegation.neg (representable A)).obj 1).HasSum
      (fun i : Bool =>
        effectPack A (if i then ofEffect E hE hE1 else ofEffect F hF hF1))
      (effectPack A (ofEffect (E + F) (hE.add hF) hEF)) := by
  have hχ :=
    SigmaMon.ChoiSum.comp_right (Superoperator.tensorLeftUnitor A)
      (ofEffect_hasSum_add E F hE hF hE1 hF1 hEF)
  simpa [effectPack, dualFiberBilinear] using
    (dayInternalHomRepresentableIso A dayTensorUnit).inv.map_sum hχ

/-- Double-dual Born reading is additive on Loewner-summable effects. -/
theorem effectExpectation_add_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E G : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hG : G.PosSemidef)
    (hE1 : E ≤ 1) (hG1 : G ≤ 1) (hEG : E + G ≤ 1) :
    effectExpectation (doubleDualEffectPairing F) (E + G) (hE.add hG) hEG =
      effectExpectation (doubleDualEffectPairing F) E hE hE1 +
        effectExpectation (doubleDualEffectPairing F) G hG hG1 := by
  simp only [effectExpectation]
  set α := doubleDualEffectPairing F
  have hF :=
    F.map_sum_right (Superoperator.identity 1)
      (effectPack_hasSum_add E G hE hG hE1 hG1 hEG)
  have hα :
      SigmaMon.ChoiSum.HasSum
        (fun i : Bool =>
          α (if i then ofEffect E hE hE1 else ofEffect G hG hG1))
        (α (ofEffect (E + G) (hE.add hG) hEG)) := by
    simp only [α, doubleDualEffectPairing]
    exact SigmaMon.ChoiSum.comp_right _
      (SigmaMon.ChoiSum.comp_right _ hF)
  have ht := (bornScalar_hasSum hα).tsum_eq
  rw [tsum_bool] at ht
  simpa [add_comm] using ht.symm

theorem effectExpectation_nonneg_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1) :
    0 ≤ (effectExpectation (doubleDualEffectPairing F) E hE hE1).re ∧
      (effectExpectation (doubleDualEffectPairing F) E hE hE1).im = 0 := by
  have h :=
    bornScalar_nonneg (doubleDualEffectPairing F (ofEffect E hE hE1))
  exact ⟨h.1, h.2.1⟩

/-- Monotonicity of the double-dual Born reading on the Loewner order. -/
theorem effectExpectation_mono_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E G : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hG : G.PosSemidef)
    (hE1 : E ≤ 1) (hG1 : G ≤ 1) (hle : E ≤ G) :
    (effectExpectation (doubleDualEffectPairing F) E hE hE1).re ≤
      (effectExpectation (doubleDualEffectPairing F) G hG hG1).re := by
  have hdiff : (G - E).PosSemidef := Matrix.le_iff.mp hle
  have hLE_diff_G : G - E ≤ G := by
    rw [Matrix.le_iff, sub_sub_cancel]
    exact hE
  have hdiff_le : G - E ≤ 1 := hLE_diff_G.trans hG1
  have hsum_eq : E + (G - E) = G := add_sub_cancel _ _
  have hEG : E + (G - E) ≤ 1 := by simpa [hsum_eq] using hG1
  have hadd :=
    effectExpectation_add_doubleDual F E (G - E) hE hdiff hE1 hdiff_le hEG
  have hn :=
    effectExpectation_nonneg_doubleDual F (G - E) hdiff hdiff_le
  have hβG :
      effectExpectation (doubleDualEffectPairing F)
          (E + (G - E)) (hE.add hdiff) hEG =
        effectExpectation (doubleDualEffectPairing F) G hG hG1 := by
    simp only [effectExpectation, hsum_eq]
  have hre := congrArg Complex.re (hβG.symm.trans hadd)
  simp only [Complex.add_re] at hre
  linarith [hn.1]


/-- Halving homogeneity of the double-dual Born reading. -/
theorem effectExpectation_half_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1) :
    effectExpectation (doubleDualEffectPairing F) E hE hE1 =
      (2 : ℂ) *
        effectExpectation (doubleDualEffectPairing F)
          (((2 : ℝ)⁻¹) • E)
          (hE.smul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹))
          (by
            have hhalf : ((2 : ℝ)⁻¹) • E ≤ E := by
              rw [Matrix.le_iff]
              have :
                  E - ((2 : ℝ)⁻¹) • E = ((1 : ℝ) - (2 : ℝ)⁻¹) • E := by
                ext i j
                simp [Matrix.sub_apply, Matrix.smul_apply]
                ring
              rw [this]
              exact hE.smul
                (by norm_num : (0 : ℝ) ≤ (1 : ℝ) - (2 : ℝ)⁻¹)
            exact hhalf.trans hE1) := by
  set E2 : Matrix (Fin A) (Fin A) ℂ := ((2 : ℝ)⁻¹) • E
  have hE2psd : E2.PosSemidef :=
    hE.smul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
  have hE2le : E2 ≤ 1 := by
    have hhalf : E2 ≤ E := by
      rw [Matrix.le_iff]
      have : E - E2 = ((1 : ℝ) - (2 : ℝ)⁻¹) • E := by
        ext
        simp [E2, Matrix.sub_apply, Matrix.smul_apply]
        ring
      rw [this]
      exact hE.smul (by norm_num : (0 : ℝ) ≤ (1 : ℝ) - (2 : ℝ)⁻¹)
    exact hhalf.trans hE1
  have hsum : E2 + E2 = E := by
    ext
    simp [E2, Matrix.add_apply, Matrix.smul_apply]
    ring
  have hE2E2 : E2 + E2 ≤ 1 := by simpa [hsum] using hE1
  have hadd :=
    effectExpectation_add_doubleDual F E2 E2 hE2psd hE2psd hE2le hE2le hE2E2
  have hcongr :
      effectExpectation (doubleDualEffectPairing F) (E2 + E2)
          (hE2psd.add hE2psd) hE2E2 =
        effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
    simp only [effectExpectation, hsum]
  rw [← hcongr, hadd]
  ring

theorem ofEffect_proof_irrel {A : ℕ} (E : Matrix (Fin A) (Fin A) ℂ)
    (h1 h1' : E.PosSemidef) (h2 h2' : E ≤ 1) :
    ofEffect E h1 h2 = ofEffect E h1' h2' := by
  apply Superoperator.ext
  apply CPMap.ext
  rfl

theorem smul_le_self_of_le_one {A : ℕ} (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (c : ℝ) (_hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (c • E) ≤ E := by
  rw [Matrix.le_iff]
  have : E - c • E = (1 - c) • E := by
    ext
    simp [Matrix.sub_apply, Matrix.smul_apply]
    ring
  rw [this]
  exact hE.smul (sub_nonneg.mpr hc1)

theorem smul_le_one_of_le_one {A : ℕ} (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (c • E) ≤ (1 : Matrix (Fin A) (Fin A) ℂ) :=
  (smul_le_self_of_le_one E hE c hc0 hc1).trans hE1

theorem two_pow_inv_nonneg (k : ℕ) : (0 : ℝ) ≤ ((2 : ℝ) ^ k)⁻¹ :=
  inv_nonneg.mpr (pow_nonneg (by norm_num) k)

theorem two_pow_inv_le_one (k : ℕ) : ((2 : ℝ) ^ k)⁻¹ ≤ (1 : ℝ) :=
  inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

/-- β(0) = 0 from additivity. -/
theorem effectExpectation_zero_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier) :
    effectExpectation (doubleDualEffectPairing F)
        (0 : Matrix (Fin A) (Fin A) ℂ) PosSemidef.zero
        (by rw [Matrix.le_iff, sub_zero]; exact PosSemidef.one) = 0 := by
  set z : Matrix (Fin A) (Fin A) ℂ := 0
  have hzpsd : z.PosSemidef := PosSemidef.zero
  have hzle : z ≤ 1 := by rw [Matrix.le_iff, sub_zero]; exact PosSemidef.one
  have hz2 : z + z = z := by simp [z]
  have hz2le : z + z ≤ 1 := by simpa [hz2] using hzle
  have hadd :=
    effectExpectation_add_doubleDual F z z hzpsd hzpsd hzle hzle hz2le
  have hcongr :
      effectExpectation (doubleDualEffectPairing F) (z + z)
          (hzpsd.add hzpsd) hz2le =
        effectExpectation (doubleDualEffectPairing F) z hzpsd hzle := by
    simp only [effectExpectation, hz2]
  have heq :
      effectExpectation (doubleDualEffectPairing F) z hzpsd hzle =
        effectExpectation (doubleDualEffectPairing F) z hzpsd hzle +
          effectExpectation (doubleDualEffectPairing F) z hzpsd hzle :=
    hcongr.symm.trans hadd
  have him := (effectExpectation_nonneg_doubleDual F z hzpsd hzle).2
  have hre0 : (effectExpectation (doubleDualEffectPairing F) z hzpsd hzle).re = 0 := by
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re] at hre
    linarith
  have hβ0 : effectExpectation (doubleDualEffectPairing F) z hzpsd hzle = 0 :=
    Complex.ext hre0 him
  simpa [z, effectExpectation] using hβ0

/-- ℕ-homogeneity of the double-dual Born reading. -/
theorem effectExpectation_nsmul_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (n : ℕ) (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1)
    (hn : ((n : ℝ) • E) ≤ 1) :
    effectExpectation (doubleDualEffectPairing F)
        ((n : ℝ) • E) (hE.smul (Nat.cast_nonneg n)) hn =
      (n : ℂ) *
        effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  induction n with
  | zero =>
    have hmat : ((0 : ℕ) : ℝ) • E = (0 : Matrix (Fin A) (Fin A) ℂ) := by simp
    have hL :
        effectExpectation (doubleDualEffectPairing F)
          (((0 : ℕ) : ℝ) • E) (hE.smul (Nat.cast_nonneg 0)) hn =
        effectExpectation (doubleDualEffectPairing F)
          (0 : Matrix (Fin A) (Fin A) ℂ) PosSemidef.zero
          (by rw [Matrix.le_iff, sub_zero]; exact PosSemidef.one) := by
      simp only [effectExpectation, hmat]
    rw [hL, effectExpectation_zero_doubleDual F]
    simp
  | succ n ih =>
    have hnE : ((n : ℝ) • E) ≤ ((n + 1 : ℕ) : ℝ) • E := by
      rw [Matrix.le_iff]
      have : ((n + 1 : ℕ) : ℝ) • E - (n : ℝ) • E = E := by
        ext
        simp [Matrix.sub_apply, Matrix.smul_apply, Nat.cast_succ]
        ring
      rw [this]
      exact hE
    have hn_le : ((n : ℝ) • E) ≤ 1 := hnE.trans hn
    have hsum : ((n : ℝ) • E) + E = (((n + 1 : ℕ) : ℝ) • E) := by
      ext
      simp [Matrix.add_apply, Matrix.smul_apply, Nat.cast_succ]
      ring
    have hsum_le : ((n : ℝ) • E) + E ≤ 1 := by simpa [hsum] using hn
    have hadd :=
      effectExpectation_add_doubleDual F ((n : ℝ) • E) E
        (hE.smul (Nat.cast_nonneg n)) hE hn_le hE1 hsum_le
    have ih' := ih hn_le
    calc
      effectExpectation (doubleDualEffectPairing F)
          (((n + 1 : ℕ) : ℝ) • E) (hE.smul (Nat.cast_nonneg _)) hn =
        effectExpectation (doubleDualEffectPairing F)
          (((n : ℝ) • E) + E)
          ((hE.smul (Nat.cast_nonneg n)).add hE) hsum_le := by
        simp only [effectExpectation, hsum]
      _ = effectExpectation (doubleDualEffectPairing F)
            ((n : ℝ) • E) (hE.smul (Nat.cast_nonneg n)) hn_le +
          effectExpectation (doubleDualEffectPairing F) E hE hE1 := hadd
      _ = (n : ℂ) * effectExpectation (doubleDualEffectPairing F) E hE hE1 +
          effectExpectation (doubleDualEffectPairing F) E hE hE1 := by rw [ih']
      _ = ((n + 1 : ℕ) : ℂ) *
          effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
        simp [Nat.cast_succ]
        ring

/-- Invert the half-homogeneity identity. -/
theorem effectExpectation_of_half {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1) :
    effectExpectation (doubleDualEffectPairing F)
        (((2 : ℝ)⁻¹) • E)
        (hE.smul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹))
        (smul_le_one_of_le_one E hE hE1 (2 : ℝ)⁻¹ (by norm_num) (by norm_num)) =
      (2 : ℂ)⁻¹ *
        effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  have h := effectExpectation_half_doubleDual F E hE hE1
  apply_fun (fun z : ℂ => (2 : ℂ)⁻¹ * z) at h
  convert h.symm using 1
  ring

/-- Dyadic power-of-two homogeneity: β(E/2^k) = β(E)/2^k. -/
theorem effectExpectation_div_pow_two {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (k : ℕ) (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1) :
    effectExpectation (doubleDualEffectPairing F)
        (((2 : ℝ) ^ k)⁻¹ • E)
        (hE.smul (two_pow_inv_nonneg k))
        (smul_le_one_of_le_one E hE hE1 _ (two_pow_inv_nonneg k) (two_pow_inv_le_one k)) =
      ((2 : ℂ) ^ k)⁻¹ *
        effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  induction k with
  | zero => simp [pow_zero, inv_one, one_smul]
  | succ k ih =>
    have hE_k_psd : (((2 : ℝ) ^ k)⁻¹ • E).PosSemidef :=
      hE.smul (two_pow_inv_nonneg k)
    have hE_k_le : ((2 : ℝ) ^ k)⁻¹ • E ≤ 1 :=
      smul_le_one_of_le_one E hE hE1 _ (two_pow_inv_nonneg k) (two_pow_inv_le_one k)
    have hmat : ((2 : ℝ) ^ (k + 1))⁻¹ • E =
        ((2 : ℝ)⁻¹) • (((2 : ℝ) ^ k)⁻¹ • E) := by
      have : ((2 : ℝ) ^ (k + 1))⁻¹ = (2 : ℝ)⁻¹ * ((2 : ℝ) ^ k)⁻¹ := by
        rw [pow_succ, mul_inv]
        ring
      rw [this, mul_smul]
    calc
      effectExpectation (doubleDualEffectPairing F)
          (((2 : ℝ) ^ (k + 1))⁻¹ • E)
          (hE.smul (two_pow_inv_nonneg (k + 1)))
          (smul_le_one_of_le_one E hE hE1 _ (two_pow_inv_nonneg (k + 1))
            (two_pow_inv_le_one (k + 1))) =
        effectExpectation (doubleDualEffectPairing F)
          (((2 : ℝ)⁻¹) • (((2 : ℝ) ^ k)⁻¹ • E))
          (hE_k_psd.smul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹))
          (smul_le_one_of_le_one _ hE_k_psd hE_k_le (2 : ℝ)⁻¹
            (by norm_num) (by norm_num)) := by
        simp only [effectExpectation, hmat]
      _ = (2 : ℂ)⁻¹ *
          effectExpectation (doubleDualEffectPairing F)
            (((2 : ℝ) ^ k)⁻¹ • E) hE_k_psd hE_k_le :=
        effectExpectation_of_half F _ hE_k_psd hE_k_le
      _ = (2 : ℂ)⁻¹ *
          (((2 : ℂ) ^ k)⁻¹ *
            effectExpectation (doubleDualEffectPairing F) E hE hE1) := by
        rw [ih]
      _ = ((2 : ℂ) ^ (k + 1))⁻¹ *
          effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
        simp only [pow_succ, mul_inv]
        ring

/-- Dyadic rational homogeneity: β((m/2^k)•E) = (m/2^k)·β(E) when scaled ≤ I. -/
theorem effectExpectation_dyadic_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (m k : ℕ) (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1)
    (hm : (((m : ℝ) / (2 : ℝ) ^ k) • E) ≤ 1) :
    effectExpectation (doubleDualEffectPairing F)
        (((m : ℝ) / (2 : ℝ) ^ k) • E)
        (hE.smul (div_nonneg (Nat.cast_nonneg m) (pow_nonneg (by norm_num) k)))
        hm =
      ((m : ℂ) / (2 : ℂ) ^ k) *
        effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  have hmat : ((m : ℝ) / (2 : ℝ) ^ k) • E =
      (m : ℝ) • (((2 : ℝ) ^ k)⁻¹ • E) := by
    rw [div_eq_mul_inv, mul_smul]
  have hEk_psd : (((2 : ℝ) ^ k)⁻¹ • E).PosSemidef :=
    hE.smul (two_pow_inv_nonneg k)
  have hEk_le : ((2 : ℝ) ^ k)⁻¹ • E ≤ 1 :=
    smul_le_one_of_le_one E hE hE1 _ (two_pow_inv_nonneg k) (two_pow_inv_le_one k)
  have hm' : ((m : ℝ) • (((2 : ℝ) ^ k)⁻¹ • E)) ≤ 1 := by simpa [hmat] using hm
  have hβ_half := effectExpectation_div_pow_two F k E hE hE1
  have hβ_n :=
    effectExpectation_nsmul_doubleDual F m (((2 : ℝ) ^ k)⁻¹ • E) hEk_psd hEk_le hm'
  calc
    effectExpectation (doubleDualEffectPairing F)
        (((m : ℝ) / (2 : ℝ) ^ k) • E)
        (hE.smul (div_nonneg (Nat.cast_nonneg m) (pow_nonneg (by norm_num) k))) hm =
      effectExpectation (doubleDualEffectPairing F)
        ((m : ℝ) • (((2 : ℝ) ^ k)⁻¹ • E))
        (hEk_psd.smul (Nat.cast_nonneg m)) hm' := by
      simp only [effectExpectation, hmat]
    _ = (m : ℂ) *
        effectExpectation (doubleDualEffectPairing F)
          (((2 : ℝ) ^ k)⁻¹ • E) hEk_psd hEk_le := hβ_n
    _ = (m : ℂ) *
        (((2 : ℂ) ^ k)⁻¹ *
          effectExpectation (doubleDualEffectPairing F) E hE hE1) := by
      rw [hβ_half]
    _ = ((m : ℂ) / (2 : ℂ) ^ k) *
        effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
      rw [div_eq_mul_inv]
      ring

theorem smul_le_smul_of_le {A : ℕ} (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) {c d : ℝ} (_hc : 0 ≤ c) (hcd : c ≤ d) :
    (c • E) ≤ (d • E) := by
  rw [Matrix.le_iff]
  have : d • E - c • E = (d - c) • E := by
    ext; simp [Matrix.sub_apply, Matrix.smul_apply]; ring
  rw [this]
  exact hE.smul (sub_nonneg.mpr hcd)

theorem abs_le_inv_pow_two_eq_zero (x : ℝ)
    (h : ∀ k : ℕ, |x| ≤ ((2 : ℝ) ^ k)⁻¹) : x = 0 := by
  by_contra hx
  have hxpos : 0 < |x| := abs_pos.mpr hx
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 : ℝ) / |x| < (2 : ℝ) ^ k :=
    pow_unbounded_of_one_lt (1 / |x|) (by norm_num : (1 : ℝ) < 2)
  have hlt : ((2 : ℝ) ^ k)⁻¹ < |x| := by
    have hpos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
    rw [inv_lt_comm₀ hpos hxpos]
    simpa [one_div] using hk
  exact lt_irrefl _ (hlt.trans_le (h k))

theorem floor_dyadic_le (t : ℝ) (ht0 : 0 ≤ t) (k : ℕ) :
    ((Nat.floor (t * (2 : ℝ) ^ k) : ℕ) : ℝ) / (2 : ℝ) ^ k ≤ t := by
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) k
  have hm : ((Nat.floor (t * (2 : ℝ) ^ k) : ℕ) : ℝ) ≤ t * (2 : ℝ) ^ k :=
    Nat.floor_le (mul_nonneg ht0 (le_of_lt hpow_pos))
  calc ((Nat.floor (t * (2 : ℝ) ^ k) : ℕ) : ℝ) / (2 : ℝ) ^ k
      ≤ (t * (2 : ℝ) ^ k) / (2 : ℝ) ^ k :=
        div_le_div_of_nonneg_right hm (le_of_lt hpow_pos)
    _ = t := by field_simp [hpow_pos.ne']

theorem floor_dyadic_gt (t : ℝ) (k : ℕ) :
    t ≤ (((Nat.floor (t * (2 : ℝ) ^ k) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k) := by
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) k
  set m := Nat.floor (t * (2 : ℝ) ^ k)
  have hm : t * (2 : ℝ) ^ k < (m : ℝ) + 1 := by
    simpa [m, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (t * (2 : ℝ) ^ k)
  have : t < ((m : ℝ) + 1) / (2 : ℝ) ^ k :=
    (lt_div_iff₀ hpow_pos).mpr (by linarith)
  exact le_of_lt (by simpa [Nat.cast_add, Nat.cast_one] using this)

theorem effectExpectation_one_smul_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1) :
    effectExpectation (doubleDualEffectPairing F) ((1 : ℝ) • E)
        (hE.smul zero_le_one) (by simpa [one_smul] using hE1) =
      effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  simp only [effectExpectation, one_smul]

theorem dyadic_gap (m k : ℕ) :
    (((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k) - ((m : ℝ) / (2 : ℝ) ^ k) =
      ((2 : ℝ) ^ k)⁻¹ := by
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) k
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by simp
  rw [hcast]
  field_simp [hpow_pos.ne']
  ring

/-- Homogeneity at a concrete dyadic rational written as `c = m/2^k`. -/
theorem effectExpectation_ofReal_dyadic {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (m k : ℕ) (c : ℝ) (hc : c = (m : ℝ) / (2 : ℝ) ^ k)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1)
    (hc0 : 0 ≤ c) (_hc1 : c ≤ 1)
    (hm : (c • E) ≤ 1) :
    effectExpectation (doubleDualEffectPairing F) (c • E) (hE.smul hc0) hm =
      (c : ℂ) * effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  have hm' : (((m : ℝ) / (2 : ℝ) ^ k) • E) ≤ 1 := by simpa [hc] using hm
  have hdy := effectExpectation_dyadic_doubleDual F m k E hE hE1 hm'
  have hL :
      effectExpectation (doubleDualEffectPairing F) (c • E) (hE.smul hc0) hm =
      effectExpectation (doubleDualEffectPairing F)
        (((m : ℝ) / (2 : ℝ) ^ k) • E)
        (hE.smul (div_nonneg (Nat.cast_nonneg m) (pow_nonneg (by norm_num) k)))
        hm' := by
    simp only [effectExpectation, hc]
  rw [hL, hdy, hc]
  simp [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_pow]

theorem effectExpectation_smul_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1) :
    effectExpectation (doubleDualEffectPairing F) (t • E)
        (hE.smul ht0) (smul_le_one_of_le_one E hE hE1 t ht0 ht1) =
      (t : ℂ) * effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  set βE := effectExpectation (doubleDualEffectPairing F) E hE hE1 with hβE_def
  have hEt_psd : (t • E).PosSemidef := hE.smul ht0
  have hEt_le : t • E ≤ 1 := smul_le_one_of_le_one E hE hE1 t ht0 ht1
  set βt := effectExpectation (doubleDualEffectPairing F) (t • E) hEt_psd hEt_le
  have himE : βE.im = 0 := by
    simpa [βE] using (effectExpectation_nonneg_doubleDual F E hE hE1).2
  have himt : βt.im = 0 := by
    simpa [βt] using (effectExpectation_nonneg_doubleDual F (t • E) hEt_psd hEt_le).2
  have hreE_nn : 0 ≤ βE.re := by
    simpa [βE] using (effectExpectation_nonneg_doubleDual F E hE hE1).1
  have hβE_re_le1 : βE.re ≤ 1 := by
    simpa [βE, effectExpectation] using
      (bornScalar_nonneg (doubleDualEffectPairing F (ofEffect E hE hE1))).2.2
  have hclose : ∀ k : ℕ, |βt.re - t * βE.re| ≤ ((2 : ℝ) ^ k)⁻¹ := by
    intro k
    set m := Nat.floor (t * (2 : ℝ) ^ k)
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) k
    have hpow_nn : (0 : ℝ) ≤ (2 : ℝ) ^ k := le_of_lt hpow_pos
    set r : ℝ := (m : ℝ) / (2 : ℝ) ^ k
    set s0 : ℝ := ((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k
    set s : ℝ := min s0 1
    have hr_le_t : r ≤ t := by simpa [r, m] using floor_dyadic_le t ht0 k
    have ht_le_s0 : t ≤ s0 := by simpa [s0, m] using floor_dyadic_gt t k
    have ht_le_s : t ≤ s := le_min ht_le_s0 ht1
    have hr0 : 0 ≤ r := div_nonneg (Nat.cast_nonneg m) hpow_nn
    have hr1 : r ≤ 1 := by
      have hm_le : (m : ℝ) ≤ t * (2 : ℝ) ^ k :=
        Nat.floor_le (mul_nonneg ht0 hpow_nn)
      exact (div_le_one hpow_pos).mpr (hm_le.trans (by nlinarith [ht1]))
    have hs0nn : 0 ≤ s :=
      le_min (div_nonneg (Nat.cast_nonneg (m + 1)) hpow_nn) zero_le_one
    have hs1 : s ≤ 1 := min_le_right _ _
    have hgap : s - r ≤ ((2 : ℝ) ^ k)⁻¹ := by
      have hs0r : s0 - r = ((2 : ℝ) ^ k)⁻¹ := by
        simpa [r, s0] using dyadic_gap m k
      cases le_total s0 1 with
      | inl h => have := min_eq_left h; linarith
      | inr h =>
        have hs_eq : s = 1 := min_eq_right h
        have : 1 - r ≤ ((2 : ℝ) ^ k)⁻¹ := by
          have : 1 - r ≤ s0 - r := sub_le_sub_right h _
          linarith
        simpa [hs_eq] using this
    have hrE_le : (r • E) ≤ t • E := smul_le_smul_of_le E hE hr0 hr_le_t
    have htE_le : t • E ≤ s • E := smul_le_smul_of_le E hE ht0 ht_le_s
    have hsE_le1 : (s • E) ≤ 1 := smul_le_one_of_le_one E hE hE1 s hs0nn hs1
    have hrE_le1 : (r • E) ≤ 1 := smul_le_one_of_le_one E hE hE1 r hr0 hr1
    have hβr :
        effectExpectation (doubleDualEffectPairing F) (r • E) (hE.smul hr0) hrE_le1 =
          (r : ℂ) * βE := by
      simpa [βE] using
        effectExpectation_ofReal_dyadic F m k r rfl E hE hE1 hr0 hr1 hrE_le1
    have hβs :
        effectExpectation (doubleDualEffectPairing F) (s • E) (hE.smul hs0nn) hsE_le1 =
          (s : ℂ) * βE := by
      cases le_total s0 1 with
      | inl h =>
        have hs_eq : s = s0 := min_eq_left h
        -- s = (m+1)/2^k
        have hs_dy : s = ((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k := hs_eq
        simpa [βE] using
          effectExpectation_ofReal_dyadic F (m + 1) k s hs_dy E hE hE1 hs0nn hs1 hsE_le1
      | inr h =>
        have hs_eq : s = (1 : ℝ) := min_eq_right h
        -- β(s•E) = β(1•E) = β(E) = 1*βE = s*βE
        have hL :
            effectExpectation (doubleDualEffectPairing F) (s • E)
              (hE.smul hs0nn) hsE_le1 =
            effectExpectation (doubleDualEffectPairing F) ((1 : ℝ) • E)
              (hE.smul zero_le_one) (by simpa [one_smul] using hE1) := by
          simp only [effectExpectation, hs_eq]
        rw [hL, effectExpectation_one_smul_doubleDual F E hE hE1, hs_eq, hβE_def]
        simp [Complex.ofReal_one]
    have hmono_r :=
      effectExpectation_mono_doubleDual F (r • E) (t • E) (hE.smul hr0) hEt_psd
        hrE_le1 hEt_le hrE_le
    have hmono_s :=
      effectExpectation_mono_doubleDual F (t • E) (s • E) hEt_psd (hE.smul hs0nn)
        hEt_le hsE_le1 htE_le
    have hβr_re :
        (effectExpectation (doubleDualEffectPairing F) (r • E)
          (hE.smul hr0) hrE_le1).re = r * βE.re := by
      rw [hβr]; simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, himE]
    have hβs_re :
        (effectExpectation (doubleDualEffectPairing F) (s • E)
          (hE.smul hs0nn) hsE_le1).re = s * βE.re := by
      rw [hβs]; simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, himE]
    have hlow : r * βE.re ≤ βt.re := by simpa [βt, hβr_re] using hmono_r
    have hhigh : βt.re ≤ s * βE.re := by simpa [βt, hβs_re] using hmono_s
    have habs : |βt.re - t * βE.re| ≤ (s - r) * βE.re := by
      rw [abs_sub_le_iff]; constructor <;> nlinarith
    have hgapβ : (s - r) * βE.re ≤ ((2 : ℝ) ^ k)⁻¹ := by
      have h1 := mul_le_mul_of_nonneg_right hgap hreE_nn
      have h2 := mul_le_mul_of_nonneg_left hβE_re_le1 (inv_nonneg.mpr hpow_nn)
      nlinarith
    exact habs.trans hgapβ
  have hre_eq : βt.re = t * βE.re := by
    have hx := abs_le_inv_pow_two_eq_zero (βt.re - t * βE.re) fun k => by
      simpa [sub_eq_add_neg] using hclose k
    linarith
  refine Complex.ext ?_ ?_
  · have hL :
        (effectExpectation (doubleDualEffectPairing F) (t • E)
          (hE.smul ht0) (smul_le_one_of_le_one E hE hE1 t ht0 ht1)).re = βt.re := by
      simp only [βt, effectExpectation]
    rw [hL, hre_eq]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, himE, βE]
  · have hL :
        (effectExpectation (doubleDualEffectPairing F) (t • E)
          (hE.smul ht0) (smul_le_one_of_le_one E hE hE1 t ht0 ht1)).im = βt.im := by
      simp only [βt, effectExpectation]
    rw [hL]
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, himE, himt, βE]


theorem conj_mul_self_eq_normSq (c : ℂ) :
    star c * c = ↑(Complex.normSq c) := by
  simpa using (Complex.normSq_eq_conj_mul_self (z := c)).symm

theorem conj_mul_self_re (c : ℂ) : (star c * c).re = Complex.normSq c := by
  rw [conj_mul_self_eq_normSq]; simp

theorem conj_mul_self_im (c : ℂ) : (star c * c).im = 0 := by
  rw [conj_mul_self_eq_normSq]; simp

theorem vecMulVec_smul_star {ι : Type*} [Fintype ι]
    (a : ℂ) (v : ι → ℂ) :
    Matrix.vecMulVec (a • v) (star (a • v)) =
      (a * star a) • Matrix.vecMulVec v (star v) := by
  ext i j
  simp [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem ofReal_sqrt_sq (x : ℝ) (hx : 0 ≤ x) :
    (↑(Real.sqrt x) : ℂ) * ↑(Real.sqrt x) = ↑x := by
  norm_cast; exact Real.mul_self_sqrt hx

theorem normalizeVec_smul_projector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (v : ι → ℂ) (_hc : c ≠ 0)
    (hv : star v ⬝ᵥ v ≠ 0) (hcv : star (c • v) ⬝ᵥ (c • v) ≠ 0) :
    Matrix.vecMulVec (normalizeVec (c • v) hcv) (star (normalizeVec (c • v) hcv)) =
      Matrix.vecMulVec (normalizeVec v hv) (star (normalizeVec v hv)) := by
  have hre_v := (star_dotProduct_self_nonneg_real v).1
  have him_v := (star_dotProduct_self_nonneg_real v).2
  have hre_cv := (star_dotProduct_self_nonneg_real (c • v)).1
  have hnrm_re : (star (c • v) ⬝ᵥ (c • v)).re =
      Complex.normSq c * (star v ⬝ᵥ v).re := by
    rw [star_dotProduct_smul_self, Complex.mul_re, conj_mul_self_im, him_v,
      conj_mul_self_re]; ring
  set svR : ℝ := Real.sqrt (star v ⬝ᵥ v).re
  set scvR : ℝ := Real.sqrt (star (c • v) ⬝ᵥ (c • v)).re
  set sv : ℂ := ↑svR
  set scv : ℂ := ↑scvR
  have hsv_ne : sv ≠ 0 := by
    intro h
    have : (star v ⬝ᵥ v).re = 0 :=
      (Real.sqrt_eq_zero hre_v).1 (by simpa [sv, svR] using congrArg Complex.re h)
    exact hv (Complex.ext this him_v)
  have hscv_ne : scv ≠ 0 := by
    intro h
    have him_cv := (star_dotProduct_self_nonneg_real (c • v)).2
    have : (star (c • v) ⬝ᵥ (c • v)).re = 0 :=
      (Real.sqrt_eq_zero hre_cv).1 (by simpa [scv, scvR] using congrArg Complex.re h)
    exact hcv (Complex.ext this him_cv)
  have hcv_proj :
      Matrix.vecMulVec (normalizeVec (c • v) hcv) (star (normalizeVec (c • v) hcv)) =
        (scv⁻¹ * star scv⁻¹) • Matrix.vecMulVec (c • v) (star (c • v)) := by
    unfold normalizeVec
    change Matrix.vecMulVec (scv⁻¹ • (c • v)) (star (scv⁻¹ • (c • v))) = _
    exact vecMulVec_smul_star scv⁻¹ (c • v)
  have hv_proj :
      Matrix.vecMulVec (normalizeVec v hv) (star (normalizeVec v hv)) =
        (sv⁻¹ * star sv⁻¹) • Matrix.vecMulVec v (star v) := by
    unfold normalizeVec
    change Matrix.vecMulVec (sv⁻¹ • v) (star (sv⁻¹ • v)) = _
    exact vecMulVec_smul_star sv⁻¹ v
  have hcv_expand :
      Matrix.vecMulVec (normalizeVec (c • v) hcv) (star (normalizeVec (c • v) hcv)) =
        ((scv⁻¹ * star scv⁻¹) * (c * star c)) • Matrix.vecMulVec v (star v) := by
    rw [hcv_proj, vecMulVec_smul_star c v, smul_smul]
  have hcoef : (scv⁻¹ * star scv⁻¹) * (c * star c) = sv⁻¹ * star sv⁻¹ := by
    have hcstar : c * star c = ↑(Complex.normSq c) := by
      simpa using Complex.mul_conj c
    have hsv_star : star sv = sv := by simp [sv, Complex.conj_ofReal]
    have hscv_star : star scv = scv := by simp [scv, Complex.conj_ofReal]
    have hsv_sq : sv * sv = ↑((star v ⬝ᵥ v).re) := by
      simp [sv, svR]; exact ofReal_sqrt_sq _ hre_v
    have hscv_sq : scv * scv = ↑(Complex.normSq c) * ↑((star v ⬝ᵥ v).re) := by
      have h := ofReal_sqrt_sq (star (c • v) ⬝ᵥ (c • v)).re hre_cv
      have hscv_def : scv = ↑(Real.sqrt (star (c • v) ⬝ᵥ (c • v)).re) := by
        simp [scv, scvR]
      rw [← hscv_def, hnrm_re] at h
      simpa [Complex.ofReal_mul] using h
    rw [hcstar, star_inv₀, star_inv₀, hsv_star, hscv_star]
    field_simp [hsv_ne, hscv_ne]
    simp only [pow_two, hsv_sq, hscv_sq]
  rw [hcv_expand, hcoef, hv_proj]

theorem effectPairingQuad_smul {A : ℕ}
    (α : Superoperator A 1 → Superoperator 1 1) (c : ℂ) (v : Fin A → ℂ) :
    effectPairingQuad α (c • v) =
      (star c * c) * effectPairingQuad α v := by
  simp only [effectPairingQuad]
  by_cases hv : star v ⬝ᵥ v = 0
  · have hcv0 : star (c • v) ⬝ᵥ (c • v) = 0 := by
      rw [star_dotProduct_smul_self, hv]; ring
    simp [hv, hcv0]
  · by_cases hcv : star (c • v) ⬝ᵥ (c • v) = 0
    · have : (star c * c) * (star v ⬝ᵥ v) = 0 := by
        simpa [star_dotProduct_smul_self] using hcv
      have hc0 : star c * c = 0 := (mul_eq_zero.mp this).resolve_right hv
      rw [dif_pos hcv, dif_neg hv, hc0, zero_mul]
    · have hc0 : c ≠ 0 := fun hc => by
        simp [hc, zero_smul, star_dotProduct_smul_self, mul_zero, zero_mul] at hcv
      have hproj := normalizeVec_smul_projector c v hc0 hv hcv
      rw [dif_neg hcv, dif_neg hv, star_dotProduct_smul_self]
      have hof :
          ofEffect
              (Matrix.vecMulVec (normalizeVec (c • v) hcv)
                (star (normalizeVec (c • v) hcv)))
              (Matrix.posSemidef_vecMulVec_self_star _)
              (vecMulVec_unit_le_one _ (normalizeVec_norm (c • v) hcv)) =
            ofEffect
              (Matrix.vecMulVec (normalizeVec v hv)
                (star (normalizeVec v hv)))
              (Matrix.posSemidef_vecMulVec_self_star _)
              (vecMulVec_unit_le_one _ (normalizeVec_norm v hv)) := by
        simp only [hproj]
      rw [hof]
      ring

theorem effectPairingPolar_self {A : ℕ}
    (α : Superoperator A 1 → Superoperator 1 1) (v : Fin A → ℂ) :
    effectPairingPolar α v v = effectPairingQuad α v := by
  simp only [effectPairingPolar]
  have hv2 : v + v = (2 : ℂ) • v := by ext; simp; ring
  have hvpi : v + Complex.I • v = (1 + Complex.I) • v := by ext; simp; ring
  have hvmi : v - Complex.I • v = (1 - Complex.I) • v := by ext; simp; ring
  have hq0 : effectPairingQuad α (v - v) = 0 := by
    simp [sub_self, effectPairingQuad]
  have hq2 := effectPairingQuad_smul α (2 : ℂ) v
  have hqpi := effectPairingQuad_smul α (1 + Complex.I) v
  have hqmi := effectPairingQuad_smul α (1 - Complex.I) v
  have h2 : star (2 : ℂ) * (2 : ℂ) = 4 := by norm_num
  have hpi : star (1 + Complex.I) * (1 + Complex.I) = 2 := by
    simp [star_add]; ring_nf; norm_num
  have hmi : star (1 - Complex.I) * (1 - Complex.I) = 2 := by
    simp [star_sub]; ring_nf; norm_num
  simp only [hv2, hvpi, hvmi]
  rw [hq2, hq0, hqpi, hqmi, h2, hpi, hmi]
  ring


theorem vecMulVec_parallelogram {ι : Type*} [Fintype ι]
    (x y : ι → ℂ) :
    Matrix.vecMulVec (x + y) (star (x + y)) +
      Matrix.vecMulVec (x - y) (star (x - y)) =
      (2 : ℂ) • Matrix.vecMulVec x (star x) +
        (2 : ℂ) • Matrix.vecMulVec y (star y) := by
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply,
    Pi.sub_apply, Pi.star_apply, smul_eq_mul, star_add, star_sub]
  ring

theorem vecMulVec_parallelogram_I {ι : Type*} [Fintype ι]
    (x y : ι → ℂ) :
    Matrix.vecMulVec (x + Complex.I • y) (star (x + Complex.I • y)) +
      Matrix.vecMulVec (x - Complex.I • y) (star (x - Complex.I • y)) =
      (2 : ℂ) • Matrix.vecMulVec x (star x) +
        (2 : ℂ) • Matrix.vecMulVec y (star y) := by
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply,
    Pi.sub_apply, Pi.star_apply, smul_eq_mul, star_add, star_sub, star_smul]
  ring_nf
  -- goal has -I^2; rewrite I^2 = -1
  rw [Complex.I_sq]
  ring

theorem vecMulVec_mulVec_self {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    (Matrix.vecMulVec v (star v)) *ᵥ v = (star v ⬝ᵥ v) • v := by
  ext i
  simp only [mulVec, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, dotProduct]
  calc ∑ j, v i * star (v j) * v j
      = ∑ j, (star (v j) * v j) * v i :=
        Finset.sum_congr rfl fun j _ => by ring
    _ = (∑ j, star (v j) * v j) * v i := (Finset.sum_mul _ _ _).symm

theorem ofReal_re_of_im_zero (z : ℂ) (him : z.im = 0) : (↑z.re : ℂ) = z := by
  apply Complex.ext
  · simp
  · simpa using him.symm

theorem star_dot_smul {A : ℕ} (c : ℂ) (v w : Fin A → ℂ) :
    star v ⬝ᵥ (c • w) = c * (star v ⬝ᵥ w) := by
  simp [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

theorem vecMulVec_le_one_normSq_le_one {A : ℕ}
    (v : Fin A → ℂ)
    (hle : Matrix.vecMulVec v (star v) ≤ (1 : Matrix (Fin A) (Fin A) ℂ)) :
    (star v ⬝ᵥ v).re ≤ 1 := by
  have him := (star_dotProduct_self_nonneg_real v).2
  set nrm := star v ⬝ᵥ v
  have hdiff : ((1 : Matrix (Fin A) (Fin A) ℂ) -
      Matrix.vecMulVec v (star v)).PosSemidef := Matrix.le_iff.mp hle
  have hpos := Matrix.PosSemidef.dotProduct_mulVec_nonneg hdiff v
  have hI : star v ⬝ᵥ (1 : Matrix (Fin A) (Fin A) ℂ) *ᵥ v = nrm := by simp [nrm]
  have hP : star v ⬝ᵥ (Matrix.vecMulVec v (star v)) *ᵥ v = nrm * nrm := by
    rw [vecMulVec_mulVec_self, star_dot_smul]
  have hsub : star v ⬝ᵥ ((1 : Matrix (Fin A) (Fin A) ℂ) -
      Matrix.vecMulVec v (star v)) *ᵥ v = nrm - nrm * nrm := by
    rw [sub_mulVec, dotProduct_sub, hI, hP]
  have hnn : 0 ≤ (nrm - nrm * nrm).re := by
    have := hpos; rw [hsub] at this
    exact (Complex.nonneg_iff.mp this).1
  have : (nrm - nrm * nrm).re = nrm.re - nrm.re * nrm.re := by
    simp [Complex.sub_re, Complex.mul_re, him]
  rw [this] at hnn
  nlinarith

theorem effectPairingQuad_eq_expectation {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (v : Fin A → ℂ)
    (hle : Matrix.vecMulVec v (star v) ≤ (1 : Matrix (Fin A) (Fin A) ℂ)) :
    effectPairingQuad (doubleDualEffectPairing F) v =
      effectExpectation (doubleDualEffectPairing F)
        (Matrix.vecMulVec v (star v))
        (Matrix.posSemidef_vecMulVec_self_star v) hle := by
  simp only [effectPairingQuad]
  by_cases hv : star v ⬝ᵥ v = 0
  · have hmat : Matrix.vecMulVec v (star v) = 0 := by
      have : v = 0 := (dotProduct_star_self_eq_zero).1 hv
      simp [this]
    have h0 := effectExpectation_zero_doubleDual (A := A) F
    simp only [effectExpectation, hv, hmat] at h0 ⊢
    simpa using h0.symm
  · set û := normalizeVec v hv
    have hre := (star_dotProduct_self_nonneg_real v).1
    have him := (star_dotProduct_self_nonneg_real v).2
    set s : ℂ := ↑(Real.sqrt (star v ⬝ᵥ v).re)
    have hv_eq : v = s • û := by
      simp only [û, normalizeVec, s]
      ext i
      have hs_ne : s ≠ 0 := by
        intro hs0
        have : (star v ⬝ᵥ v).re = 0 :=
          (Real.sqrt_eq_zero hre).1 (by simpa [s] using congrArg Complex.re hs0)
        exact hv (Complex.ext this him)
      change v i = s * (s⁻¹ * v i)
      field_simp [hs_ne]
    have hstar_s : star s = s := by simp [s, Complex.conj_ofReal]
    have hnrm_sq : star v ⬝ᵥ v = s * s := by
      apply Complex.ext
      · have : (star v ⬝ᵥ v).re = s.re * s.re := by
          simpa [s, Complex.ofReal_re] using (Real.mul_self_sqrt hre).symm
        simpa [Complex.mul_re, s] using this
      · simpa [Complex.mul_im, s] using him
    have hmat : Matrix.vecMulVec v (star v) =
        (star v ⬝ᵥ v) • Matrix.vecMulVec û (star û) := by
      calc Matrix.vecMulVec v (star v)
          = Matrix.vecMulVec (s • û) (star (s • û)) := by rw [hv_eq]
        _ = (s * star s) • Matrix.vecMulVec û (star û) := vecMulVec_smul_star s û
        _ = (s * s) • Matrix.vecMulVec û (star û) := by rw [hstar_s]
        _ = (star v ⬝ᵥ v) • Matrix.vecMulVec û (star û) := by rw [← hnrm_sq]
    have ht0 : (0 : ℝ) ≤ (star v ⬝ᵥ v).re := hre
    have ht1 : (star v ⬝ᵥ v).re ≤ 1 := vecMulVec_le_one_normSq_le_one v hle
    have hû_le : Matrix.vecMulVec û (star û) ≤ 1 :=
      vecMulVec_unit_le_one û (normalizeVec_norm v hv)
    have hnrm_ofReal : (↑((star v ⬝ᵥ v).re) : ℂ) = star v ⬝ᵥ v :=
      ofReal_re_of_im_zero _ him
    have hsmul_eq :
        ((star v ⬝ᵥ v).re : ℝ) • Matrix.vecMulVec û (star û) =
          (star v ⬝ᵥ v) • Matrix.vecMulVec û (star û) := by
      ext i j
      simp [Matrix.smul_apply, smul_eq_mul, hnrm_ofReal]
    have hmat' : Matrix.vecMulVec v (star v) =
        ((star v ⬝ᵥ v).re : ℝ) • Matrix.vecMulVec û (star û) := by
      rw [hmat, ← hsmul_eq]
    have hβ :=
      effectExpectation_smul_doubleDual F (star v ⬝ᵥ v).re ht0 ht1
        (Matrix.vecMulVec û (star û))
        (Matrix.posSemidef_vecMulVec_self_star û) hû_le
    rw [dif_neg hv]
    have hR :
        effectExpectation (doubleDualEffectPairing F)
          (Matrix.vecMulVec v (star v))
          (Matrix.posSemidef_vecMulVec_self_star v) hle =
        (↑((star v ⬝ᵥ v).re) : ℂ) *
          effectExpectation (doubleDualEffectPairing F)
            (Matrix.vecMulVec û (star û))
            (Matrix.posSemidef_vecMulVec_self_star û) hû_le := by
      have hL :
          effectExpectation (doubleDualEffectPairing F)
            (Matrix.vecMulVec v (star v))
            (Matrix.posSemidef_vecMulVec_self_star v) hle =
          effectExpectation (doubleDualEffectPairing F)
            (((star v ⬝ᵥ v).re : ℝ) • Matrix.vecMulVec û (star û))
            ((Matrix.posSemidef_vecMulVec_self_star û).smul ht0)
            (smul_le_one_of_le_one _ (Matrix.posSemidef_vecMulVec_self_star û)
              hû_le _ ht0 ht1) := by
        simp only [effectExpectation, hmat']
      rw [hL, hβ]
    have hborn :
        bornScalar (doubleDualEffectPairing F
          (ofEffect (Matrix.vecMulVec (normalizeVec v hv)
            (star (normalizeVec v hv)))
            (Matrix.posSemidef_vecMulVec_self_star _)
            (vecMulVec_unit_le_one _ (normalizeVec_norm v hv)))) =
        effectExpectation (doubleDualEffectPairing F)
          (Matrix.vecMulVec û (star û))
          (Matrix.posSemidef_vecMulVec_self_star û) hû_le := by
      simp only [effectExpectation, û]
    rw [hborn, ← hnrm_ofReal, hR]


theorem effectPairingQuad_nonneg {A : ℕ}
    (α : Superoperator A 1 → Superoperator 1 1) (v : Fin A → ℂ) :
    0 ≤ (effectPairingQuad α v).re ∧ (effectPairingQuad α v).im = 0 := by
  simp only [effectPairingQuad]
  split_ifs with h
  · simp
  · have hb :=
      bornScalar_nonneg
        (α (ofEffect
          (Matrix.vecMulVec (normalizeVec v h) (star (normalizeVec v h)))
          (Matrix.posSemidef_vecMulVec_self_star _)
          (vecMulVec_unit_le_one _ (normalizeVec_norm v h))))
    have hnrm := star_dotProduct_self_nonneg_real v
    constructor
    · simp only [Complex.mul_re, hnrm.2, hb.2.1, mul_zero, sub_zero]
      nlinarith [hnrm.1, hb.1]
    · simp [Complex.mul_im, hnrm.2, hb.2.1]

/-! ### Parallelogram / polarization recovery of the density -/

theorem smul_le_smul_one_of_le_one {A : ℕ} (E : Matrix (Fin A) (Fin A) ℂ)
    (_hE : E.PosSemidef) (hE1 : E ≤ 1) (c : ℝ) (hc0 : 0 ≤ c) :
    (c • E) ≤ (c • (1 : Matrix (Fin A) (Fin A) ℂ)) := by
  rw [Matrix.le_iff]
  have : c • (1 : Matrix (Fin A) (Fin A) ℂ) - c • E = c • (1 - E) := by
    ext; simp [Matrix.sub_apply, Matrix.smul_apply]; ring
  rw [this]
  exact (Matrix.le_iff.mp hE1).smul hc0

/-- Rank-one Loewner bound `|v⟩⟨v| ≤ ‖v‖² • I`. -/
theorem vecMulVec_le_normSq_smul_one {A : ℕ} (v : Fin A → ℂ) :
    Matrix.vecMulVec v (star v) ≤
      (((star v ⬝ᵥ v).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ)) := by
  classical
  by_cases hv : star v ⬝ᵥ v = 0
  · have hv0 : v = 0 := (dotProduct_star_self_eq_zero).1 hv
    have hre0 : (star v ⬝ᵥ v).re = 0 := by simp [hv]
    rw [show Matrix.vecMulVec v (star v) = 0 by simp [hv0],
      show (((star v ⬝ᵥ v).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ)) = 0 by
        simp [hre0]]
  · set û := normalizeVec v hv
    have hre := (star_dotProduct_self_nonneg_real v).1
    have him := (star_dotProduct_self_nonneg_real v).2
    set s : ℂ := ↑(Real.sqrt (star v ⬝ᵥ v).re)
    have hv_eq : v = s • û := by
      simp only [û, normalizeVec, s]
      ext i
      have hs_ne : s ≠ 0 := by
        intro hs0
        exact hv (Complex.ext
          ((Real.sqrt_eq_zero hre).1 (by simpa [s] using congrArg Complex.re hs0))
          him)
      change v i = s * (s⁻¹ * v i)
      field_simp [hs_ne]
    have hstar_s : star s = s := by simp [s, Complex.conj_ofReal]
    have hnrm_sq : star v ⬝ᵥ v = s * s := by
      apply Complex.ext
      · simpa [Complex.mul_re, s, Complex.ofReal_re] using
          (Real.mul_self_sqrt hre).symm
      · simpa [Complex.mul_im, s] using him
    have hmat : Matrix.vecMulVec v (star v) =
        (star v ⬝ᵥ v) • Matrix.vecMulVec û (star û) := by
      calc Matrix.vecMulVec v (star v)
          = Matrix.vecMulVec (s • û) (star (s • û)) := by rw [hv_eq]
        _ = (s * star s) • Matrix.vecMulVec û (star û) := vecMulVec_smul_star s û
        _ = (s * s) • Matrix.vecMulVec û (star û) := by rw [hstar_s]
        _ = (star v ⬝ᵥ v) • Matrix.vecMulVec û (star û) := by rw [← hnrm_sq]
    have hsmul_eq :
        ((star v ⬝ᵥ v).re : ℝ) • Matrix.vecMulVec û (star û) =
          (star v ⬝ᵥ v) • Matrix.vecMulVec û (star û) := by
      ext i j
      simp [Matrix.smul_apply, smul_eq_mul, ofReal_re_of_im_zero _ him]
    rw [hmat, ← hsmul_eq]
    exact smul_le_smul_one_of_le_one _
      (Matrix.posSemidef_vecMulVec_self_star û)
      (vecMulVec_unit_le_one û (normalizeVec_norm v hv)) _ hre

theorem vecMulVec_le_one_of_normSq_le {A : ℕ} (v : Fin A → ℂ)
    (hle : (star v ⬝ᵥ v).re ≤ 1) :
    Matrix.vecMulVec v (star v) ≤ (1 : Matrix (Fin A) (Fin A) ℂ) :=
  (vecMulVec_le_normSq_smul_one v).trans <|
    smul_le_one_of_le_one (1 : Matrix (Fin A) (Fin A) ℂ)
      PosSemidef.one le_rfl _ (star_dotProduct_self_nonneg_real v).1 hle

theorem star_dot_add_self {A : ℕ} (x y : Fin A → ℂ) :
    star (x + y) ⬝ᵥ (x + y) + star (x - y) ⬝ᵥ (x - y) =
      (2 : ℂ) * (star x ⬝ᵥ x + star y ⬝ᵥ y) := by
  simp only [dotProduct, Pi.add_apply, Pi.sub_apply, Pi.star_apply]
  have hterm : ∀ i,
      star (x i + y i) * (x i + y i) + star (x i - y i) * (x i - y i) =
        2 * (star (x i) * x i + star (y i) * y i) := by
    intro i; simp [star_add, star_sub]; ring
  calc ∑ i, star (x i + y i) * (x i + y i) +
        ∑ i, star (x i - y i) * (x i - y i)
      = ∑ i, (star (x i + y i) * (x i + y i) +
          star (x i - y i) * (x i - y i)) :=
        (Finset.sum_add_distrib).symm
    _ = ∑ i, (2 * (star (x i) * x i + star (y i) * y i)) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = 2 * ∑ i, (star (x i) * x i + star (y i) * y i) := by
        rw [← Finset.mul_sum]
    _ = 2 * (∑ i, star (x i) * x i + ∑ i, star (y i) * y i) := by
        simp [Finset.sum_add_distrib]

theorem star_dot_add_re_le {A : ℕ} (x y : Fin A → ℂ) :
    (star (x + y) ⬝ᵥ (x + y)).re ≤
      2 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) := by
  have hx := star_dotProduct_self_nonneg_real x
  have hy := star_dotProduct_self_nonneg_real y
  have hxy := (star_dotProduct_self_nonneg_real (x - y)).1
  have h := congrArg Complex.re (star_dot_add_self x y)
  simp only [Complex.add_re, Complex.mul_re, Complex.add_im, hx.2, hy.2,
    mul_zero, sub_zero, add_zero] at h
  have hsum :
      (star (x + y) ⬝ᵥ (x + y)).re + (star (x - y) ⬝ᵥ (x - y)).re =
        2 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) := by
    simpa [two_mul] using h
  linarith

theorem ofReal_smul_normSq {A : ℕ} (t : ℝ) (v : Fin A → ℂ) :
    (star ((t : ℂ) • v) ⬝ᵥ ((t : ℂ) • v)).re =
      t ^ 2 * (star v ⬝ᵥ v).re := by
  have him := (star_dotProduct_self_nonneg_real v).2
  have hstar : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  rw [star_dotProduct_smul_self, hstar]
  have hmul : ((t : ℂ) * (t : ℂ)).re = t ^ 2 := by simp [pow_two]
  have himt : ((t : ℂ) * (t : ℂ)).im = 0 := by simp
  simp [Complex.mul_re, him, himt, hmul]

theorem two_smul_vecMulVec_add_le_one {A : ℕ} (x y : Fin A → ℂ)
    (h : 2 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) ≤ 1) :
    (2 : ℝ) • Matrix.vecMulVec x (star x) +
      (2 : ℝ) • Matrix.vecMulVec y (star y) ≤
        (1 : Matrix (Fin A) (Fin A) ℂ) := by
  have hx := vecMulVec_le_normSq_smul_one x
  have hy := vecMulVec_le_normSq_smul_one y
  have hx2 : (2 : ℝ) • Matrix.vecMulVec x (star x) ≤
      (2 * (star x ⬝ᵥ x).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) := by
    rw [Matrix.le_iff]
    have : (2 * (star x ⬝ᵥ x).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) -
        (2 : ℝ) • Matrix.vecMulVec x (star x) =
        (2 : ℝ) • (((star x ⬝ᵥ x).re : ℝ) • 1 -
          Matrix.vecMulVec x (star x)) := by
      ext; simp [Matrix.sub_apply, Matrix.smul_apply]; ring
    rw [this]
    exact (Matrix.le_iff.mp hx).smul (by norm_num)
  have hy2 : (2 : ℝ) • Matrix.vecMulVec y (star y) ≤
      (2 * (star y ⬝ᵥ y).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) := by
    rw [Matrix.le_iff]
    have : (2 * (star y ⬝ᵥ y).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) -
        (2 : ℝ) • Matrix.vecMulVec y (star y) =
        (2 : ℝ) • (((star y ⬝ᵥ y).re : ℝ) • 1 -
          Matrix.vecMulVec y (star y)) := by
      ext; simp [Matrix.sub_apply, Matrix.smul_apply]; ring
    rw [this]
    exact (Matrix.le_iff.mp hy).smul (by norm_num)
  refine (add_le_add hx2 hy2).trans ?_
  have hsum :
      (2 * (star x ⬝ᵥ x).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) +
        (2 * (star y ⬝ᵥ y).re : ℝ) • 1 =
      (2 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) : ℝ) • 1 := by
    ext; simp [Matrix.add_apply, Matrix.smul_apply]; ring
  rw [hsum]
  exact smul_le_one_of_le_one (1 : Matrix (Fin A) (Fin A) ℂ)
    PosSemidef.one le_rfl _
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (add_nonneg (star_dotProduct_self_nonneg_real x).1
        (star_dotProduct_self_nonneg_real y).1)) h

/-- Scaling factor making `2(|tx⟩⟨tx|+|ty⟩⟨ty|) ≤ I`. -/
noncomputable def parallelScaleR {A : ℕ} (x y : Fin A → ℂ) : ℝ :=
  let N := (star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re
  Real.sqrt (1 / (2 * (N + 1)))

theorem parallelScaleR_pos {A : ℕ} (x y : Fin A → ℂ) :
    0 < parallelScaleR x y := by
  set N := (star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re
  have hN0 : 0 ≤ N :=
    add_nonneg (star_dotProduct_self_nonneg_real x).1
      (star_dotProduct_self_nonneg_real y).1
  have hden : 0 < 2 * (N + 1) := by
    nlinarith
  exact Real.sqrt_pos.2 (div_pos (by norm_num) hden)

theorem parallelScaleR_bound {A : ℕ} (x y : Fin A → ℂ) :
    2 * (parallelScaleR x y) ^ 2 *
      ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) ≤ 1 := by
  set N := (star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re
  have hN0 : 0 ≤ N :=
    add_nonneg (star_dotProduct_self_nonneg_real x).1
      (star_dotProduct_self_nonneg_real y).1
  have hden : 0 < 2 * (N + 1) := by nlinarith
  have hsq : (parallelScaleR x y) ^ 2 = 1 / (2 * (N + 1)) := by
    simp only [parallelScaleR, N]
    exact Real.sq_sqrt (div_nonneg (by norm_num) (le_of_lt hden))
  rw [hsq]
  have : 2 * (1 / (2 * (N + 1))) * N = N / (N + 1) := by
    field_simp [hden.ne']
  rw [this]
  exact div_le_one_of_le₀ (by linarith) (add_nonneg hN0 zero_le_one)

/-- Parallelogram identity for the double-dual Born quadratic form. -/
theorem effectPairingQuad_parallelogram {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y : Fin A → ℂ) :
    effectPairingQuad (doubleDualEffectPairing F) (x + y) +
      effectPairingQuad (doubleDualEffectPairing F) (x - y) =
      2 * effectPairingQuad (doubleDualEffectPairing F) x +
        2 * effectPairingQuad (doubleDualEffectPairing F) y := by
  set α := doubleDualEffectPairing F
  set t := parallelScaleR x y
  have ht0 : 0 < t := parallelScaleR_pos x y
  set x' : Fin A → ℂ := (t : ℂ) • x
  set y' : Fin A → ℂ := (t : ℂ) • y
  have hxN : (star x' ⬝ᵥ x').re = t ^ 2 * (star x ⬝ᵥ x).re := by
    simpa [x'] using ofReal_smul_normSq t x
  have hyN : (star y' ⬝ᵥ y').re = t ^ 2 * (star y ⬝ᵥ y).re := by
    simpa [y'] using ofReal_smul_normSq t y
  have hsumN : 2 * ((star x' ⬝ᵥ x').re + (star y' ⬝ᵥ y').re) ≤ 1 := by
    simp only [hxN, hyN]
    convert parallelScaleR_bound x y using 1
    ring
  have hx1 : Matrix.vecMulVec x' (star x') ≤ 1 :=
    vecMulVec_le_one_of_normSq_le _
      (by linarith [(star_dotProduct_self_nonneg_real y').1])
  have hy1 : Matrix.vecMulVec y' (star y') ≤ 1 :=
    vecMulVec_le_one_of_normSq_le _
      (by linarith [(star_dotProduct_self_nonneg_real x').1])
  have hxp_re : (star (x' + y') ⬝ᵥ (x' + y')).re ≤ 1 := by
    linarith [star_dot_add_re_le x' y']
  have hxm_re : (star (x' - y') ⬝ᵥ (x' - y')).re ≤ 1 := by
    have hx := star_dotProduct_self_nonneg_real x'
    have hy := star_dotProduct_self_nonneg_real y'
    have h := congrArg Complex.re (star_dot_add_self x' y')
    simp only [Complex.add_re, Complex.mul_re, Complex.add_im, hx.2, hy.2,
      mul_zero, sub_zero, add_zero] at h
    have hsum :
        (star (x' + y') ⬝ᵥ (x' + y')).re + (star (x' - y') ⬝ᵥ (x' - y')).re =
          2 * ((star x' ⬝ᵥ x').re + (star y' ⬝ᵥ y').re) := by
      simpa [two_mul] using h
    linarith [(star_dotProduct_self_nonneg_real (x' + y')).1]
  have hxp1 : Matrix.vecMulVec (x' + y') (star (x' + y')) ≤ 1 :=
    vecMulVec_le_one_of_normSq_le _ hxp_re
  have hxm1 : Matrix.vecMulVec (x' - y') (star (x' - y')) ≤ 1 :=
    vecMulVec_le_one_of_normSq_le _ hxm_re
  have hq_xp := effectPairingQuad_eq_expectation F (x' + y') hxp1
  have hq_xm := effectPairingQuad_eq_expectation F (x' - y') hxm1
  have hq_x := effectPairingQuad_eq_expectation F x' hx1
  have hq_y := effectPairingQuad_eq_expectation F y' hy1
  set Pxp := Matrix.vecMulVec (x' + y') (star (x' + y'))
  set Pxm := Matrix.vecMulVec (x' - y') (star (x' - y'))
  set Px := Matrix.vecMulVec x' (star x')
  set Py := Matrix.vecMulVec y' (star y')
  have hPxp1 : Pxp ≤ 1 := hxp1
  have hPxm1 : Pxm ≤ 1 := hxm1
  have hPx1 : Px ≤ 1 := hx1
  have hPy1 : Py ≤ 1 := hy1
  have hmatR : Pxp + Pxm = (2 : ℝ) • Px + (2 : ℝ) • Py := by
    have hmat := vecMulVec_parallelogram x' y'
    simp only [Pxp, Pxm, Px, Py]
    rw [hmat]
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply, two_smul]
  have h2le : (2 : ℝ) • Px + (2 : ℝ) • Py ≤ 1 := by
    simpa [Px, Py] using two_smul_vecMulVec_add_le_one x' y' hsumN
  have hsum_le : Pxp + Pxm ≤ 1 := by rwa [hmatR]
  have hsum_psd : (Pxp + Pxm).PosSemidef :=
    (Matrix.posSemidef_vecMulVec_self_star (x' + y')).add
      (Matrix.posSemidef_vecMulVec_self_star (x' - y'))
  have hadd_xp_xm :=
    effectExpectation_add_doubleDual F Pxp Pxm
      (Matrix.posSemidef_vecMulVec_self_star (x' + y'))
      (Matrix.posSemidef_vecMulVec_self_star (x' - y'))
      hPxp1 hPxm1 hsum_le
  have hA_eq : (2 : ℝ) • Px + (2 : ℝ) • Py = (2 : ℝ) • (Px + Py) := by
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply, two_smul]
  have h2A' : (2 : ℝ) • (Px + Py) ≤ 1 := by rwa [← hA_eq]
  have hA_le : Px + Py ≤ 1 := by
    have hhalf : Px + Py =
        ((2 : ℝ)⁻¹) • ((2 : ℝ) • (Px + Py)) := by
      ext i j
      simp [Matrix.add_apply, Matrix.smul_apply, two_smul]
      ring
    rw [hhalf]
    refine (smul_le_smul_one_of_le_one _
      (((Matrix.posSemidef_vecMulVec_self_star x').add
          (Matrix.posSemidef_vecMulVec_self_star y')).smul
        (by norm_num : (0 : ℝ) ≤ 2))
      h2A' _ (by norm_num)).trans ?_
    exact smul_le_one_of_le_one (1 : Matrix (Fin A) (Fin A) ℂ)
      PosSemidef.one le_rfl _ (by norm_num) (by norm_num)
  have hadd_xy :=
    effectExpectation_add_doubleDual F Px Py
      (Matrix.posSemidef_vecMulVec_self_star x')
      (Matrix.posSemidef_vecMulVec_self_star y')
      hPx1 hPy1 hA_le
  have hβ2 :=
    effectExpectation_nsmul_doubleDual F 2 (Px + Py)
      ((Matrix.posSemidef_vecMulVec_self_star x').add
        (Matrix.posSemidef_vecMulVec_self_star y'))
      hA_le h2A'
  have hβ_sum :
      effectExpectation α Pxp
          (Matrix.posSemidef_vecMulVec_self_star (x' + y')) hPxp1 +
        effectExpectation α Pxm
          (Matrix.posSemidef_vecMulVec_self_star (x' - y')) hPxm1 =
      (2 : ℂ) *
        (effectExpectation α Px
            (Matrix.posSemidef_vecMulVec_self_star x') hPx1 +
          effectExpectation α Py
            (Matrix.posSemidef_vecMulVec_self_star y') hPy1) := by
    have h1 :
        effectExpectation α Pxp
            (Matrix.posSemidef_vecMulVec_self_star (x' + y')) hPxp1 +
          effectExpectation α Pxm
            (Matrix.posSemidef_vecMulVec_self_star (x' - y')) hPxm1 =
        effectExpectation α (Pxp + Pxm) hsum_psd hsum_le :=
      hadd_xp_xm.symm
    have h2 :
        effectExpectation α (Pxp + Pxm) hsum_psd hsum_le =
        effectExpectation α ((2 : ℝ) • (Px + Py))
          (((Matrix.posSemidef_vecMulVec_self_star x').add
              (Matrix.posSemidef_vecMulVec_self_star y')).smul
            (by norm_num)) h2A' := by
      simp only [effectExpectation, α, hmatR, hA_eq]
    have h3 :
        effectExpectation α ((2 : ℝ) • (Px + Py))
          (((Matrix.posSemidef_vecMulVec_self_star x').add
              (Matrix.posSemidef_vecMulVec_self_star y')).smul
            (by norm_num)) h2A' =
        (2 : ℂ) * effectExpectation α (Px + Py)
          ((Matrix.posSemidef_vecMulVec_self_star x').add
            (Matrix.posSemidef_vecMulVec_self_star y')) hA_le := by
      simpa [α, Nat.cast_ofNat] using hβ2
    have h4 :
        effectExpectation α (Px + Py)
          ((Matrix.posSemidef_vecMulVec_self_star x').add
            (Matrix.posSemidef_vecMulVec_self_star y')) hA_le =
        effectExpectation α Px
            (Matrix.posSemidef_vecMulVec_self_star x') hPx1 +
          effectExpectation α Py
            (Matrix.posSemidef_vecMulVec_self_star y') hPy1 :=
      hadd_xy
    rw [h1, h2, h3, h4]
  have hq' :
      effectPairingQuad α (x' + y') + effectPairingQuad α (x' - y') =
        2 * effectPairingQuad α x' + 2 * effectPairingQuad α y' := by
    rw [hq_xp, hq_xm, hq_x, hq_y]
    simpa [α, Pxp, Pxm, Px, Py, two_mul, mul_add] using hβ_sum
  have htstar : star (t : ℂ) * (t : ℂ) = ↑(t ^ 2) := by
    simp [Complex.conj_ofReal, pow_two]
  have hxpy : x' + y' = (t : ℂ) • (x + y) := by
    ext i; simp [x', y', smul_add, mul_add]
  have hxmy : x' - y' = (t : ℂ) • (x - y) := by
    ext i; simp [x', y', smul_sub, mul_sub]
  rw [hxpy, hxmy] at hq'
  rw [effectPairingQuad_smul α (t : ℂ) (x + y),
    effectPairingQuad_smul α (t : ℂ) (x - y),
    effectPairingQuad_smul α (t : ℂ) x,
    effectPairingQuad_smul α (t : ℂ) y, htstar] at hq'
  -- hq' : ↑(t²)*q(x+y) + ↑(t²)*q(x-y) = 2*(↑(t²)*qx) + 2*(↑(t²)*qy)
  have hcoef : (↑(t ^ 2) : ℂ) ≠ 0 :=
    mod_cast (pow_ne_zero 2 ht0.ne')
  have hq'' :
      (↑(t ^ 2) : ℂ) *
          (effectPairingQuad α (x + y) + effectPairingQuad α (x - y)) =
        (↑(t ^ 2) : ℂ) *
          (2 * effectPairingQuad α x + 2 * effectPairingQuad α y) := by
    convert hq' using 1 <;> ring
  exact mul_left_cancel₀ hcoef hq''

/-- Parallelogram with `I • y` (uses `|I|² = 1`). -/
theorem effectPairingQuad_parallelogram_I {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y : Fin A → ℂ) :
    effectPairingQuad (doubleDualEffectPairing F) (x + Complex.I • y) +
      effectPairingQuad (doubleDualEffectPairing F) (x - Complex.I • y) =
      2 * effectPairingQuad (doubleDualEffectPairing F) x +
        2 * effectPairingQuad (doubleDualEffectPairing F) y := by
  have h := effectPairingQuad_parallelogram F x (Complex.I • y)
  have hI : effectPairingQuad (doubleDualEffectPairing F) (Complex.I • y) =
      effectPairingQuad (doubleDualEffectPairing F) y := by
    rw [effectPairingQuad_smul]
    have : star Complex.I * Complex.I = 1 := by
      simp [Complex.star_def, Complex.conj_I, neg_mul, Complex.I_mul_I]
    rw [this, one_mul]
  rw [hI] at h
  exact h

theorem q_phase_I {A : ℕ}
    (α : Superoperator A 1 → Superoperator 1 1) (v : Fin A → ℂ) :
    effectPairingQuad α (Complex.I • v) = effectPairingQuad α v := by
  rw [effectPairingQuad_smul]
  have : star Complex.I * Complex.I = 1 := by
    simp [Complex.conj_I, neg_mul, Complex.I_mul_I]
  rw [this, one_mul]

/-- Our polar equals the OfNorm-style polarization formula. -/
theorem effectPairingPolar_eq_ofNorm {A : ℕ}
    (α : Superoperator A 1 → Superoperator 1 1) (x y : Fin A → ℂ) :
    effectPairingPolar α x y =
      (effectPairingQuad α (x + y) - effectPairingQuad α (x - y) +
        Complex.I * effectPairingQuad α (Complex.I • x + y) -
        Complex.I * effectPairingQuad α (Complex.I • x - y)) / 4 := by
  have h1 : effectPairingQuad α (x + Complex.I • y) =
      effectPairingQuad α (Complex.I • x - y) := by
    have hmul : Complex.I • (x + Complex.I • y) = Complex.I • x - y := by
      ext i
      simp [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
      ring_nf; rw [Complex.I_sq]; ring
    calc effectPairingQuad α (x + Complex.I • y)
        = effectPairingQuad α (Complex.I • (x + Complex.I • y)) :=
          (q_phase_I α _).symm
      _ = effectPairingQuad α (Complex.I • x - y) := by rw [hmul]
  have h2 : effectPairingQuad α (x - Complex.I • y) =
      effectPairingQuad α (Complex.I • x + y) := by
    have hmul : Complex.I • (x - Complex.I • y) = Complex.I • x + y := by
      ext i
      simp [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      ring_nf; rw [Complex.I_sq]; ring
    calc effectPairingQuad α (x - Complex.I • y)
        = effectPairingQuad α (Complex.I • (x - Complex.I • y)) :=
          (q_phase_I α _).symm
      _ = effectPairingQuad α (Complex.I • x + y) := by rw [hmul]
  simp only [effectPairingPolar, h1, h2]
  ring

/-- Left additivity of the polarized form (Jordan–von Neumann / OfNorm). -/
theorem effectPairingPolar_add_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y z : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) (x + y) z =
      effectPairingPolar (doubleDualEffectPairing F) x z +
        effectPairingPolar (doubleDualEffectPairing F) y z := by
  set α := doubleDualEffectPairing F
  rw [effectPairingPolar_eq_ofNorm α (x + y) z,
    effectPairingPolar_eq_ofNorm α x z,
    effectPairingPolar_eq_ofNorm α y z]
  have H1 := effectPairingQuad_parallelogram F (x + y + z) (x - z)
  have H2 := effectPairingQuad_parallelogram F (x + y - z) (x + z)
  have H3 := effectPairingQuad_parallelogram F (y + z) z
  have H4 := effectPairingQuad_parallelogram F (y - z) z
  have H5 := effectPairingQuad_parallelogram F
    (Complex.I • (x + y) + z) (Complex.I • x - z)
  have H6 := effectPairingQuad_parallelogram F
    (Complex.I • (x + y) - z) (Complex.I • x + z)
  have H7 := effectPairingQuad_parallelogram F (Complex.I • y + z) z
  have H8 := effectPairingQuad_parallelogram F (Complex.I • y - z) z
  have s1 : x + y + z + (x - z) = (2 : ℂ) • x + y := by
    ext i; simp [two_smul]; ring
  have s1' : x + y + z - (x - z) = y + (2 : ℂ) • z := by
    ext i; simp [two_smul]; ring
  have s2 : x + y - z + (x + z) = (2 : ℂ) • x + y := by
    ext i; simp [two_smul]; ring
  have s2' : x + y - z - (x + z) = y - (2 : ℂ) • z := by
    ext i; simp [two_smul]; ring
  have s3 : (y + z) + z = y + (2 : ℂ) • z := by
    ext i; simp [two_smul]; ring
  have s3' : (y + z) - z = y := add_sub_cancel_right y z
  have s4 : (y - z) + z = y := sub_add_cancel y z
  have s4' : (y - z) - z = y - (2 : ℂ) • z := by
    ext i; simp [two_smul]; ring
  rw [s1, s1'] at H1; rw [s2, s2'] at H2
  rw [s3, s3'] at H3; rw [s4, s4'] at H4
  have t5 : Complex.I • (x + y) + z + (Complex.I • x - z) =
      Complex.I • ((2 : ℂ) • x + y) := by
    ext i; simp [two_smul, smul_add, Pi.smul_apply, smul_eq_mul]; ring
  have t5' : Complex.I • (x + y) + z - (Complex.I • x - z) =
      Complex.I • y + (2 : ℂ) • z := by
    ext i; simp [two_smul, smul_add, Pi.smul_apply, smul_eq_mul]; ring
  have t6 : Complex.I • (x + y) - z + (Complex.I • x + z) =
      Complex.I • ((2 : ℂ) • x + y) := by
    ext i; simp [two_smul, smul_add, Pi.smul_apply, smul_eq_mul]; ring
  have t6' : Complex.I • (x + y) - z - (Complex.I • x + z) =
      Complex.I • y - (2 : ℂ) • z := by
    ext i; simp [two_smul, smul_add, Pi.smul_apply, smul_eq_mul]; ring
  have t7 : Complex.I • y + z + z = Complex.I • y + (2 : ℂ) • z := by
    ext i; simp [two_smul]; ring
  have t7' : Complex.I • y + z - z = Complex.I • y :=
    add_sub_cancel_right _ _
  have t8 : Complex.I • y - z + z = Complex.I • y := sub_add_cancel _ _
  have t8' : Complex.I • y - z - z = Complex.I • y - (2 : ℂ) • z := by
    ext i; simp [two_smul]; ring
  rw [t5, t5'] at H5; rw [t6, t6'] at H6
  rw [t7, t7'] at H7; rw [t8, t8'] at H8
  have pI2 := q_phase_I α ((2 : ℂ) • x + y)
  have pIy := q_phase_I α y
  simp only [α] at H1 H2 H3 H4 H5 H6 H7 H8 pI2 pIy ⊢
  rw [pI2] at H5 H6
  rw [pIy] at H7 H8
  rw [← add_div]
  refine congrArg (fun t : ℂ => t / 4) ?_
  linear_combination
    (-H1 + H2 + H3 - H4 + Complex.I * (-H5 + H6 + H7 - H8)) / 2

theorem effectPairingPolar_zero_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) 0 y = 0 := by
  have h := effectPairingPolar_add_left F 0 0 y
  simp only [zero_add] at h
  exact (add_eq_left.mp h.symm)

theorem effectPairingPolar_nsmul_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (n : ℕ) (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) (n • x) y =
      (n : ℂ) * effectPairingPolar (doubleDualEffectPairing F) x y := by
  induction n with
  | zero => simp [effectPairingPolar_zero_left]
  | succ n ih =>
    rw [succ_nsmul, effectPairingPolar_add_left, ih]
    push_cast
    ring


/-! ### Polar sesquilinearity, density recovery, PSD, trace -/

theorem q_neg {A : ℕ} (α : Superoperator A 1 → Superoperator 1 1)
    (v : Fin A → ℂ) :
    effectPairingQuad α (-v) = effectPairingQuad α v := by
  have hv : -v = (-1 : ℂ) • v := by ext i; simp
  rw [hv, effectPairingQuad_smul]
  norm_num

theorem effectPairingQuad_star {A : ℕ}
    (α : Superoperator A 1 → Superoperator 1 1) (v : Fin A → ℂ) :
    star (effectPairingQuad α v) = effectPairingQuad α v := by
  have him := (effectPairingQuad_nonneg α v).2
  apply Complex.ext
  · simp [Complex.conj_re]
  · simp [Complex.conj_im, him]

theorem effectPairingPolar_conj_symm {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y : Fin A → ℂ) :
    star (effectPairingPolar (doubleDualEffectPairing F) y x) =
      effectPairingPolar (doubleDualEffectPairing F) x y := by
  set α := doubleDualEffectPairing F
  set Q := effectPairingQuad α
  simp only [effectPairingPolar]
  have hQ : ∀ v, star (Q v) = Q v := fun v => by
    simpa [Q] using effectPairingQuad_star α v
  have hyx : y + x = x + y := add_comm _ _
  have hyxm : Q (y - x) = Q (x - y) := by
    have : y - x = -(x - y) := by
      ext i; simp [Pi.sub_apply, Pi.neg_apply, sub_eq_add_neg]
    rw [this]; simpa [Q] using q_neg α (x - y)
  have h1 : Q (y + Complex.I • x) = Q (x - Complex.I • y) := by
    have hmul : Complex.I • (x - Complex.I • y) = Complex.I • x + y := by
      ext i; simp [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply]
      ring_nf; rw [Complex.I_sq]; ring
    have hcomm : y + Complex.I • x = Complex.I • x + y := add_comm _ _
    calc Q (y + Complex.I • x)
        = Q (Complex.I • x + y) := by rw [hcomm]
      _ = Q (Complex.I • (x - Complex.I • y)) := by rw [← hmul]
      _ = Q (x - Complex.I • y) := by simpa [Q] using q_phase_I α _
  have h2 : Q (y - Complex.I • x) = Q (x + Complex.I • y) := by
    have hmul : (-Complex.I) • (x + Complex.I • y) = y - Complex.I • x := by
      ext i; simp [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply]
      ring_nf; rw [Complex.I_sq]; ring
    have hphase : Q ((-Complex.I) • (x + Complex.I • y)) =
        Q (x + Complex.I • y) := by
      simp only [Q]
      rw [effectPairingQuad_smul]
      have : star (-(Complex.I : ℂ)) * (-Complex.I) = 1 := by
        apply Complex.ext <;> simp [Complex.conj_I, Complex.I_mul_I]
      rw [this, one_mul]
    calc Q (y - Complex.I • x)
        = Q ((-Complex.I) • (x + Complex.I • y)) := by rw [← hmul]
      _ = Q (x + Complex.I • y) := hphase
  have hstarI : star (Complex.I : ℂ) = -Complex.I := Complex.conj_I
  have hnum :
      star (Q (y + x) - Q (y - x) -
          Complex.I * Q (y + Complex.I • x) +
          Complex.I * Q (y - Complex.I • x)) =
        Q (x + y) - Q (x - y) -
          Complex.I * Q (x + Complex.I • y) +
          Complex.I * Q (x - Complex.I • y) := by
    simp only [star_sub, star_add, star_mul, hQ, hyx, hyxm, h1, h2, hstarI]
    ring
  have hdiv : star ((Q (y + x) - Q (y - x) -
      Complex.I * Q (y + Complex.I • x) +
      Complex.I * Q (y - Complex.I • x)) / 4) =
      star (Q (y + x) - Q (y - x) -
          Complex.I * Q (y + Complex.I • x) +
          Complex.I * Q (y - Complex.I • x)) / 4 := by
    rw [star_div₀]
    simp [star_ofNat]
  rw [hdiv, hnum]

theorem effectPairingPolar_add_right {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y z : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) x (y + z) =
      effectPairingPolar (doubleDualEffectPairing F) x y +
        effectPairingPolar (doubleDualEffectPairing F) x z := by
  -- conj_symm: star B(b,a) = B(a,b)
  have hyx := effectPairingPolar_conj_symm F x y
  have hzx := effectPairingPolar_conj_symm F x z
  have hyzx := effectPairingPolar_conj_symm F x (y + z)
  calc effectPairingPolar (doubleDualEffectPairing F) x (y + z)
      = star (effectPairingPolar (doubleDualEffectPairing F) (y + z) x) := hyzx.symm
    _ = star (effectPairingPolar (doubleDualEffectPairing F) y x +
          effectPairingPolar (doubleDualEffectPairing F) z x) := by
            rw [effectPairingPolar_add_left]
    _ = star (effectPairingPolar (doubleDualEffectPairing F) y x) +
          star (effectPairingPolar (doubleDualEffectPairing F) z x) := star_add _ _
    _ = effectPairingPolar (doubleDualEffectPairing F) x y +
          effectPairingPolar (doubleDualEffectPairing F) x z := by
            rw [hyx, hzx]


/-! ### Extension of Born reading off the Loewner interval -/

theorem PosSemidef.trace_mul_nonneg {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    0 ≤ Matrix.trace (X * Y) := by
  classical
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.nonneg
  rw [hC, hD]
  change 0 ≤ Matrix.trace (Cᴴ * C * (Dᴴ * D))
  have hcycle : Matrix.trace (Cᴴ * C * (Dᴴ * D)) =
      Matrix.trace ((D * Cᴴ)ᴴ * (D * Cᴴ)) := by
    simp only [Matrix.mul_assoc]
    rw [trace_mul_comm Cᴴ (C * (Dᴴ * D))]
    simp [conjTranspose_mul, Matrix.mul_assoc]
  rw [hcycle]
  exact (posSemidef_conjTranspose_mul_self (D * Cᴴ)).trace_nonneg

theorem PosSemidef.le_re_trace_smul_one {A : ℕ}
    (E : Matrix (Fin A) (Fin A) ℂ) (hE : E.PosSemidef) :
    E ≤ ((Matrix.trace E).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) := by
  rw [Matrix.le_iff]
  have h1 : IsHermitian (1 : Matrix (Fin A) (Fin A) ℂ) := isHermitian_one
  have hc : IsSelfAdjoint ((Matrix.trace E).re : ℂ) := by
    simp [IsSelfAdjoint, Complex.conj_ofReal]
  have hherm := (IsHermitian.smul h1 hc).sub hE.1
  refine PosSemidef.of_dotProduct_mulVec_nonneg hherm fun v => ?_
  have hn := star_dotProduct_self_nonneg_real v
  have hcalc :
      star v ⬝ᵥ ((((Matrix.trace E).re : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) - E) *ᵥ v) =
        ↑(Matrix.trace E).re * (star v ⬝ᵥ v) - star v ⬝ᵥ E *ᵥ v := by
    simp [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub]
  rw [hcalc]
  by_cases hv : star v ⬝ᵥ v = 0
  · have : v = 0 := (dotProduct_star_self_eq_zero).1 hv
    simp [this]
  · set û := normalizeVec v hv
    have hre := hn.1
    have him := hn.2
    set s : ℂ := ↑(Real.sqrt (star v ⬝ᵥ v).re)
    have hv_eq : v = s • û := by
      simp only [û, normalizeVec, s]
      ext i
      have hs_ne : s ≠ 0 := by
        intro hs0
        have : (star v ⬝ᵥ v).re = 0 :=
          (Real.sqrt_eq_zero hre).1 (by simpa [s] using congrArg Complex.re hs0)
        exact hv (Complex.ext this him)
      change v i = s * (s⁻¹ * v i)
      field_simp [hs_ne]
    have hstar_s : star s = s := by simp [s, Complex.conj_ofReal]
    have hnrm : star v ⬝ᵥ v = s * s := by
      apply Complex.ext
      · have : (star v ⬝ᵥ v).re = s.re * s.re := by
          simpa [s, Complex.ofReal_re] using (Real.mul_self_sqrt hre).symm
        simpa [Complex.mul_re, s] using this
      · simpa [Complex.mul_im, s] using him
    have hEv' : star v ⬝ᵥ E *ᵥ v = (s * s) * (star û ⬝ᵥ E *ᵥ û) := by
      calc star v ⬝ᵥ E *ᵥ v
          = star (s • û) ⬝ᵥ E *ᵥ (s • û) := by rw [hv_eq]
        _ = star s * s * (star û ⬝ᵥ E *ᵥ û) := quad_smul E s û
        _ = (s * s) * (star û ⬝ᵥ E *ᵥ û) := by rw [hstar_s]
    have hû1 : star û ⬝ᵥ û = 1 := normalizeVec_norm v hv
    have hP : Matrix.vecMulVec û (star û) ≤ 1 := vecMulVec_unit_le_one û hû1
    have hIPpsd : ((1 : Matrix (Fin A) (Fin A) ℂ) -
        Matrix.vecMulVec û (star û)).PosSemidef := Matrix.le_iff.mp hP
    have htr_split :
        Matrix.trace E =
          Matrix.trace (E * Matrix.vecMulVec û (star û)) +
            Matrix.trace (E * (1 - Matrix.vecMulVec û (star û))) := by
      have : Matrix.vecMulVec û (star û) + (1 - Matrix.vecMulVec û (star û)) = 1 := by abel
      rw [← Matrix.trace_add, ← Matrix.mul_add, this, Matrix.mul_one]
    have htrIP_nonneg :
        0 ≤ Matrix.trace (E * (1 - Matrix.vecMulVec û (star û))) :=
      PosSemidef.trace_mul_nonneg E _ hE hIPpsd
    have htrP :
        Matrix.trace (E * Matrix.vecMulVec û (star û)) = star û ⬝ᵥ E *ᵥ û := by
      simp only [Matrix.trace, diag_apply, mul_apply, vecMulVec_apply, dotProduct, mulVec]
      refine Finset.sum_congr rfl fun i _ => ?_
      calc ∑ j, E i j * (û j * star (û i))
          = ∑ j, star (û i) * (E i j * û j) :=
            Finset.sum_congr rfl fun j _ => by ring
        _ = star (û i) * ∑ j, E i j * û j := (Finset.mul_sum _ _ _).symm
    have himÛ : (star û ⬝ᵥ E *ᵥ û).im = 0 :=
      (Complex.nonneg_iff.mp (hE.dotProduct_mulVec_nonneg û)).2.symm
    have hre_bound : (star û ⬝ᵥ E *ᵥ û).re ≤ (Matrix.trace E).re := by
      have hsplit_re := congrArg Complex.re htr_split
      simp only [Complex.add_re] at hsplit_re
      have hnn := (Complex.nonneg_iff.mp htrIP_nonneg).1
      have : (Matrix.trace (E * Matrix.vecMulVec û (star û))).re ≤ (Matrix.trace E).re := by
        linarith
      simpa [htrP] using this
    have hss_im : (s * s).im = 0 := by simpa [← hnrm] using him
    refine Complex.nonneg_iff.mpr ⟨?_, ?_⟩
    · rw [hEv', hnrm]
      have hex :
          (((Matrix.trace E).re : ℂ) * (s * s) - (s * s) * (star û ⬝ᵥ E *ᵥ û)).re =
            (s * s).re * ((Matrix.trace E).re - (star û ⬝ᵥ E *ᵥ û).re) := by
        simp [Complex.sub_re, Complex.mul_re, hss_im, himÛ, Complex.ofReal_im]; ring
      rw [hex]
      have hss_re0 : 0 ≤ (s * s).re := by
        have : s * s = star v ⬝ᵥ v := hnrm.symm
        simpa [← this] using hre
      nlinarith [hre_bound]
    · rw [hEv', hnrm]
      simp [Complex.sub_im, Complex.mul_im, hss_im, himÛ, Complex.ofReal_re, Complex.ofReal_im]

theorem inv_smul_le_one_of_le_trace_smul {A : ℕ}
    (E : Matrix (Fin A) (Fin A) ℂ) (hE : E.PosSemidef) (c : ℝ)
    (hc : max (Matrix.trace E).re 1 ≤ c) (hc0 : 0 < c) :
    ((c⁻¹ : ℝ) • E) ≤ (1 : Matrix (Fin A) (Fin A) ℂ) := by
  have hE_le := PosSemidef.le_re_trace_smul_one E hE
  have ht_le : (Matrix.trace E).re ≤ c := (le_max_left _ _).trans hc
  have hE_le' : E ≤ (c : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) := by
    refine hE_le.trans ?_
    rw [Matrix.le_iff]
    have : (c : ℝ) • (1 : Matrix (Fin A) (Fin A) ℂ) -
        ((Matrix.trace E).re : ℝ) • 1 = (c - (Matrix.trace E).re) • 1 := by
      ext; simp [Matrix.sub_apply, Matrix.smul_apply]; ring
    rw [this]
    exact (PosSemidef.one).smul (sub_nonneg.mpr ht_le)
  rw [Matrix.le_iff] at hE_le' ⊢
  have : (1 : Matrix (Fin A) (Fin A) ℂ) - (c⁻¹ : ℝ) • E =
      (c⁻¹ : ℝ) • (c • 1 - E) := by
    ext i j
    have hc0' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> field_simp [hc0'] <;> ring
  rw [this]
  exact hE_le'.smul (inv_nonneg.mpr hc0.le)

noncomputable def effectExpectationExt {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E : Matrix (Fin A) (Fin A) ℂ) (hE : E.PosSemidef) : ℂ :=
  let c : ℝ := max (Matrix.trace E).re 1
  (c : ℂ) *
    effectExpectation (doubleDualEffectPairing F)
      ((c⁻¹ : ℝ) • E)
      (hE.smul (inv_nonneg.mpr (le_trans zero_le_one (le_max_right _ _))))
      (inv_smul_le_one_of_le_trace_smul E hE c le_rfl
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)))

theorem effectExpectation_smul_nonneg_doubleDual {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (r : ℝ) (hr0 : 0 ≤ r)
    (E : Matrix (Fin A) (Fin A) ℂ)
    (hE : E.PosSemidef) (hE1 : E ≤ 1) (hrE : (r • E) ≤ 1) :
    effectExpectation (doubleDualEffectPairing F) (r • E) (hE.smul hr0) hrE =
      (r : ℂ) * effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  by_cases hr1 : r ≤ 1
  · exact effectExpectation_smul_doubleDual F r hr0 hr1 E hE hE1
  · have hr1' : 1 < r := not_le.mp hr1
    have hrpos : 0 < r := lt_trans (by norm_num) hr1'
    have hinv0 : 0 ≤ (r⁻¹ : ℝ) := inv_nonneg.mpr hr0
    have hinv1 : (r⁻¹ : ℝ) ≤ 1 := inv_le_one_of_one_le₀ (le_of_lt hr1')
    have hRE_psd : (r • E).PosSemidef := hE.smul hr0
    have hsmul :=
      effectExpectation_smul_doubleDual F r⁻¹ hinv0 hinv1 (r • E) hRE_psd hrE
    have hE_eq : (r⁻¹ : ℝ) • (r • E) = E := by
      ext i j; simp [Matrix.smul_apply]; field_simp [hrpos.ne']
    have hr_ne : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have hβE :
        effectExpectation (doubleDualEffectPairing F) E hE hE1 =
          (r : ℂ)⁻¹ *
            effectExpectation (doubleDualEffectPairing F) (r • E) hRE_psd hrE := by
      have : effectExpectation (doubleDualEffectPairing F) E hE hE1 =
          effectExpectation (doubleDualEffectPairing F)
            ((r⁻¹ : ℝ) • (r • E)) ((hE.smul hr0).smul hinv0)
            (smul_le_one_of_le_one (r • E) hRE_psd hrE r⁻¹ hinv0 hinv1) := by
        simp only [effectExpectation, hE_eq]
      rw [this, ← Complex.ofReal_inv]
      exact hsmul
    calc effectExpectation (doubleDualEffectPairing F) (r • E) (hE.smul hr0) hrE
        = (r : ℂ) * ((r : ℂ)⁻¹ *
            effectExpectation (doubleDualEffectPairing F) (r • E) hRE_psd hrE) := by
            rw [← mul_assoc, mul_inv_cancel₀ hr_ne, one_mul]
      _ = (r : ℂ) * effectExpectation (doubleDualEffectPairing F) E hE hE1 := by rw [← hβE]

/-- Ext(E) = t * β(t⁻¹ • E) for any sufficiently large t. -/
theorem effectExpectationExt_eq_of_scale {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E : Matrix (Fin A) (Fin A) ℂ) (hE : E.PosSemidef) (t : ℝ)
    (ht : max (Matrix.trace E).re 1 ≤ t) (ht0 : 0 < t) :
    effectExpectationExt F E hE =
      (t : ℂ) * effectExpectation (doubleDualEffectPairing F) ((t⁻¹ : ℝ) • E)
        (hE.smul (inv_nonneg.mpr ht0.le))
        (inv_smul_le_one_of_le_trace_smul E hE t ht ht0) := by
  set c : ℝ := max (Matrix.trace E).re 1
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  have hle : c ≤ t := ht
  -- Ext = c β(c⁻¹ E); want t β(t⁻¹ E)
  -- t⁻¹ E = (c/t) • (c⁻¹ E)
  have hmat : (t⁻¹ : ℝ) • E = ((c / t) : ℝ) • ((c⁻¹ : ℝ) • E) := by
    ext; simp [Matrix.smul_apply]; field_simp [ht0.ne', hc0.ne']
  have hratio0 : 0 ≤ c / t := div_nonneg hc0.le ht0.le
  have hratio1 : c / t ≤ 1 := (div_le_one ht0).mpr hle
  have hE0_psd : ((c⁻¹ : ℝ) • E).PosSemidef := hE.smul (inv_nonneg.mpr hc0.le)
  have hE0_le : ((c⁻¹ : ℝ) • E) ≤ 1 :=
    inv_smul_le_one_of_le_trace_smul E hE c le_rfl hc0
  have hsmul :=
    effectExpectation_smul_nonneg_doubleDual F (c / t) hratio0
      ((c⁻¹ : ℝ) • E) hE0_psd hE0_le (by
        simpa [← hmat] using inv_smul_le_one_of_le_trace_smul E hE t ht ht0)
  have hc_ne : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have ht_ne : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  simp only [effectExpectationExt]
  have hβ :
      effectExpectation (doubleDualEffectPairing F) ((t⁻¹ : ℝ) • E)
          (hE.smul (inv_nonneg.mpr ht0.le))
          (inv_smul_le_one_of_le_trace_smul E hE t ht ht0) =
        (c / t : ℂ) *
          effectExpectation (doubleDualEffectPairing F) ((c⁻¹ : ℝ) • E)
            hE0_psd hE0_le := by
    simpa [hmat, effectExpectation, Complex.ofReal_div] using hsmul
  calc (c : ℂ) *
        effectExpectation (doubleDualEffectPairing F) ((c⁻¹ : ℝ) • E)
          (hE.smul (inv_nonneg.mpr (le_trans zero_le_one (le_max_right _ _))))
          (inv_smul_le_one_of_le_trace_smul E hE c le_rfl
            (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _))) =
      (c : ℂ) * effectExpectation (doubleDualEffectPairing F) ((c⁻¹ : ℝ) • E)
          hE0_psd hE0_le := by simp only [effectExpectation]
    _ = (t : ℂ) * ((c / t : ℂ) *
          effectExpectation (doubleDualEffectPairing F) ((c⁻¹ : ℝ) • E)
            hE0_psd hE0_le) := by field_simp [hc_ne, ht_ne]
    _ = (t : ℂ) * effectExpectation (doubleDualEffectPairing F) ((t⁻¹ : ℝ) • E)
          (hE.smul (inv_nonneg.mpr ht0.le))
          (inv_smul_le_one_of_le_trace_smul E hE t ht ht0) := by rw [← hβ]

theorem effectExpectationExt_smul {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (r : ℝ) (hr0 : 0 ≤ r)
    (E : Matrix (Fin A) (Fin A) ℂ) (hE : E.PosSemidef) :
    effectExpectationExt F (r • E) (hE.smul hr0) =
      (r : ℂ) * effectExpectationExt F E hE := by
  by_cases hr : r = 0
  · subst hr
    simp only [zero_smul, Complex.ofReal_zero, zero_mul]
    simp only [effectExpectationExt, Matrix.trace_zero, Complex.zero_re, max_eq_right zero_le_one]
    have h0 : ((1⁻¹ : ℝ) • (0 : Matrix (Fin A) (Fin A) ℂ)) = 0 := by ext; simp
    simpa [effectExpectation, h0] using effectExpectation_zero_doubleDual (A := A) F
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    set D : ℝ := max (Matrix.trace E).re 1
    have hD0 : 0 < D := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
    -- Choose U = max(D, c/r) where c = max(Tr(rE),1); equivalently U = max(D, max(Tr(rE),1)/r)
    have htr : Matrix.trace (r • E) = (r : ℂ) * Matrix.trace E := by
      simp [Matrix.trace, Finset.mul_sum, Matrix.smul_apply]
    have himE : (Matrix.trace E).im = 0 :=
      (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_nonneg hE)).2.symm
    have htRE : (Matrix.trace (r • E)).re = r * (Matrix.trace E).re := by
      have := congrArg Complex.re htr
      simpa [Complex.mul_re, himE, Complex.ofReal_re] using this
    set cRE : ℝ := max (Matrix.trace (r • E)).re 1
    have hcRE0 : 0 < cRE := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
    set U : ℝ := max D (cRE / r)
    have hU0 : 0 < U := lt_of_lt_of_le hD0 (le_max_left _ _)
    have hU_ge_D : D ≤ U := le_max_left _ _
    have hU_ge_c : cRE / r ≤ U := le_max_right _ _
    have hU_ge_E : max (Matrix.trace E).re 1 ≤ U := hU_ge_D
    have hUr_ge_RE : max (Matrix.trace (r • E)).re 1 ≤ r * U := by
      have : cRE ≤ r * U := by
        have h := (div_le_iff₀ hrpos).mp hU_ge_c
        rwa [mul_comm] at h
      simpa [cRE] using this
    have hE_eq := effectExpectationExt_eq_of_scale F E hE U hU_ge_E hU0
    have hRE_eq :=
      effectExpectationExt_eq_of_scale F (r • E) (hE.smul hr0) (r * U) hUr_ge_RE (mul_pos hrpos hU0)
    have hmat : ((r * U)⁻¹ : ℝ) • (r • E) = (U⁻¹ : ℝ) • E := by
      ext; simp [Matrix.smul_apply]; field_simp [hrpos.ne', hU0.ne']
    calc effectExpectationExt F (r • E) (hE.smul hr0)
        = (↑(r * U) : ℂ) *
            effectExpectation (doubleDualEffectPairing F) (((r * U)⁻¹ : ℝ) • (r • E))
              ((hE.smul hr0).smul (inv_nonneg.mpr (mul_pos hrpos hU0).le))
              (inv_smul_le_one_of_le_trace_smul (r • E) (hE.smul hr0) (r * U)
                hUr_ge_RE (mul_pos hrpos hU0)) := hRE_eq
      _ = (r : ℂ) * (U : ℂ) *
            effectExpectation (doubleDualEffectPairing F) ((U⁻¹ : ℝ) • E)
              (hE.smul (inv_nonneg.mpr hU0.le))
              (inv_smul_le_one_of_le_trace_smul E hE U hU_ge_E hU0) := by
            simp only [effectExpectation, hmat]; push_cast; ring
      _ = (r : ℂ) * effectExpectationExt F E hE := by
            rw [hE_eq]; ring


theorem effectExpectationExt_of_le_one {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E : Matrix (Fin A) (Fin A) ℂ) (hE : E.PosSemidef) (hE1 : E ≤ 1) :
    effectExpectationExt F E hE =
      effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
  have h := effectExpectationExt_eq_of_scale F E hE
    (max (Matrix.trace E).re 1) le_rfl
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _))
  simp only [effectExpectationExt] at h ⊢
  set c : ℝ := max (Matrix.trace E).re 1
  have hc0 : 0 ≤ c := le_trans zero_le_one (le_max_right _ _)
  have hc1 : 1 ≤ c := le_max_right _ _
  have hinv0 : 0 ≤ (c⁻¹ : ℝ) := inv_nonneg.mpr hc0
  have hinv1 : (c⁻¹ : ℝ) ≤ 1 := inv_le_one_of_one_le₀ hc1
  have hsmul := effectExpectation_smul_doubleDual F c⁻¹ hinv0 hinv1 E hE hE1
  have hc_ne : (c : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hc1)
  calc (c : ℂ) *
        effectExpectation (doubleDualEffectPairing F) ((c⁻¹ : ℝ) • E)
          (hE.smul (inv_nonneg.mpr (le_trans zero_le_one (le_max_right _ _))))
          (inv_smul_le_one_of_le_trace_smul E hE c le_rfl
            (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _))) =
      (c : ℂ) *
        effectExpectation (doubleDualEffectPairing F) ((c⁻¹ : ℝ) • E)
          (hE.smul hinv0) (smul_le_one_of_le_one E hE hE1 c⁻¹ hinv0 hinv1) := by
            simp only [effectExpectation]
    _ = (c : ℂ) * ((c⁻¹ : ℂ) *
          effectExpectation (doubleDualEffectPairing F) E hE hE1) := by
            rw [hsmul]; simp [Complex.ofReal_inv]
    _ = effectExpectation (doubleDualEffectPairing F) E hE hE1 := by
            field_simp [hc_ne]

theorem effectExpectationExt_add {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E G : Matrix (Fin A) (Fin A) ℂ) (hE : E.PosSemidef) (hG : G.PosSemidef) :
    effectExpectationExt F (E + G) (hE.add hG) =
      effectExpectationExt F E hE + effectExpectationExt F G hG := by
  set cE : ℝ := max (Matrix.trace E).re 1
  set cG : ℝ := max (Matrix.trace G).re 1
  set t : ℝ := cE + cG
  have hcE0 : 0 < cE := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  have hcG0 : 0 < cG := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  have ht0 : 0 < t := add_pos hcE0 hcG0
  have himE : (Matrix.trace E).im = 0 :=
    (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_nonneg hE)).2.symm
  have himG : (Matrix.trace G).im = 0 :=
    (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_nonneg hG)).2.symm
  have htSum : (Matrix.trace (E + G)).re =
      (Matrix.trace E).re + (Matrix.trace G).re := by
    simp [Matrix.trace_add, Complex.add_re]
  have ht_ge_sum : max (Matrix.trace (E + G)).re 1 ≤ t := by
    rw [htSum]
    refine max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) ?_
    · calc (1 : ℝ) ≤ cE := le_max_right _ _
        _ ≤ cE + cG := le_add_of_nonneg_right hcG0.le
  have ht_ge_E : max (Matrix.trace E).re 1 ≤ t :=
    le_add_of_nonneg_right hcG0.le
  have ht_ge_G : max (Matrix.trace G).re 1 ≤ t :=
    le_add_of_nonneg_left hcE0.le
  have hE_eq := effectExpectationExt_eq_of_scale F E hE t ht_ge_E ht0
  have hG_eq := effectExpectationExt_eq_of_scale F G hG t ht_ge_G ht0
  have hSum_eq :=
    effectExpectationExt_eq_of_scale F (E + G) (hE.add hG) t ht_ge_sum ht0
  have hmat : (t⁻¹ : ℝ) • (E + G) = (t⁻¹ : ℝ) • E + (t⁻¹ : ℝ) • G := smul_add _ _ _
  have hE1 : ((t⁻¹ : ℝ) • E) ≤ 1 :=
    inv_smul_le_one_of_le_trace_smul E hE t ht_ge_E ht0
  have hG1 : ((t⁻¹ : ℝ) • G) ≤ 1 :=
    inv_smul_le_one_of_le_trace_smul G hG t ht_ge_G ht0
  have hSum1 : ((t⁻¹ : ℝ) • (E + G)) ≤ 1 :=
    inv_smul_le_one_of_le_trace_smul (E + G) (hE.add hG) t ht_ge_sum ht0
  have hEG1 : ((t⁻¹ : ℝ) • E + (t⁻¹ : ℝ) • G) ≤ 1 := by
    convert hSum1 using 1
    exact hmat.symm
  have hadd :=
    effectExpectation_add_doubleDual F ((t⁻¹ : ℝ) • E) ((t⁻¹ : ℝ) • G)
      (hE.smul (inv_nonneg.mpr ht0.le)) (hG.smul (inv_nonneg.mpr ht0.le))
      hE1 hG1 hEG1
  have hSum_β :
      effectExpectation (doubleDualEffectPairing F) ((t⁻¹ : ℝ) • (E + G))
          ((hE.add hG).smul (inv_nonneg.mpr ht0.le)) hSum1 =
        effectExpectation (doubleDualEffectPairing F)
          ((t⁻¹ : ℝ) • E + (t⁻¹ : ℝ) • G)
          ((hE.smul (inv_nonneg.mpr ht0.le)).add (hG.smul (inv_nonneg.mpr ht0.le)))
          hEG1 := by
    simp only [effectExpectation, hmat]
  calc effectExpectationExt F (E + G) (hE.add hG)
      = (t : ℂ) * effectExpectation (doubleDualEffectPairing F) ((t⁻¹ : ℝ) • (E + G))
          ((hE.add hG).smul (inv_nonneg.mpr ht0.le)) hSum1 := hSum_eq
    _ = (t : ℂ) * effectExpectation (doubleDualEffectPairing F)
          ((t⁻¹ : ℝ) • E + (t⁻¹ : ℝ) • G)
          ((hE.smul (inv_nonneg.mpr ht0.le)).add (hG.smul (inv_nonneg.mpr ht0.le)))
          hEG1 := by rw [hSum_β]
    _ = (t : ℂ) * (effectExpectation (doubleDualEffectPairing F) ((t⁻¹ : ℝ) • E)
          (hE.smul (inv_nonneg.mpr ht0.le)) hE1 +
        effectExpectation (doubleDualEffectPairing F) ((t⁻¹ : ℝ) • G)
          (hG.smul (inv_nonneg.mpr ht0.le)) hG1) := by rw [hadd]
    _ = effectExpectationExt F E hE + effectExpectationExt F G hG := by
          rw [mul_add, ← hE_eq, ← hG_eq]

theorem effectPairingQuad_eq_ext {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (v : Fin A → ℂ) :
    effectPairingQuad (doubleDualEffectPairing F) v =
      effectExpectationExt F (Matrix.vecMulVec v (star v))
        (Matrix.posSemidef_vecMulVec_self_star v) := by
  by_cases hle : Matrix.vecMulVec v (star v) ≤ (1 : Matrix (Fin A) (Fin A) ℂ)
  · rw [effectPairingQuad_eq_expectation F v hle, effectExpectationExt_of_le_one]
  · have hv : star v ⬝ᵥ v ≠ 0 := by
      intro hv0
      have : v = 0 := (dotProduct_star_self_eq_zero).1 hv0
      have hmat0 : Matrix.vecMulVec v (star v) = 0 := by simp [this]
      have h0le : (0 : Matrix (Fin A) (Fin A) ℂ) ≤ 1 := by
        rw [Matrix.le_iff, sub_zero]; exact PosSemidef.one
      exact hle (by simpa [hmat0] using h0le)
    set û := normalizeVec v hv
    have hre := (star_dotProduct_self_nonneg_real v).1
    have him := (star_dotProduct_self_nonneg_real v).2
    set s : ℂ := ↑(Real.sqrt (star v ⬝ᵥ v).re)
    have hv_eq : v = s • û := by
      simp only [û, normalizeVec, s]
      ext i
      have hs_ne : s ≠ 0 := by
        intro hs0
        have : (star v ⬝ᵥ v).re = 0 :=
          (Real.sqrt_eq_zero hre).1 (by simpa [s] using congrArg Complex.re hs0)
        exact hv (Complex.ext this him)
      change v i = s * (s⁻¹ * v i)
      field_simp [hs_ne]
    have hstar_s : star s = s := by simp [s, Complex.conj_ofReal]
    have hnrm_sq : star v ⬝ᵥ v = s * s := by
      apply Complex.ext
      · have : (star v ⬝ᵥ v).re = s.re * s.re := by
          simpa [s, Complex.ofReal_re] using (Real.mul_self_sqrt hre).symm
        simpa [Complex.mul_re, s] using this
      · simpa [Complex.mul_im, s] using him
    have hmat : Matrix.vecMulVec v (star v) =
        ((star v ⬝ᵥ v).re : ℝ) • Matrix.vecMulVec û (star û) := by
      have hnrm_ofReal : (↑((star v ⬝ᵥ v).re) : ℂ) = star v ⬝ᵥ v :=
        ofReal_re_of_im_zero _ him
      have hsmul_eq :
          ((star v ⬝ᵥ v).re : ℝ) • Matrix.vecMulVec û (star û) =
            (star v ⬝ᵥ v) • Matrix.vecMulVec û (star û) := by
        ext i j; simp [Matrix.smul_apply, smul_eq_mul, hnrm_ofReal]
      calc Matrix.vecMulVec v (star v)
          = Matrix.vecMulVec (s • û) (star (s • û)) := by rw [hv_eq]
        _ = (s * star s) • Matrix.vecMulVec û (star û) := vecMulVec_smul_star s û
        _ = (s * s) • Matrix.vecMulVec û (star û) := by rw [hstar_s]
        _ = (star v ⬝ᵥ v) • Matrix.vecMulVec û (star û) := by rw [← hnrm_sq]
        _ = ((star v ⬝ᵥ v).re : ℝ) • Matrix.vecMulVec û (star û) := by rw [← hsmul_eq]
    have hû_le : Matrix.vecMulVec û (star û) ≤ 1 :=
      vecMulVec_unit_le_one û (normalizeVec_norm v hv)
    have hs0 : 0 ≤ (star v ⬝ᵥ v).re := hre
    set r : ℝ := (star v ⬝ᵥ v).re
    have hnrm_ofReal : (r : ℂ) = star v ⬝ᵥ v := ofReal_re_of_im_zero _ him
    have hQ : effectPairingQuad (doubleDualEffectPairing F) v =
        (r : ℂ) *
          effectExpectation (doubleDualEffectPairing F)
            (Matrix.vecMulVec û (star û))
            (Matrix.posSemidef_vecMulVec_self_star û) hû_le := by
      calc effectPairingQuad (doubleDualEffectPairing F) v
          = effectPairingQuad (doubleDualEffectPairing F) (s • û) := by rw [hv_eq]
        _ = (star s * s) * effectPairingQuad (doubleDualEffectPairing F) û :=
              effectPairingQuad_smul _ _ _
        _ = (s * s) * effectPairingQuad (doubleDualEffectPairing F) û := by rw [hstar_s]
        _ = (star v ⬝ᵥ v) * effectPairingQuad (doubleDualEffectPairing F) û := by
              rw [← hnrm_sq]
        _ = (r : ℂ) * effectPairingQuad (doubleDualEffectPairing F) û := by rw [← hnrm_ofReal]
        _ = (r : ℂ) *
              effectExpectation (doubleDualEffectPairing F)
                (Matrix.vecMulVec û (star û))
                (Matrix.posSemidef_vecMulVec_self_star û) hû_le := by
              rw [effectPairingQuad_eq_expectation F û hû_le]
    have hExt :=
      effectExpectationExt_smul F r hs0
        (Matrix.vecMulVec û (star û)) (Matrix.posSemidef_vecMulVec_self_star û)
    have hû_ext :=
      effectExpectationExt_of_le_one F (Matrix.vecMulVec û (star û))
        (Matrix.posSemidef_vecMulVec_self_star û) hû_le
    have hmat' : Matrix.vecMulVec v (star v) =
        (r : ℝ) • Matrix.vecMulVec û (star û) := hmat
    calc effectPairingQuad (doubleDualEffectPairing F) v
        = (r : ℂ) *
            effectExpectation (doubleDualEffectPairing F)
              (Matrix.vecMulVec û (star û))
              (Matrix.posSemidef_vecMulVec_self_star û) hû_le := hQ
      _ = (r : ℂ) *
            effectExpectationExt F (Matrix.vecMulVec û (star û))
              (Matrix.posSemidef_vecMulVec_self_star û) := by rw [← hû_ext]
      _ = effectExpectationExt F ((r : ℝ) • Matrix.vecMulVec û (star û))
            ((Matrix.posSemidef_vecMulVec_self_star û).smul hs0) := hExt.symm
      _ = effectExpectationExt F (Matrix.vecMulVec v (star v))
            (Matrix.posSemidef_vecMulVec_self_star v) := by
            simp only [effectExpectationExt, hmat']


/-! ### Polar ℂ-sesquilinearity -/

theorem effectPairingPolar_neg_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) (-x) y =
      -effectPairingPolar (doubleDualEffectPairing F) x y := by
  have h := effectPairingPolar_add_left F x (-x) y
  simp only [add_neg_cancel, effectPairingPolar_zero_left] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem effectPairingPolar_natCast_smul_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (k : ℕ) (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) ((k : ℂ) • x) y =
      (k : ℂ) * effectPairingPolar (doubleDualEffectPairing F) x y := by
  have : (k : ℂ) • x = k • x := by ext i; simp [nsmul_eq_mul]
  rw [this, effectPairingPolar_nsmul_left]

theorem effectPairingPolar_zsmul_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (n : ℤ) (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) ((n : ℂ) • x) y =
      (n : ℂ) * effectPairingPolar (doubleDualEffectPairing F) x y := by
  cases n with
  | ofNat k => simpa using effectPairingPolar_natCast_smul_left F k x y
  | negSucc k =>
    simp only [Int.cast_negSucc]
    have hk := effectPairingPolar_natCast_smul_left F (k + 1) x y
    have hneg : ∀ z : ℂ, (-z) • x = -(z • x) := fun z => by ext; rw [neg_smul]
    rw [hneg, effectPairingPolar_neg_left, hk]; ring

theorem effectPairingPolar_qsmul_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (q : ℚ) (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) ((q : ℂ) • x) y =
      (q : ℂ) * effectPairingPolar (doubleDualEffectPairing F) x y := by
  let hom : ℂ →+ ℂ := AddMonoidHom.mk'
    (fun c => effectPairingPolar (doubleDualEffectPairing F) (c • x) y)
    (fun a b => by
      simpa [add_smul] using
        effectPairingPolar_add_left F (a • x) (b • x) y)
  let lhom : ℂ →ₗ[ℚ] ℂ := AddMonoidHom.toRatLinearMap hom
  simpa [lhom, hom, Rat.smul_def, one_smul] using lhom.map_smul q (1 : ℂ)

theorem effectPairingPolar_I_smul_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) (Complex.I • x) y =
      -Complex.I * effectPairingPolar (doubleDualEffectPairing F) x y := by
  set α := doubleDualEffectPairing F
  rw [effectPairingPolar_eq_ofNorm α (Complex.I • x) y,
    effectPairingPolar_eq_ofNorm α x y]
  have hII : Complex.I • (Complex.I • x) = (-1 : ℂ) • x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  have hII' : (-1 : ℂ) • x = -x := by ext; simp
  have h3 : effectPairingQuad α (Complex.I • (Complex.I • x) + y) =
      effectPairingQuad α (x - y) := by
    rw [hII, hII']
    have : -x + y = -(x - y) := by ext; simp [sub_eq_add_neg]; abel
    rw [this, q_neg]
  have h4 : effectPairingQuad α (Complex.I • (Complex.I • x) - y) =
      effectPairingQuad α (x + y) := by
    rw [hII, hII']
    have : -x - y = -(x + y) := by ext; simp [sub_eq_add_neg]; abel
    rw [this, q_neg]
  rw [h3, h4]; ring_nf; rw [Complex.I_sq]; ring


theorem effectPairingQuad_norm_le {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (v : Fin A → ℂ) :
    ‖effectPairingQuad (doubleDualEffectPairing F) v‖ ≤ (star v ⬝ᵥ v).re := by
  have hn := star_dotProduct_self_nonneg_real v
  have hq := effectPairingQuad_nonneg (doubleDualEffectPairing F) v
  have hnorm : ‖effectPairingQuad (doubleDualEffectPairing F) v‖ =
      |(effectPairingQuad (doubleDualEffectPairing F) v).re| :=
    (Complex.abs_re_eq_norm.mpr hq.2).symm
  rw [hnorm, abs_of_nonneg hq.1]
  simp only [effectPairingQuad]
  split_ifs with h
  · exact hn.1
  · have hb := bornScalar_nonneg
      (doubleDualEffectPairing F
        (ofEffect (Matrix.vecMulVec (normalizeVec v h) (star (normalizeVec v h)))
          (Matrix.posSemidef_vecMulVec_self_star _)
          (vecMulVec_unit_le_one _ (normalizeVec_norm v h))))
    set β := bornScalar (doubleDualEffectPairing F
      (ofEffect (Matrix.vecMulVec (normalizeVec v h) (star (normalizeVec v h)))
        (Matrix.posSemidef_vecMulVec_self_star _)
        (vecMulVec_unit_le_one _ (normalizeVec_norm v h))))
    have hre : ((star v ⬝ᵥ v) * β).re = (star v ⬝ᵥ v).re * β.re := by
      simp [Complex.mul_re, hn.2, hb.2.1]
    change ((star v ⬝ᵥ v) * β).re ≤ (star v ⬝ᵥ v).re
    rw [hre]; nlinarith [hn.1, hb.2.2]

theorem re_star_dot_eq_sum_normSq {A : ℕ}
    (v : Fin A → ℂ) :
    (star v ⬝ᵥ v).re = ∑ i : Fin A, Complex.normSq (v i) := by
  simp only [dotProduct, Pi.star_apply]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : star (v i) * v i = (Complex.normSq (v i) : ℂ) := by
    simpa [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := v i)).symm
  rw [this, Complex.ofReal_re]

theorem normSq_add_le_two (z w : ℂ) :
    Complex.normSq (z + w) ≤ 2 * (Complex.normSq z + Complex.normSq w) := by
  have h := Complex.normSq_add z w
  have hsub := Complex.normSq_sub z w
  have : Complex.normSq (z + w) + Complex.normSq (z - w) =
      2 * (Complex.normSq z + Complex.normSq w) := by
    rw [h, hsub]; ring
  linarith [Complex.normSq_nonneg (z - w)]

theorem re_norm_smul_add_le {A : ℕ}
    (r : ℝ) (hr : |r| ≤ 1) (x z : Fin A → ℂ) :
    (star ((r : ℂ) • x + z) ⬝ᵥ ((r : ℂ) • x + z)).re ≤
      2 * ((star x ⬝ᵥ x).re + (star z ⬝ᵥ z).re) := by
  rw [re_star_dot_eq_sum_normSq, re_star_dot_eq_sum_normSq x, re_star_dot_eq_sum_normSq z]
  calc ∑ i : Fin A, Complex.normSq (((r : ℂ) • x + z) i)
      = ∑ i, Complex.normSq ((r : ℂ) * x i + z i) := by
          simp [Pi.add_apply, Pi.smul_apply]
    _ ≤ ∑ i, 2 * (Complex.normSq ((r : ℂ) * x i) + Complex.normSq (z i)) :=
          Finset.sum_le_sum fun i _ => normSq_add_le_two _ _
    _ = 2 * (∑ i, Complex.normSq ((r : ℂ) * x i) + ∑ i, Complex.normSq (z i)) := by
          rw [← Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 2 * (r ^ 2 * ∑ i, Complex.normSq (x i) + ∑ i, Complex.normSq (z i)) := by
          have : ∀ i, Complex.normSq ((r : ℂ) * x i) = r ^ 2 * Complex.normSq (x i) := by
            intro i; simp [Complex.normSq_mul, Complex.normSq_ofReal, sq]
          simp_rw [this, ← Finset.mul_sum]
    _ ≤ 2 * (∑ i, Complex.normSq (x i) + ∑ i, Complex.normSq (z i)) := by
          have hr2 : r ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one r).2 hr
          nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin A))) =>
            Complex.normSq_nonneg (x i))]

noncomputable def effectPairingPolarRealHom {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y : Fin A → ℂ) : ℝ →+ ℂ :=
  AddMonoidHom.mk'
    (fun r => effectPairingPolar (doubleDualEffectPairing F) ((r : ℂ) • x) y)
    (fun a b => by
      have : ((a + b : ℝ) : ℂ) • x = (a : ℂ) • x + (b : ℂ) • x := by
        ext i; simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
      rw [this, effectPairingPolar_add_left])

theorem effectPairingPolarRealHom_continuous {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x y : Fin A → ℂ) : Continuous (effectPairingPolarRealHom F x y) := by
  have hs : Metric.ball (0 : ℝ) 1 ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
  refine (effectPairingPolarRealHom F x y).continuous_of_isBounded_nhds_zero hs ?_
  rw [isBounded_iff_forall_norm_le]
  refine ⟨8 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re + 1), ?_⟩
  intro z hz
  obtain ⟨r, hrMem, rfl⟩ := (Set.mem_image _ _ _).1 hz
  have hrle : |r| ≤ 1 := le_of_lt (by
    simpa [Real.dist_eq, sub_zero] using Metric.mem_ball.mp hrMem)
  simp only [effectPairingPolarRealHom, AddMonoidHom.mk'_apply, effectPairingPolar]
  set Q := effectPairingQuad (doubleDualEffectPairing F)
  have bound (w : Fin A → ℂ) :
      ‖Q ((r : ℂ) • x + w)‖ ≤ 2 * ((star x ⬝ᵥ x).re + (star w ⬝ᵥ w).re) :=
    le_trans (effectPairingQuad_norm_le F _) (re_norm_smul_add_le r hrle x w)
  have hyI : (star (Complex.I • y) ⬝ᵥ (Complex.I • y)).re = (star y ⬝ᵥ y).re := by
    have h : star Complex.I * Complex.I = 1 := by simp [Complex.conj_I, Complex.I_mul_I]
    rw [star_dotProduct_smul_self, h, one_mul]
  have hneg (w : Fin A → ℂ) : (star (-w) ⬝ᵥ (-w)).re = (star w ⬝ᵥ w).re := by
    have : -w = (-1 : ℂ) • w := by ext; simp
    rw [this, star_dotProduct_smul_self]; simp
  have hsub (w : Fin A → ℂ) : (r : ℂ) • x - w = (r : ℂ) • x + (-w) := by
    ext; simp [sub_eq_add_neg]
  have htri :
      ‖(Q ((r:ℂ)•x+y) - Q ((r:ℂ)•x-y) - Complex.I*Q ((r:ℂ)•x+Complex.I•y) +
          Complex.I*Q ((r:ℂ)•x-Complex.I•y)) / 4‖ ≤
        ‖Q ((r:ℂ)•x+y)‖ + ‖Q ((r:ℂ)•x-y)‖ + ‖Q ((r:ℂ)•x+Complex.I•y)‖ +
          ‖Q ((r:ℂ)•x-Complex.I•y)‖ := by
    have hdiv (a : ℂ) : ‖a / 4‖ ≤ ‖a‖ := by
      rw [norm_div]
      have : ‖(4 : ℂ)‖ = 4 := by norm_num
      rw [this]; exact div_le_self (norm_nonneg _) (by norm_num)
    refine le_trans (hdiv _) ?_
    set a := Q ((r:ℂ)•x+y)
    set b := Q ((r:ℂ)•x-y)
    set c := Q ((r:ℂ)•x+Complex.I•y)
    set d := Q ((r:ℂ)•x-Complex.I•y)
    have : a - b - Complex.I * c + Complex.I * d = a + (-b) + (-(Complex.I * c)) + Complex.I * d := by
      ring
    rw [this]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
    refine le_trans (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) ?_
    simp only [norm_neg, norm_mul, Complex.norm_I, one_mul]
    exact le_rfl
  have Nx := (star_dotProduct_self_nonneg_real x).1
  have Ny := (star_dotProduct_self_nonneg_real y).1
  have b1 := bound y
  have b2 : ‖Q ((r:ℂ)•x-y)‖ ≤ 2 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) := by
    rw [hsub y]; refine le_trans (bound (-y)) ?_; rw [hneg y]
  have b3 : ‖Q ((r:ℂ)•x+Complex.I•y)‖ ≤ 2 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) := by
    refine le_trans (bound (Complex.I • y)) ?_; rw [hyI]
  have b4 : ‖Q ((r:ℂ)•x-Complex.I•y)‖ ≤ 2 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) := by
    rw [hsub (Complex.I • y)]; refine le_trans (bound (-(Complex.I • y))) ?_
    rw [hneg (Complex.I • y), hyI]
  refine le_trans htri ?_
  nlinarith [b1, b2, b3, b4, Nx, Ny]

theorem effectPairingPolar_ofReal_smul_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (r : ℝ) (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) ((r : ℂ) • x) y =
      (r : ℂ) * effectPairingPolar (doubleDualEffectPairing F) x y := by
  have h := map_real_smul (effectPairingPolarRealHom F x y) (effectPairingPolarRealHom_continuous F x y) r (1 : ℝ)
  simpa [effectPairingPolarRealHom, AddMonoidHom.mk'_apply, one_smul] using h

theorem effectPairingPolar_smul_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (c : ℂ) (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) (c • x) y =
      star c * effectPairingPolar (doubleDualEffectPairing F) x y := by
  have hre := effectPairingPolar_ofReal_smul_left F c.re x y
  have him := effectPairingPolar_ofReal_smul_left F c.im (Complex.I • x) y
  have hI := effectPairingPolar_I_smul_left F x y
  have hc : c • x = (c.re : ℂ) • x + (c.im : ℂ) • (Complex.I • x) := by
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    -- RHS = c.re * xi + c.im * (I * xi) = (c.re + c.im * I) * xi = c * xi
    trans ((c.re : ℂ) + (c.im : ℂ) * Complex.I) * x i
    · exact (Complex.re_add_im c).symm ▸ rfl
    · ring
  rw [hc, effectPairingPolar_add_left, hre, him, hI]
  have hstar : star c = (c.re : ℂ) + (c.im : ℂ) * (-Complex.I) := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  rw [hstar]; ring






theorem effectPairingPolar_smul_right {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (c : ℂ) (x y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) x (c • y) =
      c * effectPairingPolar (doubleDualEffectPairing F) x y := by
  have h1 := effectPairingPolar_conj_symm F x (c • y)
  have h2 := effectPairingPolar_smul_left F c y x
  have h3 := effectPairingPolar_conj_symm F x y
  calc effectPairingPolar (doubleDualEffectPairing F) x (c • y)
      = star (effectPairingPolar (doubleDualEffectPairing F) (c • y) x) := h1.symm
    _ = star (star c * effectPairingPolar (doubleDualEffectPairing F) y x) := by rw [h2]
    _ = star (effectPairingPolar (doubleDualEffectPairing F) y x) * star (star c) := by
          rw [star_mul]
    _ = star (effectPairingPolar (doubleDualEffectPairing F) y x) * c := by
          rw [star_star]
    _ = c * star (effectPairingPolar (doubleDualEffectPairing F) y x) := mul_comm _ _
    _ = c * effectPairingPolar (doubleDualEffectPairing F) x y := by rw [h3]

theorem effectPairingPolar_zero_right {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (x : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) x 0 = 0 := by
  have h := effectPairingPolar_conj_symm F 0 x
  have h0 := effectPairingPolar_zero_left F x
  have : star (effectPairingPolar (doubleDualEffectPairing F) x 0) = 0 := by
    rw [h, h0]
  exact (star_eq_zero.mp this)

theorem effectPairingPolar_sum_left {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (s : Finset (Fin A)) (v : Fin A → ℂ) (y : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F)
        (∑ i ∈ s, v i • Pi.single i (1 : ℂ)) y =
      ∑ i ∈ s, star (v i) * effectPairingPolar (doubleDualEffectPairing F)
        (Pi.single i (1 : ℂ)) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [effectPairingPolar_zero_left]
  | insert i s hs ih =>
    simp only [Finset.sum_insert hs]
    rw [effectPairingPolar_add_left, effectPairingPolar_smul_left, ih]

theorem effectPairingPolar_sum_right {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (s : Finset (Fin A)) (x : Fin A → ℂ) (w : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) x
        (∑ j ∈ s, w j • Pi.single j (1 : ℂ)) =
      ∑ j ∈ s, w j * effectPairingPolar (doubleDualEffectPairing F) x
        (Pi.single j (1 : ℂ)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [effectPairingPolar_zero_right]
  | insert j s hs ih =>
    simp only [Finset.sum_insert hs]
    rw [effectPairingPolar_add_right, effectPairingPolar_smul_right, ih]

theorem eq_sum_single {A : ℕ}
    (v : Fin A → ℂ) :
    v = ∑ i : Fin A, v i • Pi.single i (1 : ℂ) := by
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  classical
  -- goal: v j = ∑ i, v i * (if j = i then 1 else 0)
  symm
  calc ∑ i : Fin A, v i * (if j = i then (1 : ℂ) else 0)
      = ∑ i : Fin A, if j = i then v i else 0 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs <;> simp
    _ = v j := by simp [Finset.sum_ite_eq]


theorem sum_psd_matrix {A : ℕ} {ι : Type*}
    (s : Finset ι) (M : ι → Matrix (Fin A) (Fin A) ℂ)
    (h : ∀ i ∈ s, (M i).PosSemidef) :
    (∑ i ∈ s, M i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact PosSemidef.zero
  | insert i s hs ih =>
    rw [Finset.sum_insert hs]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem le_one_of_add_le_one_of_posSemidef {A : ℕ}
    (P S : Matrix (Fin A) (Fin A) ℂ) (hP : P.PosSemidef) (hle : P + S ≤ 1) :
    S ≤ 1 := by
  rw [Matrix.le_iff] at hle ⊢
  have : (1 : Matrix (Fin A) (Fin A) ℂ) - S = (1 - (P + S)) + P := by
    abel
  rw [this]
  exact hle.add hP

theorem sum_rankOne_eq_one {A : ℕ} :
    (∑ i : Fin A, Matrix.vecMulVec (Pi.single i (1 : ℂ))
      (star (Pi.single i (1 : ℂ)))) = (1 : Matrix (Fin A) (Fin A) ℂ) := by
  ext a b
  simp only [Matrix.one_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Pi.single_apply]
  classical
  by_cases hab : a = b
  · subst hab
    have : ∀ i, (if a = i then (1 : ℂ) else 0) * star (if a = i then (1 : ℂ) else 0) =
        if a = i then 1 else 0 := by
      intro i; split_ifs <;> simp
    simp_rw [this, Finset.sum_ite_eq]
    simp
  · have h : ∀ i, (if a = i then (1 : ℂ) else 0) * star (if b = i then (1 : ℂ) else 0) = 0 := by
      intro i
      by_cases hai : a = i
      · have hbi : b ≠ i := fun h => hab (hai.trans h.symm)
        simp [hai, hbi]
      · simp [hai]
    simp_rw [h, Finset.sum_const_zero]
    simp [hab]

theorem single_normSq_one {A : ℕ} (i : Fin A) :
    star (Pi.single i (1 : ℂ)) ⬝ᵥ Pi.single i (1 : ℂ) = 1 := by
  simp only [dotProduct, Pi.single_apply, Pi.star_apply]
  classical
  calc ∑ x : Fin A, star (if x = i then (1 : ℂ) else 0) * (if x = i then 1 else 0)
      = ∑ x : Fin A, if x = i then (1 : ℂ) else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          split_ifs <;> simp
    _ = 1 := by simp

theorem effectExpectation_sum_rankOne {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier) :
    (∑ i : Fin A, effectExpectation (doubleDualEffectPairing F)
        (Matrix.vecMulVec (Pi.single i (1 : ℂ)) (star (Pi.single i (1 : ℂ))))
        (Matrix.posSemidef_vecMulVec_self_star _)
        (vecMulVec_unit_le_one _ (single_normSq_one i))) =
      effectExpectation (doubleDualEffectPairing F)
        (1 : Matrix (Fin A) (Fin A) ℂ) PosSemidef.one le_rfl := by
  classical
  have hadd : ∀ (s : Finset (Fin A))
      (hle : (∑ i ∈ s, Matrix.vecMulVec (Pi.single i (1 : ℂ))
            (star (Pi.single i (1 : ℂ)))) ≤ (1 : Matrix (Fin A) (Fin A) ℂ)),
      effectExpectation (doubleDualEffectPairing F)
          (∑ i ∈ s, Matrix.vecMulVec (Pi.single i (1 : ℂ))
            (star (Pi.single i (1 : ℂ))))
          (sum_psd_matrix s _ (fun i _ => Matrix.posSemidef_vecMulVec_self_star _))
          hle =
        ∑ i ∈ s, effectExpectation (doubleDualEffectPairing F)
          (Matrix.vecMulVec (Pi.single i (1 : ℂ)) (star (Pi.single i (1 : ℂ))))
          (Matrix.posSemidef_vecMulVec_self_star _)
          (vecMulVec_unit_le_one _ (single_normSq_one i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro hle
      simp only [Finset.sum_empty]
      exact effectExpectation_zero_doubleDual F
    | insert i s hs ih =>
      intro hle
      simp only [Finset.sum_insert hs] at hle ⊢
      have hE := Matrix.posSemidef_vecMulVec_self_star (Pi.single i (1 : ℂ))
      have hS := sum_psd_matrix s (fun j => Matrix.vecMulVec (Pi.single j (1 : ℂ))
          (star (Pi.single j (1 : ℂ))))
        (fun j _ => Matrix.posSemidef_vecMulVec_self_star _)
      have hEle : Matrix.vecMulVec (Pi.single i (1 : ℂ))
          (star (Pi.single i (1 : ℂ))) ≤ (1 : Matrix (Fin A) (Fin A) ℂ) :=
        vecMulVec_unit_le_one _ (single_normSq_one i)
      have hSle := le_one_of_add_le_one_of_posSemidef _ _ hE hle
      rw [effectExpectation_add_doubleDual F _ _ hE hS hEle hSle hle, ih hSle]
  have huniv_le : (∑ i : Fin A, Matrix.vecMulVec (Pi.single i (1 : ℂ))
      (star (Pi.single i (1 : ℂ)))) ≤ (1 : Matrix (Fin A) (Fin A) ℂ) := by
    rw [sum_rankOne_eq_one]
  have h := hadd Finset.univ huniv_le
  have hβ :
      effectExpectation (doubleDualEffectPairing F)
          (∑ i : Fin A, Matrix.vecMulVec (Pi.single i (1 : ℂ))
            (star (Pi.single i (1 : ℂ))))
          (sum_psd_matrix Finset.univ _ (fun i _ => Matrix.posSemidef_vecMulVec_self_star _))
          huniv_le =
        effectExpectation (doubleDualEffectPairing F)
          (1 : Matrix (Fin A) (Fin A) ℂ) PosSemidef.one le_rfl := by
    simp only [effectExpectation, sum_rankOne_eq_one]
  exact hβ ▸ h.symm

theorem trace_density_le_one {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier) :
    (Matrix.trace (densityFromEffectPairing (doubleDualEffectPairing F))).re ≤ 1 := by
  set ρ := densityFromEffectPairing (doubleDualEffectPairing F)
  have htr : Matrix.trace ρ =
      ∑ i : Fin A, effectPairingQuad (doubleDualEffectPairing F)
        (Pi.single i (1 : ℂ)) := by
    change ∑ i, ρ i i = ∑ i, effectPairingQuad (doubleDualEffectPairing F) (Pi.single i 1)
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ρ, densityFromEffectPairing]
    exact effectPairingPolar_self (doubleDualEffectPairing F) (Pi.single i 1)
  have hQ : ∀ i, effectPairingQuad (doubleDualEffectPairing F) (Pi.single i (1 : ℂ)) =
      effectExpectation (doubleDualEffectPairing F)
        (Matrix.vecMulVec (Pi.single i (1 : ℂ)) (star (Pi.single i (1 : ℂ))))
        (Matrix.posSemidef_vecMulVec_self_star _)
        (vecMulVec_unit_le_one _ (single_normSq_one i)) := by
    intro i
    exact effectPairingQuad_eq_expectation F (Pi.single i (1 : ℂ))
      (vecMulVec_unit_le_one _ (single_normSq_one i))
  have hsum := effectExpectation_sum_rankOne F
  have hborn := bornScalar_nonneg
    (doubleDualEffectPairing F (ofEffect (1 : Matrix (Fin A) (Fin A) ℂ)
      PosSemidef.one le_rfl))
  calc (Matrix.trace ρ).re
      = (∑ i, effectPairingQuad (doubleDualEffectPairing F)
          (Pi.single i (1 : ℂ))).re := by rw [htr]
    _ = (effectExpectation (doubleDualEffectPairing F) 1 PosSemidef.one le_rfl).re := by
          simp_rw [hQ]; exact congrArg Complex.re hsum
    _ ≤ 1 := by simpa [effectExpectation] using hborn.2.2


theorem effectPairingPolar_basis_expansion {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (v w : Fin A → ℂ) :
    effectPairingPolar (doubleDualEffectPairing F) v w =
      ∑ i : Fin A, ∑ j : Fin A,
        star (v i) * effectPairingPolar (doubleDualEffectPairing F)
          (Pi.single i (1 : ℂ)) (Pi.single j (1 : ℂ)) * w j := by
  have step1 : effectPairingPolar (doubleDualEffectPairing F) v w =
      ∑ i : Fin A, star (v i) *
        effectPairingPolar (doubleDualEffectPairing F) (Pi.single i (1 : ℂ)) w := by
    conv_lhs => rw [eq_sum_single v]
    exact effectPairingPolar_sum_left F Finset.univ v w
  have step2 : effectPairingPolar (doubleDualEffectPairing F) v w =
      ∑ i : Fin A, star (v i) *
        (∑ j : Fin A, w j *
          effectPairingPolar (doubleDualEffectPairing F)
            (Pi.single i (1 : ℂ)) (Pi.single j (1 : ℂ))) := by
    rw [step1]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [eq_sum_single w]
    rw [effectPairingPolar_sum_right]
  rw [step2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, mul_right_comm (star (v i)) (w j)]

theorem density_quad_eq {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (v : Fin A → ℂ) :
    star v ⬝ᵥ (densityFromEffectPairing (doubleDualEffectPairing F)) *ᵥ v =
      effectPairingQuad (doubleDualEffectPairing F) v := by
  set ρ := densityFromEffectPairing (doubleDualEffectPairing F)
  have hdot : star v ⬝ᵥ ρ *ᵥ v =
      ∑ i : Fin A, ∑ j : Fin A, star (v i) * ρ i j * v j := by
    simp only [dotProduct, mulVec, Pi.star_apply]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _) ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc]
  rw [hdot, ← effectPairingPolar_self (doubleDualEffectPairing F) v,
    effectPairingPolar_basis_expansion]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [ρ, densityFromEffectPairing]

theorem densityFromDoubleDual_isHermitian {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier) :
    (densityFromEffectPairing (doubleDualEffectPairing F)).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, densityFromEffectPairing]
  exact effectPairingPolar_conj_symm F (Pi.single i (1 : ℂ)) (Pi.single j (1 : ℂ))

theorem densityFromDoubleDual_posSemidef {A : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier) :
    (densityFromEffectPairing (doubleDualEffectPairing F)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (densityFromDoubleDual_isHermitian F) ?_
  intro v
  have hq := effectPairingQuad_nonneg (doubleDualEffectPairing F) v
  rw [density_quad_eq F v]
  exact Complex.nonneg_iff.mpr ⟨hq.1, hq.2.symm⟩


/-! ### Spectral expansion for Born match -/

theorem diagonal_eq_sum_single {n : Type*} [Fintype n] [DecidableEq n] (f : n → ℂ) :
    diagonal f = ∑ i : n, f i • Matrix.single i i (1 : ℂ) := by
  ext a b
  classical
  simp only [diagonal, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.single, Matrix.of_apply]
  refine Eq.symm ?_
  by_cases hab : a = b
  · rw [if_pos hab]
    cases hab
    have hterm : ∀ i, f i * (if i = a ∧ i = a then (1 : ℂ) else 0) =
        if i = a then f a else 0 := by
      intro i; split_ifs <;> simp_all
    simp_rw [hterm]
    simpa using Finset.sum_ite_eq' (s := Finset.univ) (a := a) (f := fun _ => f a)
  · rw [if_neg hab]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ¬(i = a ∧ i = b) := fun ⟨ha, hb⟩ => hab (ha.symm.trans hb)
    simp [this]

theorem entry_mul_single {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (i : n) (a j : n) :
    (U * Matrix.single i i (1 : ℂ)) a j = if j = i then U a i else 0 := by
  classical
  simp only [Matrix.mul_apply, Matrix.single, Matrix.of_apply]
  split_ifs with hj
  · have hif : ∀ k, (i = k ∧ i = j) ↔ k = i := by
      intro k; constructor
      · intro ⟨h1, _⟩; exact h1.symm
      · intro hk; exact ⟨hk.symm, hj.symm⟩
    simp_rw [hif]
    have hterm : ∀ k, U a k * (if k = i then (1 : ℂ) else 0) =
        if k = i then U a i else 0 := by
      intro k; split_ifs <;> simp_all
    simp_rw [hterm]
    simpa using Finset.sum_ite_eq' (s := Finset.univ) (a := i) (f := fun _ => U a i)
  · refine Finset.sum_eq_zero fun k _ => ?_
    have : ¬(i = k ∧ i = j) := fun ⟨_, h2⟩ => hj h2.symm
    simp [this]

theorem mul_single_mul_star {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (i : n) :
    U * Matrix.single i i (1 : ℂ) * star U =
      Matrix.vecMulVec (fun a => U a i) (fun b => star (U b i)) := by
  classical
  set M := U * Matrix.single i i (1 : ℂ)
  have hM (a j : n) : M a j = if j = i then U a i else 0 := entry_mul_single U i a j
  ext a b
  simp only [Matrix.vecMulVec_apply, Matrix.mul_apply, star_apply]
  have hterm : ∀ j, M a j * star (U b j) =
      if j = i then U a i * star (U b i) else 0 := by
    intro j
    rw [hM]
    split_ifs with hj <;> simp [hj]
  simp_rw [hterm]
  simpa using Finset.sum_ite_eq' (s := Finset.univ) (a := i)
    (f := fun _ => U a i * star (U b i))

theorem isHermitian_eq_sum_eigenprojectors {n : Type*} [Fintype n] [DecidableEq n]
    (E : Matrix n n ℂ) (hE : E.IsHermitian) :
    E = ∑ i : n, (hE.eigenvalues i : ℂ) •
      Matrix.vecMulVec
        (fun a => (↑hE.eigenvectorUnitary : Matrix n n ℂ) a i)
        (fun b => star ((↑hE.eigenvectorUnitary : Matrix n n ℂ) b i)) := by
  set U : Matrix n n ℂ := ↑hE.eigenvectorUnitary
  have hEUD : E = U * diagonal (RCLike.ofReal ∘ hE.eigenvalues) * star U := by
    simpa [U, Unitary.conjStarAlgAut_apply] using hE.spectral_theorem
  have heq : (RCLike.ofReal ∘ hE.eigenvalues : n → ℂ) = fun i => (hE.eigenvalues i : ℂ) := by
    ext i; simp [Function.comp]
  have hD : diagonal (RCLike.ofReal ∘ hE.eigenvalues) =
      ∑ i : n, (hE.eigenvalues i : ℂ) • Matrix.single i i (1 : ℂ) := by
    rw [heq]; exact diagonal_eq_sum_single _
  calc E
      = U * diagonal (RCLike.ofReal ∘ hE.eigenvalues) * star U := hEUD
    _ = U * (∑ i : n, (hE.eigenvalues i : ℂ) • Matrix.single i i (1 : ℂ)) * star U := by
          rw [hD]
    _ = ∑ i : n, (U * ((hE.eigenvalues i : ℂ) • Matrix.single i i (1 : ℂ))) * star U := by
          rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i : n, (((hE.eigenvalues i : ℂ) • (U * Matrix.single i i (1 : ℂ))) * star U) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.mul_smul]
    _ = ∑ i : n, (hE.eigenvalues i : ℂ) • ((U * Matrix.single i i (1 : ℂ)) * star U) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.smul_mul]
    _ = ∑ i : n, (hE.eigenvalues i : ℂ) • (U * Matrix.single i i (1 : ℂ) * star U) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [Matrix.mul_assoc]
    _ = ∑ i : n, (hE.eigenvalues i : ℂ) •
          Matrix.vecMulVec (fun a => U a i) (fun b => star (U b i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_single_mul_star]

theorem eigenvectorUnitary_col_normSq {n : Type*} [Fintype n] [DecidableEq n]
    (E : Matrix n n ℂ) (hE : E.IsHermitian) (i : n) :
    star (fun a => (↑hE.eigenvectorUnitary : Matrix n n ℂ) a i) ⬝ᵥ
      (fun a => (↑hE.eigenvectorUnitary : Matrix n n ℂ) a i) = 1 := by
  have hstar : star (↑hE.eigenvectorUnitary : Matrix n n ℂ) *
      (↑hE.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
    simpa using (Unitary.coe_star_mul_self hE.eigenvectorUnitary)
  have hii : (star (↑hE.eigenvectorUnitary : Matrix n n ℂ) *
      (↑hE.eigenvectorUnitary : Matrix n n ℂ)) i i = 1 := by
    simp [hstar]
  simpa [Matrix.mul_apply, star_apply, dotProduct] using hii

/-! ### Born match and n=1 preparation -/

/-- On every Loewner effect, the double-dual Born pairing matches the density
recovered by polarization: `β(E) = Tr(E ρ)`. -/
theorem born_match_density {A : ℕ} (_hA : 0 < A)
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier)
    (E : Matrix (Fin A) (Fin A) ℂ) (hpsd : E.PosSemidef) (hle : E ≤ 1) :
    effectExpectation (doubleDualEffectPairing F) E hpsd hle =
      Matrix.trace (E * densityFromEffectPairing (doubleDualEffectPairing F)) := by
  classical
  set ρ := densityFromEffectPairing (doubleDualEffectPairing F)
  have hHerm := hpsd.isHermitian
  set U : Matrix (Fin A) (Fin A) ℂ := ↑hHerm.eigenvectorUnitary
  set u : Fin A → (Fin A → ℂ) := fun i a => U a i
  set P : Fin A → Matrix (Fin A) (Fin A) ℂ := fun i =>
    Matrix.vecMulVec (fun a => U a i) (fun b => star (U b i))
  have hPu (i : Fin A) : P i = Matrix.vecMulVec (u i) (star (u i)) := by
    simp only [P, u]; congr 1
  have hPpsd : ∀ i, (P i).PosSemidef := fun i => by
    rw [hPu]; exact Matrix.posSemidef_vecMulVec_self_star (u i)
  have hLam0 : ∀ i, 0 ≤ hHerm.eigenvalues i :=
    fun i => PosSemidef.eigenvalues_nonneg hpsd i
  have hexp : E = ∑ i : Fin A, (hHerm.eigenvalues i : ℂ) • P i := by
    simpa [P, U] using isHermitian_eq_sum_eigenprojectors E hHerm
  have hexpR : E = ∑ i : Fin A, (hHerm.eigenvalues i : ℝ) • P i := by
    convert hexp using 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ext a b
    simp [Matrix.smul_apply, smul_eq_mul]
  have hExtβ : effectExpectationExt F E hpsd =
      effectExpectation (doubleDualEffectPairing F) E hpsd hle :=
    effectExpectationExt_of_le_one F E hpsd hle
  have hExtP (i : Fin A) :
      effectExpectationExt F (P i) (hPpsd i) =
        Matrix.trace (P i * ρ) := by
    have hq := effectPairingQuad_eq_ext F (u i)
    have hd := density_quad_eq F (u i)
    have htr := trace_vecMulVec_mul ρ (u i)
    have hL : effectExpectationExt F (P i) (hPpsd i) =
        effectExpectationExt F (Matrix.vecMulVec (u i) (star (u i)))
          (Matrix.posSemidef_vecMulVec_self_star (u i)) := by
      simp only [effectExpectationExt, hPu]
    have hR : Matrix.trace (P i * ρ) =
        Matrix.trace (Matrix.vecMulVec (u i) (star (u i)) * ρ) := by
      rw [hPu]
    rw [hL, hR]
    calc effectExpectationExt F (Matrix.vecMulVec (u i) (star (u i))) _
          = effectPairingQuad (doubleDualEffectPairing F) (u i) := hq.symm
      _ = star (u i) ⬝ᵥ ρ *ᵥ u i := hd.symm
      _ = Matrix.trace (Matrix.vecMulVec (u i) (star (u i)) * ρ) := htr.symm
  have hExtLamP (i : Fin A) :
      effectExpectationExt F ((hHerm.eigenvalues i : ℝ) • P i)
          ((hPpsd i).smul (hLam0 i)) =
        (hHerm.eigenvalues i : ℂ) * effectExpectationExt F (P i) (hPpsd i) :=
    effectExpectationExt_smul F (hHerm.eigenvalues i) (hLam0 i) (P i) (hPpsd i)
  have hExtSum : effectExpectationExt F E hpsd =
      ∑ i : Fin A, effectExpectationExt F ((hHerm.eigenvalues i : ℝ) • P i)
        ((hPpsd i).smul (hLam0 i)) := by
    have hadd : ∀ (s : Finset (Fin A)),
        effectExpectationExt F
            (∑ i ∈ s, (hHerm.eigenvalues i : ℝ) • P i)
            (sum_psd_matrix s (fun i => (hHerm.eigenvalues i : ℝ) • P i)
              (fun i _ => (hPpsd i).smul (hLam0 i))) =
          ∑ i ∈ s, effectExpectationExt F ((hHerm.eigenvalues i : ℝ) • P i)
            ((hPpsd i).smul (hLam0 i)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        have h0 : effectExpectationExt F (0 : Matrix (Fin A) (Fin A) ℂ)
            PosSemidef.zero = 0 := by
          simp only [effectExpectationExt, Matrix.trace_zero, Complex.zero_re,
            max_eq_right zero_le_one]
          have hz : ((1⁻¹ : ℝ) • (0 : Matrix (Fin A) (Fin A) ℂ)) = 0 := by
            ext; simp
          simpa [effectExpectation, hz] using
            effectExpectation_zero_doubleDual (A := A) F
        convert h0 <;> simp
      | insert i s hs ih =>
        simp only [Finset.sum_insert hs]
        have hE := (hPpsd i).smul (hLam0 i)
        have hS := sum_psd_matrix s (fun j => (hHerm.eigenvalues j : ℝ) • P j)
          (fun j _ => (hPpsd j).smul (hLam0 j))
        rw [effectExpectationExt_add F _ _ hE hS, ih]
    have h := hadd Finset.univ
    have hL : effectExpectationExt F
        (∑ i : Fin A, (hHerm.eigenvalues i : ℝ) • P i)
        (sum_psd_matrix Finset.univ (fun i => (hHerm.eigenvalues i : ℝ) • P i)
          (fun i _ => (hPpsd i).smul (hLam0 i))) =
      effectExpectationExt F E hpsd := by
      simp only [effectExpectationExt, ← hexpR]
    exact hL ▸ h
  calc effectExpectation (doubleDualEffectPairing F) E hpsd hle
      = effectExpectationExt F E hpsd := hExtβ.symm
    _ = ∑ i, effectExpectationExt F ((hHerm.eigenvalues i : ℝ) • P i)
          ((hPpsd i).smul (hLam0 i)) := hExtSum
    _ = ∑ i, (hHerm.eigenvalues i : ℂ) *
          effectExpectationExt F (P i) (hPpsd i) := by
          refine Finset.sum_congr rfl fun i _ => hExtLamP i
    _ = ∑ i, (hHerm.eigenvalues i : ℂ) * Matrix.trace (P i * ρ) := by
          refine Finset.sum_congr rfl fun i _ => by rw [hExtP]
    _ = ∑ i, Matrix.trace (((hHerm.eigenvalues i : ℂ) • P i) * ρ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hsm : ((hHerm.eigenvalues i : ℂ) • P i) * ρ =
              (hHerm.eigenvalues i : ℂ) • (P i * ρ) := Matrix.smul_mul _ _ _
          rw [hsm, Matrix.trace_smul, smul_eq_mul]
    _ = Matrix.trace ((∑ i, (hHerm.eigenvalues i : ℂ) • P i) * ρ) := by
          simp [Finset.sum_mul, Matrix.trace_sum]
    _ = Matrix.trace (E * ρ) := by rw [← hexp]

/-- From Born match: a double-dual fiber at `n = 1` yields a preparation `Φ`
with `e ∘ Φ = doubleDualEffectPairing F e` for every effect `e`. -/
theorem exists_preparation_of_doubleDual {A : ℕ} (hA : 0 < A)
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj 1).Carrier) :
    ∃ Φ : Superoperator 1 A,
      ∀ e : Superoperator A 1,
        effectPrecompose Φ e = doubleDualEffectPairing F e := by
  set ρ := densityFromEffectPairing (doubleDualEffectPairing F)
  refine exists_superoperator_of_effect_pairing
    (doubleDualEffectPairing F) ρ
    (densityFromDoubleDual_posSemidef F)
    (trace_density_le_one F) ?_
  intro E hpsd hle
  simpa [effectExpectation] using born_match_density hA F E hpsd hle

/-! ### n=1 unit surjectivity (pairing lift) -/

theorem effectPack_surjective (A : ℕ) :
    Function.Surjective (effectPack A) := by
  intro b
  set χ : Superoperator (1 * A) 1 :=
    b.app (Superoperator.identity 1) (Superoperator.identity A)
  refine ⟨Superoperator.comp χ (Superoperator.tensorLeftUnitorInv A), ?_⟩
  have hiso :
      (dayInternalHomRepresentableIso A dayTensorUnit).inv.app 1
        ((dayInternalHomRepresentableIso A dayTensorUnit).hom.app 1 b) = b := by
    simpa [Hom.comp_app, Hom.id_app] using
      congrArg (fun f : Hom _ _ => f.app 1 b)
        (dayInternalHomRepresentableIso A dayTensorUnit).inv_hom
  have hhom : (dayInternalHomRepresentableIso A dayTensorUnit).hom.app 1 b = χ := rfl
  have hb : dualFiberBilinear A 1 χ = b := by
    simpa [dualFiberBilinear, hhom] using hiso
  have hχ : Superoperator.comp
      (Superoperator.comp χ (Superoperator.tensorLeftUnitorInv A))
      (Superoperator.tensorLeftUnitor A) = χ := by
    rw [← Superoperator.comp_assoc, Superoperator.tensorLeftUnitor_inv_hom,
      Superoperator.comp_identity]
  calc effectPack A (Superoperator.comp χ (Superoperator.tensorLeftUnitorInv A))
      = dualFiberBilinear A 1
          (Superoperator.comp
            (Superoperator.comp χ (Superoperator.tensorLeftUnitorInv A))
            (Superoperator.tensorLeftUnitor A)) := rfl
    _ = dualFiberBilinear A 1 χ := by rw [hχ]
    _ = b := hb

theorem dualFiberBilinear_surjective (A q : ℕ) :
    Function.Surjective (dualFiberBilinear A q) := by
  intro b
  set χ : Superoperator (q * A) 1 :=
    b.app (Superoperator.identity q) (Superoperator.identity A)
  refine ⟨χ, ?_⟩
  have hiso :
      (dayInternalHomRepresentableIso A dayTensorUnit).inv.app q
        ((dayInternalHomRepresentableIso A dayTensorUnit).hom.app q b) = b := by
    simpa [Hom.comp_app, Hom.id_app] using
      congrArg (fun f : Hom _ _ => f.app q b)
        (dayInternalHomRepresentableIso A dayTensorUnit).inv_hom
  have hhom : (dayInternalHomRepresentableIso A dayTensorUnit).hom.app q b = χ := rfl
  simpa [dualFiberBilinear, hhom] using hiso

theorem doubleDual_app_identity {A n p q : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (r : Superoperator p n)
    (b : ((DayNegation.neg (representable A)).obj q).Carrier) :
    F.app r b =
      dayTensorUnit.act (F.app (Superoperator.identity n) b)
        (Superoperator.tensor r (Superoperator.identity q)) := by
  have hF := F.naturality (Superoperator.identity n) b r (Superoperator.identity q)
  simpa [Superoperator.identity_comp,
    (DayNegation.neg (representable A)).act_id] using hF

theorem doubleDual_eq_of_app_id {A n : ℕ}
    (F G : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (h : ∀ q (b : ((DayNegation.neg (representable A)).obj q).Carrier),
      F.app (Superoperator.identity n) b = G.app (Superoperator.identity n) b) :
    F = G := by
  apply Bilinear.ext
  intro p q r b
  rw [doubleDual_app_identity F r b, doubleDual_app_identity G r b, h]

theorem pairing_eq_imp_app_fiber_one {A n : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (Φ : Superoperator n A)
    (hα : ∀ e : Superoperator A 1,
      doubleDualEffectPairing F e = effectPrecompose Φ e)
    (b : ((DayNegation.neg (representable A)).obj 1).Carrier) :
    F.app (Superoperator.identity n) b =
      ((DayNegation.unit (representable A)).app n Φ).app
        (Superoperator.identity n) b := by
  obtain ⟨e, rfl⟩ := effectPack_surjective A b
  exact pairing_eq_imp_app_effectPack F Φ hα e

theorem doubleDual_app_act {A n q q' : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (b : ((DayNegation.neg (representable A)).obj q).Carrier)
    (g : Superoperator q' q) :
    F.app (Superoperator.identity n)
        ((DayNegation.neg (representable A)).act b g) =
      dayTensorUnit.act (F.app (Superoperator.identity n) b)
        (Superoperator.tensor (Superoperator.identity n) g) := by
  have hF := F.naturality (Superoperator.identity n) b
    (Superoperator.identity n) g
  simpa [Superoperator.comp_identity] using hF

theorem superoperator_to_one_eq_of_comp_prep {k : ℕ}
    {ψ₁ ψ₂ : Superoperator k 1}
    (h : ∀ σ : Superoperator 1 k,
      Superoperator.comp ψ₁ σ = Superoperator.comp ψ₂ σ) :
    ψ₁ = ψ₂ := by
  have heff : ψ₁.cp.effect = ψ₂.cp.effect := by
    refine matrix_eq_of_forall_effect_trace ?_
    intro E hpsd _hle
    set c : ℝ := max (Matrix.trace E).re 1
    have hc_pos : (0 : ℝ) < c :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
    have hc0 : (0 : ℝ) ≤ c⁻¹ := inv_nonneg.mpr (le_of_lt hc_pos)
    set ρ : Matrix (Fin k) (Fin k) ℂ := (c⁻¹ : ℝ) • E
    have hρpsd : ρ.PosSemidef := hpsd.smul hc0
    have hρtr : (Matrix.trace ρ).re ≤ 1 := by
      have htre : (Matrix.trace ρ).re = c⁻¹ * (Matrix.trace E).re := by
        simp only [ρ, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
      rw [htre]
      calc c⁻¹ * (Matrix.trace E).re
          ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left (le_max_left _ _) hc0
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hc_pos)
    set σ := preparationOfDensity ρ hρpsd hρtr
    have h1 : bornScalar (Superoperator.comp ψ₁ σ) =
        Matrix.trace (ψ₁.cp.effect * ρ) := by
      calc bornScalar (Superoperator.comp ψ₁ σ)
          = Matrix.trace (ψ₁.cp.effect * σ.cp.applyMat 1) := by
              simpa [effectPrecompose] using bornScalar_effectPrecompose σ ψ₁
        _ = Matrix.trace (ψ₁.cp.effect * ρ) := by
              rw [preparationOfDensity_applyMat_one]
    have h2 : bornScalar (Superoperator.comp ψ₂ σ) =
        Matrix.trace (ψ₂.cp.effect * ρ) := by
      calc bornScalar (Superoperator.comp ψ₂ σ)
          = Matrix.trace (ψ₂.cp.effect * σ.cp.applyMat 1) := by
              simpa [effectPrecompose] using bornScalar_effectPrecompose σ ψ₂
        _ = Matrix.trace (ψ₂.cp.effect * ρ) := by
              rw [preparationOfDensity_applyMat_one]
    have hρtrace : Matrix.trace (ψ₁.cp.effect * ρ) =
        Matrix.trace (ψ₂.cp.effect * ρ) := by
      rw [← h1, ← h2, h]
    have hE : E = (c : ℝ) • ρ := by
      simp only [ρ]
      ext i j
      simp [Matrix.smul_apply]
      field_simp [ne_of_gt hc_pos]
    have hcyc (X Y : Matrix (Fin k) (Fin k) ℂ) :
        Matrix.trace (X * Y) = Matrix.trace (Y * X) := Matrix.trace_mul_comm _ _
    calc Matrix.trace (E * ψ₁.cp.effect)
        = Matrix.trace (((c : ℝ) • ρ) * ψ₁.cp.effect) := by rw [hE]
      _ = (c : ℂ) * Matrix.trace (ρ * ψ₁.cp.effect) := by
            simp [Matrix.trace_smul, Complex.real_smul]
      _ = (c : ℂ) * Matrix.trace (ψ₁.cp.effect * ρ) := by rw [hcyc]
      _ = (c : ℂ) * Matrix.trace (ψ₂.cp.effect * ρ) := by rw [hρtrace]
      _ = (c : ℂ) * Matrix.trace (ρ * ψ₂.cp.effect) := by rw [hcyc]
      _ = Matrix.trace (((c : ℝ) • ρ) * ψ₂.cp.effect) := by
            simp [Matrix.trace_smul, Complex.real_smul]
      _ = Matrix.trace (E * ψ₂.cp.effect) := by rw [← hE]
  apply Superoperator.ext
  apply CPMap.ext_apply
  intro ρ
  have htr : Matrix.trace (ψ₁.cp.applyMat ρ) = Matrix.trace (ψ₂.cp.applyMat ρ) := by
    rw [CPMap.trace_applyMat_eq_effect, CPMap.trace_applyMat_eq_effect, heff]
  ext i j
  fin_cases i; fin_cases j
  simpa [Matrix.trace, Fin.default_eq_zero] using htr

theorem superoperator_one_mul_eq_of_tensor_prep {q : ℕ}
    {ψ₁ ψ₂ : Superoperator (1 * q) 1}
    (h : ∀ σ : Superoperator 1 q,
      dayTensorUnit.act ψ₁
          (Superoperator.tensor (Superoperator.identity 1) σ) =
        dayTensorUnit.act ψ₂
          (Superoperator.tensor (Superoperator.identity 1) σ)) :
    ψ₁ = ψ₂ := by
  have h' : ∀ σ : Superoperator 1 q,
      Superoperator.comp ψ₁
          (Superoperator.tensor (Superoperator.identity 1) σ) =
        Superoperator.comp ψ₂
          (Superoperator.tensor (Superoperator.identity 1) σ) := by
    intro σ
    simpa [representable_act] using h σ
  set φ₁ : Superoperator q 1 :=
    Superoperator.comp ψ₁ (Superoperator.tensorLeftUnitorInv q)
  set φ₂ : Superoperator q 1 :=
    Superoperator.comp ψ₂ (Superoperator.tensorLeftUnitorInv q)
  have hφ : ∀ σ : Superoperator 1 q, Superoperator.comp φ₁ σ = Superoperator.comp φ₂ σ := by
    intro σ
    have hnat := Superoperator.tensorLeftUnitorInv_naturality σ
    calc Superoperator.comp φ₁ σ
        = Superoperator.comp ψ₁
            (Superoperator.comp (Superoperator.tensorLeftUnitorInv q) σ) := by
              simp only [φ₁, Superoperator.comp_assoc]
      _ = Superoperator.comp ψ₁
            (Superoperator.comp
              (Superoperator.tensor (Superoperator.identity 1) σ)
              (Superoperator.tensorLeftUnitorInv 1)) := by
              rw [← hnat]
      _ = Superoperator.comp
            (Superoperator.comp ψ₁
              (Superoperator.tensor (Superoperator.identity 1) σ))
            (Superoperator.tensorLeftUnitorInv 1) := Superoperator.comp_assoc _ _ _
      _ = Superoperator.comp
            (Superoperator.comp ψ₂
              (Superoperator.tensor (Superoperator.identity 1) σ))
            (Superoperator.tensorLeftUnitorInv 1) := by rw [h']
      _ = Superoperator.comp ψ₂
            (Superoperator.comp
              (Superoperator.tensor (Superoperator.identity 1) σ)
              (Superoperator.tensorLeftUnitorInv 1)) := (Superoperator.comp_assoc _ _ _).symm
      _ = Superoperator.comp ψ₂
            (Superoperator.comp (Superoperator.tensorLeftUnitorInv q) σ) := by
              rw [hnat]
      _ = Superoperator.comp φ₂ σ := by simp only [φ₂, Superoperator.comp_assoc]
  have hφeq : φ₁ = φ₂ := superoperator_to_one_eq_of_comp_prep hφ
  have hrec (ψ : Superoperator (1 * q) 1) :
      Superoperator.comp
          (Superoperator.comp ψ (Superoperator.tensorLeftUnitorInv q))
          (Superoperator.tensorLeftUnitor q) = ψ := by
    rw [← Superoperator.comp_assoc, Superoperator.tensorLeftUnitor_inv_hom,
      Superoperator.comp_identity]
  calc ψ₁ = Superoperator.comp φ₁ (Superoperator.tensorLeftUnitor q) := (hrec ψ₁).symm
    _ = Superoperator.comp φ₂ (Superoperator.tensorLeftUnitor q) := by rw [hφeq]
    _ = ψ₂ := hrec ψ₂

theorem choi_tensor_id_left {n q : ℕ} (σ : CPMap 1 q)
    (u v : Fin n) (i j : Fin q) (b a : Fin n) (c d : Fin 1) :
    (CPMap.tensor (CPMap.identity n) σ).choi
        (finProdFinEquiv (u, i), finProdFinEquiv (b, c))
        (finProdFinEquiv (v, j), finProdFinEquiv (a, d)) =
      (CPMap.identity n).choi (u, b) (v, a) * σ.choi (i, c) (j, d) := by
  rw [CPMap.choi_tensor]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  have h1 : (CPMap.choiTensorEquiv n n 1 q).symm
      (finProdFinEquiv (u, i), finProdFinEquiv (b, c)) = ((u, b), (i, c)) := by
    dsimp [CPMap.choiTensorEquiv]; simp only [Equiv.symm_apply_apply]
  have h2 : (CPMap.choiTensorEquiv n n 1 q).symm
      (finProdFinEquiv (v, j), finProdFinEquiv (a, d)) = ((v, a), (j, d)) := by
    dsimp [CPMap.choiTensorEquiv]; simp only [Equiv.symm_apply_apply]
  rw [h1, h2]; simp

theorem applyMat_one_eq_choi {q : ℕ} (σ : CPMap 1 q) (i j : Fin q) :
    σ.applyMat (1 : Matrix (Fin 1) (Fin 1) ℂ) i j = σ.choi (i, 0) (j, 0) := by
  have h := KrausFamily.applyMat_apply (CPMap.toKraus σ) 1 i j
  change KrausFamily.applyMat (CPMap.toKraus σ) 1 i j = σ.choi (i, 0) (j, 0)
  rw [h, CPMap.choi_toKraus]
  simp [Matrix.one_apply]

theorem effect_comp_id_tensor_prep {n q : ℕ}
    (ψ : Superoperator (n * q) 1) (σ : Superoperator 1 q)
    (a b : Fin n) :
    (Superoperator.comp ψ
        (Superoperator.tensor (Superoperator.identity n) σ)).cp.effect
      (finProdFinEquiv (a, (0 : Fin 1))) (finProdFinEquiv (b, (0 : Fin 1))) =
      ∑ i : Fin q, ∑ j : Fin q,
        ψ.cp.effect (finProdFinEquiv (a, j)) (finProdFinEquiv (b, i)) *
          σ.cp.applyMat (1 : Matrix (Fin 1) (Fin 1) ℂ) i j := by
  classical
  let e : Fin n × Fin q ≃ Fin (n * q) := finProdFinEquiv
  let e1 : Fin n × Fin 1 ≃ Fin (n * 1) := finProdFinEquiv
  have hcp :
      (Superoperator.comp ψ
          (Superoperator.tensor (Superoperator.identity n) σ)).cp =
        CPMap.comp ψ.cp (CPMap.tensor (CPMap.identity n) σ.cp) := by
    rw [Superoperator.cp_comp, Superoperator.cp_tensor]; rfl
  rw [hcp, effect_comp_effect]
  have hS :
      (∑ u : Fin (n * q), ∑ v : Fin (n * q),
        ψ.cp.effect v u *
          (CPMap.tensor (CPMap.identity n) σ.cp).choi
            (u, e1 (b, 0)) (v, e1 (a, 0))) =
      ∑ x : Fin n, ∑ i : Fin q, ∑ y : Fin n, ∑ j : Fin q,
        ψ.cp.effect (e (y, j)) (e (x, i)) *
          (CPMap.tensor (CPMap.identity n) σ.cp).choi
            (e (x, i), e1 (b, 0)) (e (y, j), e1 (a, 0)) := by
    rw [← Equiv.sum_comp e (fun u => ∑ v : Fin (n * q),
      ψ.cp.effect v u *
        (CPMap.tensor (CPMap.identity n) σ.cp).choi
          (u, e1 (b, 0)) (v, e1 (a, 0)))]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp e (fun v =>
      ψ.cp.effect v (e (x, i)) *
        (CPMap.tensor (CPMap.identity n) σ.cp).choi
          (e (x, i), e1 (b, 0)) (v, e1 (a, 0)))]
    rw [Fintype.sum_prod_type]
  rw [hS]
  have hten (x y : Fin n) (i j : Fin q) :
      (CPMap.tensor (CPMap.identity n) σ.cp).choi
          (e (x, i), e1 (b, 0)) (e (y, j), e1 (a, 0)) =
        (CPMap.identity n).choi (x, b) (y, a) * σ.cp.choi (i, 0) (j, 0) :=
    choi_tensor_id_left σ.cp x y i j b a 0 0
  simp_rw [hten, choi_identity_pair]
  rw [Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single a]
    · simp only [↓reduceIte, one_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact (congrArg (fun z => ψ.cp.effect (e (a, j)) (e (b, i)) * z)
        (applyMat_one_eq_choi σ.cp i j)).symm
    · intro y _ hy
      simp only [hy, ite_false, mul_zero, zero_mul, Finset.sum_const_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · intro x _ hx
    simp only [hx, ite_false, zero_mul, mul_zero, Finset.sum_const_zero]
  · intro h; exact (h (Finset.mem_univ _)).elim

theorem matrix_eq_of_forall_density_trace {k : ℕ}
    {X Y : Matrix (Fin k) (Fin k) ℂ}
    (h : ∀ (ρ : Matrix (Fin k) (Fin k) ℂ),
      ρ.PosSemidef → (Matrix.trace ρ).re ≤ 1 →
        Matrix.trace (ρ * X) = Matrix.trace (ρ * Y)) :
    X = Y := by
  refine matrix_eq_of_forall_effect_trace ?_
  intro E hpsd hle
  set c : ℝ := max (Matrix.trace E).re 1
  have hc_pos : (0 : ℝ) < c :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hc0 : (0 : ℝ) ≤ c⁻¹ := inv_nonneg.mpr (le_of_lt hc_pos)
  set ρ : Matrix (Fin k) (Fin k) ℂ := (c⁻¹ : ℝ) • E
  have hρpsd : ρ.PosSemidef := hpsd.smul hc0
  have hρtr : (Matrix.trace ρ).re ≤ 1 := by
    have htre : (Matrix.trace ρ).re = c⁻¹ * (Matrix.trace E).re := by
      simp only [ρ, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    rw [htre]
    calc c⁻¹ * (Matrix.trace E).re
        ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left (le_max_left _ _) hc0
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hc_pos)
  have hρ := h ρ hρpsd hρtr
  have hEρ : E = (c : ℝ) • ρ := by
    simp only [ρ, smul_smul]
    rw [mul_inv_cancel₀ (ne_of_gt hc_pos), one_smul]
  have hXE : Matrix.trace (E * X) = (c : ℂ) * Matrix.trace (ρ * X) := by
    rw [hEρ, Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul]
  have hYE : Matrix.trace (E * Y) = (c : ℂ) * Matrix.trace (ρ * Y) := by
    rw [hEρ, Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul]
  rw [hXE, hYE, hρ]

theorem born_block {n q : ℕ}
    (ψ : Superoperator (n * q) 1) (a b : Fin n)
    (ρ : Matrix (Fin q) (Fin q) ℂ) :
    Matrix.trace (ρ *
      (Matrix.of fun j i : Fin q =>
        ψ.cp.effect (finProdFinEquiv (a, j)) (finProdFinEquiv (b, i)))) =
      ∑ i : Fin q, ∑ j : Fin q,
        ψ.cp.effect (finProdFinEquiv (a, j)) (finProdFinEquiv (b, i)) * ρ i j := by
  simp only [Matrix.trace, diag, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem superoperator_mul_eq_of_tensor_prep {n q : ℕ}
    {ψ₁ ψ₂ : Superoperator (n * q) 1}
    (h : ∀ σ : Superoperator 1 q,
      Superoperator.comp ψ₁
          (Superoperator.tensor (Superoperator.identity n) σ) =
        Superoperator.comp ψ₂
          (Superoperator.tensor (Superoperator.identity n) σ)) :
    ψ₁ = ψ₂ := by
  have heff : ψ₁.cp.effect = ψ₂.cp.effect := by
    ext p r
    set p' := finProdFinEquiv.symm p
    set r' := finProdFinEquiv.symm r
    have hp : finProdFinEquiv p' = p := Equiv.apply_symm_apply _ _
    have hr : finProdFinEquiv r' = r := Equiv.apply_symm_apply _ _
    set a : Fin n := p'.1
    set b : Fin n := r'.1
    set M1 : Matrix (Fin q) (Fin q) ℂ :=
      Matrix.of fun j i =>
        ψ₁.cp.effect (finProdFinEquiv (a, j)) (finProdFinEquiv (b, i))
    set M2 : Matrix (Fin q) (Fin q) ℂ :=
      Matrix.of fun j i =>
        ψ₂.cp.effect (finProdFinEquiv (a, j)) (finProdFinEquiv (b, i))
    have hM : M1 = M2 := by
      refine matrix_eq_of_forall_density_trace (fun ρ hpsd htr => ?_)
      set σ := preparationOfDensity ρ hpsd htr
      have hcomp := congrArg (fun Φ : Superoperator (n * 1) 1 =>
        Φ.cp.effect (finProdFinEquiv (a, (0 : Fin 1)))
          (finProdFinEquiv (b, (0 : Fin 1)))) (h σ)
      have h1 := effect_comp_id_tensor_prep ψ₁ σ a b
      have h2 := effect_comp_id_tensor_prep ψ₂ σ a b
      have happ1 : σ.cp.applyMat (1 : Matrix (Fin 1) (Fin 1) ℂ) = ρ :=
        preparationOfDensity_applyMat_one ρ hpsd htr
      calc Matrix.trace (ρ * M1)
          = ∑ i : Fin q, ∑ j : Fin q,
              ψ₁.cp.effect (finProdFinEquiv (a, j)) (finProdFinEquiv (b, i)) *
                ρ i j := by simpa [M1] using born_block ψ₁ a b ρ
        _ = ∑ i : Fin q, ∑ j : Fin q,
              ψ₁.cp.effect (finProdFinEquiv (a, j)) (finProdFinEquiv (b, i)) *
                σ.cp.applyMat (1 : Matrix (Fin 1) (Fin 1) ℂ) i j := by
              simp only [happ1]
        _ = (Superoperator.comp ψ₁
              (Superoperator.tensor (Superoperator.identity n) σ)).cp.effect
                (finProdFinEquiv (a, (0 : Fin 1)))
                (finProdFinEquiv (b, (0 : Fin 1))) := h1.symm
        _ = (Superoperator.comp ψ₂
              (Superoperator.tensor (Superoperator.identity n) σ)).cp.effect
                (finProdFinEquiv (a, (0 : Fin 1)))
                (finProdFinEquiv (b, (0 : Fin 1))) := hcomp
        _ = ∑ i : Fin q, ∑ j : Fin q,
              ψ₂.cp.effect (finProdFinEquiv (a, j)) (finProdFinEquiv (b, i)) *
                σ.cp.applyMat (1 : Matrix (Fin 1) (Fin 1) ℂ) i j := h2
        _ = ∑ i : Fin q, ∑ j : Fin q,
              ψ₂.cp.effect (finProdFinEquiv (a, j)) (finProdFinEquiv (b, i)) *
                ρ i j := by simp only [happ1]
        _ = Matrix.trace (ρ * M2) := by
              simpa [M2] using (born_block ψ₂ a b ρ).symm
    have hentry := congrArg (fun M : Matrix (Fin q) (Fin q) ℂ => M p'.2 r'.2) hM
    simp only [M1, M2, Matrix.of_apply, a, b] at hentry
    rw [← hp, ← hr]
    exact hentry
  apply Superoperator.ext
  apply CPMap.ext_apply
  intro ρ
  have htr : Matrix.trace (ψ₁.cp.applyMat ρ) = Matrix.trace (ψ₂.cp.applyMat ρ) := by
    rw [CPMap.trace_applyMat_eq_effect, CPMap.trace_applyMat_eq_effect, heff]
  ext i j; fin_cases i; fin_cases j
  simpa [Matrix.trace, Fin.default_eq_zero] using htr

theorem pairing_eq_imp_app_id {A n : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (Φ : Superoperator n A)
    (hα : ∀ e : Superoperator A 1,
      doubleDualEffectPairing F e = effectPrecompose Φ e)
    (q : ℕ) (b : ((DayNegation.neg (representable A)).obj q).Carrier) :
    F.app (Superoperator.identity n) b =
      ((DayNegation.unit (representable A)).app n Φ).app
        (Superoperator.identity n) b := by
  obtain ⟨χ, rfl⟩ := dualFiberBilinear_surjective A q b
  set α := F.app (Superoperator.identity n) (dualFiberBilinear A q χ)
  set β := ((DayNegation.unit (representable A)).app n Φ).app
      (Superoperator.identity n) (dualFiberBilinear A q χ)
  have hmul :
      ∀ σ : Superoperator 1 q,
        Superoperator.comp α
            (Superoperator.tensor (Superoperator.identity n) σ) =
          Superoperator.comp β
            (Superoperator.tensor (Superoperator.identity n) σ) := by
    intro σ
    have hact :
        (DayNegation.neg (representable A)).act (dualFiberBilinear A q χ) σ =
          dualFiberBilinear A 1
            (Superoperator.comp χ
              (Superoperator.tensor σ (Superoperator.identity A))) :=
      act_dualFiberBilinear χ σ
    have hFσ := doubleDual_app_act F (dualFiberBilinear A q χ) σ
    have hUσ := doubleDual_app_act
        ((DayNegation.unit (representable A)).app n Φ) (dualFiberBilinear A q χ) σ
    have hfiber :
        F.app (Superoperator.identity n)
            (dualFiberBilinear A 1
              (Superoperator.comp χ
                (Superoperator.tensor σ (Superoperator.identity A)))) =
          ((DayNegation.unit (representable A)).app n Φ).app
            (Superoperator.identity n)
            (dualFiberBilinear A 1
              (Superoperator.comp χ
                (Superoperator.tensor σ (Superoperator.identity A)))) :=
      pairing_eq_imp_app_fiber_one F Φ hα _
    have hL :
        Superoperator.comp α
            (Superoperator.tensor (Superoperator.identity n) σ) =
          F.app (Superoperator.identity n)
            (dualFiberBilinear A 1
              (Superoperator.comp χ
                (Superoperator.tensor σ (Superoperator.identity A)))) := by
      have h := hFσ.symm
      simp only [α, hact] at h
      -- h : dayTensorUnit.act α (id⊗σ) = F.app ...
      exact (dayTensorUnit_act_eq_comp α
        (Superoperator.tensor (Superoperator.identity n) σ)).symm.trans h
    have hR :
        Superoperator.comp β
            (Superoperator.tensor (Superoperator.identity n) σ) =
          ((DayNegation.unit (representable A)).app n Φ).app
            (Superoperator.identity n)
            (dualFiberBilinear A 1
              (Superoperator.comp χ
                (Superoperator.tensor σ (Superoperator.identity A)))) := by
      have h := hUσ.symm
      simp only [β, hact] at h
      exact (dayTensorUnit_act_eq_comp β
        (Superoperator.tensor (Superoperator.identity n) σ)).symm.trans h
    rw [hL, hR, hfiber]
  exact superoperator_mul_eq_of_tensor_prep hmul

theorem doubleDual_eq_unit_of_pairing {A n : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (Φ : Superoperator n A)
    (hα : ∀ e : Superoperator A 1,
      doubleDualEffectPairing F e = effectPrecompose Φ e) :
    F = (DayNegation.unit (representable A)).app n Φ :=
  doubleDual_eq_of_app_id F _ (fun q b => pairing_eq_imp_app_id F Φ hα q b)

theorem representable_unit_surjective_one {A : ℕ} (hA : 0 < A) :
    Function.Surjective ((DayNegation.unit (representable A)).app 1) := by
  intro F
  obtain ⟨Φ, hΦ⟩ := exists_preparation_of_doubleDual hA F
  refine ⟨Φ, ?_⟩
  exact (doubleDual_eq_unit_of_pairing F Φ (fun e => (hΦ e).symm)).symm


/-! ### Column / cup-evaluation naturality (Path A scaffolding) -/

theorem choi_tensor_prep_id {A n : ℕ} (σ : CPMap 1 n)
    (x y : Fin n) (a b : Fin A) (i j : Fin 1) (c d : Fin A) :
    (CPMap.tensor σ (CPMap.identity A)).choi
        (finProdFinEquiv (x, a), finProdFinEquiv (i, c))
        (finProdFinEquiv (y, b), finProdFinEquiv (j, d)) =
      σ.choi (x, i) (y, j) *
        (if a = c then (1 : ℂ) else 0) * (if b = d then 1 else 0) := by
  rw [CPMap.choi_tensor]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  have h1 : (CPMap.choiTensorEquiv 1 n A A).symm
      (finProdFinEquiv (x, a), finProdFinEquiv (i, c)) = ((x, i), (a, c)) := by
    dsimp [CPMap.choiTensorEquiv]; simp only [Equiv.symm_apply_apply]
  have h2 : (CPMap.choiTensorEquiv 1 n A A).symm
      (finProdFinEquiv (y, b), finProdFinEquiv (j, d)) = ((y, j), (b, d)) := by
    dsimp [CPMap.choiTensorEquiv]; simp only [Equiv.symm_apply_apply]
  rw [h1, h2]; simp [choi_identity_pair]

theorem effect_comp_tensor_prep {A n : ℕ}
    (χ : Superoperator (n * A) 1) (σ : Superoperator 1 n)
    (i j : Fin 1) (r s : Fin A) :
    (Superoperator.comp χ
        (Superoperator.tensor σ (Superoperator.identity A))).cp.effect
      (finProdFinEquiv (i, r)) (finProdFinEquiv (j, s)) =
      ∑ x : Fin n, ∑ y : Fin n,
        χ.cp.effect (finProdFinEquiv (y, r)) (finProdFinEquiv (x, s)) *
          σ.cp.choi (x, j) (y, i) := by
  classical
  let e : Fin n × Fin A ≃ Fin (n * A) := finProdFinEquiv
  have hcp :
      (Superoperator.comp χ
          (Superoperator.tensor σ (Superoperator.identity A))).cp =
        CPMap.comp χ.cp (CPMap.tensor σ.cp (CPMap.identity A)) := by
    rw [Superoperator.cp_comp, Superoperator.cp_tensor]; rfl
  rw [hcp, effect_comp_effect]
  have hS' :
      (∑ u : Fin (n * A), ∑ v : Fin (n * A),
        χ.cp.effect v u *
          (CPMap.tensor σ.cp (CPMap.identity A)).choi
            (u, finProdFinEquiv (j, s)) (v, finProdFinEquiv (i, r))) =
      ∑ x : Fin n, ∑ a : Fin A, ∑ y : Fin n, ∑ b : Fin A,
        χ.cp.effect (e (y, b)) (e (x, a)) *
          (CPMap.tensor σ.cp (CPMap.identity A)).choi
            (e (x, a), finProdFinEquiv (j, s))
            (e (y, b), finProdFinEquiv (i, r)) := by
    rw [← Equiv.sum_comp e (fun u => ∑ v : Fin (n * A),
      χ.cp.effect v u *
        (CPMap.tensor σ.cp (CPMap.identity A)).choi
          (u, finProdFinEquiv (j, s)) (v, finProdFinEquiv (i, r)))]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => ?_
    rw [← Equiv.sum_comp e (fun v =>
      χ.cp.effect v (e (x, a)) *
        (CPMap.tensor σ.cp (CPMap.identity A)).choi
          (e (x, a), finProdFinEquiv (j, s)) (v, finProdFinEquiv (i, r)))]
    rw [Fintype.sum_prod_type]
  rw [hS']
  have hten (x y : Fin n) (a b : Fin A) :
      (CPMap.tensor σ.cp (CPMap.identity A)).choi
          (e (x, a), finProdFinEquiv (j, s))
          (e (y, b), finProdFinEquiv (i, r)) =
        σ.cp.choi (x, j) (y, i) *
          (if a = s then (1 : ℂ) else 0) * (if b = r then 1 else 0) :=
    choi_tensor_prep_id σ.cp x y a b j i s r
  simp_rw [hten]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hswap :
      (∑ a : Fin A, ∑ y : Fin n, ∑ b : Fin A,
          χ.cp.effect (e (y, b)) (e (x, a)) *
            (σ.cp.choi (x, j) (y, i) *
              (if a = s then (1 : ℂ) else 0) * (if b = r then 1 else 0))) =
        ∑ y : Fin n, ∑ a : Fin A, ∑ b : Fin A,
          χ.cp.effect (e (y, b)) (e (x, a)) *
            (σ.cp.choi (x, j) (y, i) *
              (if a = s then (1 : ℂ) else 0) * (if b = r then 1 else 0)) :=
    Finset.sum_comm
  rw [hswap]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single s]
  · rw [Finset.sum_eq_single r]
    · simp [e]
    · intro b _ hb; simp [hb]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · intro a _ ha
    simp only [ha, ite_false, mul_zero, zero_mul, Finset.sum_const_zero]
  · intro h; exact (h (Finset.mem_univ _)).elim

theorem recoverCP_comp_tensor {A n : ℕ} (hA : 0 < A)
    (χ : Superoperator (n * A) 1) (σ : Superoperator 1 n) :
    recoverCP hA
        (Superoperator.comp χ
          (Superoperator.tensor σ (Superoperator.identity A))) =
      CPMap.comp (recoverCP hA χ) σ.cp := by
  apply CPMap.ext
  ext p q
  have heff := effect_comp_tensor_prep (A := A) (n := n) χ σ q.2 p.2 q.1 p.1
  calc
    (recoverCP hA
        (Superoperator.comp χ
          (Superoperator.tensor σ (Superoperator.identity A)))).choi p q =
        (A : ℝ) •
          (Superoperator.comp χ
              (Superoperator.tensor σ (Superoperator.identity A))).cp.effect
            (finProdFinEquiv (q.2, q.1)) (finProdFinEquiv (p.2, p.1)) := by
          simp only [recoverCP_choi, cupNameCP, effectAsChoi_apply, Matrix.smul_apply]
    _ = (A : ℝ) •
          ∑ x : Fin n, ∑ y : Fin n,
            χ.cp.effect (finProdFinEquiv (y, q.1)) (finProdFinEquiv (x, p.1)) *
              σ.cp.choi (x, p.2) (y, q.2) := by rw [heff]
    _ = ∑ x : Fin n, ∑ y : Fin n,
          ((A : ℝ) •
              χ.cp.effect (finProdFinEquiv (y, q.1)) (finProdFinEquiv (x, p.1))) *
            σ.cp.choi (x, p.2) (y, q.2) := by
          simp only [Finset.smul_sum, smul_mul_assoc]
    _ = ∑ x : Fin n, ∑ y : Fin n,
          (recoverCP hA χ).choi (p.1, x) (q.1, y) * σ.cp.choi (x, p.2) (y, q.2) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          simp only [recoverCP_choi, cupNameCP, effectAsChoi_apply, Matrix.smul_apply]
    _ = (CPMap.comp (recoverCP hA χ) σ.cp).choi p q := by
          rw [CPMap.choi_comp_apply]

theorem act_app_id_cup {A n : ℕ} (hA : 0 < A)
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (σ : Superoperator 1 n) :
    ((DayNegation.neg (DayNegation.neg (representable A))).act F σ).app
        (Superoperator.identity 1) (normalizedCupProbe A hA) =
      F.app σ (normalizedCupProbe A hA) := by
  change
    (DayInternalHom.precompose σ F).app
        (Superoperator.identity 1) (normalizedCupProbe A hA) =
      F.app σ (normalizedCupProbe A hA)
  simp only [DayInternalHom.precompose, Superoperator.comp_identity]

theorem app_cupProbe_pullback {A n : ℕ} (hA : 0 < A)
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (σ : Superoperator 1 n) :
    F.app σ (normalizedCupProbe A hA) =
      Superoperator.comp
        (F.app (Superoperator.identity n) (normalizedCupProbe A hA))
        (Superoperator.tensor σ (Superoperator.identity A)) := by
  have hF := F.naturality (Superoperator.identity n) (normalizedCupProbe A hA)
    σ (Superoperator.identity A)
  have h1 : (representable n).act (Superoperator.identity n) σ = σ := by
    rw [representable_act, Superoperator.identity_comp]
  have h2 : (DayNegation.neg (representable A)).act (normalizedCupProbe A hA)
      (Superoperator.identity A) = normalizedCupProbe A hA :=
    (DayNegation.neg (representable A)).act_id _
  rw [h1, h2] at hF
  exact hF.trans (representable_act _ _)

theorem evaluationFiber_act {A n : ℕ} (hA : 0 < A)
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (σ : Superoperator 1 n) :
    evaluationFiber hA
        ((DayNegation.neg (DayNegation.neg (representable A))).act F σ) =
      CPMap.comp (evaluationFiber hA F) σ.cp := by
  unfold evaluationFiber
  rw [act_app_id_cup hA F σ, app_cupProbe_pullback hA F σ]
  exact recoverCP_comp_tensor hA _ σ

noncomputable def doubleDualColumn {A n : ℕ} (hA : 0 < A)
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (σ : Superoperator 1 n) : Superoperator 1 A :=
  Classical.choose
    (representable_unit_surjective_one hA
      ((DayNegation.neg (DayNegation.neg (representable A))).act F σ))

theorem doubleDualColumn_spec {A n : ℕ} (hA : 0 < A)
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (σ : Superoperator 1 n) :
    (DayNegation.unit (representable A)).app 1 (doubleDualColumn hA F σ) =
      (DayNegation.neg (DayNegation.neg (representable A))).act F σ :=
  Classical.choose_spec
    (representable_unit_surjective_one hA
      ((DayNegation.neg (DayNegation.neg (representable A))).act F σ))

theorem evaluationFiber_column {A n : ℕ} (hA : 0 < A)
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (σ : Superoperator 1 n) :
    evaluationFiber hA
        ((DayNegation.neg (DayNegation.neg (representable A))).act F σ) =
      (doubleDualColumn hA F σ).cp := by
  have h := congrArg (evaluationFiber hA) (doubleDualColumn_spec hA F σ)
  rw [evaluationFiber_unit] at h
  exact h.symm

theorem evaluationFiber_traceNonincreasing {A n : ℕ} (hA : 0 < A)
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier) :
    TraceNonincreasing (evaluationFiber hA F) := by
  intro ρ hρ
  set Ψ := evaluationFiber hA F
  have hnn := Matrix.PosSemidef.trace_nonneg hρ
  have hre_nn : 0 ≤ (Matrix.trace ρ).re := (Complex.nonneg_iff.mp hnn).1
  have him0 : (Matrix.trace ρ).im = 0 := (Complex.nonneg_iff.mp hnn).2.symm
  by_cases hpos : 0 < (Matrix.trace ρ).re
  · set t : ℝ := (Matrix.trace ρ).re
    set ρ' : Matrix (Fin n) (Fin n) ℂ := (t⁻¹ : ℝ) • ρ
    have ht0 : t ≠ 0 := ne_of_gt hpos
    have hρ'psd : ρ'.PosSemidef := hρ.smul (inv_nonneg.mpr (le_of_lt hpos))
    have hρ'trace_re : (Matrix.trace ρ').re = 1 := by
      simp only [ρ', Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
      exact inv_mul_cancel₀ ht0
    have hρ'tr : (Matrix.trace ρ').re ≤ 1 := le_of_eq hρ'trace_re
    set σ := preparationOfDensity ρ' hρ'psd hρ'tr
    have hcomp : TraceNonincreasing (CPMap.comp Ψ σ.cp) := by
      rw [← evaluationFiber_act hA F σ, evaluationFiber_column hA F σ]
      exact (doubleDualColumn hA F σ).trace_nonincreasing
    have hσ1 : σ.cp.applyMat (1 : Matrix (Fin 1) (Fin 1) ℂ) = ρ' :=
      preparationOfDensity_applyMat_one ρ' hρ'psd hρ'tr
    have hborn := hcomp (1 : Matrix (Fin 1) (Fin 1) ℂ) Matrix.PosSemidef.one
    have h1tr : (Matrix.trace (1 : Matrix (Fin 1) (Fin 1) ℂ)).re = 1 := by
      simp [Matrix.trace, Fin.default_eq_zero]
    rw [h1tr, CPMap.applyMat_comp, hσ1] at hborn
    have hr : ρ = (t : ℂ) • ρ' := by
      simp only [ρ']
      ext i j
      simp [Matrix.smul_apply, Complex.real_smul]
      field_simp [ht0]
    have hscale : Ψ.applyMat ρ = (t : ℂ) • Ψ.applyMat ρ' := by
      rw [hr, CPMap.applyMat_smul]
    have htr : (Matrix.trace (Ψ.applyMat ρ)).re =
        t * (Matrix.trace (Ψ.applyMat ρ')).re := by
      rw [hscale]
      simp [Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    rw [htr]
    simpa [mul_one] using mul_le_mul_of_nonneg_left hborn (le_of_lt hpos)
  · have hre0 : (Matrix.trace ρ).re = 0 := le_antisymm (not_lt.mp hpos) hre_nn
    have htr0 : Matrix.trace ρ = 0 := Complex.ext hre0 him0
    have hρ0 : ρ = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hρ).mp htr0
    have happ0 : Ψ.applyMat ρ = 0 := by
      rw [hρ0, ← zero_smul ℂ (1 : Matrix (Fin n) (Fin n) ℂ), CPMap.applyMat_smul,
        zero_smul]
    simpa [happ0, Matrix.trace_zero, htr0]

/-- Total fiber cup-evaluation as a superoperator (TNI from columns). -/
noncomputable def evaluationFiberSO_total {A n : ℕ} (hA : 0 < A)
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier) :
    Superoperator n A where
  cp := evaluationFiber hA F
  trace_nonincreasing := evaluationFiber_traceNonincreasing hA F

theorem evaluationFiberSO_total_unit {A n : ℕ} (hA : 0 < A)
    (Φ : Superoperator n A) :
    evaluationFiberSO_total hA ((DayNegation.unit (representable A)).app n Φ) = Φ := by
  apply Superoperator.ext
  exact evaluationFiber_unit hA Φ

theorem pairing_coherence {n : ℕ}
    (z : Superoperator (n * 1) 1) (σ : Superoperator 1 n) :
    Superoperator.comp
        (Superoperator.comp
          (Superoperator.comp z
            (Superoperator.tensor σ (Superoperator.identity 1)))
          (Superoperator.tensorSwap 1 1))
        (Superoperator.tensorLeftUnitorInv 1) =
      Superoperator.comp
        (Superoperator.comp
          (Superoperator.comp z (Superoperator.tensorSwap 1 n))
          (Superoperator.tensorLeftUnitorInv n))
        σ := by
  have hswap :
      Superoperator.tensor σ (Superoperator.identity 1) =
        Superoperator.comp (Superoperator.tensorSwap 1 n)
          (Superoperator.comp
            (Superoperator.tensor (Superoperator.identity 1) σ)
            (Superoperator.tensorSwap 1 1)) := by
    have hnat :=
      Superoperator.tensorSwap_naturality (a := 1) (a' := n) (b := 1) (b' := 1)
        σ (Superoperator.identity 1)
    have h :=
      congrArg (Superoperator.comp (Superoperator.tensorSwap 1 n)) hnat
    have hl :
        Superoperator.comp (Superoperator.tensorSwap 1 n)
            (Superoperator.comp (Superoperator.tensorSwap n 1)
              (Superoperator.tensor σ (Superoperator.identity 1))) =
          Superoperator.tensor σ (Superoperator.identity 1) := by
      rw [Superoperator.comp_assoc, Superoperator.tensorSwap_involutive,
        Superoperator.identity_comp]
    exact hl.symm.trans h
  rw [hswap]
  trans Superoperator.comp
      (Superoperator.comp
        (Superoperator.comp
          (Superoperator.comp z (Superoperator.tensorSwap 1 n))
          (Superoperator.tensor (Superoperator.identity 1) σ))
        (Superoperator.comp (Superoperator.tensorSwap 1 1)
          (Superoperator.tensorSwap 1 1)))
      (Superoperator.tensorLeftUnitorInv 1)
  · simp only [← Superoperator.comp_assoc]
  · rw [Superoperator.tensorSwap_involutive 1 1, Superoperator.comp_identity]
    rw [← Superoperator.comp_assoc]
    rw [Superoperator.tensorLeftUnitorInv_naturality σ]
    rw [Superoperator.comp_assoc]


/-! ### Double-dual evaluation Hom / reflexivity packaging -/

theorem act_app_id {A n : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (σ : Superoperator 1 n)
    (b : ((DayNegation.neg (representable A)).obj 1).Carrier) :
    ((DayNegation.neg (DayNegation.neg (representable A))).act F σ).app
        (Superoperator.identity 1) b =
      F.app σ b := by
  change (DayInternalHom.precompose σ F).app (Superoperator.identity 1) b = F.app σ b
  simp only [DayInternalHom.precompose, Superoperator.comp_identity]

theorem evaluationFiberSO_total_comp_prep {A n : ℕ} (hA : 0 < A)
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (σ : Superoperator 1 n) :
    Superoperator.comp (evaluationFiberSO_total hA F) σ =
      doubleDualColumn hA F σ := by
  apply Superoperator.ext
  have h1 := evaluationFiber_act hA F σ
  have h2 := evaluationFiber_column hA F σ
  change (evaluationFiber hA F).comp σ.cp = (doubleDualColumn hA F σ).cp
  rw [← h1, h2]

theorem pairing_act_eq {A n : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (σ : Superoperator 1 n) (e : Superoperator A 1) :
    doubleDualEffectPairing
        ((DayNegation.neg (DayNegation.neg (representable A))).act F σ) e =
      Superoperator.comp (doubleDualEffectPairing F e) σ := by
  set z : Superoperator (n * 1) 1 :=
    F.app (Superoperator.identity n) (effectPack A e)
  have hLHS :
      doubleDualEffectPairing
          ((DayNegation.neg (DayNegation.neg (representable A))).act F σ) e =
        Superoperator.comp
          (Superoperator.comp
            (Superoperator.comp z
              (Superoperator.tensor σ (Superoperator.identity 1)))
            (Superoperator.tensorSwap 1 1))
          (Superoperator.tensorLeftUnitorInv 1) := by
    unfold doubleDualEffectPairing
    rw [act_app_id F σ (effectPack A e), doubleDual_app_identity F σ (effectPack A e)]
    rw [show dayTensorUnit.act
          (F.app (Superoperator.identity n) (effectPack A e))
          (Superoperator.tensor σ (Superoperator.identity 1)) =
        Superoperator.comp z (Superoperator.tensor σ (Superoperator.identity 1)) from by
      simpa [z] using (dayTensorUnit_act_eq_comp
        (F.app (Superoperator.identity n) (effectPack A e))
        (Superoperator.tensor σ (Superoperator.identity 1)))]
  have hRHS :
      Superoperator.comp (doubleDualEffectPairing F e) σ =
        Superoperator.comp
          (Superoperator.comp
            (Superoperator.comp z (Superoperator.tensorSwap 1 n))
            (Superoperator.tensorLeftUnitorInv n))
          σ := by
    unfold doubleDualEffectPairing; rfl
  rw [hLHS, hRHS]
  exact pairing_coherence z σ

theorem pairing_eq_evaluationFiberSO_total {A n : ℕ} (hA : 0 < A)
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (e : Superoperator A 1) :
    doubleDualEffectPairing F e =
      effectPrecompose (evaluationFiberSO_total hA F) e := by
  set Φ := evaluationFiberSO_total hA F
  refine (superoperator_to_one_eq_of_comp_prep (fun σ => ?_)).symm
  have hcol : Superoperator.comp Φ σ = doubleDualColumn hA F σ :=
    evaluationFiberSO_total_comp_prep hA F σ
  have hunit := doubleDualColumn_spec hA F σ
  calc Superoperator.comp (effectPrecompose Φ e) σ
      = Superoperator.comp (Superoperator.comp e Φ) σ := rfl
    _ = Superoperator.comp e (Superoperator.comp Φ σ) :=
          (Superoperator.comp_assoc e Φ σ).symm
    _ = Superoperator.comp e (doubleDualColumn hA F σ) := by rw [hcol]
    _ = effectPrecompose (doubleDualColumn hA F σ) e := rfl
    _ = doubleDualEffectPairing
          ((DayNegation.unit (representable A)).app 1 (doubleDualColumn hA F σ)) e :=
            (doubleDualEffectPairing_unit _ e).symm
    _ = doubleDualEffectPairing
          ((DayNegation.neg (DayNegation.neg (representable A))).act F σ) e := by
            rw [hunit]
    _ = Superoperator.comp (doubleDualEffectPairing F e) σ := pairing_act_eq F σ e

theorem representable_unit_surjective {A n : ℕ} (hA : 0 < A) :
    Function.Surjective ((DayNegation.unit (representable A)).app n) := by
  intro F
  refine ⟨evaluationFiberSO_total hA F, ?_⟩
  exact (doubleDual_eq_unit_of_pairing F (evaluationFiberSO_total hA F)
    (fun e => pairing_eq_evaluationFiberSO_total hA F e)).symm

theorem recoverCP_choi_hasSum {A n : ℕ} (hA : 0 < A)
    {ι : Type} [Countable ι]
    {f : ι → Superoperator (n * A) 1} {χ : Superoperator (n * A) 1}
    (h : SigmaMon.ChoiSum.HasSum f χ) :
    _root_.HasSum (fun i => (recoverCP hA (f i)).choi)
      (recoverCP hA χ).choi := by
  apply Pi.hasSum.mpr; intro p
  apply Pi.hasSum.mpr; intro q
  have hentry (ψ : Superoperator (n * A) 1) :
      (recoverCP hA ψ).choi p q =
        (A : ℝ) • ψ.cp.effect
          (finProdFinEquiv (q.2, q.1)) (finProdFinEquiv (p.2, p.1)) := by
    simp only [recoverCP_choi, cupNameCP, effectAsChoi_apply, Matrix.smul_apply]
  simp_rw [hentry]
  have heff (ψ : Superoperator (n * A) 1) (i j : Fin (n * A)) :
      ψ.cp.effect i j = ψ.cp.choi ((0 : Fin 1), j) ((0 : Fin 1), i) := by
    simp [CPMap.effect, Fin.default_eq_zero]
  simp_rw [heff]
  have hchoi :=
    Pi.hasSum.mp (Pi.hasSum.mp h
      ((0 : Fin 1), finProdFinEquiv (p.2, p.1)))
      ((0 : Fin 1), finProdFinEquiv (q.2, q.1))
  simpa [Complex.real_smul, smul_eq_mul] using hchoi.mul_left ((A : ℝ) : ℂ)

theorem evaluationFiberSO_total_naturality {A n m : ℕ} (hA : 0 < A)
    (F : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier)
    (f : Superoperator m n) :
    evaluationFiberSO_total hA
        ((DayNegation.neg (DayNegation.neg (representable A))).act F f) =
      Superoperator.comp (evaluationFiberSO_total hA F) f := by
  set Φ := evaluationFiberSO_total hA F
  have hF : F = (DayNegation.unit (representable A)).app n Φ :=
    doubleDual_eq_unit_of_pairing F Φ
      (fun e => pairing_eq_evaluationFiberSO_total hA F e)
  have hnat := (DayNegation.unit (representable A)).naturality Φ f
  -- hnat: unit.app m (act Φ f) = act (unit.app n Φ) f
  -- representable.act Φ f = Φ ∘ f
  have hnat' :
      (DayNegation.unit (representable A)).app m (Superoperator.comp Φ f) =
        (DayNegation.neg (DayNegation.neg (representable A))).act
          ((DayNegation.unit (representable A)).app n Φ) f := by
    simpa [representable_act] using hnat
  calc evaluationFiberSO_total hA
          ((DayNegation.neg (DayNegation.neg (representable A))).act F f)
      = evaluationFiberSO_total hA
          ((DayNegation.neg (DayNegation.neg (representable A))).act
            ((DayNegation.unit (representable A)).app n Φ) f) := by rw [hF]
    _ = evaluationFiberSO_total hA
          ((DayNegation.unit (representable A)).app m (Superoperator.comp Φ f)) :=
            hnat'.symm ▸ rfl
    _ = Superoperator.comp Φ f := evaluationFiberSO_total_unit hA _

noncomputable def representableDoubleDualEvaluation (A : ℕ) (hA : 0 < A) :
    Hom (DayNegation.neg (DayNegation.neg (representable A))) (representable A) where
  app := fun n F => evaluationFiberSO_total hA F
  map_zero := by
    intro n
    have hz :
        (0 : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier) =
          (DayNegation.unit (representable A)).app n 0 :=
      ((DayNegation.unit (representable A)).map_zero n).symm
    rw [hz]
    exact evaluationFiberSO_total_unit hA (0 : Superoperator n A)
  map_sum := by
    intro ι _ n f x hf
    change SigmaMon.ChoiSum.HasSum
      (fun i => evaluationFiberSO_total hA (f i))
      (evaluationFiberSO_total hA x)
    have happ : SigmaMon.ChoiSum.HasSum
        (fun i => (f i).app (Superoperator.identity n) (normalizedCupProbe A hA))
        (x.app (Superoperator.identity n) (normalizedCupProbe A hA)) :=
      hf n A (Superoperator.identity n) (normalizedCupProbe A hA)
    -- convert to choi HasSum of recoverCP
    change _root_.HasSum
        (fun i => (evaluationFiberSO_total hA (f i)).cp.choi)
        (evaluationFiberSO_total hA x).cp.choi
    have hcp (G : ((DayNegation.neg (DayNegation.neg (representable A))).obj n).Carrier) :
        (evaluationFiberSO_total hA G).cp =
          recoverCP hA (G.app (Superoperator.identity n) (normalizedCupProbe A hA)) := rfl
    simp_rw [hcp]
    exact recoverCP_choi_hasSum hA happ
  naturality := by
    intro m n F f
    simpa [representable_act] using evaluationFiberSO_total_naturality hA F f

theorem representableDoubleDualEvaluation_unit (A : ℕ) (hA : 0 < A) :
    Hom.comp (representableDoubleDualEvaluation A hA)
      (DayNegation.unit (representable A)) =
      Hom.id (representable A) := by
  apply Hom.ext
  intro n Φ
  exact evaluationFiberSO_total_unit hA Φ

noncomputable def representableReflexivityOfSurjective (A : ℕ) (hA : 0 < A)
    (h : ∀ n, Function.Surjective ((DayNegation.unit (representable A)).app n)) :
    RepresentableReflexivity A where
  inv := representableDoubleDualEvaluation A hA
  hom_inv := by
    apply Hom.ext
    intro n F
    obtain ⟨x, rfl⟩ := h n F
    have hret := congrArg
      (fun f : Hom (representable A) (representable A) => f.app n x)
      (representableDoubleDualEvaluation_unit A hA)
    exact congrArg ((DayNegation.unit (representable A)).app n) hret
  inv_hom := representableDoubleDualEvaluation_unit A hA

noncomputable def representableReflexivity (A : ℕ) (hA : 0 < A) :
    RepresentableReflexivity A :=
  representableReflexivityOfSurjective A hA
    (fun _ => representable_unit_surjective hA)

noncomputable def representableClassicalObject (A : ℕ) (hA : 0 < A) :
    ClassicalObject DayNegation.data :=
  representableBiorthogonalObject A hA (representableReflexivity A hA)

/-! ### Retraction / reflexivity status

Defined: `normalizedCup`, `normalizedCupProbe`, `cupName`,
`evaluationFiber`, `effectPack`, `doubleDualEffectPairing`,
`bornScalar`, `effectExpectation`, `preparationOfDensity`,
`densityFromEffectPairing`, `exists_superoperator_of_effect_pairing`.

* **Retraction** `evaluation ∘ unit = id` on fibers: **proved**.
* **Cup-generation** for `A > 1`: **falsified** (single-probe path only).
* **Effect-family pairing on unit image**: **proved**
  (`doubleDualEffectPairing_unit`, `pairing_eq_imp_app_effectPack`,
  `effectExpectation_unit`, `effect_pairing_unique`).
* **n=1 analytic reconstruction**: packaging gate
  `exists_superoperator_of_effect_pairing` **proved** (density `ρ` as data);
  `preparationOfDensity` / Born extensionality for `1→1` **proved**;
  `effectPairingQuad_unit` / `effectPairingQuad_nonneg` **proved**;
  double-dual Born calculus **proved**:
  `effectExpectation_add_doubleDual`, `effectExpectation_mono_doubleDual`,
  `effectExpectation_half_doubleDual`, `bornScalar_nonneg`,
  `effectExpectation_nsmul_doubleDual`, `effectExpectation_div_pow_two`,
  `effectExpectation_dyadic_doubleDual`, `effectExpectation_smul_doubleDual`
  (ℝ-homogeneity on `[0,1]` via dyadic squeeze).
  Polarization foundations **proved**:
  `effectPairingQuad_smul`, `effectPairingPolar_self`,
  `effectPairingQuad_eq_expectation` (q(v)=β(|v⟩⟨v|) when ≤ I),
  `vecMulVec_parallelogram` / `_I`,
  `vecMulVec_le_normSq_smul_one`, `effectPairingQuad_parallelogram` / `_I`,
  `effectPairingPolar_eq_ofNorm`, `effectPairingPolar_add_left`,
  `effectPairingPolar_zero_left`, `effectPairingPolar_nsmul_left`.
  Polar sesquilinearity **proved**: `conj_symm`, `add_right`, ℤ/ℚ/`I`/ℝ/ℂ-smul,
  basis expansion, `density_quad_eq`, `densityFromDoubleDual_posSemidef`,
  `trace_density_le_one`.
  Born match **proved**: `born_match_density`.
  Preparation gate **proved**: `exists_preparation_of_doubleDual`.
  Lift **proved**: `effectPack_surjective`, `dualFiberBilinear_surjective`,
  `pairing_eq_imp_app_fiber_one`, `pairing_eq_imp_app_id`,
  `doubleDual_eq_unit_of_pairing`, `representable_unit_surjective_one`.
* Column / cup-evaluation scaffolding **proved**:
  `choi_tensor_prep_id`, `effect_comp_tensor_prep`, `recoverCP_comp_tensor`,
  `act_app_id_cup`, `app_cupProbe_pullback`, `evaluationFiber_act`,
  `doubleDualColumn`, `evaluationFiber_column`,
  `evaluationFiber_traceNonincreasing`, `evaluationFiberSO_total`,
  `pairing_coherence`.
* `A > 0` bipolar: **CLOSED** (`RepresentableReflexivity A` / `representableClassicalObject`)
  (`superoperator_mul_eq_of_tensor_prep`, general pairing lift,
  `representable_unit_surjective`, `representableDoubleDualEvaluation`,
  `representableReflexivity`, `representableClassicalObject`).
-/

end SuperoperatorModule

end QLambda.Domain.Presheaf
