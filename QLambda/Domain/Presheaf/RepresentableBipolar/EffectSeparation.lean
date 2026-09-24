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
# Effect separation for positive representables

Effect pairing, precompose injectivity, closed-adjunction transport, unit reshape,
and fiberwise injectivity of the representable unit.
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


end SuperoperatorModule

end QLambda.Domain.Presheaf
