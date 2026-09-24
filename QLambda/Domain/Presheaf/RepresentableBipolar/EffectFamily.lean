/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.RepresentableBipolar.NormalizedCup

/-!
# Effect-family reconstruction

Effect packs, Born scalars, preparations, and density packaging toward n=1 surjectivity.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder InnerProductSpace Kronecker

universe u

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



end SuperoperatorModule

end QLambda.Domain.Presheaf
