/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.RepresentableBipolar.EffectSeparation

/-!
# Normalized cup and dual probes

Cup obstruction for raw Choi(`id`), normalized cup, snake/Choi recovery, and
cup-probe non-generation for `A > 1`.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder InnerProductSpace Kronecker

universe u

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


end SuperoperatorModule

end QLambda.Domain.Presheaf
