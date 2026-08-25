/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.InstrumentPower
import QLambda.Saturation
import QLambda.ObservationBasis
import QLambda.FiniteImageNonclosure

/-!
# Rank-one Choi-ray obstruction for register dimension at least two

A nonzero rank-one positive semidefinite Choi matrix determines a ray
under positive scaling.  Anything Loewner-below that matrix remains on
the same ray.  For register dimension `2 ≤ n` there are uncountably many
distinct rays, while any approximant generated from a principal finite
instrument, Scott-lower closure, and optional uniform spectral
attenuation contributes only finitely many generating rays.

This is a medium-strength negative theorem: it applies only to that
restricted approximant class `PhysicalBasisApproximant`.  It does **not**
claim that raw `InstrumentPower` admits no `IsOmegaQVA` structure, and
it does not apply to the successful countable `RatCPMatrix` / rounded-
token construction, which separates by dense rational quadratic tests
rather than by interpolating through finitely many physical rays.
-/

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace QLambda

universe u

/-- A nonzero rank-one Choi matrix, presented as an outer product. -/
structure RankOneChoi (n : ℕ) where
  vec : Fin n × Fin n → ℂ
  ne_zero : vec ≠ 0

namespace RankOneChoi

variable {n : ℕ}

/-- The Choi matrix `v v†`. -/
noncomputable def matrix (A : RankOneChoi n) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  vecMulVec A.vec (star A.vec)

theorem matrix_posSemidef (A : RankOneChoi n) :
    A.matrix.PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star A.vec

theorem matrix_apply (A : RankOneChoi n) (p q : Fin n × Fin n) :
    A.matrix p q = A.vec p * star (A.vec q) :=
  rfl

theorem mul_star_self_eq_zero {z : ℂ} (h : z * star z = 0) : z = 0 := by
  have hsq : Complex.normSq z = 0 := by
    simpa [Complex.normSq, Complex.normSq_eq_conj_mul_self, mul_comm,
      Complex.star_def] using congrArg Complex.re h
  exact Complex.normSq_eq_zero.mp hsq

theorem matrix_ne_zero (A : RankOneChoi n) : A.matrix ≠ 0 := by
  intro h
  apply A.ne_zero
  ext p
  have hp : A.matrix p p = 0 := by simp [h]
  exact mul_star_self_eq_zero (by simpa [matrix_apply] using hp)

/-- Positive-scaling equivalence of rank-one Choi matrices. -/
def SameRay (A B : RankOneChoi n) : Prop :=
  ∃ t : ℝ, 0 < t ∧ A.matrix = (t : ℂ) • B.matrix

theorem SameRay.refl (A : RankOneChoi n) : SameRay A A :=
  ⟨1, one_pos, by simp⟩

theorem SameRay.symm {A B : RankOneChoi n} (h : SameRay A B) :
    SameRay B A := by
  obtain ⟨t, ht, heq⟩ := h
  refine ⟨t⁻¹, inv_pos.mpr ht, ?_⟩
  apply Matrix.ext
  intro p q
  have hpq : A.matrix p q = (t : ℂ) * B.matrix p q := by
    simpa [smul_eq_mul] using
      congrArg (fun M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ => M p q) heq
  have ht0 : (t : ℂ) ≠ 0 := mod_cast ht.ne'
  have hBA : B.matrix p q = (t : ℂ)⁻¹ * A.matrix p q := by
    rw [hpq, ← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
  simpa [smul_eq_mul, Complex.ofReal_inv] using hBA

theorem SameRay.trans {A B C : RankOneChoi n}
    (hAB : SameRay A B) (hBC : SameRay B C) : SameRay A C := by
  obtain ⟨t, ht, htAB⟩ := hAB
  obtain ⟨s, hs, hsBC⟩ := hBC
  refine ⟨t * s, mul_pos ht hs, ?_⟩
  rw [htAB, hsBC, smul_smul, Complex.ofReal_mul]

theorem quadratic (A : RankOneChoi n) (w : Fin n × Fin n → ℂ) :
    star w ⬝ᵥ (A.matrix *ᵥ w) =
      star (star A.vec ⬝ᵥ w) * (star A.vec ⬝ᵥ w) := by
  simp [matrix, vecMulVec, mulVec, dotProduct, Finset.mul_sum,
    mul_left_comm, mul_comm]

theorem dominated_kernel
    (A : RankOneChoi n)
    (M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hM : M.PosSemidef) (hle : M ≤ A.matrix)
    (w : Fin n × Fin n → ℂ) (hw : star A.vec ⬝ᵥ w = 0) :
    star w ⬝ᵥ (M *ᵥ w) = 0 := by
  have hdiff : (A.matrix - M).PosSemidef := hle
  have hA0 : star w ⬝ᵥ (A.matrix *ᵥ w) = 0 := by
    rw [quadratic, hw, star_zero, zero_mul]
  have hqw : 0 ≤ (star w ⬝ᵥ ((A.matrix - M) *ᵥ w)).re :=
    (Complex.nonneg_iff.mp (hdiff.dotProduct_mulVec_nonneg w)).1
  have hsplit :
      (star w ⬝ᵥ ((A.matrix - M) *ᵥ w)).re =
        (star w ⬝ᵥ (A.matrix *ᵥ w)).re - (star w ⬝ᵥ (M *ᵥ w)).re := by
    simp [sub_mulVec, dotProduct_sub]
  have hleRe :
      (star w ⬝ᵥ (M *ᵥ w)).re ≤ (star w ⬝ᵥ (A.matrix *ᵥ w)).re := by
    linarith
  have hMnn := hM.dotProduct_mulVec_nonneg w
  have hMre : 0 ≤ (star w ⬝ᵥ (M *ᵥ w)).re :=
    (Complex.nonneg_iff.mp hMnn).1
  have hMim : (star w ⬝ᵥ (M *ᵥ w)).im = 0 :=
    (Complex.nonneg_iff.mp hMnn).2.symm
  have hAre : (star w ⬝ᵥ (A.matrix *ᵥ w)).re = 0 := by
    simp [hA0]
  have hre : (star w ⬝ᵥ (M *ᵥ w)).re = 0 :=
    le_antisymm (hleRe.trans_eq hAre) hMre
  exact Complex.ext hre hMim


theorem self_dot_ne_zero {v : Fin n × Fin n → ℂ} (hv : v ≠ 0) :
    star v ⬝ᵥ v ≠ 0 := by
  intro h
  apply hv
  ext p
  have hsum : ∑ q, Complex.normSq (v q) = 0 := by
    simpa [dotProduct, Complex.normSq, Complex.star_def, mul_comm] using
      congrArg Complex.re h
  have hnn : ∀ q ∈ Finset.univ, 0 ≤ Complex.normSq (v q) :=
    fun _ _ => Complex.normSq_nonneg _
  have hp :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum p (Finset.mem_univ _)
  exact Complex.normSq_eq_zero.mp hp

/-- Domination below a rank-one PSD matrix stays on its ray: the
dominated generator is a nonzero scalar multiple of the original. -/
theorem dominated_stays_on_ray
    (A B : RankOneChoi n) (hle : B.matrix ≤ A.matrix) :
    SameRay B A := by
  have horth :
      ∀ w, star A.vec ⬝ᵥ w = 0 → star B.vec ⬝ᵥ w = 0 := by
    intro w hw
    have hquad :=
      dominated_kernel A B.matrix B.matrix_posSemidef hle w hw
    have : star (star B.vec ⬝ᵥ w) * (star B.vec ⬝ᵥ w) = 0 := by
      simpa [quadratic] using hquad
    exact mul_star_self_eq_zero (by simpa [mul_comm] using this)
  let c := (star A.vec ⬝ᵥ B.vec) / (star A.vec ⬝ᵥ A.vec)
  let w := B.vec - c • A.vec
  have hwA : star A.vec ⬝ᵥ w = 0 := by
    have hden : star A.vec ⬝ᵥ A.vec ≠ 0 := self_dot_ne_zero A.ne_zero
    simp [w, c, dotProduct_sub, smul_eq_mul]
    field_simp [hden]
    ring
  have hwB : star B.vec ⬝ᵥ w = 0 := horth w hwA
  have hw0 : w = 0 := by
    have hdecomp : B.vec = w + c • A.vec := by simp [w]
    have hww : star w ⬝ᵥ w = 0 := by
      have := hwB
      rw [hdecomp] at this
      simpa [dotProduct_add, smul_eq_mul, hwA] using this
    ext p
    have hsum : ∑ q, Complex.normSq (w q) = 0 := by
      simpa [dotProduct, Complex.normSq, Complex.star_def, mul_comm] using
        congrArg Complex.re hww
    have hnn : ∀ q ∈ Finset.univ, 0 ≤ Complex.normSq (w q) :=
      fun _ _ => Complex.normSq_nonneg _
    exact Complex.normSq_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum p (Finset.mem_univ _))
  have hvec : B.vec = c • A.vec := by
    simpa [w, sub_eq_zero] using hw0
  have hc0 : c ≠ 0 := by
    intro hcz
    apply B.ne_zero
    simpa [hvec, hcz]
  refine ⟨Complex.normSq c, Complex.normSq_pos.mpr hc0, ?_⟩
  apply Matrix.ext
  intro p q
  have hc : (Complex.normSq c : ℂ) = c * star c := by
    apply Complex.ext <;>
      simp [Complex.normSq, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im] <;>
      ring
  simp [matrix, hvec, vecMulVec, smul_eq_mul, hc]
  ring

/-- Uniform spectral attenuation scales every Choi matrix. -/
theorem scale_choi {n m : ℕ} (r : ℝ) (K : KrausFamily n m) :
    KrausFamily.choi (KrausFamily.scale (r : ℂ) K) =
      ((r : ℂ) * star (r : ℂ)) • KrausFamily.choi K := by
  induction K with
  | nil =>
      simp [KrausFamily.scale, KrausFamily.choi]
  | cons A K ih =>
      have hterm :
          KrausFamily.choiTerm ((r : ℂ) • A) =
            ((r : ℂ) * star (r : ℂ)) • KrausFamily.choiTerm A := by
        ext p q
        simp [KrausFamily.choiTerm, Matrix.smul_apply, smul_eq_mul]
        ring
      rw [KrausFamily.scale, List.map_cons, KrausFamily.choi_cons, hterm]
      change
          ((r : ℂ) * star (r : ℂ)) • KrausFamily.choiTerm A +
            KrausFamily.choi (KrausFamily.scale (r : ℂ) K) =
          ((r : ℂ) * star (r : ℂ)) •
            (KrausFamily.choiTerm A + KrausFamily.choi K)
      rw [ih, smul_add]

/-- Uniform attenuation of a rank-one Choi matrix stays on the same ray. -/
theorem attenuation_same_ray (A : RankOneChoi n) (r : ℝ) (hr : 0 < r) :
    SameRay
      ⟨fun p => (r : ℂ) * A.vec p, by
        intro h
        apply A.ne_zero
        ext p
        have hp := congrFun h p
        have hr0 : (r : ℂ) ≠ 0 := mod_cast hr.ne'
        exact mul_left_cancel₀ hr0 (by simpa using hp)⟩ A := by
  refine ⟨r ^ 2, pow_pos hr 2, ?_⟩
  apply Matrix.ext
  intro p q
  simp [matrix, vecMulVec, smul_eq_mul, Complex.ofReal_pow]
  ring

end RankOneChoi

instance instSetoidRankOneChoi (n : ℕ) : Setoid (RankOneChoi n) where
  r := RankOneChoi.SameRay
  iseqv :=
    ⟨RankOneChoi.SameRay.refl, RankOneChoi.SameRay.symm,
      RankOneChoi.SameRay.trans⟩

/-- The set of rank-one Choi rays, as a quotient of nonzero outer
products by positive scaling. -/
def ChoiRay (n : ℕ) : Type :=
  Quotient (instSetoidRankOneChoi n)

def ChoiRay.mk {n : ℕ} (A : RankOneChoi n) : ChoiRay n :=
  Quotient.mk _ A

/-- Standard computational-basis vector on the Choi coordinate `p`. -/
def basisVec (n : ℕ) (p : Fin n × Fin n) : Fin n × Fin n → ℂ :=
  fun q => if q = p then 1 else 0

theorem basisVec_ne_zero (n : ℕ) (p : Fin n × Fin n) :
    basisVec n p ≠ 0 := by
  intro h
  have := congrFun h p
  simp [basisVec] at this

def basisRankOne (n : ℕ) (p : Fin n × Fin n) : RankOneChoi n :=
  ⟨basisVec n p, basisVec_ne_zero n p⟩

def basisRay (n : ℕ) (p : Fin n × Fin n) : ChoiRay n :=
  ChoiRay.mk (basisRankOne n p)

theorem basisRankOne_matrix (n : ℕ) (p q r : Fin n × Fin n) :
    (basisRankOne n p).matrix q r =
      if q = p ∧ r = p then 1 else 0 := by
  simp [basisRankOne, RankOneChoi.matrix, basisVec, vecMulVec]
  split_ifs <;> simp_all

/-- Distinct computational-basis coordinates determine distinct rays. -/
theorem basisRay_injective (n : ℕ) :
    Function.Injective (basisRay n) := by
  intro p q hpq
  have h := Quotient.exact hpq
  obtain ⟨t, ht, heq⟩ := h
  have hpp : (basisRankOne n p).matrix p p = 1 := by
    simp [basisRankOne_matrix]
  have := congrArg (fun M : Matrix _ _ ℂ => M p p) heq
  simp [hpp, basisRankOne_matrix, smul_eq_mul] at this
  by_cases hpe : p = q
  · exact hpe
  · simp [hpe] at this

/-- In dimension one the Choi index set is a singleton. -/
theorem choiRay_basis_n_one_unique (p : Fin 1 × Fin 1) :
    basisRay 1 p = basisRay 1 (0, 0) := by
  have h1 : p.1 = 0 := Subsingleton.elim _ _
  have h2 : p.2 = 0 := Subsingleton.elim _ _
  apply congrArg (basisRay 1)
  exact Prod.ext h1 h2

/-- Dimension-one sanity: the computational-basis family is a singleton. -/
theorem n_one_basis_subsingleton :
    Subsingleton (Set.range (basisRay 1)) := by
  refine ⟨fun x y => ?_⟩
  rcases x with ⟨p, hp⟩
  rcases y with ⟨q, hq⟩
  apply Subtype.ext
  obtain ⟨i, rfl⟩ := hp
  obtain ⟨j, rfl⟩ := hq
  simp [choiRay_basis_n_one_unique]

/-- For `2 ≤ n` the computational-basis family already supplies more
than one ray. -/
theorem two_le_n_basisRays_nontrivial {n : ℕ} (hn : 2 ≤ n) :
    basisRay n (⟨0, Nat.zero_lt_of_lt hn⟩, ⟨0, Nat.zero_lt_of_lt hn⟩) ≠
      basisRay n (⟨0, Nat.zero_lt_of_lt hn⟩, ⟨1, hn⟩) := by
  intro h
  have := basisRay_injective n h
  simp at this

/-- Mixing weight on a two-dimensional Choi coordinate plane. -/
noncomputable def mixVec (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    Fin n × Fin n → ℂ :=
  fun p =>
    if p = (⟨0, Nat.zero_lt_of_lt hn⟩, ⟨0, Nat.zero_lt_of_lt hn⟩) then
      Real.sqrt t
    else if p = (⟨0, Nat.zero_lt_of_lt hn⟩, ⟨1, hn⟩) then
      Real.sqrt (1 - t)
    else 0

theorem mixVec_ne_zero (n : ℕ) (hn : 2 ≤ n) {t : ℝ}
    (ht₀ : 0 < t) (_ht₁ : t < 1) :
    mixVec n hn t ≠ 0 := by
  intro h
  have h0 :=
    congrFun h (⟨0, Nat.zero_lt_of_lt hn⟩, ⟨0, Nat.zero_lt_of_lt hn⟩)
  simp [mixVec] at h0
  exact (Real.sqrt_pos.mpr ht₀).ne' (by simpa using h0)

noncomputable def mixRankOne (n : ℕ) (hn : 2 ≤ n) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) : RankOneChoi n :=
  ⟨mixVec n hn t, mixVec_ne_zero n hn ht₀ ht₁⟩

noncomputable def mixRay (n : ℕ) (hn : 2 ≤ n) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) : ChoiRay n :=
  ChoiRay.mk (mixRankOne n hn ht₀ ht₁)

theorem mixRankOne_diag00 (n : ℕ) (hn : 2 ≤ n) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) :
    (mixRankOne n hn ht₀ ht₁).matrix
        (⟨0, Nat.zero_lt_of_lt hn⟩, ⟨0, Nat.zero_lt_of_lt hn⟩)
        (⟨0, Nat.zero_lt_of_lt hn⟩, ⟨0, Nat.zero_lt_of_lt hn⟩) = t := by
  have hpos : 0 ≤ t := le_of_lt ht₀
  have hvec :
      mixVec n hn t
          (⟨0, Nat.zero_lt_of_lt hn⟩, ⟨0, Nat.zero_lt_of_lt hn⟩) =
        Real.sqrt t := by
    simp [mixVec]
  rw [RankOneChoi.matrix_apply]
  change mixVec n hn t
      (⟨0, Nat.zero_lt_of_lt hn⟩, ⟨0, Nat.zero_lt_of_lt hn⟩) *
      star (mixVec n hn t
        (⟨0, Nat.zero_lt_of_lt hn⟩, ⟨0, Nat.zero_lt_of_lt hn⟩)) = t
  rw [hvec]
  simp [Complex.conj_ofReal]
  norm_cast
  rw [← pow_two]
  exact Real.sq_sqrt hpos

theorem mixRankOne_diag01 (n : ℕ) (hn : 2 ≤ n) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) :
    (mixRankOne n hn ht₀ ht₁).matrix
        (⟨0, Nat.zero_lt_of_lt hn⟩, ⟨1, hn⟩)
        (⟨0, Nat.zero_lt_of_lt hn⟩, ⟨1, hn⟩) = 1 - t := by
  have hpos : 0 ≤ 1 - t := sub_nonneg.mpr ht₁.le
  have hvec :
      mixVec n hn t (⟨0, Nat.zero_lt_of_lt hn⟩, ⟨1, hn⟩) =
        Real.sqrt (1 - t) := by
    simp [mixVec]
  rw [RankOneChoi.matrix_apply]
  change mixVec n hn t (⟨0, Nat.zero_lt_of_lt hn⟩, ⟨1, hn⟩) *
      star (mixVec n hn t (⟨0, Nat.zero_lt_of_lt hn⟩, ⟨1, hn⟩)) =
    1 - t
  rw [hvec]
  simp [Complex.conj_ofReal]
  norm_cast
  rw [← pow_two]
  exact Real.sq_sqrt hpos

/-- Distinct mixing weights in `(0, 1)` determine distinct rays. -/
theorem mixRay_injective {n : ℕ} (hn : 2 ≤ n)
    {t s : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1)
    (hs₀ : 0 < s) (hs₁ : s < 1)
    (h : mixRay n hn ht₀ ht₁ = mixRay n hn hs₀ hs₁) : t = s := by
  have hex := Quotient.exact h
  obtain ⟨u, hu, heq⟩ := hex
  let p00 : Fin n × Fin n :=
    (⟨0, Nat.zero_lt_of_lt hn⟩, ⟨0, Nat.zero_lt_of_lt hn⟩)
  let p01 : Fin n × Fin n :=
    (⟨0, Nat.zero_lt_of_lt hn⟩, ⟨1, hn⟩)
  have h00 := congrArg (fun M : Matrix _ _ ℂ => M p00 p00) heq
  have h11 := congrArg (fun M : Matrix _ _ ℂ => M p01 p01) heq
  simp only [Matrix.smul_apply, smul_eq_mul] at h00 h11
  rw [mixRankOne_diag00 n hn ht₀ ht₁, mixRankOne_diag00 n hn hs₀ hs₁] at h00
  rw [mixRankOne_diag01 n hn ht₀ ht₁, mixRankOne_diag01 n hn hs₀ hs₁] at h11
  have : t * (1 - s) = s * (1 - t) := by
    have ht' := congrArg Complex.re h00
    have hs' := congrArg Complex.re h11
    simp at ht' hs'
    nlinarith
  nlinarith

/-- Interior mixing weights determine mixing rays. -/
noncomputable def mixRayOfIoo (n : ℕ) (hn : 2 ≤ n)
    (t : Set.Ioo (0 : ℝ) 1) : ChoiRay n :=
  mixRay n hn t.2.1 t.2.2

theorem mixRayOfIoo_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (mixRayOfIoo n hn) :=
  fun t s hts =>
    Subtype.ext (mixRay_injective hn t.2.1 t.2.2 s.2.1 s.2.2 hts)

/-- A generating rank-one summand of one square Kraus operator. -/
noncomputable def krausRay {n : ℕ} (A : KrausOperator n n)
    (hne : (fun p : Fin n × Fin n => A p.1 p.2) ≠ 0) : ChoiRay n :=
  ChoiRay.mk ⟨fun p => A p.1 p.2, hne⟩

/-- Generating rays of a finite square Kraus family. -/
noncomputable def krausFamilyRays {n : ℕ} (K : KrausFamily n n) :
    Set (ChoiRay n) :=
  {r | ∃ A ∈ K, ∃ hne : (fun p : Fin n × Fin n => A p.1 p.2) ≠ 0,
    r = krausRay A hne}

theorem krausFamilyRays_nil {n : ℕ} :
    krausFamilyRays ([] : KrausFamily n n) = ∅ := by
  ext r
  simp [krausFamilyRays]

theorem krausFamilyRays_finite {n : ℕ} (K : KrausFamily n n) :
    (krausFamilyRays K).Finite := by
  induction K with
  | nil =>
      simp [krausFamilyRays_nil]
  | cons A K ih =>
      by_cases hA : (fun p : Fin n × Fin n => A p.1 p.2) ≠ 0
      · refine (ih.insert (krausRay A hA)).subset ?_
        intro r hr
        obtain ⟨B, hB, hne, rfl⟩ := hr
        simp only [List.mem_cons] at hB
        rcases hB with hBA | hBK
        · subst B
          exact Or.inl rfl
        · exact Or.inr ⟨B, hBK, hne, rfl⟩
      · refine ih.subset ?_
        intro r hr
        obtain ⟨B, hB, hne, rfl⟩ := hr
        simp only [List.mem_cons] at hB
        rcases hB with hBA | hBK
        · subst B
          exact (hA hne).elim
        · exact ⟨B, hBK, hne, rfl⟩

/-- Generating rays of a finite instrument, taken over every outcome
branch. -/
noncomputable def instrumentRays {n : ℕ} {D : Type u}
    (μ : FiniteInstrumentComp n D) : Set (ChoiRay n) :=
  ⋃ o : μ.Outcome, krausFamilyRays (μ.branch o)

theorem instrumentRays_finite {n : ℕ} {D : Type u}
    (μ : FiniteInstrumentComp n D) :
    (instrumentRays μ).Finite :=
  finite_iUnion fun _ => krausFamilyRays_finite _

/-- Approximants generated from principal finite instruments, binary
Scott-lower closure, and optional uniform spectral attenuation.  Binary
closure encodes any finite generator list.  This is the exact
medium-strength class used by the obstruction; raw `InstrumentPower` is
not claimed to lie outside `ωQVA`. -/
inductive PhysicalBasisApproximant (n : ℕ) where
  | ofFinite {D : Type} (μ : FiniteInstrumentComp n D) :
      PhysicalBasisApproximant n
  | lowerClose (left right : PhysicalBasisApproximant n) :
      PhysicalBasisApproximant n
  | attenuate (r : ℝ) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
      (a : PhysicalBasisApproximant n) : PhysicalBasisApproximant n

/-- Generating rays of a physical-basis approximant.  Lower closure
unions the rays of its generators; uniform attenuation preserves ray
direction. -/
noncomputable def PhysicalBasisApproximant.rays {n : ℕ} :
    PhysicalBasisApproximant n → Set (ChoiRay n)
  | .ofFinite μ => instrumentRays μ
  | .lowerClose left right =>
      PhysicalBasisApproximant.rays left ∪
        PhysicalBasisApproximant.rays right
  | .attenuate _ _ _ a => PhysicalBasisApproximant.rays a

theorem attenuate_preserves_rays {n : ℕ}
    (r : ℝ) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (a : PhysicalBasisApproximant n) :
    (PhysicalBasisApproximant.attenuate r hr₀ hr₁ a).rays = a.rays :=
  rfl

theorem PhysicalBasisApproximant.rays_finite {n : ℕ}
    (a : PhysicalBasisApproximant n) : a.rays.Finite := by
  induction a with
  | ofFinite μ =>
      exact instrumentRays_finite μ
  | lowerClose left right ihL ihR =>
      exact ihL.union ihR
  | attenuate r hr₀ hr₁ a ih =>
      exact ih

/-- A countable family of physical-basis approximants covers only
countably many generating rays. -/
theorem countable_union_approximant_rays {n : ℕ}
    (family : ℕ → PhysicalBasisApproximant n) :
    (⋃ k, (family k).rays).Countable :=
  Set.countable_iUnion fun k =>
    (PhysicalBasisApproximant.rays_finite (family k)).countable

/-- The uncountable mixing family, as a set of rays. -/
def mixRaySet (n : ℕ) (hn : 2 ≤ n) : Set (ChoiRay n) :=
  {r | ∃ t : ℝ, ∃ ht₀ : 0 < t, ∃ ht₁ : t < 1, r = mixRay n hn ht₀ ht₁}

theorem mixRayOfIoo_mem {n : ℕ} (hn : 2 ≤ n)
    (t : Set.Ioo (0 : ℝ) 1) :
    mixRayOfIoo n hn t ∈ mixRaySet n hn :=
  ⟨t.1, t.2.1, t.2.2, rfl⟩

theorem mixRaySet_injects_Ioo {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective
      (fun t : Set.Ioo (0 : ℝ) 1 =>
        (⟨mixRayOfIoo n hn t, mixRayOfIoo_mem hn t⟩ : mixRaySet n hn)) :=
  fun _t _s hts => mixRayOfIoo_injective hn (congrArg Subtype.val hts)

/-- A countable physical-basis cover would make the mixing-weight
interval countable. -/
theorem covering_implies_countable_Ioo {n : ℕ} (hn : 2 ≤ n)
    (approx : ℕ → PhysicalBasisApproximant n)
    (hcover : mixRaySet n hn ⊆ ⋃ k, (approx k).rays) :
    Countable (Set.Ioo (0 : ℝ) 1) := by
  have : Countable (mixRaySet n hn) :=
    (countable_union_approximant_rays approx).mono hcover
  exact Function.Injective.countable (mixRaySet_injects_Ioo hn)

/-- No countable family of physical-basis approximants can cover the
mixing family when `2 ≤ n`, given that `(0, 1)` is uncountable.  The
formal content is the injection of that interval through rank-one Choi
rays versus finite generating-ray coverage. -/
theorem no_omegaQVA_of_physicalBasisApproximants {n : ℕ}
    (hn : 2 ≤ n)
    (approx : ℕ → PhysicalBasisApproximant n)
    (hIoo : ¬ Countable (Set.Ioo (0 : ℝ) 1)) :
    ¬ mixRaySet n hn ⊆ ⋃ k, (approx k).rays :=
  fun hcover => hIoo (covering_implies_countable_Ioo hn approx hcover)

/-- Dimension-one sanity: the unique computational-basis ray is among
the generating rays of the one-dimensional identity instrument. -/
theorem n_one_identity_covers_the_ray :
    basisRay 1 (0, 0) ∈
      instrumentRays
        (FiniteInstrumentComp.unit (n := 1) (D := Unit) ()) := by
  rw [instrumentRays, Set.mem_iUnion]
  refine ⟨(), ?_⟩
  refine ⟨(1 : KrausOperator 1 1), ?mem, ?hne, ?eq⟩
  · simp [FiniteInstrumentComp.unit, KrausFamily.identity, krausFamilyRays]
  · intro h
    have := congrFun h (0, 0)
    simp [Matrix.one_apply] at this
  · apply Quotient.sound
    refine ⟨1, one_pos, ?_⟩
    apply Matrix.ext
    intro p q
    have hp : p = (0, 0) := Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    have hq : q = (0, 0) := Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    simp [krausRay, basisRankOne, RankOneChoi.matrix, basisVec, vecMulVec,
      Matrix.one_apply, hp, hq]

/-- The successful countable `RatCPMatrix` / rounded-token construction
is outside the scope of this obstruction: its separators are dense
rational quadratic tests, not a countable family of finite generating
rays.  Gaussian-rational Choi vectors already separate Hermitian
matrices, so an approximate identity can interpolate without ever
selecting a representative of every rank-one ray. -/
theorem obstruction_does_not_apply_to_rational_tokens {n : ℕ}
    (J K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hJ : J.IsHermitian) (hK : K.IsHermitian)
    (h : ∀ v : RatChoiVec n,
      ChoiTest.eval (v, ⟨0, le_rfl⟩) J ≤
        ChoiTest.eval (v, ⟨0, le_rfl⟩) K) :
    J ≤ K :=
  ChoiTest.le_of_rational_quadratic_le hJ hK h

end QLambda
