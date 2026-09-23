/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumCPO

/-!
# Intrinsic finite-dimensional completely positive maps

`CPMap n m` is a positive semidefinite Choi matrix, rather than a quotient or
a chosen Kraus presentation.  A Kraus family can always be recovered
noncomputably in finite dimensions; this is used to transport composition and
positivity results from the existing operator-sum development.
-/

namespace QLambda

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder NNReal

namespace KrausFamily

variable {n m : ℕ}

/-- The input effect `∑ᵢ Aᵢ† Aᵢ` of a Kraus family. -/
def effect (K : KrausFamily n m) : Matrix (Fin n) (Fin n) ℂ :=
  (K.map fun A => Aᴴ * A).sum

private theorem trace_mul_vecMulVec
    (E : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    Matrix.trace (E * Matrix.vecMulVec x (star x)) =
      star x ⬝ᵥ E *ᵥ x := by
  change (∑ i, ∑ j, E i j * (x j * star (x i))) =
    ∑ i, star (x i) * ∑ j, E i j * x j
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem trace_vecMulVec_self (x : Fin n → ℂ) :
    Matrix.trace (Matrix.vecMulVec x (star x)) = star x ⬝ᵥ x := by
  rw [Matrix.trace_vecMulVec]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem quad_sub_one
    (E : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    star x ⬝ᵥ (1 - E) *ᵥ x =
      Matrix.trace (Matrix.vecMulVec x (star x)) -
        Matrix.trace (E * Matrix.vecMulVec x (star x)) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    trace_mul_vecMulVec, trace_vecMulVec_self]

/-- Trace of a Kraus action is pairing with its input effect. -/
theorem trace_applyMat_eq_effect (K : KrausFamily n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (applyMat K ρ) = Matrix.trace (effect K * ρ) := by
  induction K with
  | nil => simp [applyMat, effect]
  | cons A K ih =>
    rw [applyMat_cons, Matrix.trace_add, ih]
    rw [Matrix.trace_mul_comm (A * ρ) Aᴴ, ← Matrix.mul_assoc]
    simp [effect, Matrix.add_mul, Matrix.trace_add]

theorem effect_posSemidef (K : KrausFamily n m) :
    (effect K).PosSemidef := by
  induction K with
  | nil =>
    simpa [effect] using
      (Matrix.PosSemidef.zero :
        (0 : Matrix (Fin n) (Fin n) ℂ).PosSemidef)
  | cons A K ih =>
    simp only [effect, List.map_cons, List.sum_cons]
    exact (Matrix.posSemidef_conjTranspose_mul_self A).add ih

/-- Testing TNI on all positive inputs forces the input effect below identity. -/
theorem effect_le_one_of_trace_nonincreasing (K : KrausFamily n m)
    (hK : ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (applyMat K ρ)).re ≤ (Matrix.trace ρ).re) :
    effect K ≤ 1 := by
  rw [Matrix.le_iff]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.IsHermitian.sub Matrix.isHermitian_one
      (effect_posSemidef K).isHermitian
  · intro x
    let ρ := Matrix.vecMulVec x (star x)
    have hρ : ρ.PosSemidef :=
      Matrix.posSemidef_vecMulVec_self_star x
    have hout : 0 ≤ Matrix.trace (applyMat K ρ) :=
      (applyMat_posSemidef K hρ).trace_nonneg
    have hin : 0 ≤ Matrix.trace ρ := hρ.trace_nonneg
    have hle : Matrix.trace (applyMat K ρ) ≤ Matrix.trace ρ := by
      rw [Complex.le_def]
      exact
        ⟨hK ρ hρ,
          (Complex.nonneg_iff.mp hout).2.symm.trans
            (Complex.nonneg_iff.mp hin).2⟩
    rw [quad_sub_one, ← trace_applyMat_eq_effect]
    exact sub_nonneg.mpr hle

private theorem trace_mul_nonneg_of_posSemidef
    {A ρ : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hρ : ρ.PosSemidef) :
    0 ≤ Matrix.trace (A * ρ) := by
  obtain ⟨k, v, rfl⟩ :=
    Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hρ
  rw [Matrix.mul_sum, Matrix.trace_sum]
  exact Finset.sum_nonneg fun i _ => by
    rw [trace_mul_vecMulVec]
    exact hA.dotProduct_mulVec_nonneg (v i)

/-- The effect bound implies trace non-increase on every positive input. -/
theorem trace_nonincreasing_of_effect_le_one (K : KrausFamily n m)
    (hK : effect K ≤ 1) :
    ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (applyMat K ρ)).re ≤ (Matrix.trace ρ).re := by
  intro ρ hρ
  have hdiff : (1 - effect K).PosSemidef := Matrix.le_iff.mp hK
  have htr := trace_mul_nonneg_of_posSemidef hdiff hρ
  have hre := (Complex.nonneg_iff.mp htr).1
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at hre
  rw [trace_applyMat_eq_effect]
  exact sub_nonneg.mp hre

end KrausFamily

end QLambda

namespace QLambda.Domain.Presheaf

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder

/-- An intrinsic completely positive map, represented by its positive
semidefinite Choi matrix. -/
structure CPMap (n m : ℕ) where
  choi : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ
  choi_pos : choi.PosSemidef

namespace CPMap

variable {n m ℓ r : ℕ}

@[ext]
theorem ext {Φ Ψ : CPMap n m} (h : Φ.choi = Ψ.choi) : Φ = Ψ := by
  cases Φ
  cases Ψ
  cases h
  rfl

instance : LE (CPMap n m) :=
  ⟨fun Φ Ψ => Φ.choi ≤ Ψ.choi⟩

instance : PartialOrder (CPMap n m) where
  le_refl Φ := by
    change Φ.choi ≤ Φ.choi
    exact le_rfl
  le_trans Φ Ψ Χ hΦΨ hΨΧ := by
    change Φ.choi ≤ Χ.choi
    exact le_trans hΦΨ hΨΧ
  le_antisymm Φ Ψ hΦΨ hΨΦ := by
    apply ext
    exact le_antisymm hΦΨ hΨΦ

/-- A finite Kraus presentation determines an intrinsic CP map. -/
def ofKraus (K : KrausFamily n m) : CPMap n m where
  choi := KrausFamily.choi K
  choi_pos := KrausFamily.choi_posSemidef K

@[simp]
theorem choi_ofKraus (K : KrausFamily n m) :
    (ofKraus K).choi = KrausFamily.choi K :=
  rfl

/-- Every intrinsic finite-dimensional CP map has a finite Kraus
presentation.  No choice of presentation is exposed as semantic data. -/
noncomputable def toKraus (Φ : CPMap n m) : KrausFamily n m :=
  Classical.choose (KrausFamily.exists_krausFamily_choi_eq Φ.choi_pos)

@[simp]
theorem choi_toKraus (Φ : CPMap n m) :
    KrausFamily.choi (toKraus Φ) = Φ.choi :=
  Classical.choose_spec
    (KrausFamily.exists_krausFamily_choi_eq Φ.choi_pos)

@[simp]
theorem ofKraus_toKraus (Φ : CPMap n m) : ofKraus (toKraus Φ) = Φ :=
  ext (choi_toKraus Φ)

theorem ofKraus_eq_iff (K L : KrausFamily n m) :
    ofKraus K = ofKraus L ↔ KrausFamily.SemEq K L := by
  rw [KrausFamily.semEq_iff_choi_eq]
  exact ⟨fun h => congrArg choi h, fun h => ext h⟩

/-- Application to an arbitrary matrix. -/
noncomputable def applyMat (Φ : CPMap n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  KrausFamily.applyMat (toKraus Φ) ρ

@[simp]
theorem applyMat_ofKraus (K : KrausFamily n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat (ofKraus K) ρ = KrausFamily.applyMat K ρ := by
  apply KrausFamily.semEq_of_choi_eq
  simp

theorem ext_apply {Φ Ψ : CPMap n m}
    (h : ∀ ρ, applyMat Φ ρ = applyMat Ψ ρ) : Φ = Ψ := by
  apply ext
  rw [← choi_toKraus Φ, ← choi_toKraus Ψ]
  exact KrausFamily.choi_eq_of_semEq h

theorem applyMat_posSemidef (Φ : CPMap n m)
    {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.PosSemidef) :
    (applyMat Φ ρ).PosSemidef :=
  KrausFamily.applyMat_posSemidef (toKraus Φ) hρ

theorem applyMat_add (Φ : CPMap n m)
    (ρ σ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat Φ (ρ + σ) = applyMat Φ ρ + applyMat Φ σ :=
  KrausFamily.applyMat_add (toKraus Φ) ρ σ

theorem applyMat_smul (Φ : CPMap n m) (c : ℂ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat Φ (c • ρ) = c • applyMat Φ ρ :=
  KrausFamily.applyMat_smul (toKraus Φ) c ρ

/-- The intrinsic input effect, obtained by tracing the Choi matrix over its
output coordinate.  The transposed input coordinates agree with `∑ᵢ Aᵢ†Aᵢ`. -/
def effect (Φ : CPMap n m) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ∑ a, Φ.choi (a, j) (a, i)

@[simp]
theorem effect_ofKraus (K : KrausFamily n m) :
    effect (ofKraus K) = KrausFamily.effect K := by
  ext i j
  induction K with
  | nil => simp [effect, KrausFamily.effect, KrausFamily.choi]
  | cons A K ih =>
    simp only [effect, choi_ofKraus, KrausFamily.choi_cons,
      Matrix.add_apply, Finset.sum_add_distrib, KrausFamily.effect,
      List.map_cons, List.sum_cons]
    change (∑ a, KrausFamily.choiTerm A (a, j) (a, i)) +
      effect (ofKraus K) i j =
        (Aᴴ * A) i j + KrausFamily.effect K i j
    rw [ih]
    apply congrArg (· + KrausFamily.effect K i j)
    simp only [KrausFamily.choiTerm, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro a _
    ring

theorem effect_posSemidef (Φ : CPMap n m) :
    Φ.effect.PosSemidef := by
  rw [← ofKraus_toKraus Φ, effect_ofKraus]
  exact KrausFamily.effect_posSemidef _

/-- Trace of an intrinsic CP action is pairing with its input effect. -/
theorem trace_applyMat_eq_effect (Φ : CPMap n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (applyMat Φ ρ) = Matrix.trace (Φ.effect * ρ) := by
  rw [← ofKraus_toKraus Φ, applyMat_ofKraus, effect_ofKraus]
  exact KrausFamily.trace_applyMat_eq_effect _ _

/-- Intrinsic finite-dimensional TNI is equivalent to the Choi partial trace
being below identity. -/
theorem effect_le_one_of_trace_nonincreasing (Φ : CPMap n m)
    (hΦ : ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (applyMat Φ ρ)).re ≤ (Matrix.trace ρ).re) :
    Φ.effect ≤ 1 := by
  let K := toKraus Φ
  have hK : ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (KrausFamily.applyMat K ρ)).re ≤
        (Matrix.trace ρ).re := by
    intro ρ hρ
    rw [← applyMat_ofKraus]
    simpa [K] using hΦ ρ hρ
  calc
    Φ.effect = effect (ofKraus K) := by
      change Φ.effect = effect (ofKraus (toKraus Φ))
      rw [ofKraus_toKraus]
    _ = KrausFamily.effect K := effect_ofKraus K
    _ ≤ 1 := KrausFamily.effect_le_one_of_trace_nonincreasing K hK

theorem trace_nonincreasing_of_effect_le_one (Φ : CPMap n m)
    (hΦ : Φ.effect ≤ 1) :
    ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (applyMat Φ ρ)).re ≤ (Matrix.trace ρ).re := by
  let K := toKraus Φ
  have hK : KrausFamily.effect K ≤ 1 := by
    rw [← effect_ofKraus]
    simpa [K] using hΦ
  intro ρ hρ
  rw [show applyMat Φ ρ = KrausFamily.applyMat K ρ by
    rw [← applyMat_ofKraus]
    simp [K]]
  exact KrausFamily.trace_nonincreasing_of_effect_le_one K hK ρ hρ

/-- The zero CP map. -/
def zero : CPMap n m :=
  ofKraus KrausFamily.zero

instance : Zero (CPMap n m) := ⟨zero⟩

@[simp]
theorem choi_zero : (0 : CPMap n m).choi = 0 := by
  exact KrausFamily.choi_nil

@[simp]
theorem applyMat_zero (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat (0 : CPMap n m) ρ = 0 := by
  rw [show (0 : CPMap n m) = ofKraus KrausFamily.zero from rfl,
    applyMat_ofKraus, KrausFamily.applyMat_zero]

/-- Addition of CP maps is addition of their Choi matrices. -/
def add (Φ Ψ : CPMap n m) : CPMap n m where
  choi := Φ.choi + Ψ.choi
  choi_pos := Φ.choi_pos.add Ψ.choi_pos

instance : Add (CPMap n m) := ⟨add⟩

@[simp]
theorem choi_add (Φ Ψ : CPMap n m) :
    (Φ + Ψ).choi = Φ.choi + Ψ.choi :=
  rfl

@[simp]
theorem ofKraus_append (K L : KrausFamily n m) :
    ofKraus (K ++ L) = ofKraus K + ofKraus L := by
  apply ext
  exact KrausFamily.choi_append K L

@[simp]
theorem applyMat_add_map (Φ Ψ : CPMap n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat (Φ + Ψ) ρ = applyMat Φ ρ + applyMat Ψ ρ := by
  have h :
      Φ + Ψ = ofKraus (toKraus Φ ++ toKraus Ψ) := by
    apply ext
    simp
  rw [h, applyMat_ofKraus, KrausFamily.applyMat_append]
  rfl

instance : AddCommMonoid (CPMap n m) where
  zero := 0
  add := (· + ·)
  zero_add Φ := ext (zero_add Φ.choi)
  add_zero Φ := ext (add_zero Φ.choi)
  add_assoc Φ Ψ Χ := ext (add_assoc Φ.choi Ψ.choi Χ.choi)
  add_comm Φ Ψ := ext (add_comm Φ.choi Ψ.choi)
  nsmul := nsmulRec

instance : OrderBot (CPMap n m) where
  bot := 0
  bot_le Φ := by
    change (0 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) ≤ Φ.choi
    rw [Matrix.le_iff]
    simpa using Φ.choi_pos

/-- Scaling by a nonnegative real preserves complete positivity. -/
noncomputable def scaleNonneg
    (c : ℝ) (hc : 0 ≤ c) (Φ : CPMap n m) : CPMap n m where
  choi := c • Φ.choi
  choi_pos := Φ.choi_pos.smul hc

@[simp]
theorem choi_scaleNonneg (c : ℝ) (hc : 0 ≤ c) (Φ : CPMap n m) :
    (scaleNonneg c hc Φ).choi = c • Φ.choi :=
  rfl

@[simp]
theorem scaleNonneg_zero (Φ : CPMap n m) :
    scaleNonneg 0 le_rfl Φ = 0 := by
  apply ext
  simp

@[simp]
theorem scaleNonneg_one (Φ : CPMap n m) :
    scaleNonneg 1 zero_le_one Φ = Φ := by
  apply ext
  simp

theorem scaleNonneg_add (c : ℝ) (hc : 0 ≤ c) (Φ Ψ : CPMap n m) :
    scaleNonneg c hc (Φ + Ψ) =
      scaleNonneg c hc Φ + scaleNonneg c hc Ψ := by
  apply ext
  simp [scaleNonneg, smul_add]

/-- Canonical nonnegative-real scalar multiplication on intrinsic CP maps. -/
noncomputable def nnsmul (c : NNReal) (Φ : CPMap n m) : CPMap n m where
  choi := (c : ℂ) • Φ.choi
  choi_pos :=
    Φ.choi_pos.smul
      (Complex.nonneg_iff.mpr ⟨c.property, by simp⟩)

noncomputable instance : SMul NNReal (CPMap n m) :=
  ⟨nnsmul⟩

@[simp]
theorem choi_nnsmul (c : NNReal) (Φ : CPMap n m) :
    (c • Φ).choi = (c : ℂ) • Φ.choi :=
  rfl

noncomputable instance : Module NNReal (CPMap n m) where
  one_smul Φ := by
    apply ext
    simp
  mul_smul c d Φ := by
    apply ext
    simp [mul_smul]
  smul_add c Φ Ψ := by
    apply ext
    simp [smul_add]
  smul_zero c := by
    apply ext
    simp
  add_smul c d Φ := by
    apply ext
    simp [add_smul]
  zero_smul Φ := by
    apply ext
    simp

@[simp]
theorem effect_nnsmul (c : NNReal) (Φ : CPMap n m) :
    effect (c • Φ) = (c : ℂ) • effect Φ := by
  ext i j
  simp [effect, Finset.mul_sum]

/-- Continuous linear operator represented by the input effect. -/
noncomputable def effectCLM (Φ : CPMap n m) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Φ.effect)

/-- Operator norm of the positive input effect. -/
noncomputable def effectNorm (Φ : CPMap n m) : ℝ :=
  ‖effectCLM Φ‖

theorem effectNorm_nonneg (Φ : CPMap n m) :
    0 ≤ effectNorm Φ :=
  norm_nonneg _

@[simp]
theorem effectCLM_nnsmul (c : NNReal) (Φ : CPMap n m) :
    effectCLM (c • Φ) = (c : ℂ) • effectCLM Φ := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toEuclideanLin (effect (c • Φ)) x = _
  rw [effect_nnsmul, map_smul]
  rfl

@[simp]
theorem effectNorm_nnsmul (c : NNReal) (Φ : CPMap n m) :
    effectNorm (c • Φ) = (c : ℝ) * effectNorm Φ := by
  rw [effectNorm, effectCLM_nnsmul, norm_smul]
  simp [effectNorm]

/-- The positive residual witnessing refinement of intrinsic CP maps. -/
def residualOfLE {Φ Ψ : CPMap n m} (h : Φ ≤ Ψ) : CPMap n m where
  choi := Ψ.choi - Φ.choi
  choi_pos := Matrix.le_iff.mp h

@[simp]
theorem add_residualOfLE {Φ Ψ : CPMap n m} (h : Φ ≤ Ψ) :
    Φ + residualOfLE h = Ψ := by
  apply ext
  simp [residualOfLE]

/-- Choi order is exactly existence of a completely positive residual. -/
theorem le_iff_exists_add (Φ Ψ : CPMap n m) :
    Φ ≤ Ψ ↔ ∃ Χ : CPMap n m, Φ + Χ = Ψ := by
  constructor
  · intro h
    exact ⟨residualOfLE h, add_residualOfLE h⟩
  · rintro ⟨Χ, rfl⟩
    change Φ.choi ≤ (Φ + Χ).choi
    rw [Matrix.le_iff]
    simpa using Χ.choi_pos

/-- Identity CP map. -/
def identity (n : ℕ) : CPMap n n :=
  ofKraus (KrausFamily.identity n)

/-- The identity channel is unital: its input effect is `I`. -/
@[simp]
theorem effect_identity (n : ℕ) : (identity n).effect = 1 := by
  rw [identity, effect_ofKraus]
  simp [KrausFamily.effect, KrausFamily.identity]

@[simp]
theorem applyMat_identity (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat (identity n) ρ = ρ := by
  simp [identity]

/-- Sequential composition, written in diagrammatic order: `comp Ψ Φ`
first applies `Φ`, then `Ψ`. -/
noncomputable def comp (Ψ : CPMap m ℓ) (Φ : CPMap n m) : CPMap n ℓ :=
  ofKraus (KrausFamily.comp (toKraus Ψ) (toKraus Φ))

@[simp]
theorem applyMat_comp (Ψ : CPMap m ℓ) (Φ : CPMap n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat (comp Ψ Φ) ρ = applyMat Ψ (applyMat Φ ρ) := by
  rw [comp, applyMat_ofKraus, KrausFamily.applyMat_comp]
  rfl

@[simp]
theorem identity_comp (Φ : CPMap n m) : comp (identity m) Φ = Φ := by
  apply ext_apply
  intro ρ
  simp

@[simp]
theorem comp_identity (Φ : CPMap n m) : comp Φ (identity n) = Φ := by
  apply ext_apply
  intro ρ
  simp

theorem comp_assoc (Χ : CPMap ℓ r) (Ψ : CPMap m ℓ) (Φ : CPMap n m) :
    comp Χ (comp Ψ Φ) = comp (comp Χ Ψ) Φ := by
  apply ext_apply
  intro ρ
  simp

theorem comp_add_left (Χ : CPMap m ℓ) (Φ Ψ : CPMap n m) :
    comp Χ (Φ + Ψ) = comp Χ Φ + comp Χ Ψ := by
  apply ext_apply
  intro ρ
  simp [applyMat_add]

theorem comp_add_right (Φ Ψ : CPMap m ℓ) (Χ : CPMap n m) :
    comp (Φ + Ψ) Χ = comp Φ Χ + comp Ψ Χ := by
  apply ext_apply
  intro ρ
  simp

@[simp]
theorem comp_zero_left (Φ : CPMap n m) :
    comp (0 : CPMap m ℓ) Φ = 0 := by
  apply ext_apply
  intro ρ
  simp

@[simp]
theorem comp_zero_right (Ψ : CPMap m ℓ) :
    comp Ψ (0 : CPMap n m) = 0 := by
  apply ext_apply
  intro ρ
  rw [applyMat_comp, applyMat_zero]
  simpa using
    (applyMat_smul Ψ (0 : ℂ) (0 : Matrix (Fin m) (Fin m) ℂ))

/-- Coordinate formula for intrinsic Choi composition. -/
theorem choi_comp_apply (Ψ : CPMap m ℓ) (Φ : CPMap n m)
    (a b : Fin ℓ) (i j : Fin n) :
    (comp Ψ Φ).choi (a, i) (b, j) =
      ∑ x, ∑ y, Ψ.choi (a, x) (b, y) * Φ.choi (x, i) (y, j) := by
  rw [comp, choi_ofKraus, KrausFamily.choi_comp_apply,
    choi_toKraus, choi_toKraus]

/-- The permutation that changes the Kronecker ordering
`(output₁,input₁,output₂,input₂)` into the Choi ordering
`(output₁,output₂,input₁,input₂)`. -/
def choiTensorEquiv (n m ℓ r : ℕ) :
    ((Fin m × Fin n) × (Fin r × Fin ℓ)) ≃
      (Fin (m * r) × Fin (n * ℓ)) where
  toFun p :=
    (finProdFinEquiv (p.1.1, p.2.1),
      finProdFinEquiv (p.1.2, p.2.2))
  invFun p :=
    (((finProdFinEquiv.symm p.1).1, (finProdFinEquiv.symm p.2).1),
      ((finProdFinEquiv.symm p.1).2, (finProdFinEquiv.symm p.2).2))
  left_inv := by
    rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩
    simp
  right_inv := by
    rintro ⟨i, j⟩
    apply Prod.ext
    · exact Equiv.apply_symm_apply finProdFinEquiv i
    · exact Equiv.apply_symm_apply finProdFinEquiv j

/-- Intrinsic tensor product of CP maps.  It is defined directly on Choi
matrices, with the canonical shuffle from Kronecker to Choi index order. -/
def tensor (Φ : CPMap n m) (Ψ : CPMap ℓ r) :
    CPMap (n * ℓ) (m * r) where
  choi :=
    Matrix.reindex (choiTensorEquiv n m ℓ r) (choiTensorEquiv n m ℓ r)
      (Φ.choi ⊗ₖ Ψ.choi)
  choi_pos := by
    simpa [Matrix.reindex_apply] using
      (Φ.choi_pos.kronecker Ψ.choi_pos).submatrix
        (choiTensorEquiv n m ℓ r).symm

/-- The intrinsic tensor is independent of every Kraus presentation: its Choi
matrix is exactly the shuffled Kronecker product of the two intrinsic Choi
matrices. -/
@[simp]
theorem choi_tensor (Φ : CPMap n m) (Ψ : CPMap ℓ r) :
    (tensor Φ Ψ).choi =
      Matrix.reindex (choiTensorEquiv n m ℓ r) (choiTensorEquiv n m ℓ r)
        (Φ.choi ⊗ₖ Ψ.choi) :=
  rfl

theorem tensor_congr {Φ Φ' : CPMap n m} {Ψ Ψ' : CPMap ℓ r}
    (hΦ : Φ = Φ') (hΨ : Ψ = Ψ') :
    tensor Φ Ψ = tensor Φ' Ψ' := by
  subst Φ'
  subst Ψ'
  rfl

/-- Tensor is additive in its first CP-map argument. -/
theorem tensor_add_left (Φ Φ' : CPMap n m) (Ψ : CPMap ℓ r) :
    tensor (Φ + Φ') Ψ = tensor Φ Ψ + tensor Φ' Ψ := by
  apply ext
  ext i j
  simp [tensor, Matrix.add_kronecker, Matrix.reindex_apply]

/-- Tensor is additive in its second CP-map argument. -/
theorem tensor_add_right (Φ : CPMap n m) (Ψ Ψ' : CPMap ℓ r) :
    tensor Φ (Ψ + Ψ') = tensor Φ Ψ + tensor Φ Ψ' := by
  apply ext
  ext i j
  simp [tensor, Matrix.kronecker_add, Matrix.reindex_apply]

@[simp]
theorem tensor_zero_left (Ψ : CPMap ℓ r) :
    tensor (0 : CPMap n m) Ψ = 0 := by
  apply ext
  simp [tensor]

@[simp]
theorem tensor_zero_right (Φ : CPMap n m) :
    tensor Φ (0 : CPMap ℓ r) = 0 := by
  apply ext
  simp [tensor]

/-- The input effect of a tensor is the shuffled Kronecker product of the
factor effects. -/
theorem effect_tensor (Φ : CPMap n m) (Ψ : CPMap ℓ r) :
    effect (tensor Φ Ψ) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (effect Φ ⊗ₖ effect Ψ) := by
  ext p q
  change (∑ a : Fin (m * r), (tensor Φ Ψ).choi (a, q) (a, p)) = _
  rw [← (finProdFinEquiv : Fin m × Fin r ≃ Fin (m * r)).sum_comp]
  simp only [choi_tensor, Matrix.reindex_apply, Matrix.submatrix_apply]
  dsimp [choiTensorEquiv]
  simp_rw [Equiv.symm_apply_apply]
  change (∑ a : Fin m × Fin r,
      Φ.choi (a.1, (finProdFinEquiv.symm q).1)
          (a.1, (finProdFinEquiv.symm p).1) *
        Ψ.choi (a.2, (finProdFinEquiv.symm q).2)
          (a.2, (finProdFinEquiv.symm p).2)) = _
  rw [Fintype.sum_prod_type]
  change (∑ a : Fin m, ∑ b : Fin r,
      Φ.choi (a, (finProdFinEquiv.symm q).1)
          (a, (finProdFinEquiv.symm p).1) *
        Ψ.choi (b, (finProdFinEquiv.symm q).2)
          (b, (finProdFinEquiv.symm p).2)) = _
  simp only [effect]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]

private theorem kronecker_le_one
    {E : Matrix (Fin n) (Fin n) ℂ} {F : Matrix (Fin ℓ) (Fin ℓ) ℂ}
    (hEpos : E.PosSemidef) (hEle : E ≤ 1) (hFle : F ≤ 1) :
    E ⊗ₖ F ≤ 1 := by
  rw [Matrix.le_iff]
  have hEq :
      (1 : Matrix (Fin n × Fin ℓ) (Fin n × Fin ℓ) ℂ) - E ⊗ₖ F =
        (1 - E) ⊗ₖ (1 : Matrix (Fin ℓ) (Fin ℓ) ℂ) +
          E ⊗ₖ (1 - F) := by
    rw [← Matrix.one_kronecker_one]
    ext ⟨i, k⟩ ⟨j, l⟩
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.kronecker_apply]
    ring
  rw [hEq]
  exact
    ((Matrix.le_iff.mp hEle).kronecker Matrix.PosSemidef.one).add
      (hEpos.kronecker (Matrix.le_iff.mp hFle))

private theorem reindex_le_one {a c : Type} [DecidableEq a] [DecidableEq c]
    (e : a ≃ c) {E : Matrix a a ℂ} (hE : E ≤ 1) :
    Matrix.reindex e e E ≤ 1 := by
  rw [Matrix.le_iff]
  have hp : (Matrix.submatrix (1 - E) e.symm e.symm).PosSemidef :=
    (Matrix.le_iff.mp hE).submatrix e.symm
  have heq :
      (1 : Matrix c c ℂ) - Matrix.reindex e e E =
        Matrix.submatrix (1 - E) e.symm e.symm := by
    ext i j
    simp [Matrix.reindex_apply, Matrix.one_apply]
  rw [heq]
  exact hp

/-- Tensoring two intrinsic TNI maps remains TNI.  The proof uses the effect
criterion, so its input may be entangled across the two factors. -/
theorem trace_nonincreasing_tensor (Φ : CPMap n m) (Ψ : CPMap ℓ r)
    (hΦ : ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (applyMat Φ ρ)).re ≤ (Matrix.trace ρ).re)
    (hΨ : ∀ ρ : Matrix (Fin ℓ) (Fin ℓ) ℂ, ρ.PosSemidef →
      (Matrix.trace (applyMat Ψ ρ)).re ≤ (Matrix.trace ρ).re) :
    ∀ ρ : Matrix (Fin (n * ℓ)) (Fin (n * ℓ)) ℂ, ρ.PosSemidef →
      (Matrix.trace (applyMat (tensor Φ Ψ) ρ)).re ≤
        (Matrix.trace ρ).re := by
  apply trace_nonincreasing_of_effect_le_one
  rw [effect_tensor]
  apply reindex_le_one
  exact kronecker_le_one Φ.effect_posSemidef
    (effect_le_one_of_trace_nonincreasing Φ hΦ)
    (effect_le_one_of_trace_nonincreasing Ψ hΨ)

/-- Tensor preserves sequential composition in both variables. -/
theorem tensor_comp {p q : ℕ}
    (Φ₂ : CPMap m p) (Φ₁ : CPMap n m)
    (Ψ₂ : CPMap r q) (Ψ₁ : CPMap ℓ r) :
    tensor (comp Φ₂ Φ₁) (comp Ψ₂ Ψ₁) =
      comp (tensor Φ₂ Ψ₂) (tensor Φ₁ Ψ₁) := by
  apply ext
  ext ai bj
  rcases ai with ⟨a, i⟩
  rcases bj with ⟨b, j⟩
  simp only [choi_tensor, Matrix.reindex_apply, Matrix.submatrix_apply]
  dsimp [choiTensorEquiv]
  rw [choi_comp_apply, choi_comp_apply, choi_comp_apply]
  simp_rw [
    ← (finProdFinEquiv : Fin m × Fin r ≃ Fin (m * r)).sum_comp]
  simp only [choi_tensor, Matrix.reindex_apply, Matrix.submatrix_apply]
  dsimp [choiTensorEquiv]
  simp_rw [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Tensor sends identity CP maps to the identity on the product dimension. -/
@[simp]
theorem tensor_identity (n ℓ : ℕ) :
    tensor (identity n) (identity ℓ) = identity (n * ℓ) := by
  apply ext
  ext p q
  rcases p with ⟨a, i⟩
  rcases q with ⟨b, j⟩
  simp only [choi_tensor, Matrix.reindex_apply, Matrix.submatrix_apply]
  dsimp [choiTensorEquiv, identity, KrausFamily.identity,
    KrausFamily.choi, KrausFamily.choiTerm]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  have split {x y : Fin (n * ℓ)} (h : x ≠ y) :
      (finProdFinEquiv.symm x).1 ≠ (finProdFinEquiv.symm y).1 ∨
      (finProdFinEquiv.symm x).2 ≠ (finProdFinEquiv.symm y).2 := by
    by_contra hxy
    push Not at hxy
    exact h (finProdFinEquiv.symm.injective (Prod.ext hxy.1 hxy.2))
  by_cases hai : a = i
  · subst i
    by_cases hbj : b = j
    · subst j
      simp [KrausFamily.choiTerm]
    · rcases split hbj with h | h
      · have h' : b.divNat ≠ j.divNat := by simpa using h
        simp [KrausFamily.choiTerm, Matrix.one_apply, h', hbj]
      · have h' : b.modNat ≠ j.modNat := by simpa using h
        simp [KrausFamily.choiTerm, Matrix.one_apply, h', hbj]
  · rcases split hai with h | h
    · have h' : a.divNat ≠ i.divNat := by simpa using h
      simp [KrausFamily.choiTerm, Matrix.one_apply, h', hai]
    · have h' : a.modNat ≠ i.modNat := by simpa using h
      simp [KrausFamily.choiTerm, Matrix.one_apply, h', hai]

/-- Convert the intrinsic map to the existing presentation-independent
antisymmetrization. -/
noncomputable def toCompleted (Φ : CPMap n m) : CompletedCP n m :=
  CompletedCP.ofKraus (toKraus Φ)

/-- Convert the existing antisymmetrized Kraus semantics to its intrinsic
Choi matrix. -/
noncomputable def ofCompleted (Φ : CompletedCP n m) : CPMap n m :=
  Quotient.lift
    (fun P : CPPresentation n m => ofKraus P.kraus)
    (fun P Q h => by
      apply ext
      apply le_antisymm
      · exact
          (KrausFamily.residualRefines_iff_choiRefines P.kraus Q.kraus).mp h.1
      · exact
          (KrausFamily.residualRefines_iff_choiRefines Q.kraus P.kraus).mp h.2)
    Φ

@[simp]
theorem ofCompleted_ofKraus (K : KrausFamily n m) :
    ofCompleted (CompletedCP.ofKraus K) = ofKraus K :=
  rfl

@[simp]
theorem ofCompleted_toCompleted (Φ : CPMap n m) :
    ofCompleted (toCompleted Φ) = Φ := by
  simp [toCompleted]

@[simp]
theorem toCompleted_ofCompleted (Φ : CompletedCP n m) :
    toCompleted (ofCompleted Φ) = Φ := by
  induction Φ using Antisymmetrization.induction_on with
  | _ P =>
      change
        CompletedCP.ofKraus (toKraus (ofKraus P.kraus)) =
          CompletedCP.ofKraus P.kraus
      apply CompletedCP.ofKraus_eq_of_semEq
      apply KrausFamily.semEq_of_choi_eq
      exact choi_toKraus (ofKraus P.kraus)

@[simp]
theorem toCompleted_ofKraus (K : KrausFamily n m) :
    toCompleted (ofKraus K) = CompletedCP.ofKraus K := by
  rw [← ofCompleted_ofKraus K, toCompleted_ofCompleted]

/-- Intrinsic Choi maps are equivalent to the existing completed Kraus
semantics. -/
noncomputable def completedEquiv : CPMap n m ≃ CompletedCP n m where
  toFun := toCompleted
  invFun := ofCompleted
  left_inv := ofCompleted_toCompleted
  right_inv := toCompleted_ofCompleted

end CPMap

end QLambda.Domain.Presheaf
