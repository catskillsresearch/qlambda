/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Data.Fintype.Sigma
import Mathlib.Analysis.Real.Sqrt
import QLambda.QuantumStateSpace

/-!
# Finite quantum operations and instruments

A finite Kraus family denotes a completely positive map by the
operator-sum formula.  Trace non-increase is recorded separately; an
instrument is a finite family whose *total* outcome probability is
trace non-increasing.

`FiniteInstrumentComp` is the Type-level computational monad of a
fixed finite register with classical outcomes in `D`.  It is not a
complete lattice, so it is not yet an `IsQuantumPowerModel`.  The
Scott-complete instrument powerdomain is a later milestone.
-/

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace QLambda

/-- A linear operator from an `n`-dimensional register to an
`m`-dimensional register. -/
abbrev KrausOperator (n m : ℕ) :=
  Matrix (Fin m) (Fin n) ℂ

/-- A finite operator-sum presentation of a completely positive map. -/
abbrev KrausFamily (n m : ℕ) :=
  List (KrausOperator n m)

namespace KrausFamily

variable {n m : ℕ}

/-- Rank-one Choi contribution of one Kraus operator. -/
def choiTerm (A : KrausOperator n m) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  fun p q => A p.1 p.2 * star (A q.1 q.2)

/-- Choi matrix of a Kraus presentation.  Unlike the Kraus list, this
matrix is intrinsic to the represented completely positive map. -/
def choi (K : KrausFamily n m) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  (K.map choiTerm).sum

/-- The matrix action `ρ ↦ Σᵢ Kᵢ ρ Kᵢ†` of a finite Kraus family. -/
def applyMat (K : KrausFamily n m) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  (K.map fun A => A * ρ * Aᴴ).sum

/-- The empty family is the zero CP map. -/
def zero : KrausFamily n m :=
  []

/-- The identity channel's one-element Kraus presentation. -/
def identity (n : ℕ) : KrausFamily n n :=
  [1]

/-- Sequential composition of two operator-sum presentations. -/
def comp {ℓ : ℕ} (L : KrausFamily m ℓ) (K : KrausFamily n m) :
    KrausFamily n ℓ :=
  L.flatMap fun B => K.map fun A => B * A

/-- Scale every Kraus operator by a scalar. -/
def scale (c : ℂ) (K : KrausFamily n m) : KrausFamily n m :=
  K.map (c • ·)

@[simp] theorem choi_nil :
    choi ([] : KrausFamily n m) = 0 := by
  simp [choi]

@[simp] theorem choi_single (A : KrausOperator n m) :
    choi [A] = choiTerm A := by
  simp [choi]

theorem choi_cons (A : KrausOperator n m) (K : KrausFamily n m) :
    choi (A :: K) = choiTerm A + choi K := by
  simp [choi]

theorem choi_append (K L : KrausFamily n m) :
    choi (K ++ L) = choi K + choi L := by
  simp [choi, List.map_append, List.sum_append]

theorem choiTerm_posSemidef (A : KrausOperator n m) :
    (choiTerm A).PosSemidef := by
  let v : Fin m × Fin n → ℂ := fun p => A p.1 p.2
  change (Matrix.vecMulVec v (star v)).PosSemidef
  exact Matrix.posSemidef_vecMulVec_self_star v

theorem choi_posSemidef (K : KrausFamily n m) :
    (choi K).PosSemidef := by
  induction K with
  | nil => simpa using (Matrix.PosSemidef.zero :
      (0 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ).PosSemidef)
  | cons A K ih =>
      rw [choi_cons]
      exact (choiTerm_posSemidef A).add ih

theorem choi_nonneg (K : KrausFamily n m) : 0 ≤ choi K := by
  rw [Matrix.le_iff]
  simpa using choi_posSemidef K

/-- Equality of Choi denotations. -/
def ChoiSemEq (K L : KrausFamily n m) : Prop :=
  choi K = choi L

/-- The CP order: `K ⊑ L` when the Choi difference is positive
semidefinite. -/
def ChoiRefines (K L : KrausFamily n m) : Prop :=
  choi K ≤ choi L

/-- Extensional equality of the represented operator-sum maps. -/
def SemEq (K L : KrausFamily n m) : Prop :=
  ∀ ρ, applyMat K ρ = applyMat L ρ

/-- Presentation-independent CP refinement witnessed by a residual
Kraus family.  Thus `K ⊑ᵣ L` means `L = K + R` as CP maps. -/
def Refines (K L : KrausFamily n m) : Prop :=
  ∃ R : KrausFamily n m, SemEq L (K ++ R)

abbrev ApplySemEq := @SemEq
abbrev ResidualRefines := @Refines

theorem applySemEq_refl (K : KrausFamily n m) : ApplySemEq K K :=
  fun _ => rfl

theorem applySemEq_symm {K L : KrausFamily n m} :
    ApplySemEq K L → ApplySemEq L K :=
  fun h ρ => (h ρ).symm

theorem applySemEq_trans {K L M : KrausFamily n m}
    (hKL : ApplySemEq K L) (hLM : ApplySemEq L M) :
    ApplySemEq K M :=
  fun ρ => (hKL ρ).trans (hLM ρ)

theorem choiSemEq_iff_choiRefines (K L : KrausFamily n m) :
    ChoiSemEq K L ↔ ChoiRefines K L ∧ ChoiRefines L K := by
  simp only [ChoiSemEq, ChoiRefines]
  exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩

@[simp] theorem applyMat_zero (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat (zero : KrausFamily n m) ρ = 0 := by
  simp [applyMat, zero]

@[simp] theorem applyMat_nil (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat ([] : KrausFamily n m) ρ = 0 := by
  simp [applyMat]

@[simp] theorem applyMat_single (A : KrausOperator n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat [A] ρ = A * ρ * Aᴴ := by
  simp [applyMat]

theorem applyMat_cons (A : KrausOperator n m) (K : KrausFamily n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat (A :: K) ρ = A * ρ * Aᴴ + applyMat K ρ := by
  simp [applyMat]

theorem applyMat_append (K L : KrausFamily n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat (K ++ L) ρ = applyMat K ρ + applyMat L ρ := by
  induction K with
  | nil => simp [applyMat]
  | cons A K ih =>
    simp [applyMat_cons, ih, add_assoc]

theorem applyMat_flatMap {α : Type*} (xs : List α)
    (f : α → KrausFamily n m) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat (xs.flatMap f) ρ = (xs.map fun x => applyMat (f x) ρ).sum := by
  induction xs with
  | nil => simp [applyMat]
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
      rw [applyMat_append, ih]

theorem residualRefines_refl (K : KrausFamily n m) :
    ResidualRefines K K := by
  refine ⟨[], ?_⟩
  intro ρ
  simp

theorem residualRefines_of_semEq {K L : KrausFamily n m}
    (hKL : SemEq K L) : ResidualRefines K L := by
  refine ⟨[], fun ρ => ?_⟩
  simpa using (hKL ρ).symm

theorem residualRefines_antisymmRel_of_semEq {K L : KrausFamily n m}
    (hKL : SemEq K L) :
    AntisymmRel ResidualRefines K L :=
  ⟨residualRefines_of_semEq hKL,
    residualRefines_of_semEq (applySemEq_symm hKL)⟩

theorem residualRefines_trans {K L M : KrausFamily n m}
    (hKL : ResidualRefines K L) (hLM : ResidualRefines L M) :
    ResidualRefines K M := by
  obtain ⟨R, hR⟩ := hKL
  obtain ⟨S, hS⟩ := hLM
  refine ⟨R ++ S, fun ρ => ?_⟩
  rw [← List.append_assoc, applyMat_append, applyMat_append]
  calc
    applyMat M ρ = applyMat (L ++ S) ρ := hS ρ
    _ = applyMat L ρ + applyMat S ρ := applyMat_append L S ρ
    _ = applyMat (K ++ R) ρ + applyMat S ρ := congrArg (· + applyMat S ρ) (hR ρ)
    _ = (applyMat K ρ + applyMat R ρ) + applyMat S ρ := by
      rw [applyMat_append]

instance instIsPreorderResidualRefines :
    IsPreorder (KrausFamily n m) ResidualRefines where
  refl := residualRefines_refl
  trans _ _ _ := residualRefines_trans

@[simp] theorem applyMat_identity (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat (identity n) ρ = ρ := by
  simp [identity, applyMat]

theorem applyMat_add (K : KrausFamily n m)
    (ρ σ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat K (ρ + σ) = applyMat K ρ + applyMat K σ := by
  induction K with
  | nil => simp [applyMat]
  | cons A K ih =>
    rw [applyMat_cons, applyMat_cons, applyMat_cons, ih]
    have hA :
        A * (ρ + σ) * A.conjTranspose =
          A * ρ * A.conjTranspose + A * σ * A.conjTranspose := by
      let A' : Matrix (Fin m) (Fin n) ℂ := A
      change A' * (ρ + σ) * A'.conjTranspose =
        A' * ρ * A'.conjTranspose + A' * σ * A'.conjTranspose
      rw [Matrix.mul_add A' ρ σ, Matrix.add_mul (A' * ρ) (A' * σ) A'.conjTranspose]
    rw [hA]
    ac_rfl

theorem applyMat_smul (K : KrausFamily n m) (c : ℂ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat K (c • ρ) = c • applyMat K ρ := by
  induction K with
  | nil => simp [applyMat]
  | cons A K ih =>
    rw [applyMat_cons, applyMat_cons, ih]
    have : A * (c • ρ) * A.conjTranspose = c • (A * ρ * A.conjTranspose) := by
      let A' : Matrix (Fin m) (Fin n) ℂ := A
      change A' * (c • ρ) * A'.conjTranspose = c • (A' * ρ * A'.conjTranspose)
      rw [Matrix.mul_smul A' c ρ, Matrix.smul_mul c (A' * ρ) A'.conjTranspose]
    rw [this, smul_add]

theorem applyMat_sub (K : KrausFamily n m)
    (ρ σ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat K (ρ - σ) = applyMat K ρ - applyMat K σ := by
  rw [sub_eq_add_neg, applyMat_add, ← neg_one_smul ℂ σ, applyMat_smul,
    neg_one_smul, sub_eq_add_neg]

theorem applyMat_map_mul {ℓ : ℕ} (B : KrausOperator m ℓ)
    (K : KrausFamily n m) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat (K.map fun A => B * A) ρ = B * applyMat K ρ * Bᴴ := by
  induction K with
  | nil => simp [applyMat]
  | cons A K ih =>
    rw [List.map_cons, applyMat_cons, applyMat_cons, ih, conjTranspose_mul]
    have hA :
        B * A * ρ * (A.conjTranspose * B.conjTranspose) =
          B * (A * ρ * A.conjTranspose) * B.conjTranspose := by
      let A' : Matrix (Fin m) (Fin n) ℂ := A
      let B' : Matrix (Fin ℓ) (Fin m) ℂ := B
      simp [Matrix.mul_assoc]
    have hsum :
        B * (A * ρ * A.conjTranspose) * B.conjTranspose +
            B * applyMat K ρ * B.conjTranspose =
          B * (A * ρ * A.conjTranspose + applyMat K ρ) * B.conjTranspose := by
      let B' : Matrix (Fin ℓ) (Fin m) ℂ := B
      let X : Matrix (Fin m) (Fin m) ℂ := A * ρ * A.conjTranspose
      let Y : Matrix (Fin m) (Fin m) ℂ := applyMat K ρ
      change B' * X * B'.conjTranspose + B' * Y * B'.conjTranspose =
        B' * (X + Y) * B'.conjTranspose
      rw [Matrix.mul_add B' X Y, Matrix.add_mul (B' * X) (B' * Y) B'.conjTranspose]
    rw [hA, hsum]

theorem applyMat_comp {ℓ : ℕ} (L : KrausFamily m ℓ) (K : KrausFamily n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat (comp L K) ρ = applyMat L (applyMat K ρ) := by
  induction L with
  | nil => simp [comp, applyMat]
  | cons B L ih =>
    rw [comp, List.flatMap_cons, applyMat_append, applyMat_map_mul]
    change B * applyMat K ρ * Bᴴ + applyMat (comp L K) ρ =
      applyMat (B :: L) (applyMat K ρ)
    rw [ih, applyMat_cons]

theorem applyMat_scale (c : ℂ) (K : KrausFamily n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat (scale c K) ρ = (c * star c) • applyMat K ρ := by
  induction K with
  | nil => simp [scale, applyMat]
  | cons A K ih =>
    simp only [scale, List.map_cons, applyMat_cons] at ih ⊢
    rw [ih, conjTranspose_smul]
    have hA :
        (c • A) * ρ * (star c • A.conjTranspose) =
          (c * star c) • (A * ρ * A.conjTranspose) := by
      let A' : Matrix (Fin m) (Fin n) ℂ := A
      change (c • A') * ρ * (star c • A'.conjTranspose) =
        (c * star c) • (A' * ρ * A'.conjTranspose)
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
        mul_comm (star c) c]
    rw [hA, smul_add]

/-- The operator-sum of a Kraus family is completely positive. -/
theorem applyMat_posSemidef (K : KrausFamily n m)
    {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.PosSemidef) :
    (applyMat K ρ).PosSemidef := by
  induction K with
  | nil =>
    simpa [applyMat] using PosSemidef.zero (n := Fin m) (R := ℂ)
  | cons A K ih =>
    rw [applyMat_cons]
    exact (hρ.mul_mul_conjTranspose_same A).add ih

/-- Operator-sum is Loewner-monotone. -/
theorem applyMat_mono (K : KrausFamily n m)
    {ρ σ : Matrix (Fin n) (Fin n) ℂ} (h : ρ ≤ σ) :
    applyMat K ρ ≤ applyMat K σ := by
  change (applyMat K σ - applyMat K ρ).PosSemidef
  rw [← applyMat_sub]
  exact applyMat_posSemidef K h

@[simp] theorem identity_comp (K : KrausFamily n m) :
    comp (identity m) K = K := by
  simp [comp, identity]

@[simp] theorem comp_identity (K : KrausFamily n m) :
    comp K (identity n) = K := by
  simp [comp, identity]

theorem map_comp {ℓ r : ℕ} (C : KrausOperator ℓ r)
    (L : KrausFamily m ℓ) (K : KrausFamily n m) :
    (comp L K).map (fun A => C * A) = comp (L.map (fun B => C * B)) K := by
  induction L with
  | nil => simp [comp]
  | cons B L ih =>
    simp only [comp, List.flatMap_cons, List.map_append, List.map_map,
      Function.comp_def]
    have hmul :
        K.map (fun x => C * (B * x)) = K.map (fun A => C * B * A) :=
      List.map_congr_left fun a _ => by
        let C' : Matrix (Fin r) (Fin ℓ) ℂ := C
        let B' : Matrix (Fin ℓ) (Fin m) ℂ := B
        change C' * (B' * a) = C' * B' * a
        exact (Matrix.mul_assoc C' B' a).symm
    rw [hmul]
    change
      K.map (fun A => C * B * A) ++ (comp L K).map (fun A => C * A) =
        comp ((C * B) :: L.map (fun B => C * B)) K
    rw [ih]
    simp [comp, List.flatMap_cons]

theorem comp_append {ℓ : ℕ} (L₁ L₂ : KrausFamily m ℓ) (K : KrausFamily n m) :
    comp (L₁ ++ L₂) K = comp L₁ K ++ comp L₂ K := by
  simp [comp, List.flatMap_append]

theorem comp_assoc {ℓ r : ℕ} (M : KrausFamily ℓ r)
    (L : KrausFamily m ℓ) (K : KrausFamily n m) :
    comp M (comp L K) = comp (comp M L) K := by
  induction M with
  | nil => simp [comp]
  | cons C M ih =>
    change
      (comp L K).map (fun A => C * A) ++ comp M (comp L K) =
        comp (comp (C :: M) L) K
    rw [map_comp, ih, ← comp_append]
    rfl

/-- Residual CP refinement is preserved by postcomposition. -/
theorem residualRefines_comp_left {ℓ : ℕ} (M : KrausFamily m ℓ)
    {K L : KrausFamily n m} (hKL : ResidualRefines K L) :
    ResidualRefines (comp M K) (comp M L) := by
  obtain ⟨R, hR⟩ := hKL
  refine ⟨comp M R, fun ρ => ?_⟩
  rw [applyMat_append, applyMat_comp, applyMat_comp, applyMat_comp]
  calc
    applyMat M (applyMat L ρ) =
        applyMat M (applyMat (K ++ R) ρ) := congrArg (applyMat M) (hR ρ)
    _ = applyMat M (applyMat K ρ + applyMat R ρ) := by
      rw [applyMat_append]
    _ = applyMat M (applyMat K ρ) + applyMat M (applyMat R ρ) :=
      applyMat_add M _ _

/-- Residual CP refinement is preserved by precomposition. -/
theorem residualRefines_comp_right {ℓ : ℕ} (M : KrausFamily ℓ n)
    {K L : KrausFamily n m} (hKL : ResidualRefines K L) :
    ResidualRefines (comp K M) (comp L M) := by
  obtain ⟨R, hR⟩ := hKL
  refine ⟨comp R M, fun ρ => ?_⟩
  rw [← comp_append, applyMat_comp, applyMat_comp]
  exact hR (applyMat M ρ)

/-- Residual refinement is additive in the left summand. -/
theorem residualRefines_append_left (M : KrausFamily n m)
    {K L : KrausFamily n m} (hKL : ResidualRefines K L) :
    ResidualRefines (M ++ K) (M ++ L) := by
  obtain ⟨R, hR⟩ := hKL
  refine ⟨R, fun ρ => ?_⟩
  have hRρ := hR ρ
  rw [applyMat_append] at hRρ
  simp only [applyMat_append]
  calc
    applyMat M ρ + applyMat L ρ =
        applyMat M ρ + (applyMat K ρ + applyMat R ρ) :=
      congrArg (applyMat M ρ + ·) hRρ
    _ = (applyMat M ρ + applyMat K ρ) + applyMat R ρ :=
      (add_assoc _ _ _).symm

/-- Residual refinement is additive in the right summand. -/
theorem residualRefines_append_right (M : KrausFamily n m)
    {K L : KrausFamily n m} (hKL : ResidualRefines K L) :
    ResidualRefines (K ++ M) (L ++ M) := by
  obtain ⟨R, hR⟩ := hKL
  refine ⟨R, fun ρ => ?_⟩
  simp only [applyMat_append]
  calc
    applyMat L ρ + applyMat M ρ =
        (applyMat K ρ + applyMat R ρ) + applyMat M ρ := by
          rw [← applyMat_append K R, ← hR ρ]
    _ = (applyMat K ρ + applyMat M ρ) + applyMat R ρ := by
      ac_rfl

theorem residualRefines_append {K₁ K₂ L₁ L₂ : KrausFamily n m}
    (h₁ : ResidualRefines K₁ L₁) (h₂ : ResidualRefines K₂ L₂) :
    ResidualRefines (K₁ ++ K₂) (L₁ ++ L₂) :=
  residualRefines_trans
    (residualRefines_append_right K₂ h₁)
    (residualRefines_append_left L₁ h₂)

theorem residualRefines_flatMap {α : Type*} (xs : List α)
    {f g : α → KrausFamily n m}
    (hfg : ∀ x ∈ xs, ResidualRefines (f x) (g x)) :
    ResidualRefines (xs.flatMap f) (xs.flatMap g) := by
  induction xs with
  | nil =>
      exact residualRefines_refl []
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      exact residualRefines_append
        (hfg x (by simp))
        (ih fun y hy => hfg y (by simp [hy]))

/-- If `A` is an isometry (`A† A = I`), the one-element family is
trace-preserving. -/
theorem trace_applyMat_isometry {k : ℕ} (A : KrausOperator n k)
    (hA : Aᴴ * A = 1) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (applyMat [A] ρ) = Matrix.trace ρ := by
  rw [applyMat_single, Matrix.trace_mul_comm (A * ρ) Aᴴ, ← Matrix.mul_assoc,
    hA, Matrix.one_mul]

end KrausFamily

/-- A trace-nonincreasing completely positive map, represented by
finitely many Kraus operators. -/
structure QuantumOperation (n m : ℕ) where
  kraus : KrausFamily n m
  trace_nonincreasing :
    ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (KrausFamily.applyMat kraus ρ)).re ≤
        (Matrix.trace ρ).re

namespace QuantumOperation

/-- The identity quantum operation. -/
def identity (n : ℕ) : QuantumOperation n n where
  kraus := KrausFamily.identity n
  trace_nonincreasing := by
    intro ρ _
    rw [KrausFamily.applyMat_identity]

/-- The zero (completely forgetful) operation. -/
def zero (n m : ℕ) : QuantumOperation n m where
  kraus := KrausFamily.zero
  trace_nonincreasing := by
    intro ρ hρ
    have htr : 0 ≤ Matrix.trace ρ := PosSemidef.trace_nonneg hρ
    rw [KrausFamily.applyMat_zero, Matrix.trace_zero, Complex.zero_re]
    exact (RCLike.nonneg_iff (K := ℂ).mp htr).1

/-- Sequential composition of trace-nonincreasing CP maps. -/
def comp {n m ℓ : ℕ} (Ψ : QuantumOperation m ℓ) (Φ : QuantumOperation n m) :
    QuantumOperation n ℓ where
  kraus := KrausFamily.comp Ψ.kraus Φ.kraus
  trace_nonincreasing := by
    intro ρ hρ
    rw [KrausFamily.applyMat_comp]
    exact (Ψ.trace_nonincreasing _ (KrausFamily.applyMat_posSemidef Φ.kraus hρ)).trans
      (Φ.trace_nonincreasing ρ hρ)

/-- Action on a sub-normalized density. -/
def apply {n m : ℕ} (Φ : QuantumOperation n m) (ρ : SubNormalizedDensity n) :
    SubNormalizedDensity m where
  mat := KrausFamily.applyMat Φ.kraus ρ.mat
  posSemidef := KrausFamily.applyMat_posSemidef Φ.kraus ρ.posSemidef
  trace_le_one :=
    (Φ.trace_nonincreasing ρ.mat ρ.posSemidef).trans ρ.trace_le_one

/-- One-element family of an isometry is a quantum operation. -/
def ofIsometry {n m : ℕ} (A : KrausOperator n m) (hA : Aᴴ * A = 1) :
    QuantumOperation n m where
  kraus := [A]
  trace_nonincreasing := by
    intro ρ _
    rw [KrausFamily.trace_applyMat_isometry A hA]

end QuantumOperation

/-- A finite quantum instrument. Each outcome is CP, while trace
non-increase is required of the sum over all outcomes. -/
structure QuantumInstrument (n m outcomes : ℕ) where
  branch : Fin outcomes → KrausFamily n m
  trace_nonincreasing :
    ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (∑ i, (Matrix.trace (KrausFamily.applyMat (branch i) ρ)).re) ≤
        (Matrix.trace ρ).re

namespace QuantumInstrument

/-- Regard a quantum operation as a one-outcome instrument. -/
def singleton {n m : ℕ} (Φ : QuantumOperation n m) :
    QuantumInstrument n m 1 where
  branch := fun _ => Φ.kraus
  trace_nonincreasing := by
    intro ρ hρ
    simpa using Φ.trace_nonincreasing ρ hρ

end QuantumInstrument

/-- A finite `D`-valued computation on an `n`-dimensional register:
an instrument together with a classical outcome embedding into `D`.

This is a Type-level monad, not a complete lattice.  It therefore
cannot yet instantiate `IsQuantumPowerModel`. -/
structure FiniteInstrumentComp (n : ℕ) (D : Type*) where
  Outcome : Type
  [outcomeFintype : Fintype Outcome]
  branch : Outcome → KrausFamily n n
  value : Outcome → D
  trace_nonincreasing :
    ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (∑ o : Outcome, (Matrix.trace (KrausFamily.applyMat (branch o) ρ)).re) ≤
        (Matrix.trace ρ).re

attribute [instance] FiniteInstrumentComp.outcomeFintype

namespace FiniteInstrumentComp

variable {n : ℕ} {D E F : Type*}

/-- Outcome probability `Tr(Φ_o(ρ))`. -/
def outcomeProb (μ : FiniteInstrumentComp n D) (ρ : SubNormalizedDensity n)
    (o : μ.Outcome) : ℝ :=
  (Matrix.trace (KrausFamily.applyMat (μ.branch o) ρ.mat)).re

/-- Deterministic return of a classical value, leaving the register
untouched. -/
def unit (d : D) : FiniteInstrumentComp n D where
  Outcome := Unit
  branch := fun _ => KrausFamily.identity n
  value := fun _ => d
  trace_nonincreasing := by
    intro ρ _
    simp [KrausFamily.applyMat_identity]

/-- Post-compose classical outcomes. -/
def map (f : D → E) (μ : FiniteInstrumentComp n D) :
    FiniteInstrumentComp n E where
  Outcome := μ.Outcome
  outcomeFintype := μ.outcomeFintype
  branch := μ.branch
  value := f ∘ μ.value
  trace_nonincreasing := μ.trace_nonincreasing

@[simp] theorem map_id (μ : FiniteInstrumentComp n D) :
    map id μ = μ :=
  rfl

@[simp] theorem map_comp (g : E → F) (f : D → E) (μ : FiniteInstrumentComp n D) :
    map (g ∘ f) μ = map g (map f μ) :=
  rfl

/-- Kleisli extension: run `μ`, then the continuation at the returned
value.  Sequential composition of Kraus families implements the
quantum effect. -/
def bind (μ : FiniteInstrumentComp n D) (f : D → FiniteInstrumentComp n E) :
    FiniteInstrumentComp n E where
  Outcome := Σ o : μ.Outcome, (f (μ.value o)).Outcome
  outcomeFintype :=
    letI := μ.outcomeFintype
    letI : ∀ o : μ.Outcome, Fintype ((f (μ.value o)).Outcome) :=
      fun o => (f (μ.value o)).outcomeFintype
    inferInstance
  branch := fun p =>
    KrausFamily.comp ((f (μ.value p.1)).branch p.2) (μ.branch p.1)
  value := fun p => (f (μ.value p.1)).value p.2
  trace_nonincreasing := by
    intro ρ hρ
    let _ := μ.outcomeFintype
    let _ : ∀ o : μ.Outcome, Fintype ((f (μ.value o)).Outcome) :=
      fun o => (f (μ.value o)).outcomeFintype
    have hcont :
        ∀ o : μ.Outcome,
          (∑ o' : (f (μ.value o)).Outcome,
              (Matrix.trace
                (KrausFamily.applyMat
                  (KrausFamily.comp ((f (μ.value o)).branch o') (μ.branch o))
                  ρ)).re) ≤
            (Matrix.trace (KrausFamily.applyMat (μ.branch o) ρ)).re := by
      intro o
      have hpos := KrausFamily.applyMat_posSemidef (μ.branch o) hρ
      have hTNI := (f (μ.value o)).trace_nonincreasing
        (KrausFamily.applyMat (μ.branch o) ρ) hpos
      refine le_trans ?_ hTNI
      refine Finset.sum_le_sum ?_
      intro o' _
      rw [KrausFamily.applyMat_comp]
    calc
      (∑ p : (Σ o : μ.Outcome, (f (μ.value o)).Outcome),
          (Matrix.trace
            (KrausFamily.applyMat
              (KrausFamily.comp ((f (μ.value p.1)).branch p.2) (μ.branch p.1))
              ρ)).re)
          = ∑ o : μ.Outcome, ∑ o' : (f (μ.value o)).Outcome,
              (Matrix.trace
                (KrausFamily.applyMat
                  (KrausFamily.comp ((f (μ.value o)).branch o') (μ.branch o))
                  ρ)).re := by
            rw [Fintype.sum_sigma]
      _ ≤ ∑ o : μ.Outcome,
            (Matrix.trace (KrausFamily.applyMat (μ.branch o) ρ)).re :=
          Finset.sum_le_sum fun o _ => hcont o
      _ ≤ (Matrix.trace ρ).re :=
          μ.trace_nonincreasing ρ hρ

/-- Wrap a single quantum operation as a computation returning `d`. -/
def ofOperation (Φ : QuantumOperation n n) (d : D) :
    FiniteInstrumentComp n D where
  Outcome := Unit
  branch := fun _ => Φ.kraus
  value := fun _ => d
  trace_nonincreasing := by
    intro ρ hρ
    simpa using Φ.trace_nonincreasing ρ hρ

end FiniteInstrumentComp

namespace Qubit

/-- Pauli-X on a qubit. -/
def pauliX : KrausOperator 2 2 :=
  fun i j => if i = j then 0 else 1

theorem pauliX_conjTranspose : pauliXᴴ = pauliX := by
  ext i j
  simp [pauliX, conjTranspose]
  fin_cases i <;> fin_cases j <;> simp

theorem pauliX_mul_self : pauliXᴴ * pauliX = 1 := by
  rw [pauliX_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply]

/-- Pauli-X as a quantum operation. -/
def pauliXOp : QuantumOperation 2 2 :=
  QuantumOperation.ofIsometry pauliX pauliX_mul_self

/-- Computational-basis projector `|0⟩⟨0|`. -/
def proj0 : KrausOperator 2 2 :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- Computational-basis projector `|1⟩⟨1|`. -/
def proj1 : KrausOperator 2 2 :=
  fun i j => if i = 1 ∧ j = 1 then 1 else 0

theorem proj0_mul_self : proj0 * proj0 = proj0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, Matrix.mul_apply]

theorem proj1_mul_self : proj1 * proj1 = proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj1, Matrix.mul_apply]

theorem proj0_conjTranspose : proj0ᴴ = proj0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, conjTranspose]

theorem proj1_conjTranspose : proj1ᴴ = proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj1, conjTranspose]

theorem proj0_add_proj1 : proj0 + proj1 = (1 : KrausOperator 2 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, proj1]

theorem trace_proj_apply (P : KrausOperator 2 2)
    (hP : P * P = P) (hHerm : Pᴴ = P)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (KrausFamily.applyMat [P] ρ) = Matrix.trace (P * ρ) := by
  rw [KrausFamily.applyMat_single, Matrix.trace_mul_comm (P * ρ) Pᴴ, hHerm,
    ← Matrix.mul_assoc, hP]

/-- Computational-basis measurement as a two-outcome instrument. -/
def measureZ : QuantumInstrument 2 2 2 where
  branch := fun i => if i = 0 then [proj0] else [proj1]
  trace_nonincreasing := by
    intro ρ _
    have h0 := trace_proj_apply proj0 proj0_mul_self proj0_conjTranspose ρ
    have h1 := trace_proj_apply proj1 proj1_mul_self proj1_conjTranspose ρ
    have hsum :
        Matrix.trace (proj0 * ρ) + Matrix.trace (proj1 * ρ) =
          Matrix.trace ρ := by
      rw [← Matrix.trace_add, ← Matrix.add_mul, proj0_add_proj1, Matrix.one_mul]
    rw [Fin.sum_univ_two]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ↓reduceIte]
    rw [h0, h1, ← Complex.add_re, hsum]

/-- Computational-basis measurement returning a boolean. -/
def measureZComp : FiniteInstrumentComp 2 Bool where
  Outcome := Bool
  branch := fun b => if b then [proj1] else [proj0]
  value := id
  trace_nonincreasing := by
    intro ρ _
    have h0 := trace_proj_apply proj0 proj0_mul_self proj0_conjTranspose ρ
    have h1 := trace_proj_apply proj1 proj1_mul_self proj1_conjTranspose ρ
    have hsum :
        Matrix.trace (proj0 * ρ) + Matrix.trace (proj1 * ρ) =
          Matrix.trace ρ := by
      rw [← Matrix.trace_add, ← Matrix.add_mul, proj0_add_proj1, Matrix.one_mul]
    rw [Fintype.sum_bool]
    change
      (KrausFamily.applyMat [proj1] ρ).trace.re +
        (KrausFamily.applyMat [proj0] ρ).trace.re ≤ _
    rw [h1, h0, ← Complex.add_re, add_comm, hsum]

end Qubit

end QLambda
