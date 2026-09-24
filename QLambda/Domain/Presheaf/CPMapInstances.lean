/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.CPMap
import QLambda.Domain.Presheaf.instLECPMap
import QLambda.Domain.Presheaf.instPartialOrderCPMap
import QLambda.Domain.Presheaf.instZeroCPMap
import QLambda.Domain.Presheaf.instAddCPMap
import QLambda.Domain.Presheaf.instAddCommMonoidCPMap
import QLambda.Domain.Presheaf.instOrderBotCPMap
import QLambda.Domain.Presheaf.instSMulNNRealCPMap
import QLambda.Domain.Presheaf.instModuleNNRealCPMap

/-!
# Instances from `CPMap`

Barrel re-exporting `QLambda.Domain.Presheaf.CPMap` and its typeclass instances.
-/

namespace QLambda.Domain.Presheaf
namespace CPMap

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder

variable {n m ℓ r : ℕ}

@[simp]
theorem applyMat_zero (ρ : Matrix (Fin n) (Fin n) ℂ) :
    applyMat (0 : CPMap n m) ρ = 0 := by
  rw [show (0 : CPMap n m) = ofKraus KrausFamily.zero from rfl,
    applyMat_ofKraus, KrausFamily.applyMat_zero]

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

/-- Scaling by a nonnegative real preserves complete positivity. -/
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
