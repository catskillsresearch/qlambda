/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.RepresentableBipolar.BornRiesz

/-!
# Representable unit surjectivity and classical packaging

n=1 unit surjectivity, column lift, double-dual evaluation Hom, and
`representableClassicalObject`.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder InnerProductSpace Kronecker

universe u

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
