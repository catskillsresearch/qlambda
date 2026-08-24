import QLambda.TTResultAlgebra
import QLambda.TTRoundedTheory

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace QLambda

namespace KrausFamily

variable {n m : ℕ}

theorem trace_choi_eq_trace_applyMat_one (K : KrausFamily n m) :
    Matrix.trace (choi K) =
      Matrix.trace (applyMat K (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  calc
    Matrix.trace (choi K) =
        ∑ a : Fin m, ∑ i : Fin n, choi K (a, i) (a, i) :=
      Fintype.sum_prod_type _
    _ = Matrix.trace (applyMat K (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      simp only [Matrix.trace, Matrix.diag_apply]
      simp_rw [applyMat_apply, Matrix.one_apply]
      simp

theorem choi_diagonal_re_le_input_dim (K : KrausFamily n m)
    (hK : ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (applyMat K ρ)).re ≤ (Matrix.trace ρ).re)
    (p : Fin m × Fin n) :
    0 ≤ (choi K p p).re ∧ (choi K p p).re ≤ n := by
  have hpos := choi_posSemidef K
  have hdiag : ∀ q : Fin m × Fin n, 0 ≤ (choi K q q).re := by
    intro q
    exact Complex.nonneg_iff.mp hpos.diag_nonneg |>.1
  constructor
  · exact hdiag p
  · have hp :
        (choi K p p).re ≤ ∑ q : Fin m × Fin n, (choi K q q).re := by
      simpa using Finset.single_le_sum
        (s := Finset.univ) (fun q _ => hdiag q) (Finset.mem_univ p)
    have htrace :
        (∑ q : Fin m × Fin n, (choi K q q).re) =
          (Matrix.trace (choi K)).re := by
      simp [Matrix.trace]
    rw [htrace] at hp
    exact hp.trans (by
      rw [trace_choi_eq_trace_applyMat_one]
      simpa using hK (1 : Matrix (Fin n) (Fin n) ℂ) Matrix.PosSemidef.one)

theorem two_mul_norm_choi_entry_le_diagonal (K : KrausFamily n m)
    (p q : Fin m × Fin n) :
    2 * ‖choi K p q‖ ≤ (choi K p p).re + (choi K q q).re := by
  induction K with
  | nil => simp [choi]
  | cons A K ih =>
    rw [choi_cons]
    simp only [Matrix.add_apply, choiTerm]
    calc
      2 * ‖A p.1 p.2 * star (A q.1 q.2) + choi K p q‖ ≤
          2 * (‖A p.1 p.2 * star (A q.1 q.2)‖ + ‖choi K p q‖) := by
        gcongr
        exact norm_add_le _ _
      _ ≤ (A p.1 p.2 * star (A p.1 p.2)).re +
          (A q.1 q.2 * star (A q.1 q.2)).re +
          ((choi K p p).re + (choi K q q).re) := by
        rw [mul_add]
        gcongr
        simp only [norm_mul, norm_star]
        rw [show (A p.1 p.2 * star (A p.1 p.2)).re =
              ‖A p.1 p.2‖ ^ 2 by
              simp [Complex.sq_norm, Complex.normSq_apply],
            show (A q.1 q.2 * star (A q.1 q.2)).re =
              ‖A q.1 q.2‖ ^ 2 by
              simp [Complex.sq_norm, Complex.normSq_apply]]
        simpa [mul_assoc] using
          two_mul_le_add_sq ‖A p.1 p.2‖ ‖A q.1 q.2‖
      _ = (A p.1 p.2 * star (A p.1 p.2) + choi K p p).re +
          (A q.1 q.2 * star (A q.1 q.2) + choi K q q).re := by
        simp
        ring

theorem norm_choi_entry_le_input_dim (K : KrausFamily n m)
    (hK : ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (applyMat K ρ)).re ≤ (Matrix.trace ρ).re)
    (p q : Fin m × Fin n) :
    ‖choi K p q‖ ≤ n := by
  have hp := (choi_diagonal_re_le_input_dim K hK p).2
  have hq := (choi_diagonal_re_le_input_dim K hK q).2
  have hpq := two_mul_norm_choi_entry_le_diagonal K p q
  linarith

end KrausFamily

namespace QuantumOperation

variable {n m : ℕ}

theorem choi_trace_le_input_dim (Φ : QuantumOperation n m) :
    (Matrix.trace (KrausFamily.choi Φ.kraus)).re ≤ n := by
  rw [KrausFamily.trace_choi_eq_trace_applyMat_one]
  simpa using Φ.trace_nonincreasing
    (1 : Matrix (Fin n) (Fin n) ℂ) Matrix.PosSemidef.one

end QuantumOperation

namespace FiniteInstrumentComp

variable {n : ℕ}

/-- A single branch of a finite instrument, regarded as a TNI operation. -/
noncomputable def branchOperation {D : Type*}
    (μ : FiniteInstrumentComp n D) (o : μ.Outcome) :
    QuantumOperation n n where
  kraus := μ.branch o
  trace_nonincreasing := by
    intro ρ hρ
    have hnonneg : ∀ i : μ.Outcome,
        0 ≤ (Matrix.trace (KrausFamily.applyMat (μ.branch i) ρ)).re := by
      intro i
      simpa [Matrix.trace] using
        (Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) =>
          (Complex.nonneg_iff.mp
            (KrausFamily.applyMat_posSemidef (μ.branch i) hρ).diag_nonneg).1)
    exact (Finset.single_le_sum (fun i _ => hnonneg i)
      (Finset.mem_univ o)).trans (μ.trace_nonincreasing ρ hρ)

def precomposeResult (Φ : QuantumOperation n n)
    (μ : FiniteInstrumentComp n PUnit.{1}) :
    FiniteInstrumentComp n PUnit.{1} :=
  (FiniteInstrumentComp.ofOperation Φ (PUnit.unit : PUnit.{1})).bind
    (fun _ => μ)

theorem totalOperation_precomposeResult_semEq
    (Φ : QuantumOperation n n) (μ : FiniteInstrumentComp n PUnit.{1}) :
    KrausFamily.SemEq (μ.precomposeResult Φ).totalOperation.kraus
      (QuantumOperation.comp μ.totalOperation Φ).kraus := by
  intro ρ
  rw [FiniteInstrumentComp.applyMat_totalOperation]
  change
    (∑ o, KrausFamily.applyMat ((μ.precomposeResult Φ).branch o) ρ) =
      KrausFamily.applyMat
        (KrausFamily.comp μ.totalOperation.kraus Φ.kraus) ρ
  rw [KrausFamily.applyMat_comp,
    FiniteInstrumentComp.applyMat_totalOperation]
  change
    (∑ p : Σ _ : Unit, μ.Outcome,
      KrausFamily.applyMat
        (KrausFamily.comp (μ.branch p.2) Φ.kraus) ρ) =
      ∑ o, KrausFamily.applyMat (μ.branch o)
        (KrausFamily.applyMat Φ.kraus ρ)
  rw [Fintype.sum_sigma]
  simp [KrausFamily.applyMat_comp]

end FiniteInstrumentComp

namespace TTResultApproximation

variable {n : ℕ}

def pulledVector (A : KrausOperator n n)
    (v : Fin n × Fin n → ℂ) : Fin n × Fin n → ℂ :=
  fun p => ∑ i, star (A p.2 i) * v (p.1, i)

theorem star_pulledVector (A : KrausOperator n n)
    (v : Fin n × Fin n → ℂ) (p : Fin n × Fin n) :
    star (pulledVector A v) p =
      ∑ i, star (v (p.1, i)) * A p.2 i := by
  change (starRingEnd ℂ) (∑ i, star (A p.2 i) * v (p.1, i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul]
  change star (star (A p.2 i)) * star (v (p.1, i)) = _
  rw [star_star]
  exact mul_comm _ _

private theorem sum_six_permute
    (f : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ a, ∑ i, ∑ b, ∑ j, ∑ x, ∑ y, f a i b j x y) =
      ∑ a, ∑ x, ∑ b, ∑ y, ∑ j, ∑ i, f a i b j x y := by
  apply Fintype.sum_congr
  intro a
  calc
    (∑ i, ∑ b, ∑ j, ∑ x, ∑ y, f a i b j x y) =
        ∑ b, ∑ i, ∑ j, ∑ x, ∑ y, f a i b j x y := Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ i, ∑ x, ∑ y, f a i b j x y := by
      apply Fintype.sum_congr
      intro b
      exact Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ x, ∑ i, ∑ y, f a i b j x y := by
      apply Fintype.sum_congr
      intro b
      apply Fintype.sum_congr
      intro j
      exact Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ x, ∑ y, ∑ i, f a i b j x y := by
      apply Fintype.sum_congr
      intro b
      apply Fintype.sum_congr
      intro j
      apply Fintype.sum_congr
      intro x
      exact Finset.sum_comm
    _ = ∑ b, ∑ x, ∑ j, ∑ y, ∑ i, f a i b j x y := by
      apply Fintype.sum_congr
      intro b
      exact Finset.sum_comm
    _ = ∑ x, ∑ b, ∑ j, ∑ y, ∑ i, f a i b j x y := Finset.sum_comm
    _ = ∑ x, ∑ b, ∑ y, ∑ j, ∑ i, f a i b j x y := by
      apply Fintype.sum_congr
      intro x
      apply Fintype.sum_congr
      intro b
      exact Finset.sum_comm

noncomputable def complexQuadratic (v : Fin n × Fin n → ℂ)
    (J : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) : ℂ :=
  star v ⬝ᵥ (J *ᵥ v)

theorem complexQuadratic_comp (L K : KrausFamily n n)
    (v : Fin n × Fin n → ℂ) :
    complexQuadratic v (KrausFamily.choi (KrausFamily.comp L K)) =
      (K.map fun A => complexQuadratic (pulledVector A v)
        (KrausFamily.choi L)).sum := by
  simp only [complexQuadratic, dotProduct, Matrix.mulVec]
  simp_rw [Fintype.sum_prod_type, KrausFamily.choi_comp_apply]
  induction K with
  | nil => simp [KrausFamily.choi]
  | cons A K ih =>
    simp only [List.map_cons, List.sum_cons, KrausFamily.choi_cons,
      Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
    rw [ih]
    simp_rw [pulledVector, star_pulledVector]
    simp only [KrausFamily.choiTerm, Finset.mul_sum, Finset.sum_mul]
    rw [add_left_inj]
    rw [sum_six_permute]
    simp only [Pi.star_apply]
    apply Fintype.sum_congr
    intro a
    apply Fintype.sum_congr
    intro x
    apply Fintype.sum_congr
    intro b
    apply Fintype.sum_congr
    intro y
    apply Fintype.sum_congr
    intro j
    apply Fintype.sum_congr
    intro i
    ring

noncomputable def quadraticErrorBound (x y : Fin n × Fin n → ℂ) : ℝ :=
  n * ((∑ p, ‖x p - y p‖) * (∑ q, ‖x q‖) +
    (∑ p, ‖y p‖) * (∑ q, ‖x q - y q‖))

theorem norm_complexQuadratic_sub_le (x y : Fin n × Fin n → ℂ)
    (J : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hJ : ∀ p q, ‖J p q‖ ≤ n) :
    ‖complexQuadratic x J - complexQuadratic y J‖ ≤
      quadraticErrorBound x y := by
  have hrearrange :
      complexQuadratic x J - complexQuadratic y J =
        ∑ p, ∑ q,
          ((star (x p) - star (y p)) * J p q * x q +
            star (y p) * J p q * (x q - y q)) := by
    simp only [complexQuadratic, dotProduct, Matrix.mulVec, Pi.star_apply,
      Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Fintype.sum_congr
    intro p
    rw [← Finset.sum_sub_distrib]
    apply Fintype.sum_congr
    intro q
    ring
  rw [hrearrange]
  calc
    ‖∑ p, ∑ q,
        ((star (x p) - star (y p)) * J p q * x q +
          star (y p) * J p q * (x q - y q))‖ ≤
        ∑ p, ‖∑ q,
          ((star (x p) - star (y p)) * J p q * x q +
            star (y p) * J p q * (x q - y q))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p, ∑ q,
          ‖(star (x p) - star (y p)) * J p q * x q +
            star (y p) * J p q * (x q - y q)‖ := by
      gcongr with p
      exact norm_sum_le _ _
    _ ≤ ∑ p, ∑ q,
          (‖x p - y p‖ * n * ‖x q‖ +
            ‖y p‖ * n * ‖x q - y q‖) := by
      gcongr with p q
      calc
        ‖(star (x p) - star (y p)) * J p q * x q +
            star (y p) * J p q * (x q - y q)‖ ≤
            ‖(star (x p) - star (y p)) * J p q * x q‖ +
              ‖star (y p) * J p q * (x q - y q)‖ :=
          norm_add_le _ _
        _ = ‖x p - y p‖ * ‖J p q‖ * ‖x q‖ +
              ‖y p‖ * ‖J p q‖ * ‖x q - y q‖ := by
          simp only [norm_mul, norm_star, ← star_sub]
        _ ≤ ‖x p - y p‖ * n * ‖x q‖ +
              ‖y p‖ * n * ‖x q - y q‖ := by
          gcongr <;> exact hJ p q
    _ = quadraticErrorBound x y := by
      have h₁ :
          (∑ p, ∑ q, ‖x p - y p‖ * n * ‖x q‖) =
            n * (∑ p, ‖x p - y p‖) * (∑ q, ‖x q‖) := by
        calc
          (∑ p, ∑ q, ‖x p - y p‖ * n * ‖x q‖) =
              ∑ p, ‖x p - y p‖ * (n * ∑ q, ‖x q‖) := by
            apply Fintype.sum_congr
            intro p
            rw [Finset.mul_sum]
            rw [Finset.mul_sum]
            apply Fintype.sum_congr
            intro q
            ring
          _ = (∑ p, ‖x p - y p‖) * (n * ∑ q, ‖x q‖) := by
            rw [Finset.sum_mul]
          _ = n * (∑ p, ‖x p - y p‖) * (∑ q, ‖x q‖) := by
            ring
      have h₂ :
          (∑ p, ∑ q, ‖y p‖ * n * ‖x q - y q‖) =
            n * (∑ p, ‖y p‖) * (∑ q, ‖x q - y q‖) := by
        calc
          (∑ p, ∑ q, ‖y p‖ * n * ‖x q - y q‖) =
              ∑ p, ‖y p‖ * (n * ∑ q, ‖x q - y q‖) := by
            apply Fintype.sum_congr
            intro p
            rw [Finset.mul_sum]
            rw [Finset.mul_sum]
            apply Fintype.sum_congr
            intro q
            ring
          _ = (∑ p, ‖y p‖) * (n * ∑ q, ‖x q - y q‖) := by
            rw [Finset.sum_mul]
          _ = n * (∑ p, ‖y p‖) * (∑ q, ‖x q - y q‖) := by
            ring
      simp only [Finset.sum_add_distrib, h₁, h₂, quadraticErrorBound]
      ring

theorem abs_re_complexQuadratic_sub_le (x y : Fin n × Fin n → ℂ)
    (J : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hJ : ∀ p q, ‖J p q‖ ≤ n) :
    |(complexQuadratic x J).re - (complexQuadratic y J).re| ≤
      quadraticErrorBound x y := by
  calc
    |(complexQuadratic x J).re - (complexQuadratic y J).re| =
        |(complexQuadratic x J - complexQuadratic y J).re| := by
      rw [Complex.sub_re]
    _ ≤ ‖complexQuadratic x J - complexQuadratic y J‖ :=
      Complex.abs_re_le_norm _
    _ ≤ quadraticErrorBound x y :=
      norm_complexQuadratic_sub_le x y J hJ

theorem continuous_quadraticErrorBound (x : Fin n × Fin n → ℂ) :
    Continuous (quadraticErrorBound x) := by
  apply Continuous.const_mul
  apply Continuous.add
  · apply Continuous.mul
    · apply continuous_finsetSum Finset.univ
      intro p _
      exact (continuous_const.sub (continuous_apply p)).norm
    · exact continuous_const
  · apply Continuous.mul
    · apply continuous_finsetSum Finset.univ
      intro p _
      exact (continuous_apply p).norm
    · apply continuous_finsetSum Finset.univ
      intro q _
      exact (continuous_const.sub (continuous_apply q)).norm

theorem quadraticErrorBound_self (x : Fin n × Fin n → ℂ) :
    quadraticErrorBound x x = 0 := by
  simp [quadraticErrorBound]

theorem exists_ratChoiVec_error_lt (x : Fin n × Fin n → ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : RatChoiVec n, quadraticErrorBound x v.toComplex < ε := by
  let f : (Fin n × Fin n → RatComplex) →
      (Fin n × Fin n → ℂ) :=
    Pi.map fun _ => RatComplex.toComplex
  have hf : DenseRange f :=
    DenseRange.piMap fun _ => RatComplex.denseRange_toComplex
  let U : Set (Fin n × Fin n → ℂ) :=
    {y | quadraticErrorBound x y < ε}
  have hUopen : IsOpen U :=
    isOpen_lt (continuous_quadraticErrorBound x) continuous_const
  have hxU : x ∈ U := by
    change quadraticErrorBound x x < ε
    rw [quadraticErrorBound_self]
    exact hε
  obtain ⟨q, hq⟩ := hf.exists_mem_open hUopen ⟨x, hxU⟩
  let v : RatChoiVec n := fun k => q (finProdFinEquiv.symm k)
  have hv : v.toComplex = f q := by
    funext i
    change (q (finProdFinEquiv.symm (finProdFinEquiv i))).toComplex =
      (q i).toComplex
    rw [Equiv.symm_apply_apply]
  exact ⟨v, by simpa [U, hv] using hq⟩

theorem complexQuadratic_add_real_smul (x w : Fin n × Fin n → ℂ)
    (J : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (c : ℝ) :
    complexQuadratic (x + (c : ℂ) • w) J =
      complexQuadratic x J +
        (c : ℂ) * (star x ⬝ᵥ (J *ᵥ w) + star w ⬝ᵥ (J *ᵥ x)) +
        (c : ℂ) ^ 2 * complexQuadratic w J := by
  simp only [complexQuadratic]
  rw [star_add, star_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
    add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct,
    dotProduct_smul]
  rw [smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  ring

theorem exists_positive_in_open_of_positive
    (J : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hJ : J.PosSemidef) (w : Fin n × Fin n → ℂ)
    (hw : 0 < (complexQuadratic w J).re)
    {U : Set (Fin n × Fin n → ℂ)} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ z ∈ U, 0 < (complexQuadratic z J).re := by
  obtain ⟨x, hxU⟩ := hUne
  by_cases hx : 0 < (complexQuadratic x J).re
  · exact ⟨x, hxU, hx⟩
  have hxnonneg : 0 ≤ (complexQuadratic x J).re := by
    exact hJ.re_dotProduct_nonneg x
  have hxzero : (complexQuadratic x J).re = 0 := le_antisymm (not_lt.mp hx) hxnonneg
  let path : ℝ → (Fin n × Fin n → ℂ) :=
    fun c => x + (c : ℂ) • w
  have hpath : Continuous path := by
    apply continuous_const.add
    exact (Complex.continuous_ofReal.comp continuous_id).smul continuous_const
  have hpre : IsOpen (path ⁻¹' U) := hpath.isOpen_preimage U hU
  have hzero : (0 : ℝ) ∈ path ⁻¹' U := by
    simpa [path] using hxU
  obtain ⟨η, hη, hball⟩ := (Metric.isOpen_iff.mp hpre) 0 hzero
  let cross : ℝ :=
    (star x ⬝ᵥ (J *ᵥ w) + star w ⬝ᵥ (J *ᵥ x)).re
  let c : ℝ := if 0 ≤ cross then η / 2 else -(η / 2)
  have hcabs : |c| = η / 2 := by
    dsimp [c]
    split
    · rw [abs_of_nonneg]
      linarith
    · rw [abs_neg, abs_of_nonneg]
      linarith
  have hcpos : 0 < |c| := by rw [hcabs]; linarith
  have hcdist : dist (0 : ℝ) c < η := by
    simpa [Real.dist_eq, hcabs] using (show η / 2 < η by linarith)
  have hcU : path c ∈ U := hball (by simpa [Metric.mem_ball] using hcdist)
  have hcs : 0 ≤ c * cross := by
    dsimp [c]
    split_ifs with hs
    · exact mul_nonneg (by linarith) hs
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith)
        (le_of_not_ge hs)
  have hc2 : 0 < c ^ 2 * (complexQuadratic w J).re := by
    exact mul_pos (sq_pos_of_ne_zero (abs_pos.mp hcpos)) hw
  refine ⟨path c, hcU, ?_⟩
  have hformula := congrArg Complex.re
    (complexQuadratic_add_real_smul x w J c)
  rw [← Complex.ofReal_pow] at hformula
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hformula
  rw [hformula, hxzero]
  change 0 < 0 + c * cross + c ^ 2 * (complexQuadratic w J).re
  linarith

theorem exists_ratChoiVec_error_lt_eval_pos
    (J : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hJ : J.PosSemidef) (w x : Fin n × Fin n → ℂ)
    (hw : 0 < (complexQuadratic w J).re)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : RatChoiVec n,
      quadraticErrorBound x v.toComplex < ε ∧
      0 < (complexQuadratic v.toComplex J).re := by
  let U : Set (Fin n × Fin n → ℂ) :=
    {y | quadraticErrorBound x y < ε}
  let V : Set (Fin n × Fin n → ℂ) :=
    {y | 0 < (complexQuadratic y J).re}
  have hU : IsOpen U :=
    isOpen_lt (continuous_quadraticErrorBound x) continuous_const
  have hxU : x ∈ U := by
    change quadraticErrorBound x x < ε
    rw [quadraticErrorBound_self]
    exact hε
  obtain ⟨z, hzU, hzV⟩ :=
    exists_positive_in_open_of_positive J hJ w hw hU ⟨x, hxU⟩
  have hV : IsOpen V :=
    isOpen_lt continuous_const (by
      simpa [complexQuadratic] using ChoiTest.continuous_quadratic J)
  have hUV : IsOpen (U ∩ V) := hU.inter hV
  let f : (Fin n × Fin n → RatComplex) →
      (Fin n × Fin n → ℂ) :=
    Pi.map fun _ => RatComplex.toComplex
  have hf : DenseRange f :=
    DenseRange.piMap fun _ => RatComplex.denseRange_toComplex
  obtain ⟨q, hq⟩ := hf.exists_mem_open hUV ⟨z, hzU, hzV⟩
  let v : RatChoiVec n := fun k => q (finProdFinEquiv.symm k)
  have hv : v.toComplex = f q := by
    funext i
    change (q (finProdFinEquiv.symm (finProdFinEquiv i))).toComplex =
      (q i).toComplex
    rw [Equiv.symm_apply_apply]
  exact ⟨v, by simpa [U, V, hv] using hq.1,
    by simpa [U, V, hv] using hq.2⟩

noncomputable def sourceAtom (post : RatStepPostCode n) (t : ChoiTest n) :
    TTObservationAtom n :=
  ⟨post, t⟩

noncomputable def sourceToken (post : RatStepPostCode n)
    (tests : List (ChoiTest n)) : TTObservationToken n :=
  tests.map (sourceAtom post)

noncomputable def sourceEval (post : RatStepPostCode n)
    (t : ChoiTest n) (μ : FiniteInstrumentComp n PUnit.{1}) : ℝ :=
  t.eval (KrausFamily.choi (μ.wpKraus (post.decode TTContinuation.resultCode)))

theorem norm_sourceChoi_entry_le_dim (post : RatStepPostCode n)
    (μ : FiniteInstrumentComp n PUnit.{1})
    (p q : Fin n × Fin n) :
    ‖KrausFamily.choi
        (μ.wpKraus (post.decode TTContinuation.resultCode)) p q‖ ≤ n :=
  KrausFamily.norm_choi_entry_le_input_dim
    (μ.wpKraus (post.decode TTContinuation.resultCode))
    (μ.wpKraus_result_trace_nonincreasing post) p q

theorem wpKraus_precomposeResult_semEq
    (Φ : QuantumOperation n n) (μ : FiniteInstrumentComp n PUnit.{1})
    (P : PUnit.{1} → KrausFamily n n) :
    KrausFamily.SemEq ((μ.precomposeResult Φ).wpKraus P)
      (KrausFamily.comp (μ.wpKraus P) Φ.kraus) := by
  apply KrausFamily.applySemEq_trans
    (FiniteInstrumentComp.wpKraus_bind_semEq
      (FiniteInstrumentComp.ofOperation Φ (PUnit.unit : PUnit.{1}))
      (fun _ => μ) P)
  intro ρ
  rw [FiniteInstrumentComp.applyMat_wpKraus]
  change (∑ _ : Unit,
      KrausFamily.applyMat
        (KrausFamily.comp (μ.wpKraus P) Φ.kraus) ρ) =
    KrausFamily.applyMat (KrausFamily.comp (μ.wpKraus P) Φ.kraus) ρ
  simp

noncomputable def targetEval (Φ : QuantumOperation n n)
    (a : TTObservationAtom n) (μ : FiniteInstrumentComp n PUnit.{1}) : ℝ :=
  a.choi.eval
    (KrausFamily.choi
      ((μ.precomposeResult Φ).wpKraus
        (a.post.decode TTContinuation.resultCode)))

theorem targetEval_eq_sum_pulled (Φ : QuantumOperation n n)
    (a : TTObservationAtom n) (μ : FiniteInstrumentComp n PUnit.{1}) :
    targetEval Φ a μ =
      (Φ.kraus.map fun A =>
        (complexQuadratic (pulledVector A a.choi.vector)
          (KrausFamily.choi
            (μ.wpKraus
              (a.post.decode TTContinuation.resultCode)))).re).sum := by
  have hsem := wpKraus_precomposeResult_semEq Φ μ
    (a.post.decode TTContinuation.resultCode)
  have hchoi := KrausFamily.choi_eq_of_semEq hsem
  rw [targetEval, ChoiTest.eval, hchoi]
  change (complexQuadratic a.choi.vector
    (KrausFamily.choi
      (KrausFamily.comp
        (μ.wpKraus (a.post.decode TTContinuation.resultCode))
        Φ.kraus))).re = _
  rw [complexQuadratic_comp]
  generalize Φ.kraus = K
  induction K with
  | nil => simp
  | cons A K ih => simp [ih]

private theorem choiTest_eval_list_sum (t : ChoiTest n)
    (Js : List (Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)) :
    t.eval Js.sum = (Js.map t.eval).sum := by
  induction Js with
  | nil => simp [ChoiTest.eval]
  | cons J Js ih =>
      simp only [List.sum_cons, List.map_cons]
      rw [← ih]
      simp [ChoiTest.eval, Matrix.add_mulVec, dotProduct_add]

private theorem choiTest_eval_comp (t : ChoiTest n)
    (L K : KrausFamily n n) :
    t.eval (KrausFamily.choi (KrausFamily.comp L K)) =
      (K.map fun A =>
        (complexQuadratic (pulledVector A t.vector)
          (KrausFamily.choi L)).re).sum := by
  change (complexQuadratic t.vector
    (KrausFamily.choi (KrausFamily.comp L K))).re = _
  rw [complexQuadratic_comp]
  induction K with
  | nil => simp
  | cons A K ih => simp [ih]

/-- A bind target is the sum of the targets contributed by the instrument
branches. -/
theorem targetEval_bind_eq_sum {D : Type*}
    [CompleteLattice D] (μ : FiniteInstrumentComp n D)
    (ν : D → FiniteInstrumentComp n PUnit.{1})
    (a : TTObservationAtom n) :
    a.choi.eval
        (KrausFamily.choi
          ((μ.bind ν).wpKraus
            (a.post.decode TTContinuation.resultCode))) =
      ∑ o : μ.Outcome,
        targetEval (μ.branchOperation o) a (ν (μ.value o)) := by
  classical
  let P := a.post.decode TTContinuation.resultCode
  have hbind := KrausFamily.choi_eq_of_semEq
    (FiniteInstrumentComp.wpKraus_bind_semEq μ ν P)
  rw [hbind]
  unfold FiniteInstrumentComp.wpKraus
  rw [FiniteInstrumentComp.choi_flatMap]
  rw [choiTest_eval_list_sum]
  simp_rw [targetEval_eq_sum_pulled]
  rw [List.map_map]
  have hlist (f : μ.Outcome → ℝ) :
      (Finset.univ.toList.map f).sum = ∑ o, f o := by
    rw [← List.sum_toFinset f (Finset.nodup_toList Finset.univ)]
    simp
  rw [hlist]
  apply Finset.sum_congr rfl
  intro o _
  change a.choi.eval
      (KrausFamily.choi
        (KrausFamily.comp
          ((ν (μ.value o)).wpKraus P)
          (μ.branch o))) =
    ((μ.branch o).map fun A =>
      (complexQuadratic (pulledVector A a.choi.vector)
        (KrausFamily.choi ((ν (μ.value o)).wpKraus P))).re).sum
  exact choiTest_eval_comp a.choi
    ((ν (μ.value o)).wpKraus P) (μ.branch o)

private theorem exists_mem_pos_of_sum_pos (xs : List ℝ)
    (h : 0 < xs.sum) : ∃ x ∈ xs, 0 < x := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      by_cases hx : 0 < x
      · exact ⟨x, by simp, hx⟩
      · have htail : 0 < xs.sum := by
          simp only [List.sum_cons] at h
          linarith
        obtain ⟨y, hy, hypos⟩ := ih htail
        exact ⟨y, by simp [hy], hypos⟩

private theorem exists_rational_threshold_tests
    {α : Type*} (value : α → ℝ) (xs : List α)
    (hpos : ∀ x ∈ xs, 0 < value x) {L : ℝ}
    (hL : L < (xs.map value).sum) :
    ∃ ts : List (α × NonnegRat),
      ts.map Prod.fst = xs ∧
      (∀ t ∈ ts, (t.2.1 : ℝ) < value t.1) ∧
      L < (ts.map fun t => (t.2.1 : ℝ)).sum := by
  induction xs generalizing L with
  | nil =>
      exact ⟨[], rfl, by simp, by simpa using hL⟩
  | cons x xs ih =>
      have hxpos : 0 < value x := hpos x (by simp)
      have hL' : L < value x + (xs.map value).sum := by
        simpa only [List.map_cons, List.sum_cons] using hL
      have hlower : max (0 : ℝ) (L - (xs.map value).sum) < value x := by
        apply max_lt hxpos
        linarith
      obtain ⟨q, hqlower, hqvalue⟩ := exists_rat_btwn hlower
      have hqnonneg : 0 ≤ q := by
        exact_mod_cast (show (0 : ℝ) ≤ (q : ℝ) from
          (le_max_left _ _).trans hqlower.le)
      let qr : NonnegRat := ⟨q, hqnonneg⟩
      have htail : L - (q : ℝ) < (xs.map value).sum := by
        have hq : L - (xs.map value).sum < (q : ℝ) :=
          (le_max_right _ _).trans_lt hqlower
        linarith
      obtain ⟨ts, hfst, hall, hsum⟩ :=
        ih (fun y hy => hpos y (by simp [hy])) htail
      refine ⟨(x, qr) :: ts, by simp [hfst], ?_, ?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact hqvalue
        · exact hall t ht
      · simp only [List.map_cons, List.sum_cons]
        dsimp [qr]
        linarith

private theorem abs_list_sum_le_sum_abs (xs : List ℝ) :
    |xs.sum| ≤ (xs.map abs).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.sum_cons, List.map_cons]
      exact (abs_add_le x xs.sum).trans (add_le_add (le_refl _) ih)

structure RationalLocalCertificate (Φ : QuantumOperation n n) where
  target : TTObservationAtom n
  tests : List (ChoiTest n)
  tests_nonempty : tests ≠ []
  error : ℝ
  error_nonneg : 0 ≤ error
  target_add_error_lt_threshold_sum :
    target.choi.threshold + error <
      (tests.map ChoiTest.threshold).sum
  uniform_error : ∀ μ : FiniteInstrumentComp n PUnit.{1},
    |(tests.map fun t => sourceEval target.post t μ).sum -
      targetEval Φ target μ| ≤ error

namespace RationalLocalCertificate

variable {Φ : QuantumOperation n n}

noncomputable def source (c : RationalLocalCertificate Φ) :
    TTObservationToken n :=
  sourceToken c.target.post c.tests

theorem source_holds_iff (c : RationalLocalCertificate Φ)
    (μ : FiniteInstrumentComp n PUnit.{1}) :
    TTObservationToken.Holds TTContinuation.resultCode c.source μ ↔
      ∀ t ∈ c.tests, t.threshold < sourceEval c.target.post t μ := by
  constructor
  · intro h t ht
    apply h (sourceAtom c.target.post t)
    · exact List.mem_map.mpr ⟨t, ht, rfl⟩
  · intro h a ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
    exact h t ht

theorem source_entails_target (c : RationalLocalCertificate Φ) :
    ∀ μ : FiniteInstrumentComp n PUnit.{1},
      TTObservationToken.Holds TTContinuation.resultCode c.source μ →
      TTObservationAtom.Holds TTContinuation.resultCode c.target
        (μ.precomposeResult Φ) := by
  intro μ hμ
  have hall : ∀ t ∈ c.tests,
      t.threshold ≤ sourceEval c.target.post t μ := by
    intro t ht
    exact ((c.source_holds_iff μ).mp hμ t ht).le
  have hex : ∃ t ∈ c.tests,
      t.threshold < sourceEval c.target.post t μ := by
    obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil c.tests c.tests_nonempty
    exact ⟨t, ht, (c.source_holds_iff μ).mp hμ t ht⟩
  have hsum :
      (c.tests.map ChoiTest.threshold).sum <
        (c.tests.map fun t => sourceEval c.target.post t μ).sum :=
    List.sum_lt_sum ChoiTest.threshold
      (fun t => sourceEval c.target.post t μ) hall hex
  have happ :
      (c.tests.map fun t => sourceEval c.target.post t μ).sum -
          targetEval Φ c.target μ ≤ c.error :=
    (le_abs_self _).trans (c.uniform_error μ)
  change c.target.choi.threshold < targetEval Φ c.target μ
  linarith [c.target_add_error_lt_threshold_sum, hsum]

theorem exists_source_of_certificate_at
    (c : RationalLocalCertificate Φ)
    (μ : FiniteInstrumentComp n PUnit.{1})
    (hμ : TTObservationToken.Holds TTContinuation.resultCode c.source μ) :
    ∃ s : TTObservationToken n,
      TTObservationToken.Holds TTContinuation.resultCode s μ ∧
      (∀ ν : FiniteInstrumentComp n PUnit.{1},
        TTObservationToken.Holds TTContinuation.resultCode s ν →
        TTObservationAtom.Holds TTContinuation.resultCode c.target
          (ν.precomposeResult Φ)) :=
  ⟨c.source, hμ, c.source_entails_target⟩

end RationalLocalCertificate

theorem exists_rationalLocalCertificate
    (Φ : QuantumOperation n n) (a : TTObservationAtom n)
    (μ : FiniteInstrumentComp n PUnit.{1})
    (hμ : TTObservationAtom.Holds TTContinuation.resultCode a
      (μ.precomposeResult Φ)) :
    ∃ c : RationalLocalCertificate Φ,
      c.target = a ∧
      TTObservationToken.Holds TTContinuation.resultCode c.source μ := by
  classical
  let Jμ := KrausFamily.choi
    (μ.wpKraus (a.post.decode TTContinuation.resultCode))
  let exactValue : KrausOperator n n → ℝ :=
    fun A => (complexQuadratic (pulledVector A a.choi.vector) Jμ).re
  have htarget : a.choi.threshold < targetEval Φ a μ := hμ
  have hsumpos : 0 < (Φ.kraus.map exactValue).sum := by
    rw [← targetEval_eq_sum_pulled Φ a μ]
    have hthreshold_nonneg : (0 : ℝ) ≤ a.choi.threshold := by
      change (0 : ℝ) ≤ (a.choi.2.1 : ℝ)
      exact_mod_cast a.choi.2.2
    exact hthreshold_nonneg.trans_lt htarget
  obtain ⟨r, hrmem, hrpos⟩ :=
    exists_mem_pos_of_sum_pos (Φ.kraus.map exactValue) hsumpos
  obtain ⟨Aw, hAw, rfl⟩ := List.mem_map.mp hrmem
  let witness := pulledVector Aw a.choi.vector
  have hwitness : 0 < (complexQuadratic witness Jμ).re := hrpos
  let margin : ℝ := targetEval Φ a μ - a.choi.threshold
  have hmargin : 0 < margin := sub_pos.mpr htarget
  let δ : ℝ := margin / (4 * ((Φ.kraus.length : ℝ) + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have happ : ∀ A : KrausOperator n n,
      ∃ v : RatChoiVec n,
        quadraticErrorBound (pulledVector A a.choi.vector) v.toComplex < δ ∧
        0 < (complexQuadratic v.toComplex Jμ).re := by
    intro A
    exact exists_ratChoiVec_error_lt_eval_pos Jμ
      (KrausFamily.choi_posSemidef _) witness
      (pulledVector A a.choi.vector) hwitness hδ
  choose v hvError hvPos using happ
  let vectors : List (RatChoiVec n) := Φ.kraus.map v
  let error : ℝ := Φ.kraus.length * δ
  have herror_nonneg : 0 ≤ error := by
    dsimp [error]
    positivity
  have htwice_error : 2 * error < margin := by
    have hk : (0 : ℝ) ≤ Φ.kraus.length := by positivity
    have hk1 : 0 < (Φ.kraus.length : ℝ) + 1 := by positivity
    have hfrac : (Φ.kraus.length : ℝ) /
        ((Φ.kraus.length : ℝ) + 1) < 1 := by
      rw [div_lt_one hk1]
      linarith
    dsimp [error, δ]
    rw [show (Φ.kraus.length : ℝ) *
          (margin / (4 * ((Φ.kraus.length : ℝ) + 1))) =
        margin / 4 *
          ((Φ.kraus.length : ℝ) /
            ((Φ.kraus.length : ℝ) + 1)) by
      field_simp]
    nlinarith
  have approx_error :
      ∀ ν : FiniteInstrumentComp n PUnit.{1},
        |(Φ.kraus.map fun A =>
            (complexQuadratic (v A).toComplex
              (KrausFamily.choi
                (ν.wpKraus
                  (a.post.decode TTContinuation.resultCode)))).re).sum -
          targetEval Φ a ν| ≤ error := by
    intro ν
    let Jν := KrausFamily.choi
      (ν.wpKraus (a.post.decode TTContinuation.resultCode))
    rw [targetEval_eq_sum_pulled]
    have hdiff :
        (Φ.kraus.map fun A => (complexQuadratic (v A).toComplex Jν).re).sum -
          (Φ.kraus.map fun A =>
            (complexQuadratic (pulledVector A a.choi.vector) Jν).re).sum =
          (Φ.kraus.map fun A =>
            (complexQuadratic (v A).toComplex Jν).re -
              (complexQuadratic (pulledVector A a.choi.vector) Jν).re).sum := by
      induction Φ.kraus with
      | nil => simp
      | cons A K ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [← ih]
          ring
    rw [hdiff]
    apply (abs_list_sum_le_sum_abs _).trans
    have hterms :
        (Φ.kraus.map fun A =>
          |(complexQuadratic (v A).toComplex Jν).re -
            (complexQuadratic (pulledVector A a.choi.vector) Jν).re|).sum ≤
          Φ.kraus.length * δ := by
      induction Φ.kraus with
      | nil => simp
      | cons A K ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons,
            Nat.cast_add, Nat.cast_one]
          have hA :
              |(complexQuadratic (v A).toComplex Jν).re -
                (complexQuadratic
                  (pulledVector A a.choi.vector) Jν).re| ≤ δ := by
            rw [abs_sub_comm]
            exact (abs_re_complexQuadratic_sub_le
              (pulledVector A a.choi.vector) (v A).toComplex Jν
              (fun p q => norm_sourceChoi_entry_le_dim a.post ν p q)).trans
                (hvError A).le
          nlinarith
    simpa [List.map_map, Function.comp_def, error] using hterms
  have hsourceSum :
      a.choi.threshold + error <
        (vectors.map fun rv =>
          (complexQuadratic rv.toComplex Jμ).re).sum := by
    have happμ := approx_error μ
    have happμ' :
        |(vectors.map fun rv =>
            (complexQuadratic rv.toComplex Jμ).re).sum -
          targetEval Φ a μ| ≤ error := by
      dsimp [vectors, Jμ]
      rw [List.map_map]
      simpa only [Function.comp_def] using happμ
    have hlower :
        targetEval Φ a μ - error ≤
          (vectors.map fun rv =>
            (complexQuadratic rv.toComplex Jμ).re).sum := by
      linarith [happμ', neg_abs_le
        ((vectors.map fun rv =>
          (complexQuadratic rv.toComplex Jμ).re).sum -
            targetEval Φ a μ)]
    dsimp [margin] at htwice_error
    linarith
  have hvectors_pos : ∀ rv ∈ vectors,
      0 < (complexQuadratic rv.toComplex Jμ).re := by
    intro rv hrv
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hrv
    exact hvPos A
  obtain ⟨tests, htests_vectors, htests_pos, htests_sum⟩ :=
    exists_rational_threshold_tests
      (fun rv : RatChoiVec n => (complexQuadratic rv.toComplex Jμ).re)
      vectors hvectors_pos hsourceSum
  have htests_ne : tests ≠ [] := by
    intro hnil
    have hvnil : vectors = [] := by simpa [hnil] using htests_vectors.symm
    have hknil : Φ.kraus = [] := by
      simpa [vectors] using hvnil
    simp [hknil] at hsumpos
  let c : RationalLocalCertificate Φ := {
    target := a
    tests := tests
    tests_nonempty := htests_ne
    error := error
    error_nonneg := herror_nonneg
    target_add_error_lt_threshold_sum := htests_sum
    uniform_error := by
      intro ν
      have happν := approx_error ν
      have hevals :
          (tests.map fun t => sourceEval a.post t ν).sum =
            (vectors.map fun rv =>
              (complexQuadratic rv.toComplex
                (KrausFamily.choi
                  (ν.wpKraus
                    (a.post.decode TTContinuation.resultCode)))).re).sum := by
        calc
          (tests.map fun t => sourceEval a.post t ν).sum =
              ((tests.map Prod.fst).map fun rv =>
                (complexQuadratic rv.toComplex
                  (KrausFamily.choi
                    (ν.wpKraus
                      (a.post.decode TTContinuation.resultCode)))).re).sum := by
            simp [sourceEval, ChoiTest.eval, complexQuadratic,
              ChoiTest.vector, List.map_map, Function.comp_def]
          _ = _ := by rw [htests_vectors]
      rw [hevals]
      dsimp [vectors]
      rw [List.map_map]
      simpa only [Function.comp_def] using happν
  }
  refine ⟨c, rfl, ?_⟩
  rw [RationalLocalCertificate.source_holds_iff]
  intro t ht
  have htpos := htests_pos t ht
  change (t.2.1 : ℝ) < (complexQuadratic t.1.toComplex Jμ).re
  exact htpos

theorem exists_rational_source_token
    (Φ : QuantumOperation n n) (a : TTObservationAtom n)
    (μ : FiniteInstrumentComp n PUnit.{1})
    (hμ : TTObservationAtom.Holds TTContinuation.resultCode a
      (μ.precomposeResult Φ)) :
    ∃ s : TTObservationToken n,
      TTObservationToken.Holds TTContinuation.resultCode s μ ∧
      ∀ ν : FiniteInstrumentComp n PUnit.{1},
        TTObservationToken.Holds TTContinuation.resultCode s ν →
        TTObservationAtom.Holds TTContinuation.resultCode a
          (ν.precomposeResult Φ) := by
  obtain ⟨c, rfl, hc⟩ := exists_rationalLocalCertificate Φ a μ hμ
  exact c.exists_source_of_certificate_at μ hc

noncomputable def tokenSource {Φ : QuantumOperation n n}
    (cs : List (RationalLocalCertificate Φ)) : TTObservationToken n :=
  cs.flatMap RationalLocalCertificate.source

theorem tokenSource_holds {Φ : QuantumOperation n n}
    (cs : List (RationalLocalCertificate Φ))
    (μ : FiniteInstrumentComp n PUnit.{1})
    (h : ∀ c ∈ cs,
      TTObservationToken.Holds TTContinuation.resultCode c.source μ) :
    TTObservationToken.Holds TTContinuation.resultCode (tokenSource cs) μ := by
  intro a ha
  obtain ⟨c, hc, hac⟩ := List.mem_flatMap.mp ha
  exact h c hc a hac

theorem tokenSource_entails_targets {Φ : QuantumOperation n n}
    (cs : List (RationalLocalCertificate Φ))
    (ν : FiniteInstrumentComp n PUnit.{1})
    (hν : TTObservationToken.Holds TTContinuation.resultCode
      (tokenSource cs) ν) :
    TTObservationToken.Holds TTContinuation.resultCode
      (cs.map RationalLocalCertificate.target) (ν.precomposeResult Φ) := by
  intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  apply c.source_entails_target ν
  intro b hb
  apply hν b
  exact List.mem_flatMap.mpr ⟨c, hc, hb⟩

theorem exists_source_token_of_certificates_at
    {Φ : QuantumOperation n n}
    (cs : List (RationalLocalCertificate Φ))
    (μ : FiniteInstrumentComp n PUnit.{1})
    (hμ : ∀ c ∈ cs,
      TTObservationToken.Holds TTContinuation.resultCode c.source μ) :
    ∃ s : TTObservationToken n,
      TTObservationToken.Holds TTContinuation.resultCode s μ ∧
      (∀ ν : FiniteInstrumentComp n PUnit.{1},
        TTObservationToken.Holds TTContinuation.resultCode s ν →
        TTObservationToken.Holds TTContinuation.resultCode
          (cs.map RationalLocalCertificate.target)
          (ν.precomposeResult Φ)) :=
  ⟨tokenSource cs, tokenSource_holds cs μ hμ,
    tokenSource_entails_targets cs⟩

theorem exists_precompose_source_token
    (Φ : QuantumOperation n n) (u : TTObservationToken n)
    (ν : FiniteInstrumentComp n PUnit.{1})
    (hu : TTObservationToken.Holds TTContinuation.resultCode u
      (ν.precomposeResult Φ)) :
    ∃ s : TTObservationToken n,
      TTObservationToken.Holds TTContinuation.resultCode s ν ∧
      ∀ ν' : FiniteInstrumentComp n PUnit.{1},
        TTObservationToken.Holds TTContinuation.resultCode s ν' →
        TTObservationToken.Holds TTContinuation.resultCode u
          (ν'.precomposeResult Φ) := by
  classical
  let cs : List (RationalLocalCertificate Φ) :=
    (u.attach.map fun ⟨a, ha⟩ =>
      Classical.choose (exists_rationalLocalCertificate Φ a ν (hu a ha)))
  have hμ : ∀ c ∈ cs,
      TTObservationToken.Holds TTContinuation.resultCode c.source ν := by
    intro c hc
    obtain ⟨⟨a, ha⟩, _, rfl⟩ := List.mem_map.mp hc
    exact (Classical.choose_spec
      (exists_rationalLocalCertificate Φ a ν (hu a ha))).2
  obtain ⟨s, hs, hall⟩ :=
    exists_source_token_of_certificates_at cs ν hμ
  refine ⟨s, hs, fun ν' hs' a ha => ?_⟩
  have hmem :
      Classical.choose
          (exists_rationalLocalCertificate Φ a ν (hu a ha)) ∈ cs := by
    refine List.mem_map.mpr ⟨⟨a, ha⟩, ?_, rfl⟩
    simp
  have hct :
      (Classical.choose
          (exists_rationalLocalCertificate Φ a ν (hu a ha))).target = a :=
    (Classical.choose_spec
      (exists_rationalLocalCertificate Φ a ν (hu a ha))).left
  exact hall ν' hs' a (List.mem_map.mpr ⟨_, hmem, hct⟩)

/-- A single observation of a finite bind has finitely many branch-local
source tokens which entail it. -/
theorem exists_bind_source_atoms {D : Type*} [CompleteLattice D]
    (μ : FiniteInstrumentComp n D) (a : TTObservationAtom n)
    (ν : D → FiniteInstrumentComp n PUnit.{1})
    (ha : TTObservationAtom.Holds TTContinuation.resultCode a (μ.bind ν)) :
    ∃ sources : μ.Outcome → TTObservationToken n,
      (∀ o, TTObservationToken.Holds TTContinuation.resultCode
        (sources o) (ν (μ.value o))) ∧
      ∀ ν' : D → FiniteInstrumentComp n PUnit.{1},
        (∀ o, TTObservationToken.Holds TTContinuation.resultCode
          (sources o) (ν' (μ.value o))) →
        TTObservationAtom.Holds TTContinuation.resultCode a (μ.bind ν') := by
  classical
  let value : μ.Outcome → ℝ := fun o =>
    targetEval (μ.branchOperation o) a (ν (μ.value o))
  have hvalue_nonneg (o : μ.Outcome) : 0 ≤ value o := by
    exact a.choi.eval_nonneg (KrausFamily.choi_posSemidef _)
  let positive : List μ.Outcome :=
    (Finset.univ.filter fun o => 0 < value o).toList
  have hpositive (o : μ.Outcome) (ho : o ∈ positive) : 0 < value o := by
    simpa [positive] using ho
  have hsum_value :
      (positive.map value).sum = ∑ o : μ.Outcome, value o := by
    have hlist :
        (positive.map value).sum =
          ∑ o ∈ Finset.univ.filter (fun o => 0 < value o), value o := by
      rw [← List.sum_toFinset value
        (Finset.nodup_toList (Finset.univ.filter fun o => 0 < value o))]
      simp
    rw [hlist]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro o _ ho
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ho
    exact le_antisymm (not_lt.mp ho) (hvalue_nonneg o)
  have hthreshold :
      a.choi.threshold < (positive.map value).sum := by
    rw [hsum_value, ← targetEval_bind_eq_sum μ ν a]
    exact ha
  obtain ⟨tests, htests_fst, htests_value, htests_sum⟩ :=
    exists_rational_threshold_tests value positive hpositive hthreshold
  have htests_ne : tests ≠ [] := by
    intro hnil
    have hqnonneg : 0 ≤ a.choi.threshold := by
      change (0 : ℝ) ≤ (a.choi.2.1 : ℝ)
      exact_mod_cast a.choi.2.2
    simp [hnil] at htests_sum
    linarith
  let componentAtom (t : μ.Outcome × NonnegRat) : TTObservationAtom n :=
    ⟨a.post, (a.choi.1, t.2)⟩
  have hcomponent (t : μ.Outcome × NonnegRat) (ht : t ∈ tests) :
      TTObservationAtom.Holds TTContinuation.resultCode (componentAtom t)
        ((ν (μ.value t.1)).precomposeResult (μ.branchOperation t.1)) := by
    change (t.2.1 : ℝ) < value t.1
    exact htests_value t ht
  let sourceFor (t : {t // t ∈ tests}) : TTObservationToken n :=
    Classical.choose
      (exists_rational_source_token (μ.branchOperation t.1.1)
        (componentAtom t.1) (ν (μ.value t.1.1)) (hcomponent t.1 t.2))
  have sourceFor_spec (t : {t // t ∈ tests}) :
      TTObservationToken.Holds TTContinuation.resultCode (sourceFor t)
          (ν (μ.value t.1.1)) ∧
        ∀ ξ : FiniteInstrumentComp n PUnit.{1},
          TTObservationToken.Holds TTContinuation.resultCode (sourceFor t) ξ →
          TTObservationAtom.Holds TTContinuation.resultCode
            (componentAtom t.1)
            (ξ.precomposeResult (μ.branchOperation t.1.1)) :=
    Classical.choose_spec
      (exists_rational_source_token (μ.branchOperation t.1.1)
        (componentAtom t.1) (ν (μ.value t.1.1)) (hcomponent t.1 t.2))
  let sources : μ.Outcome → TTObservationToken n := fun o =>
    (tests.attach.filter fun t => t.1.1 = o).flatMap sourceFor
  refine ⟨sources, ?_, ?_⟩
  · intro o b hb
    obtain ⟨t, ht, hbt⟩ := List.mem_flatMap.mp hb
    have hto : t.1.1 = o := by
      simpa [sources] using ht
    subst o
    exact (sourceFor_spec t).1 b hbt
  · intro ν' hsources
    have htest (t : {t // t ∈ tests}) :
        TTObservationAtom.Holds TTContinuation.resultCode
          (componentAtom t.1)
          ((ν' (μ.value t.1.1)).precomposeResult
            (μ.branchOperation t.1.1)) := by
      apply (sourceFor_spec t).2
      intro b hb
      apply hsources t.1.1 b
      apply List.mem_flatMap.mpr
      exact ⟨t, by simp, hb⟩
    have hterms : ∀ t ∈ tests,
        (t.2.1 : ℝ) ≤
          targetEval (μ.branchOperation t.1) a (ν' (μ.value t.1)) := by
      intro t ht
      exact (htest ⟨t, ht⟩).le
    have hex : ∃ t ∈ tests,
        (t.2.1 : ℝ) <
          targetEval (μ.branchOperation t.1) a (ν' (μ.value t.1)) := by
      obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil tests htests_ne
      exact ⟨t, ht, htest ⟨t, ht⟩⟩
    have hstrict :
        (tests.map fun t => (t.2.1 : ℝ)).sum <
          (tests.map fun t =>
            targetEval (μ.branchOperation t.1) a
              (ν' (μ.value t.1))).sum :=
      List.sum_lt_sum _ _ hterms hex
    have hselected :
        (tests.map fun t =>
            targetEval (μ.branchOperation t.1) a
              (ν' (μ.value t.1))).sum ≤
          ∑ o : μ.Outcome,
            targetEval (μ.branchOperation o) a (ν' (μ.value o)) := by
      let value' : μ.Outcome → ℝ := fun o =>
        targetEval (μ.branchOperation o) a (ν' (μ.value o))
      change (tests.map fun t => value' t.1).sum ≤ ∑ o, value' o
      have hmap :
          tests.map (fun t => value' t.1) =
            (tests.map Prod.fst).map value' := by
        rw [List.map_map]
        rfl
      rw [hmap, htests_fst]
      have hlist :
          (positive.map value').sum =
            ∑ o ∈ positive.toFinset, value' o := by
        rw [← List.sum_toFinset value'
          (Finset.nodup_toList (Finset.univ.filter fun o => 0 < value o))]
      rw [hlist]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro o ho
        simp
      · intro o _ _
        exact a.choi.eval_nonneg (KrausFamily.choi_posSemidef _)
    change a.choi.threshold <
      a.choi.eval
        (KrausFamily.choi
          ((μ.bind ν').wpKraus
            (a.post.decode TTContinuation.resultCode)))
    rw [targetEval_bind_eq_sum μ ν' a]
    linarith

/-- A finite token held by a bind has one finite source token at each
instrument outcome, uniformly entailing the target token. -/
theorem exists_bind_source_tokens {D : Type*} [CompleteLattice D]
    (μ : FiniteInstrumentComp n D) (u : TTObservationToken n)
    (ν : D → FiniteInstrumentComp n PUnit.{1})
    (hu : TTObservationToken.Holds TTContinuation.resultCode u (μ.bind ν)) :
    ∃ sources : μ.Outcome → TTObservationToken n,
      (∀ o, TTObservationToken.Holds TTContinuation.resultCode
        (sources o) (ν (μ.value o))) ∧
      ∀ ν' : D → FiniteInstrumentComp n PUnit.{1},
        (∀ o, TTObservationToken.Holds TTContinuation.resultCode
          (sources o) (ν' (μ.value o))) →
        TTObservationToken.Holds TTContinuation.resultCode u (μ.bind ν') := by
  classical
  let atomSources (p : {a // a ∈ u}) :
      μ.Outcome → TTObservationToken n :=
    Classical.choose (exists_bind_source_atoms μ p.1 ν (hu p.1 p.2))
  have atomSources_spec (p : {a // a ∈ u}) :
      (∀ o, TTObservationToken.Holds TTContinuation.resultCode
        (atomSources p o) (ν (μ.value o))) ∧
      ∀ ν' : D → FiniteInstrumentComp n PUnit.{1},
        (∀ o, TTObservationToken.Holds TTContinuation.resultCode
          (atomSources p o) (ν' (μ.value o))) →
        TTObservationAtom.Holds TTContinuation.resultCode p.1 (μ.bind ν') :=
    Classical.choose_spec
      (exists_bind_source_atoms μ p.1 ν (hu p.1 p.2))
  let sources : μ.Outcome → TTObservationToken n := fun o =>
    u.attach.flatMap fun p => atomSources p o
  refine ⟨sources, ?_, ?_⟩
  · intro o b hb
    obtain ⟨p, hp, hbp⟩ := List.mem_flatMap.mp hb
    exact (atomSources_spec p).1 o b hbp
  · intro ν' hsources a ha
    let p : {a // a ∈ u} := ⟨a, ha⟩
    apply (atomSources_spec p).2 ν'
    intro o b hb
    apply hsources o b
    exact List.mem_flatMap.mpr ⟨p, by simp, hb⟩

end TTResultApproximation

end QLambda
