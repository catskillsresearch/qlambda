import QLambda.Domain.Enriched
import QLambda.Domain.Presheaf.ClassicalCategory
import QLambda.Domain.Presheaf.SuperoperatorInstances
import QLambda.Domain.Presheaf.instPartialOrderSuperoperator
import QLambda.Domain.Presheaf.instOrderBotSuperoperator

/-!
# Choi-order ωCPO enrichment

Finite-dimensional trace-nonincreasing superoperators form pointed ωCPO
homs in Choi order.  Suprema are constructed by summing the positive
residuals of an increasing chain.  The trace bound makes those residuals
summable, and closedness of the finite-dimensional positive cone preserves
trace non-increase at the limit.  Composition is Scott-continuous in both
arguments by its finite Choi-coordinate formula.  The same order, taken
pointwise, makes maps into the Day tensor unit a pointed ωCPO, with
precomposition and postcomposition Scott-continuous.  The Day closed
pairing `Hom(M,N) ≃ Hom(M ⊗ ¬N, I)` transports that enrichment to
biorthogonal classical homs, yielding `biorthogonalOmegaCategory`.
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace Superoperator

/-- The positive residual between Choi-comparable TNI maps. -/
noncomputable def residual {n m : ℕ} {f g : Superoperator n m}
    (h : f ≤ g) : Superoperator n m :=
  Superoperator.ofLE (CPMap.residualOfLE h) g (by
    change g.cp.choi - f.cp.choi ≤ g.cp.choi
    rw [Matrix.le_iff]
    have heq : g.cp.choi - (g.cp.choi - f.cp.choi) = f.cp.choi := by
      abel
    rw [heq]
    exact f.cp.choi_pos)

@[simp]
theorem cp_residual {n m : ℕ} {f g : Superoperator n m} (h : f ≤ g) :
    (residual h).cp = CPMap.residualOfLE h :=
  rfl

theorem cp_add_residual {n m : ℕ} {f g : Superoperator n m} (h : f ≤ g) :
    f.cp + (residual h).cp = g.cp :=
  CPMap.add_residualOfLE h

/-- Positive increments of an increasing chain. -/
noncomputable def chainIncrement {n m : ℕ}
    (c : ℕ → Superoperator n m) (hc : Monotone c) :
    ℕ → Superoperator n m
  | 0 => c 0
  | k + 1 => residual (hc (Nat.le_succ k))

theorem sum_chainIncrement_cp {n m : ℕ}
    (c : ℕ → Superoperator n m) (hc : Monotone c) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (chainIncrement c hc k).cp =
      (c N).cp := by
  induction N with
  | zero => simp [chainIncrement]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      exact cp_add_residual (hc (Nat.le_succ N))

theorem trace_choi_eq_trace_effect {n m : ℕ} (f : CPMap n m) :
    Matrix.trace f.choi = Matrix.trace f.effect := by
  change (∑ p : Fin m × Fin n, f.choi p p) =
    ∑ i : Fin n, ∑ a : Fin m, f.choi (a, i) (a, i)
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem trace_choi_re_le_input_dim {n m : ℕ}
    (f : Superoperator n m) :
    (Matrix.trace f.cp.choi).re ≤ n := by
  have he :=
    CPMap.effect_le_one_of_trace_nonincreasing f.cp
      f.trace_nonincreasing
  have hp : (1 - f.cp.effect).PosSemidef := Matrix.le_iff.mp he
  have ht := hp.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_one] at ht
  have htre := (RCLike.nonneg_iff.mp ht).1
  rw [trace_choi_eq_trace_effect]
  simpa using htre

theorem choi_finset_sum {ι : Type} {n m : ℕ} [DecidableEq ι]
    (s : Finset ι) (f : ι → CPMap n m) :
    (∑ i ∈ s, f i).choi = ∑ i ∈ s, (f i).choi := by
  induction s using Finset.induction with
  | empty => simp [CPMap.choi_zero]
  | @insert a s ha ih => simp [ha, ih, CPMap.choi_add]

theorem trace_choi_finset_sum {ι : Type} {n m : ℕ}
    (s : Finset ι) (f : ι → CPMap n m) :
    Matrix.trace (∑ i ∈ s, f i).choi =
      ∑ i ∈ s, Matrix.trace (f i).choi := by
  classical
  induction s using Finset.induction with
  | empty => simp [CPMap.choi_zero]
  | @insert a s ha ih =>
      simp [ha, ih, CPMap.choi_add, Matrix.trace_add]

/-- Positive increments of every Choi-increasing TNI chain are summable. -/
theorem chainIncrement_summable {n m : ℕ}
    (c : ℕ → Superoperator n m) (hc : Monotone c) :
    Summable (fun k => (chainIncrement c hc k).cp.choi) := by
  let d := chainIncrement c hc
  let T : ℕ → ℝ := fun k => (Matrix.trace (d k).cp.choi).re
  have hTnonneg : 0 ≤ T :=
    fun k => SigmaMon.ChoiSum.trace_re_nonneg (d k).cp.choi_pos
  have hTsum : Summable T := by
    apply summable_of_sum_le hTnonneg (c := n)
    intro s
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst s
      simp
    · let N := s.max' hs
      have hsubset : s ⊆ Finset.range (N + 1) := by
        intro k hk
        exact Finset.mem_range.mpr
          (Nat.lt_succ_of_le (Finset.le_max' s k hk))
      calc
        ∑ k ∈ s, T k ≤ ∑ k ∈ Finset.range (N + 1), T k :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun i _ _ => hTnonneg i)
        _ = (Matrix.trace (c N).cp.choi).re := by
          rw [← sum_chainIncrement_cp c hc N]
          rw [trace_choi_finset_sum]
          change
            (∑ k ∈ Finset.range (N + 1),
              Complex.reCLM
                (Matrix.trace (chainIncrement c hc k).cp.choi)) =
              Complex.reCLM
                (∑ k ∈ Finset.range (N + 1),
                  Matrix.trace (chainIncrement c hc k).cp.choi)
          exact
            (map_sum Complex.reCLM
              (fun k =>
                Matrix.trace (chainIncrement c hc k).cp.choi)
              (Finset.range (N + 1))).symm
        _ ≤ n := trace_choi_re_le_input_dim (c N)
  apply Pi.summable.mpr
  intro i
  apply Pi.summable.mpr
  intro j
  apply Summable.of_norm_bounded hTsum
  intro k
  exact SigmaMon.ChoiSum.entry_norm_le_trace_re
    (chainIncrement c hc k).cp.choi_pos i j

/-- The linear operation taking a Choi matrix to its input effect. -/
noncomputable def effectLinearMap (n m : ℕ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin n) (Fin n) ℂ where
  toFun A := fun i j => ∑ a, A (a, j) (a, i)
  map_add' A B := by
    ext i j
    change
      (∑ a : Fin m, (A (a, j) (a, i) + B (a, j) (a, i))) = _
    rw [Finset.sum_add_distrib]
    rfl
  map_smul' c A := by
    ext i j
    change (∑ a : Fin m, (c * A (a, j) (a, i))) = _
    rw [← Finset.mul_sum]
    rfl

@[simp]
theorem effectLinearMap_choi {n m : ℕ} (f : CPMap n m) :
    effectLinearMap n m f.choi = f.effect :=
  rfl

/-- Choi-limit of an increasing TNI chain. -/
noncomputable def omegaSup {n m : ℕ}
    (c : ℕ → Superoperator n m) (hc : Monotone c) :
    Superoperator n m := by
  let d := chainIncrement c hc
  let A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
    ∑' k, (d k).cp.choi
  have hs : _root_.HasSum (fun k => (d k).cp.choi) A :=
    (chainIncrement_summable c hc).hasSum
  have hpos : A.PosSemidef :=
    SigmaMon.ChoiSum.hasSum_posSemidef hs
      (fun k => (d k).cp.choi_pos)
  let Φ : CPMap n m := ⟨A, hpos⟩
  refine ⟨Φ, CPMap.trace_nonincreasing_of_effect_le_one Φ ?_⟩
  have heff : _root_.HasSum
      (fun k => effectLinearMap n m (d k).cp.choi) Φ.effect := by
    change _root_.HasSum
      (fun k => effectLinearMap n m (d k).cp.choi)
      (effectLinearMap n m A)
    exact hs.map (effectLinearMap n m)
      (LinearMap.continuous_of_finiteDimensional _)
  have ht := heff.tendsto_sum_nat
  rw [Matrix.le_iff, Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · exact Matrix.isHermitian_one.sub Φ.effect_posSemidef.isHermitian
  · intro x
    let E : ℕ → Matrix (Fin n) (Fin n) ℂ := fun K =>
      ∑ k ∈ Finset.range K, effectLinearMap n m (d k).cp.choi
    have htE : Filter.Tendsto E Filter.atTop (nhds Φ.effect) := ht
    have hRpos (K : ℕ) : (1 - E K).PosSemidef := by
      cases K with
      | zero =>
          simpa [E] using
            (Matrix.PosSemidef.one :
              (1 : Matrix (Fin n) (Fin n) ℂ).PosSemidef)
      | succ K =>
          have hcp := sum_chainIncrement_cp c hc K
          have hchoi :
              ∑ k ∈ Finset.range (K + 1), (d k).cp.choi =
                (c K).cp.choi := by
            rw [← hcp]
            induction Finset.range (K + 1) using Finset.induction with
            | empty => simp
            | @insert a s ha ih =>
                simp [ha, ih, CPMap.choi_add, d]
          have heq : E (K + 1) = (c K).cp.effect := by
            change
              (∑ k ∈ Finset.range (K + 1),
                effectLinearMap n m (d k).cp.choi) = _
            rw [← map_sum (effectLinearMap n m)
              (fun k => (d k).cp.choi) (Finset.range (K + 1)),
              hchoi]
            rfl
          rw [heq]
          exact Matrix.le_iff.mp
            (CPMap.effect_le_one_of_trace_nonincreasing
              (c K).cp (c K).trace_nonincreasing)
    have htR : Filter.Tendsto (fun K => 1 - E K) Filter.atTop
        (nhds (1 - Φ.effect)) :=
      tendsto_const_nhds.sub htE
    have hentry (i j : Fin n) : Filter.Tendsto
        (fun K => (1 - E K) i j) Filter.atTop
        (nhds ((1 - Φ.effect) i j)) :=
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp htR i) j
    have hquad : Filter.Tendsto
        (fun K => star x ⬝ᵥ ((1 - E K) *ᵥ x)) Filter.atTop
        (nhds (star x ⬝ᵥ ((1 - Φ.effect) *ᵥ x))) := by
      simp only [dotProduct, mulVec]
      apply tendsto_finsetSum Finset.univ
      intro i hi
      apply tendsto_const_nhds.mul
      apply tendsto_finsetSum Finset.univ
      intro j hj
      exact (hentry i j).mul tendsto_const_nhds
    apply RCLike.nonneg_iff.mpr
    constructor
    · apply ge_of_tendsto
        (Complex.continuous_re.continuousAt.tendsto.comp hquad)
      exact Filter.Eventually.of_forall
        (fun K => (hRpos K).re_dotProduct_nonneg x)
    · have him : Filter.Tendsto
          (fun K => (star x ⬝ᵥ ((1 - E K) *ᵥ x)).im)
          Filter.atTop
          (nhds (star x ⬝ᵥ ((1 - Φ.effect) *ᵥ x)).im) :=
        Complex.continuous_im.continuousAt.tendsto.comp hquad
      have hzero : Filter.Tendsto
          (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds
      exact tendsto_nhds_unique_of_eventuallyEq him hzero
        (Filter.Eventually.of_forall fun K =>
          (RCLike.nonneg_iff.mp
            ((hRpos K).dotProduct_mulVec_nonneg x)).2)

end Superoperator

/-- Monotone convergence commutes with every defined countable Choi sum.
This is the finite-dimensional positive Fubini argument used below to take
pointwise suprema of natural transformations into the tensor unit. -/
theorem SigmaMon.ChoiSum.hasSum_omegaSup
    {ι : Type} [Countable ι] {n m : ℕ}
    (f : ℕ → ι → Superoperator n m)
    (g : ℕ → Superoperator n m)
    (hf : ∀ i, Monotone (fun k => f k i))
    (hg : Monotone g)
    (hsum : ∀ k, SigmaMon.ChoiSum.HasSum (f k) (g k)) :
    SigmaMon.ChoiSum.HasSum
      (fun i => Superoperator.omegaSup (fun k => f k i) (hf i))
      (Superoperator.omegaSup g hg) := by
  let d : ℕ → ι → Superoperator n m :=
    fun k i => Superoperator.chainIncrement (fun r => f r i) (hf i) k
  let e : ℕ → Superoperator n m :=
    Superoperator.chainIncrement g hg
  have hrows : ∀ k, SigmaMon.ChoiSum.HasSum (d k) (e k) := by
    intro k
    cases k with
    | zero =>
        exact hsum 0
    | succ k =>
        change _root_.HasSum
          (fun i =>
            (f (k + 1) i).cp.choi - (f k i).cp.choi)
          ((g (k + 1)).cp.choi - (g k).cp.choi)
        exact (hsum (k + 1)).sub (hsum k)
  have he :
      SigmaMon.ChoiSum.HasSum e (Superoperator.omegaSup g hg) :=
    (Superoperator.chainIncrement_summable g hg).hasSum
  have hflatSummable :
      Summable
        (fun p : Σ _ : ℕ, ι => (d p.1 p.2).cp.choi) :=
    SigmaMon.ChoiSum.regroupingComplete d e hrows
      (Superoperator.chainIncrement_summable g hg)
  have hflat :
      SigmaMon.ChoiSum.HasSum
        (fun p : Σ _ : ℕ, ι => d p.1 p.2)
        (Superoperator.omegaSup g hg) :=
    SigmaMon.ChoiSum.flatten_of_summable d e
      (Superoperator.omegaSup g hg) hrows he hflatSummable
  let swap : (Σ _ : ι, ℕ) ≃ (Σ _ : ℕ, ι) :=
    { toFun := fun p => ⟨p.2, p.1⟩
      invFun := fun p => ⟨p.2, p.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hswap :
      SigmaMon.ChoiSum.HasSum
        (fun p : Σ _ : ι, ℕ => d p.2 p.1)
        (Superoperator.omegaSup g hg) := by
    exact (SigmaMon.ChoiSum.reindex swap
      (fun p : Σ _ : ℕ, ι => d p.1 p.2)
      (Superoperator.omegaSup g hg)).2 hflat
  apply SigmaMon.ChoiSum.group
    (fun i k => d k i)
    (fun i => Superoperator.omegaSup (fun k => f k i) (hf i))
    (Superoperator.omegaSup g hg) hswap
  intro i
  exact (Superoperator.chainIncrement_summable
    (fun k => f k i) (hf i)).hasSum

/-- The positive cone of finite complex matrices is sequentially closed. -/
theorem posSemidef_of_tendsto {q : Type} [Fintype q]
    (A : ℕ → Matrix q q ℂ) (B : Matrix q q ℂ)
    (hA : ∀ k, (A k).PosSemidef)
    (hlim : Filter.Tendsto A Filter.atTop (nhds B)) :
    B.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    have hij := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim i) j
    have hji :=
      (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim j) i).star
    apply tendsto_nhds_unique hji
    apply hij.congr'
    exact Filter.Eventually.of_forall fun k =>
      (hA k).isHermitian.apply i j |>.symm
  · intro x
    have hentry (i j : q) : Filter.Tendsto
        (fun k => A k i j) Filter.atTop (nhds (B i j)) :=
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim i) j
    have hquad : Filter.Tendsto
        (fun k => star x ⬝ᵥ (A k *ᵥ x)) Filter.atTop
        (nhds (star x ⬝ᵥ (B *ᵥ x))) := by
      simp only [dotProduct, mulVec]
      apply tendsto_finsetSum Finset.univ
      intro i hi
      apply tendsto_const_nhds.mul
      apply tendsto_finsetSum Finset.univ
      intro j hj
      exact (hentry i j).mul tendsto_const_nhds
    apply RCLike.nonneg_iff.mpr
    constructor
    · apply ge_of_tendsto
        (Complex.continuous_re.continuousAt.tendsto.comp hquad)
      exact Filter.Eventually.of_forall
        (fun k => (hA k).re_dotProduct_nonneg x)
    · have him := Complex.continuous_im.continuousAt.tendsto.comp hquad
      exact tendsto_nhds_unique_of_eventuallyEq him tendsto_const_nhds
        (Filter.Eventually.of_forall fun k =>
          (RCLike.nonneg_iff.mp
            ((hA k).dotProduct_mulVec_nonneg x)).2)

namespace Superoperator

theorem le_omegaSup {n m : ℕ} (c : ℕ → Superoperator n m)
    (hc : Monotone c) (N : ℕ) :
    c N ≤ omegaSup c hc := by
  let d := chainIncrement c hc
  let F : ℕ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
    fun k => (d k).cp.choi
  have hs : Summable F := chainIncrement_summable c hc
  let s : Finset ℕ := Finset.range (N + 1)
  let R := ∑' k : Set.compl (↑s : Set ℕ), F k
  have hR : R.PosSemidef :=
    SigmaMon.ChoiSum.hasSum_posSemidef
      (hs.subtype (Set.compl (↑s : Set ℕ))).hasSum
      (fun k => (d k.1).cp.choi_pos)
  have hdecomp :=
    hs.tsum_subtype_add_tsum_subtype_compl (↑s : Set ℕ)
  have hprefix : ∑' k : (↑s : Set ℕ), F k = (c N).cp.choi := by
    change (∑' k : {k // k ∈ s}, F k) = _
    rw [Finset.tsum_subtype s F]
    have hcp := congrArg CPMap.choi (sum_chainIncrement_cp c hc N)
    rw [choi_finset_sum] at hcp
    simpa only [s, F, d] using hcp
  change (c N).cp.choi ≤ (omegaSup c hc).cp.choi
  rw [Matrix.le_iff]
  have htotal : ∑' k, F k = (omegaSup c hc).cp.choi := rfl
  rw [← htotal, ← hdecomp, hprefix, add_sub_cancel_left]
  exact hR

theorem omegaSup_le {n m : ℕ} (c : ℕ → Superoperator n m)
    (hc : Monotone c) (x : Superoperator n m)
    (hx : ∀ N, c N ≤ x) :
    omegaSup c hc ≤ x := by
  let d := chainIncrement c hc
  have hs : _root_.HasSum (fun k => (d k).cp.choi)
      (omegaSup c hc).cp.choi :=
    (chainIncrement_summable c hc).hasSum
  let P : ℕ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
    fun K => ∑ k ∈ Finset.range K, (d k).cp.choi
  have htP : Filter.Tendsto P Filter.atTop
      (nhds (omegaSup c hc).cp.choi) :=
    hs.tendsto_sum_nat
  have hpos (K : ℕ) : (x.cp.choi - P K).PosSemidef := by
    cases K with
    | zero => simpa [P] using x.cp.choi_pos
    | succ K =>
        have hcp := sum_chainIncrement_cp c hc K
        have heq : P (K + 1) = (c K).cp.choi := by
          change
            (∑ k ∈ Finset.range (K + 1), (d k).cp.choi) = _
          rw [← hcp]
          induction Finset.range (K + 1) using Finset.induction with
          | empty => simp
          | @insert a s ha ih =>
              simp [ha, ih, CPMap.choi_add, d]
        rw [heq]
        exact Matrix.le_iff.mp (hx K)
  change (omegaSup c hc).cp.choi ≤ x.cp.choi
  rw [Matrix.le_iff]
  exact posSemidef_of_tendsto
    (fun K => x.cp.choi - P K)
    (x.cp.choi - (omegaSup c hc).cp.choi) hpos
    (tendsto_const_nhds.sub htP)

theorem comp_mono_left {n m l : ℕ} (g : Superoperator n m) :
    Monotone (fun f : Superoperator m l => comp f g) := by
  intro f h hfh
  let r := residual hfh
  change CPMap.comp f.cp g.cp ≤ CPMap.comp h.cp g.cp
  apply (CPMap.le_iff_exists_add _ _).2
  refine ⟨CPMap.comp r.cp g.cp, ?_⟩
  rw [← CPMap.comp_add_right, cp_add_residual]

theorem comp_mono_right {n m l : ℕ} (f : Superoperator m l) :
    Monotone (fun g : Superoperator n m => comp f g) := by
  intro g h hgh
  let r := residual hgh
  change CPMap.comp f.cp g.cp ≤ CPMap.comp f.cp h.cp
  apply (CPMap.le_iff_exists_add _ _).2
  refine ⟨CPMap.comp f.cp r.cp, ?_⟩
  rw [← CPMap.comp_add_left, cp_add_residual]

theorem choi_tendsto_omegaSup {n m : ℕ}
    (c : ℕ → Superoperator n m) (hc : Monotone c) :
    Filter.Tendsto (fun N => (c N).cp.choi) Filter.atTop
      (nhds (omegaSup c hc).cp.choi) := by
  let d := chainIncrement c hc
  have hs : _root_.HasSum (fun k => (d k).cp.choi)
      (omegaSup c hc).cp.choi :=
    (chainIncrement_summable c hc).hasSum
  have ht :=
    hs.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  convert ht using 1
  funext N
  have hcp := congrArg CPMap.choi (sum_chainIncrement_cp c hc N)
  rw [choi_finset_sum] at hcp
  simpa only [d, Function.comp_apply] using hcp.symm

theorem choi_comp_tendsto_left {n m l : ℕ}
    (c : ℕ → Superoperator m l) (hc : Monotone c)
    (g : Superoperator n m) :
    Filter.Tendsto (fun N => (comp (c N) g).cp.choi) Filter.atTop
      (nhds (comp (omegaSup c hc) g).cp.choi) := by
  have ht := choi_tendsto_omegaSup c hc
  apply tendsto_pi_nhds.mpr
  intro ai
  apply tendsto_pi_nhds.mpr
  intro bj
  rcases ai with ⟨a, i⟩
  rcases bj with ⟨b, j⟩
  simp only [cp_comp, CPMap.choi_comp_apply]
  apply tendsto_finsetSum Finset.univ
  intro x hx
  apply tendsto_finsetSum Finset.univ
  intro y hy
  exact
    (tendsto_pi_nhds.mp
      (tendsto_pi_nhds.mp ht (a, x)) (b, y)).mul
      tendsto_const_nhds

theorem choi_comp_tendsto_right {n m l : ℕ}
    (f : Superoperator m l) (c : ℕ → Superoperator n m)
    (hc : Monotone c) :
    Filter.Tendsto (fun N => (comp f (c N)).cp.choi) Filter.atTop
      (nhds (comp f (omegaSup c hc)).cp.choi) := by
  have ht := choi_tendsto_omegaSup c hc
  apply tendsto_pi_nhds.mpr
  intro ai
  apply tendsto_pi_nhds.mpr
  intro bj
  rcases ai with ⟨a, i⟩
  rcases bj with ⟨b, j⟩
  simp only [cp_comp, CPMap.choi_comp_apply]
  apply tendsto_finsetSum Finset.univ
  intro x hx
  apply tendsto_finsetSum Finset.univ
  intro y hy
  exact tendsto_const_nhds.mul
    (tendsto_pi_nhds.mp
      (tendsto_pi_nhds.mp ht (x, i)) (y, j))


end Superoperator

namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-! ## Closed pairing and classical hom enrichment

Transport the pointed ωCPO on `Hom(-, I)` across the Day closed pairing
`Hom(M, N) ≃ Hom(M ⊗ ¬N, I)` for biorthogonal `N`.  Precomposition lifts from
`unitHom_precomp_*`; postcomposition lifts via right naturality of the pairing
along Day negation, reducing to `unitHom_precomp_*` on the unit side.
-/

/-- Postcomposition by an isomorphism of codomains. -/
noncomputable def Hom.postcompEquiv {M N P : Module} (ρ : Iso N P) :
    Hom M N ≃ Hom M P where
  toFun f := Hom.comp ρ.hom f
  invFun g := Hom.comp ρ.inv g
  left_inv f := by
    change Hom.comp ρ.inv (Hom.comp ρ.hom f) = f
    rw [Hom.comp_assoc, ρ.inv_hom, Hom.id_comp]
  right_inv g := by
    change Hom.comp ρ.hom (Hom.comp ρ.inv g) = g
    rw [Hom.comp_assoc, ρ.hom_inv, Hom.id_comp]

/-- Day closedness specialized to maps into the tensor unit:
`Hom(M, ¬¬N) ≃ Hom(M ⊗ ¬N, I)`. -/
noncomputable def closedPairingDoubleDual (M N : Module) :
    Hom M (DayNegation.neg (DayNegation.neg N)) ≃
      Hom (dayTensor M (DayNegation.neg N)) dayTensorUnit :=
  (dayClosedPresentation.closed M (DayNegation.neg N)
    dayTensorUnit).symm

/-- Closed pairing for an exhibited double-dual isomorphism. -/
noncomputable def closedPairingEquivOfIso (M N : Module)
    (ρ : Iso N (DayNegation.neg (DayNegation.neg N))) :
    Hom M N ≃
      Hom (dayTensor M (DayNegation.neg N)) dayTensorUnit :=
  (Hom.postcompEquiv ρ).trans (closedPairingDoubleDual M N)

/-- Closed pairing for a Day-biorthogonal classical object:
`Hom(M,N) ≃ Hom(M ⊗ ¬N, I)`. -/
noncomputable def closedPairingEquiv (M : Module)
    (N : BiorthogonalObject) :
    Hom M N.module ≃
      Hom (dayTensor M (DayNegation.neg N.module)) dayTensorUnit :=
  closedPairingEquivOfIso M N.module N.reflexive

/-- Evaluation of the closed adjunction on generators. -/
theorem dayClosed_app {X A L : Module}
    (φ : Hom (dayTensor X A) L) {n p q : ℕ}
    (x : (X.obj n).Carrier) (r : Superoperator p n)
    (y : (A.obj q).Carrier) :
    ((dayClosedPresentation.closed X A L φ).app n x).app r y =
      φ.app (p * q) ((DayCoend.intro X A).app (X.act x r) y) := by
  dsimp [dayClosedPresentation, DayClosedPresentation.closed]
  rfl

/-- Left naturality of Day closedness. -/
theorem dayClosed_comp_left {X X' A L : Module}
    (u : Hom X' X) (φ : Hom (dayTensor X A) L) :
    Hom.comp (dayClosedPresentation.closed X A L φ) u =
      dayClosedPresentation.closed X' A L
        (Hom.comp φ (DayTensor.map u (Hom.id A))) := by
  apply Hom.ext
  intro n x
  apply Bilinear.ext
  intro p q r y
  change Superoperator p n at r
  have hL := dayClosed_app φ (u.app n x) r y
  have hR :=
    dayClosed_app (Hom.comp φ (DayTensor.map u (Hom.id A))) x r y
  refine hL.trans (Eq.trans ?_ hR.symm)
  rw [Hom.comp_app, DayTensor.map_intro, Hom.id_app, u.naturality]

/-- Inverse form of left naturality used by the closed pairing. -/
theorem closedPairingDoubleDual_comp_left {M M' N : Module}
    (u : Hom M' M)
    (φ : Hom M (DayNegation.neg (DayNegation.neg N))) :
    closedPairingDoubleDual M' N (Hom.comp φ u) =
      Hom.comp (closedPairingDoubleDual M N φ)
        (DayTensor.map u (Hom.id (DayNegation.neg N))) := by
  let e :=
    dayClosedPresentation.closed M' (DayNegation.neg N) dayTensorUnit
  let e₀ :=
    dayClosedPresentation.closed M (DayNegation.neg N) dayTensorUnit
  have h := dayClosed_comp_left u (closedPairingDoubleDual M N φ)
  have hφ : e₀ (closedPairingDoubleDual M N φ) = φ :=
    Equiv.apply_symm_apply e₀ φ
  rw [hφ] at h
  have h' := congrArg e.symm h
  rw [Equiv.symm_apply_apply] at h'
  exact h'

theorem closedPairingEquivOfIso_comp_left {M M' N : Module}
    (ρ : Iso N (DayNegation.neg (DayNegation.neg N)))
    (u : Hom M' M) (f : Hom M N) :
    closedPairingEquivOfIso M' N ρ (Hom.comp f u) =
      Hom.comp (closedPairingEquivOfIso M N ρ f)
        (DayTensor.map u (Hom.id (DayNegation.neg N))) := by
  change closedPairingDoubleDual M' N
      (Hom.comp ρ.hom (Hom.comp f u)) =
    Hom.comp (closedPairingDoubleDual M N (Hom.comp ρ.hom f))
      (DayTensor.map u (Hom.id (DayNegation.neg N)))
  rw [Hom.comp_assoc]
  exact closedPairingDoubleDual_comp_left u (Hom.comp ρ.hom f)

theorem closedPairingEquiv_comp_left {M M' : Module}
    (N : BiorthogonalObject) (u : Hom M' M)
    (f : Hom M N.module) :
    closedPairingEquiv M' N (Hom.comp f u) =
      Hom.comp (closedPairingEquiv M N f)
        (DayTensor.map u (Hom.id (DayNegation.neg N.module))) :=
  closedPairingEquivOfIso_comp_left N.reflexive u f

/-- Right naturality of Day closedness into the tensor unit. -/
theorem dayClosed_comp_right_unit {X A A' : Module}
    (h : Hom A' A) (φ : Hom (dayTensor X A) dayTensorUnit) :
    Hom.comp (DayNegation.map h)
      (dayClosedPresentation.closed X A dayTensorUnit φ) =
      dayClosedPresentation.closed X A' dayTensorUnit
        (Hom.comp φ (DayTensor.map (Hom.id X) h)) := by
  apply Hom.ext
  intro n x
  apply Bilinear.ext
  intro p q r y
  change Superoperator p n at r
  have hL := dayClosed_app φ x r (h.app q y)
  have hR :=
    dayClosed_app (Hom.comp φ (DayTensor.map (Hom.id X) h)) x r y
  change
    ((dayClosedPresentation.closed X A dayTensorUnit φ).app n x).app r
        (h.app q y) =
      ((dayClosedPresentation.closed X A' dayTensorUnit
          (Hom.comp φ (DayTensor.map (Hom.id X) h))).app n x).app r y
  refine hL.trans (Eq.trans ?_ hR.symm)
  rw [Hom.comp_app, DayTensor.map_intro, Hom.id_app]

/-- Inverse form of right naturality for the closed pairing. -/
theorem closedPairingDoubleDual_comp_right {M N N' : Module}
    (v : Hom N N')
    (φ : Hom M (DayNegation.neg (DayNegation.neg N))) :
    closedPairingDoubleDual M N'
        (Hom.comp (DayNegation.map (DayNegation.map v)) φ) =
      Hom.comp (closedPairingDoubleDual M N φ)
        (DayTensor.map (Hom.id M) (DayNegation.map v)) := by
  let e' :=
    dayClosedPresentation.closed M (DayNegation.neg N') dayTensorUnit
  let e :=
    dayClosedPresentation.closed M (DayNegation.neg N) dayTensorUnit
  have h :=
    dayClosed_comp_right_unit (DayNegation.map v)
      (closedPairingDoubleDual M N φ)
  have hφ : e (closedPairingDoubleDual M N φ) = φ :=
    Equiv.apply_symm_apply e φ
  rw [hφ] at h
  have h' := congrArg e'.symm h
  rw [Equiv.symm_apply_apply] at h'
  exact h'

theorem closedPairingEquivOfIso_comp_right {M N N' : Module}
    (ρ : Iso N (DayNegation.neg (DayNegation.neg N)))
    (ρ' : Iso N' (DayNegation.neg (DayNegation.neg N')))
    (hunit : ∀ v : Hom N N',
      Hom.comp ρ'.hom v =
        Hom.comp (DayNegation.map (DayNegation.map v)) ρ.hom)
    (v : Hom N N') (f : Hom M N) :
    closedPairingEquivOfIso M N' ρ' (Hom.comp v f) =
      Hom.comp (closedPairingEquivOfIso M N ρ f)
        (DayTensor.map (Hom.id M) (DayNegation.map v)) := by
  change closedPairingDoubleDual M N'
      (Hom.comp ρ'.hom (Hom.comp v f)) =
    Hom.comp (closedPairingDoubleDual M N (Hom.comp ρ.hom f))
      (DayTensor.map (Hom.id M) (DayNegation.map v))
  rw [Hom.comp_assoc, hunit v, ← Hom.comp_assoc]
  exact closedPairingDoubleDual_comp_right v (Hom.comp ρ.hom f)

theorem closedPairingEquiv_comp_right {M : Module}
    {N N' : BiorthogonalObject} (v : Hom N.module N'.module)
    (f : Hom M N.module) :
    closedPairingEquiv M N' (Hom.comp v f) =
      Hom.comp (closedPairingEquiv M N f)
        (DayTensor.map (Hom.id M) (DayNegation.map v)) := by
  refine closedPairingEquivOfIso_comp_right
      N.reflexive N'.reflexive ?_ v f
  intro w
  have hN' : N'.reflexive.hom = DayNegation.unit N'.module := by
    simpa [DayNegation.data] using N'.canonical
  have hN : N.reflexive.hom = DayNegation.unit N.module := by
    simpa [DayNegation.data] using N.canonical
  rw [hN', hN]
  exact DayNegation.unit_natural w

theorem dayClosed_zero (X A L : Module) :
    dayClosedPresentation.closed X A L 0 = 0 := by
  apply Hom.ext
  intro n x
  apply Bilinear.ext
  intro p q r y
  dsimp [dayClosedPresentation, DayClosedPresentation.closed]
  rfl

theorem closedPairingDoubleDual_zero (M N : Module) :
    closedPairingDoubleDual M N 0 = 0 := by
  let e :=
    dayClosedPresentation.closed M (DayNegation.neg N) dayTensorUnit
  apply e.injective
  change e (e.symm 0) = e 0
  rw [Equiv.apply_symm_apply, dayClosed_zero]

theorem closedPairingEquivOfIso_zero {M N : Module}
    (ρ : Iso N (DayNegation.neg (DayNegation.neg N))) :
    closedPairingEquivOfIso M N ρ 0 = 0 := by
  change closedPairingDoubleDual M N (Hom.comp ρ.hom 0) = 0
  have h0 : Hom.comp ρ.hom (0 : Hom M N) = 0 := by
    ext n x
    exact ρ.hom.map_zero n
  rw [h0, closedPairingDoubleDual_zero]

theorem closedPairingEquiv_zero (M : Module) (N : BiorthogonalObject) :
    closedPairingEquiv M N 0 = 0 :=
  closedPairingEquivOfIso_zero N.reflexive


end SuperoperatorModule

end QLambda.Domain.Presheaf
