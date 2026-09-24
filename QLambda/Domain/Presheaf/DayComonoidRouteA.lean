/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.DayComonoidCore

/-!
# Route A bang-split effects and transfer gates
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

set_option maxHeartbeats 8000000

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-! ## Degree reindexing of comultiplication components -/

/-- Ordered partitions of a fixed total degree. -/
abbrev DegreePartition (k : ℕ) := Fin (k + 1)

/-- Encode an ordered partition of `k` as a pair of natural numbers. -/
def degreePartitionToPair (k : ℕ) (p : DegreePartition k) : ℕ × ℕ :=
  (p.val, k - p.val)

/-- Decode a pair into the partition sigma type (total degree `p + q`). -/
def pairToDegreePartition (pq : ℕ × ℕ) :
    (k : ℕ) × DegreePartition k :=
  ⟨pq.1 + pq.2, ⟨pq.1, Nat.lt_succ_of_le (Nat.le_add_right pq.1 pq.2)⟩⟩

@[simp]
theorem pairToDegreePartition_toPair (pq : ℕ × ℕ) :
    degreePartitionToPair (pairToDegreePartition pq).1
        (pairToDegreePartition pq).2 =
      pq := by
  cases pq with
  | mk p q =>
    simp [degreePartitionToPair, pairToDegreePartition]

@[simp]
theorem degreePartitionToPair_fst (k : ℕ) (p : DegreePartition k) :
    (degreePartitionToPair k p).1 = p.val :=
  rfl

@[simp]
theorem degreePartitionToPair_snd_add (k : ℕ) (p : DegreePartition k) :
    (degreePartitionToPair k p).1 + (degreePartitionToPair k p).2 = k :=
  Nat.add_sub_of_le (Nat.le_of_lt_succ p.isLt)

/-! ## Route A: joint effect of the canonical bang-split family

Each homogeneous split is `ofEquivalence(tensorSplitEquiv) ∘ coeff`, so by
`effect_comp_ofEquivalence_left` every partition `p+q=k` has **the same**
input effect as the unsplit degree-`k` coefficient.  The finite family over
`DegreePartition k` therefore has Choi/effect sum
`(k+1) • effect(coeff)`, which is **not** Loewner-below `effect(coeff)`
(nor below `I`) whenever the coefficient is trace-preserving and `k ≥ 1`.
The splits are full reindexings of one channel, not complementary instrument
branches — “instrument completeness” does not apply.
-/

/-- Effect of a canonical bang split equals the effect of the shared
homogeneous coefficient (unitary postprocessing). -/
theorem bangSplitComponent_effect (A p q n : ℕ)
    (x : ((bang A).obj n).Carrier) :
    ((bangSplitComponent A p q).app n x).cp.effect =
      (x (p + q)).val.cp.effect := by
  change
      (Superoperator.comp
          (Superoperator.ofEquivalence (tensorSplitEquiv A p q))
          (x (p + q)).val).cp.effect =
        (x (p + q)).val.cp.effect
  exact Superoperator.effect_comp_ofEquivalence_left
    (tensorSplitEquiv A p q) (x (p + q)).val

/-- Finite family of split effects on the degree-`k` diagonal. -/
noncomputable def bangSplitFamilyEffect (A k n : ℕ)
    (x : ((bang A).obj n).Carrier) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ p : DegreePartition k,
    ((bangSplitComponent A
        (degreePartitionToPair k p).1
        (degreePartitionToPair k p).2).app n x).cp.effect

/-- Proposed Route A joint TNI bound: the Loewner sum of canonical split
effects over `p+q=k` lies below the unsplit coefficient effect. -/
def BangSplitFamilyEffectLe (A k n : ℕ)
    (x : ((bang A).obj n).Carrier) : Prop :=
  bangSplitFamilyEffect A k n x ≤ (x k).val.cp.effect

/-- Proposed Route A bound against the identity effect. -/
def BangSplitFamilyEffectLeOne (A k n : ℕ)
    (x : ((bang A).obj n).Carrier) : Prop :=
  bangSplitFamilyEffect A k n x ≤ (1 : Matrix (Fin n) (Fin n) ℂ)

/-- Every diagonal split shares the degree-`k` coefficient's effect. -/
theorem bangSplitFamilyEffect_eq (A k n : ℕ)
    (x : ((bang A).obj n).Carrier) :
    bangSplitFamilyEffect A k n x =
      ∑ _p : DegreePartition k, (x k).val.cp.effect := by
  unfold bangSplitFamilyEffect
  congr 1
  funext p
  have hpq := degreePartitionToPair_snd_add k p
  rw [bangSplitComponent_effect, hpq]

/-- Cardinality form: the joint effect is `(k+1)` copies of the coefficient
effect. -/
theorem bangSplitFamilyEffect_nsmul (A k n : ℕ)
    (x : ((bang A).obj n).Carrier) :
    bangSplitFamilyEffect A k n x =
      (k + 1) • (x k).val.cp.effect := by
  rw [bangSplitFamilyEffect_eq, Finset.sum_const]
  simp [Fintype.card_fin]

/-- Degree-one identity coefficient (only the trivial factor permutation). -/
noncomputable def bangIdentitySymmetricOne (A : ℕ) :
    SymmetricElement A 1 (tensorPowerDimension A 1) where
  val := Superoperator.identity (tensorPowerDimension A 1)
  invariant := by
    intro σ
    have hσ : σ = Equiv.refl _ := Subsingleton.elim _ _
    subst hσ
    change
        Superoperator.comp (factorPermutation A 1 (Equiv.refl _))
          (Superoperator.identity _) =
        Superoperator.identity _
    have hperm :
        factorPermutation A 1 (Equiv.refl _) =
          Superoperator.identity (tensorPowerDimension A 1) := by
      change Superoperator.ofEquivalence (factorPermutationEquiv A 1 (Equiv.refl _)) =
        Superoperator.identity _
      have he :
          factorPermutationEquiv A 1 (Equiv.refl _) = Equiv.refl _ := by
        unfold factorPermutationEquiv
        simp only [Equiv.arrowCongr_refl, Equiv.refl_trans,
          Equiv.symm_trans_self]
      rw [he, Superoperator.ofEquivalence_refl]
    rw [hperm, Superoperator.identity_comp]

/-- Series supported only at degree one, with the identity coefficient. -/
noncomputable def bangIdentityDegreeOne (A : ℕ) :
    ((bang A).obj (tensorPowerDimension A 1)).Carrier
  | 1 => bangIdentitySymmetricOne A
  | _ => 0

theorem bangIdentityDegreeOne_coeff (A : ℕ) :
    (bangIdentityDegreeOne A 1).val =
      Superoperator.identity (tensorPowerDimension A 1) :=
  rfl

/-- Loewner obstruction: `2 • I ≰ I` on any nonempty system. -/
theorem two_nsmul_one_not_le_one {n : ℕ} (hn : 0 < n) :
    ¬ ((2 : ℕ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤
        (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  intro hle
  have hpsd : (1 - (2 : ℕ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef :=
    Matrix.le_iff.mp hle
  have hdiag := SigmaMon.ChoiSum.diag_re_nonneg hpsd ⟨0, hn⟩
  have heq :
      ((1 : Matrix (Fin n) (Fin n) ℂ) -
          (2 : ℕ) • (1 : Matrix (Fin n) (Fin n) ℂ)) ⟨0, hn⟩ ⟨0, hn⟩ =
        (-1 : ℂ) := by
    simp only [two_nsmul, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
      ↓reduceIte]
    norm_num
  rw [heq] at hdiag
  norm_num at hdiag

/-- Route A fails already for `A = 2`, degree `1`: two splits of `id₂` have
joint effect `2 I ≰ I`. -/
theorem not_bangSplitFamilyEffectLe_two_one :
    ¬ BangSplitFamilyEffectLe 2 1 (tensorPowerDimension 2 1)
        (bangIdentityDegreeOne 2) := by
  intro hle
  have hdim : tensorPowerDimension 2 1 = 2 := by
    simp [tensorPowerDimension_eq_pow]
  have hid_eff :
      (Superoperator.identity (tensorPowerDimension 2 1)).cp.effect =
        (1 : Matrix (Fin (tensorPowerDimension 2 1))
          (Fin (tensorPowerDimension 2 1)) ℂ) := by
    change (CPMap.identity (tensorPowerDimension 2 1)).effect = 1
    exact CPMap.effect_identity _
  have hsum :
      bangSplitFamilyEffect 2 1 (tensorPowerDimension 2 1)
          (bangIdentityDegreeOne 2) =
        (2 : ℕ) • (1 : Matrix (Fin (tensorPowerDimension 2 1))
          (Fin (tensorPowerDimension 2 1)) ℂ) := by
    rw [bangSplitFamilyEffect_nsmul, bangIdentityDegreeOne_coeff, hid_eff]
  have hcoeff :
      ((bangIdentityDegreeOne 2) 1).val.cp.effect =
        (1 : Matrix (Fin (tensorPowerDimension 2 1))
          (Fin (tensorPowerDimension 2 1)) ℂ) := by
    rw [bangIdentityDegreeOne_coeff, hid_eff]
  change
      bangSplitFamilyEffect 2 1 (tensorPowerDimension 2 1)
          (bangIdentityDegreeOne 2) ≤
        ((bangIdentityDegreeOne 2) 1).val.cp.effect at hle
  rw [hsum, hcoeff] at hle
  exact two_nsmul_one_not_le_one (Nat.pos_of_ne_zero (by
    rw [hdim]; decide)) hle

/-- Same witness against the `≤ I` packaging of the Route A bound. -/
theorem not_bangSplitFamilyEffectLeOne_two_one :
    ¬ BangSplitFamilyEffectLeOne 2 1 (tensorPowerDimension 2 1)
        (bangIdentityDegreeOne 2) := by
  intro hle
  have hdim : tensorPowerDimension 2 1 = 2 := by
    simp [tensorPowerDimension_eq_pow]
  have hid_eff :
      (Superoperator.identity (tensorPowerDimension 2 1)).cp.effect =
        (1 : Matrix (Fin (tensorPowerDimension 2 1))
          (Fin (tensorPowerDimension 2 1)) ℂ) := by
    change (CPMap.identity (tensorPowerDimension 2 1)).effect = 1
    exact CPMap.effect_identity _
  have hsum :
      bangSplitFamilyEffect 2 1 (tensorPowerDimension 2 1)
          (bangIdentityDegreeOne 2) =
        (2 : ℕ) • (1 : Matrix (Fin (tensorPowerDimension 2 1))
          (Fin (tensorPowerDimension 2 1)) ℂ) := by
    rw [bangSplitFamilyEffect_nsmul, bangIdentityDegreeOne_coeff, hid_eff]
  change
      bangSplitFamilyEffect 2 1 (tensorPowerDimension 2 1)
          (bangIdentityDegreeOne 2) ≤ 1 at hle
  rw [hsum] at hle
  exact two_nsmul_one_not_le_one (Nat.pos_of_ne_zero (by
    rw [hdim]; decide)) hle

/-- Named theorem form requested by the Route A gate: the structured joint
bound does **not** hold for the canonical bang-split family. -/
theorem bangSplitFamily_effect_le :
    ¬ (∀ (A k n : ℕ) (x : ((bang A).obj n).Carrier),
        BangSplitFamilyEffectLe A k n x) := by
  intro h
  exact not_bangSplitFamilyEffectLe_two_one
    (h 2 1 (tensorPowerDimension 2 1) (bangIdentityDegreeOne 2))

/-! ## Gates 6–9: Day transfer gap and claim boundary

Route A refutes a *joint-effect* bound on the raw split Superoperators.  The
Day gate `BangComultComponentsAdmissible` quantifies over every bilinear
interpretation.  Transferring the effect witness into that quantifier needs a
bilinear `β` that returns **both** ordered degree-one splits in the **same**
TNI fiber so they are added together.  Fixed projection pairs
`(proj₀, proj₁)` recover only one ordering; product modules place the two
ids in different summands; ambient CP always admits sums.  We therefore
record an explicit transfer obligation rather than claiming
`¬ BangComultComponentsAdmissible 2`.

`BangSplitEffectAdmissible` is a **global universal quantification** of the
Route A bound over every series element — not a hereditary carrier-membership
predicate for a subobject of `bang A`.  Its failure at `A = 2` therefore
refutes that global bound, not “every hereditary subobject”.

**L8 terminal route (replacement category):** no TNI/representable
construction of `BangComultDayTransferWitness` is claimed.  The named
replacement `AmbientCPDayBangCategory` (`cpmModule` fibers) restores
`Fiber.HasSumAdd` and `HasActSumFromDim`; see `DayBangBoundary.lean` for the
Gate-8 test suite `ambientCP_gate8_testSuite`.
-/

/-- Gate 6 transfer obligation: a bilinear into a TNI/representable module
that recovers both ordered degree-one splits of the identity series in one
fiber (so the fiber-2 / Route A obstruction applies to Day evaluation).
A constructed witness would imply `¬ BangComultComponentsAdmissible 2`.
No such TNI witness is constructed; L8 resolves via the ambient-CP
replacement category in `DayBangBoundary.lean`. -/
def BangComultDayTransferWitness : Prop :=
  ∃ (L : Module) (β : Bilinear (bang 2) (bang 2) L)
    (z₀₁ z₁₀ : (L.obj (tensorPowerDimension 2 1)).Carrier),
    DayCoend.evaluate L β
        (bangComultComponentFamily 2 (tensorPowerDimension 2 1)
          (bangIdentityDegreeOne 2) (0, 1)) =
      z₀₁ ∧
    DayCoend.evaluate L β
        (bangComultComponentFamily 2 (tensorPowerDimension 2 1)
          (bangIdentityDegreeOne 2) (1, 0)) =
      z₁₀ ∧
    ¬ ∃ Φ : (L.obj (tensorPowerDimension 2 1)).Carrier,
        (L.obj (tensorPowerDimension 2 1)).HasSum
          (fun i : Bool => bif i then z₀₁ else z₁₀) Φ

/-- A Day-transfer witness isolates an inadmissible two-term row of the full
component family, and therefore refutes mixed-component admissibility at
dimension two. -/
theorem bangComultDayTransferWitness_not_admissible :
    BangComultDayTransferWitness → ¬ BangComultComponentsAdmissible 2 := by
  rintro ⟨L, β, z₀₁, z₁₀, hz₀₁, hz₁₀, hbad⟩ hAd
  let n := tensorPowerDimension 2 1
  let x := bangIdentityDegreeOne 2
  let F : ℕ × ℕ → (L.obj n).Carrier := fun pq =>
    DayCoend.evaluate L β (bangComultComponentFamily 2 n x pq)
  obtain ⟨z, hz⟩ := hAd n x L β
  have hzF : (L.obj n).HasSum F z := by
    simpa [F, n, x] using hz
  let S : Set (ℕ × ℕ) :=
    {pq | pq = (0, 1) ∨ pq = (1, 0)}
  let κ : Bool → Type := fun b =>
    bif b then (Sᶜ : Set (ℕ × ℕ)) else S
  let e : (Σ b, κ b) ≃ ℕ × ℕ :=
    (Equiv.sumEquivSigmaBool S (Sᶜ : Set (ℕ × ℕ))).symm.trans
      (Equiv.Set.sumCompl S)
  have hκ : ∀ b, Countable (κ b) := by
    intro b
    cases b <;> simp [κ]
    all_goals exact Set.to_countable _
  letI (b : Bool) : Countable (κ b) := hκ b
  have hzReindexed :
      (L.obj n).HasSum (F ∘ e) z :=
    ((L.obj n).summation.reindex e F z).mpr hzF
  obtain ⟨g, hrows, _⟩ :=
    ((L.obj n).summation.flatten
      (fun b (j : κ b) => F (e ⟨b, j⟩)) z).mp hzReindexed
  have hselected :
      (L.obj n).HasSum (fun j : κ false => F (e ⟨false, j⟩))
        (g false) :=
    hrows false
  let selectedEquiv : Bool ≃ S :=
    { toFun := fun b => match b with
        | true => ⟨(0, 1), Or.inl rfl⟩
        | false => ⟨(1, 0), Or.inr rfl⟩
      invFun := fun pq => if pq.1.1 = 0 then true else false
      left_inv := by
        intro b
        cases b <;> simp
      right_inv := by
        rintro ⟨pq, hpq⟩
        rcases hpq with rfl | rfl <;> simp }
  have hboolF :
      (L.obj n).HasSum
        (fun i : Bool => F (selectedEquiv i)) (g false) := by
    have hre :=
      ((L.obj n).summation.reindex selectedEquiv
        (fun j : κ false => F (e ⟨false, j⟩)) (g false)).mpr hselected
    convert hre using 1
    funext i
    cases i <;> rfl
  apply hbad
  refine ⟨g false, ?_⟩
  refine ((L.obj n).hasSum_congr ?_).mp hboolF
  intro i
  cases i with
  | false =>
      change
        DayCoend.evaluate L β
            (bangComultComponentFamily 2 n x (1, 0)) =
          bif false then z₀₁ else z₁₀
      rw [hz₁₀]
      rfl
  | true =>
      change
        DayCoend.evaluate L β
            (bangComultComponentFamily 2 n x (0, 1)) =
          bif true then z₀₁ else z₁₀
      rw [hz₀₁]
      rfl

/-- Any Day-transfer witness target must fail Bool-add at the obstruction
fiber (so ambient-CP targets with `Fiber.HasSumAdd` cannot host it). -/
theorem bangComultDayTransferWitness_requires_nonadditive_target :
    BangComultDayTransferWitness →
      ∃ L : Module.{0},
        ¬ Fiber.HasSumAdd (L.obj (tensorPowerDimension 2 1)) := by
  rintro ⟨L, β, z₀₁, z₁₀, hz₀₁, hz₁₀, hbad⟩
  refine ⟨L, ?_⟩
  intro hadd
  exact hbad (hadd z₀₁ z₁₀)

/-- Gate 6 (honest form): Route A alone closes a joint-effect bound, not the
Day admissibility quantifier; the missing bridge is
`BangComultDayTransferWitness`. -/
theorem routeA_refutation_exists :
    ∃ A k n x, ¬ BangSplitFamilyEffectLe A k n x :=
  ⟨2, 1, tensorPowerDimension 2 1, bangIdentityDegreeOne 2,
    not_bangSplitFamilyEffectLe_two_one⟩

/-- Global universal form of the raw Route A joint-effect bound (not a
carrier-membership / hereditary-subobject predicate). -/
def BangSplitEffectAdmissible (A : ℕ) : Prop :=
  ∀ (k n : ℕ) (x : ((bang A).obj n).Carrier),
    BangSplitFamilyEffectLeOne A k n x

/-- The global raw split-effect bound fails at `A = 2`: it excludes the
degree-one identity series needed by dereliction / cofree lift of `id`.
This does **not** refute every hereditary subobject of `bang 2`. -/
theorem bangSplitEffectAdmissible_excludes_identity_two :
    ¬ BangSplitEffectAdmissible 2 := by
  intro h
  exact not_bangSplitFamilyEffectLeOne_two_one
    (h 1 (tensorPowerDimension 2 1) (bangIdentityDegreeOne 2))

/-- Alias retained for earlier theorem-index citations; same statement as
`bangSplitEffectAdmissible_excludes_identity_two`. -/
theorem raw_global_effect_bound_fails_at_two :
    ¬ BangSplitEffectAdmissible 2 :=
  bangSplitEffectAdmissible_excludes_identity_two

/-- Normalized degree-one split weights: the raw joint effect scaled by
`1/2`.  Joint effect is then `I`, repairing the raw Route A *matrix*
obstruction at `(A,k) = (2,1)`.  This is not by itself a counital
comultiplication (see `half_scale_not_counital_bang_repair`). -/
noncomputable def bangNormalizedSplitFamilyEffect_two_one :
    Matrix (Fin (tensorPowerDimension 2 1))
      (Fin (tensorPowerDimension 2 1)) ℂ :=
  ((2 : ℕ) : ℂ)⁻¹ •
      bangSplitFamilyEffect 2 1 (tensorPowerDimension 2 1)
        (bangIdentityDegreeOne 2)

theorem bangNormalizedSplitFamilyEffect_two_one_eq_one :
    bangNormalizedSplitFamilyEffect_two_one =
      (1 : Matrix (Fin (tensorPowerDimension 2 1))
        (Fin (tensorPowerDimension 2 1)) ℂ) := by
  have hid_eff :
      (Superoperator.identity (tensorPowerDimension 2 1)).cp.effect =
        (1 : Matrix (Fin (tensorPowerDimension 2 1))
          (Fin (tensorPowerDimension 2 1)) ℂ) := by
    change (CPMap.identity (tensorPowerDimension 2 1)).effect = 1
    exact CPMap.effect_identity _
  unfold bangNormalizedSplitFamilyEffect_two_one
  rw [bangSplitFamilyEffect_nsmul, bangIdentityDegreeOne_coeff, hid_eff]
  -- `(2:ℂ)⁻¹ • (2 • I) = I`
  have hscale :
      ((2 : ℕ) : ℂ)⁻¹ • ((2 : ℕ) • (1 : Matrix
          (Fin (tensorPowerDimension 2 1))
          (Fin (tensorPowerDimension 2 1)) ℂ)) =
        1 := by
    rw [two_nsmul]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs with hij
    · -- diagonal: (2:ℂ)⁻¹ * (1 + 1) = 1
      norm_num
    · -- off-diagonal: (2:ℂ)⁻¹ * (0 + 0) = 0
      ring
  exact hscale

theorem bangNormalizedSplitFamilyEffect_two_one_le_one :
    bangNormalizedSplitFamilyEffect_two_one ≤
      (1 : Matrix (Fin (tensorPowerDimension 2 1))
        (Fin (tensorPowerDimension 2 1)) ℂ) := by
  rw [bangNormalizedSplitFamilyEffect_two_one_eq_one]

/-- Half of the identity matrix is not the identity on a nonempty system. -/
theorem half_one_ne_one {n : ℕ} (hn : 0 < n) :
    ((2 : ℕ) : ℂ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ) ≠
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
  intro heq
  have h00 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M ⟨0, hn⟩ ⟨0, hn⟩) heq
  simp only [Matrix.smul_apply, Matrix.one_apply, ↓reduceIte, smul_eq_mul,
    mul_one] at h00
  -- `(2:ℂ)⁻¹ = 1` is false
  have : ((2 : ℕ) : ℂ)⁻¹ ≠ 1 := by norm_num
  exact this h00


end SuperoperatorModule

end QLambda.Domain.Presheaf
