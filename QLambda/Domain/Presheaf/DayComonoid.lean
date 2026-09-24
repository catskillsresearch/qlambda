/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.ComonoidHom

/-!
# Bang / symmetric-series comonoid constructions (Day tensor)

Gate progress and blockers: see module docstring historically attached to
`Comonoid.lean`. Abstract `Comonoid` / `ComonoidHom` live in their own files.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

set_option maxHeartbeats 8000000

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder


/-! ## Symmetric series and the coefficientwise Day comparison -/

/-- The intended exponential carrier (symmetric formal power series). -/
noncomputable abbrev bang (A : ℕ) : Module :=
  symmetricFormalPowerSeries A

/-- Fibers of `bang` are unrestricted pointwise products, not finite-support
formal series. -/
theorem bang_obj_carrier (A n : ℕ) :
    ((bang A).obj n).Carrier = ∀ k, SymmetricElement A k n :=
  rfl

/-- Canonical bilinear pairing of series into the coefficientwise formal
square. -/
noncomputable def symmetricSeriesDayBilinear (A : ℕ) :
    Bilinear (bang A) (bang A) (symmetricFormalTensorSquare A) where
  app := fun {m n} x y p q =>
    Superoperator.tensor (x p).val (y q).val
  map_zero_left := by
    intro m n y
    funext p q
    exact Superoperator.tensor_zero_left (y q).val
  map_zero_right := by
    intro m n x
    funext p q
    exact Superoperator.tensor_zero_right (x p).val
  map_sum_left := by
    intro ι _ m n x s y h p q
    exact SigmaMon.ChoiSum.tensor_hasSum_left (h p) (y q).val
  map_sum_right := by
    intro ι _ m n x y s h p q
    exact SigmaMon.ChoiSum.tensor_hasSum_right (x p).val (h q)
  naturality := by
    intro m' m n' n x y f g
    funext p q
    exact Superoperator.tensor_comp (x p).val f (y q).val g

/-- Comparison from the genuine Day tensor of series to the coefficientwise
formal square. -/
noncomputable def symmetricSeriesDayCompare (A : ℕ) :
    Hom (dayTensor (bang A) (bang A)) (symmetricFormalTensorSquare A) :=
  DayCoend.lift (symmetricSeriesDayBilinear A)

@[simp]
theorem symmetricSeriesDayCompare_intro (A : ℕ) {m n : ℕ}
    (x : ((bang A).obj m).Carrier) (y : ((bang A).obj n).Carrier) :
    (symmetricSeriesDayCompare A).app (m * n)
        ((DayCoend.intro (bang A) (bang A)).app x y) =
      (symmetricSeriesDayBilinear A).app x y :=
  DayCoend.evaluate_intro (symmetricSeriesDayBilinear A) x y

theorem symmetricSeriesDayCompare_postcomp_intro (A : ℕ) :
    Bilinear.postcomp (symmetricSeriesDayCompare A)
        (DayCoend.intro (bang A) (bang A)) =
      symmetricSeriesDayBilinear A := by
  apply Bilinear.ext
  intro m n x y
  exact symmetricSeriesDayCompare_intro A x y

/-! ## Obstruction witnesses -/

/-- Block averaging on every homogeneous pair of the coefficientwise
square. -/
noncomputable def symmetricFormalSquareAverage (A : ℕ) :
    Hom (symmetricFormalTensorSquare A)
      (symmetricFormalTensorSquare A) where
  app := fun _ x p q =>
    Superoperator.comp
      (Superoperator.tensor
        (symmetricAverage A p) (symmetricAverage A q))
      (x p q)
  map_zero := by
    intro n
    funext p q
    exact Superoperator.comp_zero_right _
  map_sum := by
    intro ι _ n f x h p q
    exact SigmaMon.ChoiSum.comp_left
      (Superoperator.tensor
        (symmetricAverage A p) (symmetricAverage A q))
      (h p q)
  naturality := by
    intro m n x f
    funext p q
    exact Superoperator.comp_assoc _ _ _

/-- Averaging fixes every pure tensor of symmetric homogeneous
coefficients.  Thus the series bilinear factors through the symmetric
projector on the ambient square. -/
theorem symmetricFormalSquareAverage_fixes_series_bilinear (A : ℕ) :
    Bilinear.postcomp (symmetricFormalSquareAverage A)
        (symmetricSeriesDayBilinear A) =
      symmetricSeriesDayBilinear A := by
  apply Bilinear.ext
  intro m n x y
  funext p q
  change
    Superoperator.comp
        (Superoperator.tensor
          (symmetricAverage A p) (symmetricAverage A q))
        (Superoperator.tensor (x p).val (y q).val) =
      Superoperator.tensor (x p).val (y q).val
  rw [← Superoperator.tensor_comp,
    SymmetricElement.average_val (x p),
    SymmetricElement.average_val (y q)]

/-- Gate-3 ambient obstruction (cf. `choiIdentity_not_le_one`): the
coefficientwise square is built from ambient representable tensor powers,
which admit a nontrivial factor transposition when `A > 1`.  Symmetric
series coefficients are invariant under all such permutations, so the square
is strictly ambient relative to the series Day tensor. -/
theorem factorPermutationEquiv_swap_ne_refl
    (A : ℕ) (hA : 1 < A) :
    factorPermutationEquiv A 2 (Equiv.swap (0 : Fin 2) 1) ≠
      Equiv.refl (Fin (tensorPowerDimension A 2)) := by
  intro h
  let z0 : Fin A := ⟨0, Nat.zero_lt_of_lt hA⟩
  let z1 : Fin A := ⟨1, hA⟩
  let t : Fin 2 → Fin A := ![z0, z1]
  have hfix : ∀ x, factorPermutationEquiv A 2 (Equiv.swap (0 : Fin 2) 1) x = x := by
    intro x
    rw [h]
    rfl
  -- The swap-equiv acts on packed tuples by precomposition with `swap`.
  have hact :
      factorPermutationEquiv A 2 (Equiv.swap (0 : Fin 2) 1)
          (tensorTupleEquiv A 2 t) =
        tensorTupleEquiv A 2 (t ∘ Equiv.swap (0 : Fin 2) 1) := by
    change
      ((tensorTupleEquiv A 2).symm.trans
          ((Equiv.arrowCongr (Equiv.swap (0 : Fin 2) 1)
              (Equiv.refl (Fin A))).trans
            (tensorTupleEquiv A 2)))
        (tensorTupleEquiv A 2 t) =
      tensorTupleEquiv A 2 (t ∘ Equiv.swap (0 : Fin 2) 1)
    rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
    -- `arrowCongr swap refl t = t ∘ swap`
    rfl
  have hpack :
      tensorTupleEquiv A 2 (t ∘ Equiv.swap (0 : Fin 2) 1) =
        tensorTupleEquiv A 2 t := by
    rw [← hact, hfix]
  have ht := (tensorTupleEquiv A 2).injective hpack
  have h01 := congrFun ht 0
  -- LHS: `(t ∘ swap) 0 = t 1 = z1`; RHS: `t 0 = z0`.
  change z1 = z0 at h01
  exact (Nat.zero_ne_one (congrArg Fin.val h01.symm))

/-- Existence of a Day-valued comultiplication factoring the coefficientwise
`symmetricContraction` through `symmetricSeriesDayCompare`. Closed for `A ≤ 1`. -/
def SymmetricContractionDayFactorization (A : ℕ) : Prop :=
  ∃ δ : Hom (bang A) (dayTensor (bang A) (bang A)),
    Hom.comp (symmetricSeriesDayCompare A) δ = symmetricContraction A

/-- A section of the Day comparison would yield Day factorization of every
map out of the square that is already defined on series pure tensors; no
such section is constructed. -/
def SymmetricSeriesDayCompareSection (A : ℕ) : Prop :=
  ∃ s : Hom (symmetricFormalTensorSquare A)
      (dayTensor (bang A) (bang A)),
    Hom.comp (symmetricSeriesDayCompare A) s =
      Hom.id (symmetricFormalTensorSquare A)

/-- Counit: weakening into the Day tensor unit. -/
noncomputable def bangCounit (A : ℕ) : Hom (bang A) dayTensorUnit :=
  symmetricWeakening A

/-- Dereliction as the degree-one projection to `y(A)`. -/
noncomputable def bangDereliction (A : ℕ) : Hom (bang A) (representable A) :=
  symmetricDereliction A

/-! ## Genuine Day comultiplication components -/

/-- Inclusion of a homogeneous symmetric degree into the series. -/
noncomputable def bangInjection (A k : ℕ) :
    Hom (symmetricPower A k) (bang A) :=
  countableProductInjection (fun j => symmetricPower A j) k

/-- Projection of the series onto a homogeneous symmetric degree. -/
noncomputable def bangProjection (A k : ℕ) :
    Hom (bang A) (symmetricPower A k) :=
  countableProductProjection (fun j => symmetricPower A j) k

/-- Embed a representable tensor power into the series by averaging then
injecting. -/
noncomputable def representableToBang (A k : ℕ) :
    Hom (representable (tensorPowerDimension A k)) (bang A) :=
  Hom.comp (bangInjection A k) (symmetricPowerProjection A k)

/-- The `(p,q)` homogeneous split into the ambient representable
`y(dim_p * dim_q)`. -/
noncomputable def bangSplitComponent (A p q : ℕ) :
    Hom (bang A)
      (representable
        (tensorPowerDimension A p * tensorPowerDimension A q)) where
  app := fun _ x =>
    Superoperator.comp
      (Superoperator.ofEquivalence (tensorSplitEquiv A p q))
      (x (p + q)).val
  map_zero := fun _ => Superoperator.comp_zero_right _
  map_sum := fun h =>
    SigmaMon.ChoiSum.comp_left
      (Superoperator.ofEquivalence (tensorSplitEquiv A p q))
      (h (p + q))
  naturality := fun _ _ => Superoperator.comp_assoc _ _ _

/-- Representable Day inverse:
`y(dim_p * dim_q) → dayTensor(y(dim_p), y(dim_q))`. -/
noncomputable def bangSplitToRepDay (A p q : ℕ) :
    Hom
      (representable
        (tensorPowerDimension A p * tensorPowerDimension A q))
      (dayTensor
        (representable (tensorPowerDimension A p))
        (representable (tensorPowerDimension A q))) :=
  (dayTensorRepresentableIso
    (tensorPowerDimension A p) (tensorPowerDimension A q)).inv

/-- `dayTensor(y(dim_p), y(dim_q)) → dayTensor(!A, !A)`. -/
noncomputable def bangRepDayToSeriesDay (A p q : ℕ) :
    Hom
      (dayTensor
        (representable (tensorPowerDimension A p))
        (representable (tensorPowerDimension A q)))
      (dayTensor (bang A) (bang A)) :=
  DayTensor.map
    (representableToBang A p) (representableToBang A q)

/-- Homogeneous Day comultiplication component through the `(p,q)` split. -/
noncomputable def bangComultComponent (A p q : ℕ) :
    Hom (bang A) (dayTensor (bang A) (bang A)) :=
  Hom.comp (bangRepDayToSeriesDay A p q)
    (Hom.comp (bangSplitToRepDay A p q) (bangSplitComponent A p q))

/-- Fiberwise family of Day comultiplication components. -/
noncomputable def bangComultComponentFamily (A : ℕ) (n : ℕ)
    (x : ((bang A).obj n).Carrier) :
    ℕ × ℕ → ((dayTensor (bang A) (bang A)).obj n).Carrier :=
  fun pq => (bangComultComponent A pq.1 pq.2).app n x

/-- Mixed-degree Day summability of homogeneous split components.
Assembling `δ : Hom (!A) (dayTensor (!A) (!A))` as the coend sum of
`bangComultComponent` requires this obligation — the Day-form of the
mixed-partition TNI gate recorded in `Exponential.lean`. -/
def BangComultComponentsAdmissible (A : ℕ) : Prop :=
  ∀ (n : ℕ) (x : ((bang A).obj n).Carrier)
    (L : Module) (β : Bilinear (bang A) (bang A) L),
    ∃ z : (L.obj n).Carrier,
      (L.obj n).HasSum
        (fun pq : ℕ × ℕ =>
          DayCoend.evaluate L β
            (bangComultComponentFamily A n x pq))
        z

/-- Under mixed-degree admissibility, the fiberwise Day comultiplication is
the coend sum of homogeneous split components. -/
noncomputable def bangComultApp (A : ℕ)
    (h : BangComultComponentsAdmissible A)
    (n : ℕ) (x : ((bang A).obj n).Carrier) :
    ((dayTensor (bang A) (bang A)).obj n).Carrier :=
  DayCoend.sumOfAdmissible
    (bangComultComponentFamily A n x)
    (fun L β => h n x L β)

theorem bangComultApp_evaluate (A : ℕ)
    (h : BangComultComponentsAdmissible A)
    (n : ℕ) (x : ((bang A).obj n).Carrier)
    (L : Module) (β : Bilinear (bang A) (bang A) L)
    (z : (L.obj n).Carrier)
    (hz : (L.obj n).HasSum
      (fun pq : ℕ × ℕ =>
        DayCoend.evaluate L β (bangComultComponentFamily A n x pq))
      z) :
    DayCoend.evaluate L β (bangComultApp A h n x) = z :=
  DayCoend.evaluate_sumOfAdmissible
    (bangComultComponentFamily A n x)
    (fun L β => h n x L β) L β z hz

theorem bangComultComponentFamily_zero (A n : ℕ) (pq : ℕ × ℕ) :
    bangComultComponentFamily A n 0 pq = 0 :=
  (bangComultComponent A pq.1 pq.2).map_zero n

/-- Under admissibility the fiberwise Day sum vanishes at zero. -/
theorem bangComultApp_zero (A : ℕ)
    (h : BangComultComponentsAdmissible A) (n : ℕ) :
    bangComultApp A h n 0 = 0 := by
  have hsum0 :
      DayCoend.HasSum (bangComultComponentFamily A n 0) 0 := by
    intro L β
    have hfun :
        (fun pq : ℕ × ℕ =>
            DayCoend.evaluate L β
              (bangComultComponentFamily A n 0 pq)) =
          fun _ => (0 : (L.obj n).Carrier) := by
      funext pq
      rw [bangComultComponentFamily_zero]
      exact DayCoend.evaluate_zero β
    rw [hfun, DayCoend.evaluate_zero β]
    exact Fiber.hasSum_zero (L.obj n) (ι := ℕ × ℕ)
  have hsum :
      DayCoend.HasSum (bangComultComponentFamily A n 0)
        (bangComultApp A h n 0) := by
    intro L β
    have hz := hsum0 L β
    have hz0 :
        (L.obj n).HasSum
          (fun pq : ℕ × ℕ =>
            DayCoend.evaluate L β
              (bangComultComponentFamily A n 0 pq))
          (0 : (L.obj n).Carrier) := by
      rwa [DayCoend.evaluate_zero β] at hz
    have he :=
      bangComultApp_evaluate A h n 0 L β
        (0 : (L.obj n).Carrier) hz0
    exact he ▸ hz0
  exact ((dayTensor (bang A) (bang A)).obj n).summation.unique
    hsum hsum0

/-- The coend sum of homogeneous components under admissibility. -/
theorem bangComultApp_hasSum (A : ℕ)
    (h : BangComultComponentsAdmissible A)
    (n : ℕ) (x : ((bang A).obj n).Carrier) :
    DayCoend.HasSum (bangComultComponentFamily A n x)
      (bangComultApp A h n x) := by
  intro L β
  obtain ⟨z, hz⟩ := h n x L β
  have he := bangComultApp_evaluate A h n x L β z hz
  exact he ▸ hz

/-- Each homogeneous component of coefficientwise contraction is the split
used by `bangComultComponent`. -/
theorem bangSplitComponent_eq_contraction_slot (A p q n : ℕ)
    (x : ((bang A).obj n).Carrier) :
    (bangSplitComponent A p q).app n x =
      (symmetricContraction A).app n x p q :=
  rfl

/-- Under mixed-degree admissibility, the Day comultiplication is the coend
sum of homogeneous split components, promoted to a module morphism. -/
noncomputable def bangComult (A : ℕ)
    (h : BangComultComponentsAdmissible A) :
    Hom (bang A) (dayTensor (bang A) (bang A)) where
  app := bangComultApp A h
  map_zero := bangComultApp_zero A h
  map_sum := by
    intro ι _ n f s hf L β
    let ψ : ι → ℕ × ℕ → (L.obj n).Carrier := fun i pq =>
      DayCoend.evaluate L β (bangComultComponentFamily A n (f i) pq)
    have hrow (i : ι) :
        (L.obj n).HasSum (ψ i)
          (DayCoend.evaluate L β (bangComultApp A h n (f i))) :=
      bangComultApp_hasSum A h n (f i) L β
    have hcol (pq : ℕ × ℕ) :
        (L.obj n).HasSum (fun i : ι => ψ i pq)
          (DayCoend.evaluate L β
            (bangComultComponentFamily A n s pq)) := by
      have hc :=
        (DayCoend.lift β).map_sum
          ((bangComultComponent A pq.1 pq.2).map_sum hf)
      simpa [ψ, bangComultComponentFamily, DayCoend.lift] using hc
    have hsumCol :
        (L.obj n).HasSum
          (fun pq : ℕ × ℕ =>
            DayCoend.evaluate L β
              (bangComultComponentFamily A n s pq))
          (DayCoend.evaluate L β (bangComultApp A h n s)) :=
      bangComultApp_hasSum A h n s L β
    have hflat :
        (L.obj n).HasSum
          (fun p : Σ _ : ℕ × ℕ, ι => ψ p.2 p.1)
          (DayCoend.evaluate L β (bangComultApp A h n s)) := by
      exact
        ((L.obj n).summation.flatten
          (fun pq i => ψ i pq)
          (DayCoend.evaluate L β (bangComultApp A h n s))).mpr
          ⟨fun pq =>
            DayCoend.evaluate L β
              (bangComultComponentFamily A n s pq),
            hcol, hsumCol⟩
    have hswap :
        (L.obj n).HasSum
          (fun p : Σ _ : ι, ℕ × ℕ => ψ p.1 p.2)
          (DayCoend.evaluate L β (bangComultApp A h n s)) := by
      exact
        ((L.obj n).summation.reindex
          (sigmaSwapEquiv ι (ℕ × ℕ))
          (fun p : Σ _ : ℕ × ℕ, ι => ψ p.2 p.1)
          (DayCoend.evaluate L β (bangComultApp A h n s))).mpr hflat
    obtain ⟨g, hrows, hsumg⟩ :=
      ((L.obj n).summation.flatten ψ
        (DayCoend.evaluate L β (bangComultApp A h n s))).mp hswap
    have hg : g = fun i =>
        DayCoend.evaluate L β (bangComultApp A h n (f i)) := by
      funext i
      exact (L.obj n).summation.unique (hrows i) (hrow i)
    rw [hg] at hsumg
    exact hsumg
  naturality := by
    intro m n x g
    have hleft :
        DayCoend.HasSum
          (bangComultComponentFamily A m
            ((bang A).act x g))
          (bangComultApp A h m ((bang A).act x g)) :=
      bangComultApp_hasSum A h m ((bang A).act x g)
    have hfam :
        bangComultComponentFamily A m ((bang A).act x g) =
          fun pq =>
            (dayTensor (bang A) (bang A)).act
              (bangComultComponentFamily A n x pq) g := by
      funext pq
      exact (bangComultComponent A pq.1 pq.2).naturality x g
    have hright :
        DayCoend.HasSum
          (bangComultComponentFamily A m ((bang A).act x g))
          ((dayTensor (bang A) (bang A)).act
            (bangComultApp A h n x) g) := by
      intro L β
      rw [hfam]
      have hact :=
        L.act_sum_element g (bangComultApp_hasSum A h n x L β)
      convert hact using 1
      · funext i
        exact DayCoend.evaluate_action β
          (bangComultComponentFamily A n x i) g
      · exact DayCoend.evaluate_action β
          (bangComultApp A h n x) g
    exact ((dayTensor (bang A) (bang A)).obj m).summation.unique
      hleft hright

@[simp]
theorem bangComult_app (A : ℕ)
    (h : BangComultComponentsAdmissible A)
    (n : ℕ) (x : ((bang A).obj n).Carrier) :
    (bangComult A h).app n x = bangComultApp A h n x :=
  rfl

/-- Conditional Day comonoid package: requires
`BangComultComponentsAdmissible` (to assemble `bangComult`) together with
`SymmetricContractionDayFactorization` (compare recovers contraction) and
transport of coefficientwise counit/coassoc/cocomm laws. -/
def BangDayComonoid (A : ℕ) : Prop :=
  BangComultComponentsAdmissible A ∧
    SymmetricContractionDayFactorization A

/-- Resume marker: the standard split-sum construction of Day comultiplication
is exactly `BangComultComponentsAdmissible`. -/
theorem bang_day_comult_gate (A : ℕ) :
    BangComultComponentsAdmissible A ↔
      ∀ (n : ℕ) (x : ((bang A).obj n).Carrier)
        (L : Module) (β : Bilinear (bang A) (bang A) L),
        ∃ z : (L.obj n).Carrier,
          (L.obj n).HasSum
            (fun pq : ℕ × ℕ =>
              DayCoend.evaluate L β
                ((bangComultComponent A pq.1 pq.2).app n x))
            z := by
  constructor
  · intro h n x L β
    simpa [bangComultComponentFamily] using h n x L β
  · intro h n x L β
    simpa [bangComultComponentFamily] using h n x L β

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

/-- Yoneda unit at homogeneous degree `k`, injected into the series. -/
noncomputable def bangDegreeUnit (A k : ℕ) :
    ((bang A).obj (tensorPowerDimension A k)).Carrier :=
  (representableToBang A k).app (tensorPowerDimension A k)
    (Superoperator.identity (tensorPowerDimension A k))

/-- Unfolding of `bangSplitToRepDay` on a representable element. -/
theorem bangSplitToRepDay_app (A p q n : ℕ)
    (Φ : ((representable
        (tensorPowerDimension A p * tensorPowerDimension A q)).obj n).Carrier) :
    (bangSplitToRepDay A p q).app n Φ =
      (dayTensor
          (representable (tensorPowerDimension A p))
          (representable (tensorPowerDimension A q))).act
        ((DayCoend.intro
            (representable (tensorPowerDimension A p))
            (representable (tensorPowerDimension A q))).app
          (Superoperator.identity (tensorPowerDimension A p)
            : ((representable (tensorPowerDimension A p)).obj
                (tensorPowerDimension A p)).Carrier)
          (Superoperator.identity (tensorPowerDimension A q)
            : ((representable (tensorPowerDimension A q)).obj
                (tensorPowerDimension A q)).Carrier))
        Φ :=
  rfl

/-- Evaluation of a Day comultiplication component: the series Day map of the
Yoneda coend unit, acted by the contraction split. -/
theorem bangComultComponent_evaluate (A p q n : ℕ)
    (x : ((bang A).obj n).Carrier)
    (L : Module) (β : Bilinear (bang A) (bang A) L) :
    DayCoend.evaluate L β ((bangComultComponent A p q).app n x) =
      L.act
        (β.app (bangDegreeUnit A p) (bangDegreeUnit A q))
        ((bangSplitComponent A p q).app n x) := by
  let idp : ((representable (tensorPowerDimension A p)).obj
      (tensorPowerDimension A p)).Carrier :=
    Superoperator.identity (tensorPowerDimension A p)
  let idq : ((representable (tensorPowerDimension A q)).obj
      (tensorPowerDimension A q)).Carrier :=
    Superoperator.identity (tensorPowerDimension A q)
  let Φ : Superoperator n
      (tensorPowerDimension A p * tensorPowerDimension A q) :=
    (bangSplitComponent A p q).app n x
  let gen :=
    (DayCoend.intro
        (representable (tensorPowerDimension A p))
        (representable (tensorPowerDimension A q))).app idp idq
  -- `bangComultComponent = map ∘ splitToRepDay ∘ split`.
  change
      (DayCoend.lift β).app n
          ((DayTensor.map
              (representableToBang A p) (representableToBang A q)).app n
            ((bangSplitToRepDay A p q).app n Φ)) =
        L.act (β.app (bangDegreeUnit A p) (bangDegreeUnit A q)) Φ
  have hsplit :
      (bangSplitToRepDay A p q).app n Φ =
        (dayTensor
            (representable (tensorPowerDimension A p))
            (representable (tensorPowerDimension A q))).act gen Φ :=
    bangSplitToRepDay_app A p q n Φ
  rw [hsplit]
  -- Push the Day bifunctor through the Yoneda action.
  rw [(DayTensor.map (representableToBang A p)
      (representableToBang A q)).naturality gen Φ]
  -- Push `lift β` through the series Day action.
  rw [(DayCoend.lift β).naturality _ Φ]
  -- Reduce the mapped generator.
  have hintro :
      (DayTensor.map
          (representableToBang A p) (representableToBang A q)).app
          (tensorPowerDimension A p * tensorPowerDimension A q) gen =
        (DayCoend.intro (bang A) (bang A)).app
          (bangDegreeUnit A p) (bangDegreeUnit A q) := by
    unfold gen idp idq bangDegreeUnit representableToBang
    exact DayTensor.map_intro
      (representableToBang A p) (representableToBang A q)
      (Superoperator.identity (tensorPowerDimension A p))
      (Superoperator.identity (tensorPowerDimension A q))
  rw [hintro]
  -- `lift.app (intro x y) = β.app x y` after `act_id`.
  change
      L.act
          (DayCoend.evaluate L β
            ((DayCoend.intro (bang A) (bang A)).app
              (bangDegreeUnit A p) (bangDegreeUnit A q)))
          Φ =
        L.act (β.app (bangDegreeUnit A p) (bangDegreeUnit A q)) Φ
  rw [DayCoend.evaluate_intro]

/-- Off-degree injections are annihilated by a fixed split component. -/
theorem bangComultComponent_comp_injection_eq_zero (A p q k n : ℕ)
    (hk : k ≠ p + q)
    (y : ((symmetricPower A k).obj n).Carrier) :
    (bangComultComponent A p q).app n
        ((bangInjection A k).app n y) = 0 := by
  have hsplit :
      (bangSplitComponent A p q).app n
          ((bangInjection A k).app n y) = 0 := by
    change
        Superoperator.comp
          (Superoperator.ofEquivalence (tensorSplitEquiv A p q))
          ((((countableProductInjection
              (fun j => symmetricPower A j) k).app n y)
            (p + q)).val) =
          0
    have hz :
        ((countableProductInjection
            (fun j => symmetricPower A j) k).app n y) (p + q) =
          (0 : SymmetricElement A (p + q) n) := by
      change (if h : p + q = k then h.symm ▸ y else 0) =
        (0 : SymmetricElement A (p + q) n)
      simp [Ne.symm hk]
    rw [hz, SymmetricElement.zero_val, Superoperator.comp_zero_right]
  change
      (bangRepDayToSeriesDay A p q).app n
          ((bangSplitToRepDay A p q).app n
            ((bangSplitComponent A p q).app n
              ((bangInjection A k).app n y))) =
        0
  rw [hsplit, (bangSplitToRepDay A p q).map_zero,
    (bangRepDayToSeriesDay A p q).map_zero]

/-- A comultiplication component depends only on the homogeneous
coefficient of total degree `p + q`. -/
theorem bangComultComponent_eq_of_injection (A p q n : ℕ)
    (x : ((bang A).obj n).Carrier) :
    (bangComultComponent A p q).app n x =
      (bangComultComponent A p q).app n
        ((bangInjection A (p + q)).app n (x (p + q))) := by
  have hx :=
    (bangComultComponent A p q).map_sum
      (countableProduct_hasSum_coordinates
        (fun j => symmetricPower A j) n x)
  have hsupp :
      ∀ k, k ≠ p + q →
        (bangComultComponent A p q).app n
            ((bangInjection A k).app n (x k)) = 0 :=
    fun k hk => bangComultComponent_comp_injection_eq_zero A p q k n hk _
  have hfam :
      (fun k =>
          (bangComultComponent A p q).app n
            ((bangInjection A k).app n (x k))) =
        fun k =>
          if k = p + q then
            (bangComultComponent A p q).app n
              ((bangInjection A (p + q)).app n (x (p + q)))
          else 0 := by
    funext k
    by_cases hk : k = p + q
    · subst hk; simp
    · rw [hsupp k hk, if_neg hk]
  have hx' :
      ((dayTensor (bang A) (bang A)).obj n).HasSum
        (fun k =>
          if k = p + q then
            (bangComultComponent A p q).app n
              ((bangInjection A (p + q)).app n (x (p + q)))
          else 0)
        ((bangComultComponent A p q).app n x) := by
    convert hx using 1
    exact hfam.symm
  have hsingle :=
    Fiber.hasSum_singleCoordinate
      ((dayTensor (bang A) (bang A)).obj n) (p + q)
      ((bangComultComponent A p q).app n
        ((bangInjection A (p + q)).app n (x (p + q))))
  exact ((dayTensor (bang A) (bang A)).obj n).summation.unique
    hx' hsingle

/-- For `A = 1` every tensor-power dimension is `1`. -/
theorem tensorPowerDimension_one_eq (k : ℕ) :
    tensorPowerDimension 1 k = 1 := by
  simp [tensorPowerDimension_eq_pow, one_pow]

/-- Cast of an `A = 1` homogeneous coefficient to fiber dimension `1`. -/
noncomputable def bangOneCoeff (n k : ℕ)
    (x : SymmetricElement 1 k n) : Superoperator n 1 :=
  (tensorPowerDimension_one_eq k) ▸ x.val

/-- The `A = 1` series with identity in every homogeneous degree (fiber `1`). -/
noncomputable def bangOneDegreeUnits :
    ((bang 1).obj 1).Carrier :=
  fun k =>
    (symmetricPowerProjection 1 k).app 1 <|
      show Superoperator 1 (tensorPowerDimension 1 k) from
        cast (congrArg (Superoperator 1) (tensorPowerDimension_one_eq k).symm)
          (Superoperator.identity 1)

/-- Degree-`k` unit, injected into the common fiber `1`. -/
noncomputable def bangDegreeUnitOne (k : ℕ) :
    ((bang 1).obj 1).Carrier :=
  (bangInjection 1 k).app 1 (bangOneDegreeUnits k)

theorem bangDegreeUnitOne_hasSum :
    ((bang 1).obj 1).HasSum bangDegreeUnitOne bangOneDegreeUnits :=
  countableProduct_hasSum_coordinates
    (fun j => symmetricPower 1 j) 1 bangOneDegreeUnits

/-- Rectangle summability of `β` on the `A = 1` degree-unit series. -/
theorem bangOne_degreeUnit_rectangle_hasSum
    (L : Module.{0}) (β : Bilinear (bang 1) (bang 1) L) :
    (L.obj (1 * 1)).HasSum
      (fun pq : ℕ × ℕ =>
        β.app (bangDegreeUnitOne pq.1) (bangDegreeUnitOne pq.2))
      (β.app bangOneDegreeUnits bangOneDegreeUnits) := by
  have hU := bangDegreeUnitOne_hasSum
  have hrows (p : ℕ) :
      (L.obj (1 * 1)).HasSum
        (fun q : ℕ => β.app (bangDegreeUnitOne p) (bangDegreeUnitOne q))
        (β.app (bangDegreeUnitOne p) bangOneDegreeUnits) :=
    β.map_sum_right (bangDegreeUnitOne p) hU
  have hcol :
      (L.obj (1 * 1)).HasSum
        (fun p : ℕ => β.app (bangDegreeUnitOne p) bangOneDegreeUnits)
        (β.app bangOneDegreeUnits bangOneDegreeUnits) :=
    β.map_sum_left bangOneDegreeUnits hU
  have hflat :=
    ((L.obj (1 * 1)).summation.flatten
      (fun p q => β.app (bangDegreeUnitOne p) (bangDegreeUnitOne q))
      (β.app bangOneDegreeUnits bangOneDegreeUnits)).mpr
        ⟨fun p => β.app (bangDegreeUnitOne p) bangOneDegreeUnits,
          hrows, hcol⟩
  exact
    ((L.obj (1 * 1)).summation.reindex (Equiv.sigmaEquivProd ℕ ℕ)
      (fun pq : ℕ × ℕ =>
        β.app (bangDegreeUnitOne pq.1) (bangDegreeUnitOne pq.2))
      (β.app bangOneDegreeUnits bangOneDegreeUnits)).mp hflat

/-- Outer series gate for assembling `A = 1` admissibility from homogeneous
diagonal rows: joint `L.act d_k Φ_k` with summable `(d_k)`. -/
def BangComultSeriesActHasSum : Prop :=
  ∀ (n : ℕ) (x : ((bang 1).obj n).Carrier)
    (L : Module.{0}) (d : ℕ → (L.obj 1).Carrier) (D : (L.obj 1).Carrier),
    (L.obj 1).HasSum d D →
      ∃ z : (L.obj n).Carrier,
        (L.obj n).HasSum (fun k => L.act (d k) (bangOneCoeff n k (x k))) z

/-- The outer series gate is `Module.act_sum_from_one` (fiber `1 = 1 * 1`). -/
theorem bangComultSeriesActHasSum_holds : BangComultSeriesActHasSum := by
  intro n x L d D hD
  exact L.act_sum_from_one (fun k => bangOneCoeff n k (x k)) hD

/-- Identity cast along a dimension equality as a basis equivalence. -/
theorem cast_identity_eq_ofEquivalence {a b : ℕ} (h : a = b) :
    cast (congrArg (Superoperator a) h) (Superoperator.identity a) =
      Superoperator.ofEquivalence (finCongr h) := by
  cases h
  exact (Superoperator.ofEquivalence_refl a).symm

/-- `A = 1` Yoneda degree unit is the fiber-`1` unit acted by the dimension cast. -/
theorem bangDegreeUnit_eq_act (k : ℕ) :
    bangDegreeUnit 1 k =
      (bang 1).act (bangDegreeUnitOne k)
        (Superoperator.ofEquivalence
          (finCongr (tensorPowerDimension_one_eq k))) := by
  let h := tensorPowerDimension_one_eq k
  change
    (bangInjection 1 k).app (tensorPowerDimension 1 k)
        ((symmetricPowerProjection 1 k).app (tensorPowerDimension 1 k)
          (Superoperator.identity (tensorPowerDimension 1 k))) =
      (bang 1).act
        ((bangInjection 1 k).app 1 (bangOneDegreeUnits k))
        (Superoperator.ofEquivalence (finCongr h))
  have hn :=
    (bangInjection 1 k).naturality (bangOneDegreeUnits k)
      (Superoperator.ofEquivalence (finCongr h))
  refine Eq.trans ?_ hn
  congr 1
  change
    (symmetricPowerProjection 1 k).app (tensorPowerDimension 1 k)
        (Superoperator.identity (tensorPowerDimension 1 k)) =
      (symmetricPower 1 k).act
        ((symmetricPowerProjection 1 k).app 1
          (cast (congrArg (Superoperator 1) h.symm)
            (Superoperator.identity 1)))
        (Superoperator.ofEquivalence (finCongr h))
  have hp :=
    (symmetricPowerProjection 1 k).naturality
      (cast (congrArg (Superoperator 1) h.symm)
        (Superoperator.identity 1))
      (Superoperator.ofEquivalence (finCongr h))
  refine Eq.trans ?_ hp
  congr 1
  show Superoperator.identity (tensorPowerDimension 1 k) =
    Superoperator.comp
      (cast (congrArg (Superoperator 1) h.symm) (Superoperator.identity 1))
      (Superoperator.ofEquivalence (finCongr h))
  rw [cast_identity_eq_ofEquivalence h.symm, Superoperator.ofEquivalence_comp]
  have : (finCongr h).trans (finCongr h.symm) = Equiv.refl _ := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    simp
  rw [this, Superoperator.ofEquivalence_refl]

/-- Every index of a one-element `Fin` is zero. -/
theorem fin_val_eq_zero_of_card_one {d : ℕ} (hd : d = 1) (i : Fin d) :
    (i : ℕ) = 0 := by
  have : (i : ℕ) < 1 := hd ▸ i.isLt
  exact Nat.lt_one_iff.mp this

/-- Split channel for `A = 1`, after tensoring dimension casts, equals `bangOneCoeff`. -/
theorem bangSplit_tensor_cast_eq_oneCoeff (p q n : ℕ)
    (x : ((bang 1).obj n).Carrier) :
    Superoperator.comp
      (Superoperator.tensor
        (Superoperator.ofEquivalence (finCongr (tensorPowerDimension_one_eq p)))
        (Superoperator.ofEquivalence (finCongr (tensorPowerDimension_one_eq q))))
      ((bangSplitComponent 1 p q).app n x) =
      bangOneCoeff n (p + q) (x (p + q)) := by
  simp only [bangSplitComponent, bangOneCoeff]
  rw [Superoperator.comp_assoc]
  let hp := tensorPowerDimension_one_eq p
  let hq := tensorPowerDimension_one_eq q
  let hk := tensorPowerDimension_one_eq (p + q)
  have htarget :
      Superoperator.comp
          (Superoperator.tensor
            (Superoperator.ofEquivalence (finCongr hp))
            (Superoperator.ofEquivalence (finCongr hq)))
          (Superoperator.ofEquivalence (tensorSplitEquiv 1 p q)) =
        Superoperator.ofEquivalence (finCongr hk) := by
    rw [Superoperator.tensor_ofEquivalence, Superoperator.ofEquivalence_comp]
    congr 1
    apply Equiv.ext
    intro i
    apply Fin.ext
    have hL :
        ((((tensorSplitEquiv 1 p q).trans
          (Superoperator.tensorEquiv (finCongr hp) (finCongr hq))) i :
            Fin (1 * 1)) : ℕ) = 0 :=
      fin_val_eq_zero_of_card_one (by rfl) _
    have hR : (((finCongr hk) i : Fin 1) : ℕ) = 0 :=
      fin_val_eq_zero_of_card_one rfl _
    exact hL.trans hR.symm
  have hΦ :=
    congrArg (fun Φ => Superoperator.comp Φ (x (p + q)).val) htarget
  exact hΦ.trans (Superoperator.comp_ofEquivalence_finCongr hk (x (p + q)).val)

/-- Equivalence between pairs and ordered partitions of their total degree. -/
def degreePartitionEquiv : ℕ × ℕ ≃ (Σ t : ℕ, DegreePartition t) where
  toFun := pairToDegreePartition
  invFun := fun p => degreePartitionToPair p.1 p.2
  left_inv := pairToDegreePartition_toPair
  right_inv := by
    rintro ⟨t, part⟩
    dsimp [pairToDegreePartition, degreePartitionToPair]
    have hs : part.val + (t - part.val) = t :=
      Nat.add_sub_of_le (Nat.le_of_lt_succ part.isLt)
    refine Sigma.ext hs ?_
    let lhs : Fin (part.val + (t - part.val) + 1) :=
      ⟨part.val, Nat.lt_succ_of_le (Nat.le_add_right _ _)⟩
    let hs' : part.val + (t - part.val) + 1 = t + 1 :=
      congrArg (· + 1) hs
    have hEq : Fin.cast hs' lhs = part := by
      apply Fin.ext
      exact Fin.val_cast hs' lhs
    refine HEq.trans (b := Fin.cast hs' lhs) ?_ (heq_of_eq hEq)
    have hfun : (Fin.cast hs' : Fin _ → Fin _) =
        cast (congrArg Fin hs') :=
      Fin.cast_eq_cast hs'
    show lhs ≍ Fin.cast hs' lhs
    rw [show Fin.cast hs' lhs = cast (congrArg Fin hs') lhs from
      congrFun hfun lhs]
    exact (cast_heq (congrArg Fin hs') lhs).symm

/-- Homogeneous `A = 1` family vanishes off the diagonal `p + q = k`. -/
theorem bangComultComponent_evaluate_injection_eq_zero
    (p q k n : ℕ) (hk : k ≠ p + q)
    (y : ((symmetricPower 1 k).obj n).Carrier)
    (L : Module) (β : Bilinear (bang 1) (bang 1) L) :
    DayCoend.evaluate L β
        ((bangComultComponent 1 p q).app n
          ((bangInjection 1 k).app n y)) =
      0 := by
  rw [bangComultComponent_comp_injection_eq_zero 1 p q k n hk y]
  exact DayCoend.evaluate_zero β

/-- Evaluation at `A = 1`: Day component equals rectangle coefficient acted by
the total-degree series channel. -/
theorem bangComultComponent_evaluate_one (p q n : ℕ)
    (x : ((bang 1).obj n).Carrier)
    (L : Module) (β : Bilinear (bang 1) (bang 1) L) :
    DayCoend.evaluate L β ((bangComultComponent 1 p q).app n x) =
      L.act (β.app (bangDegreeUnitOne p) (bangDegreeUnitOne q))
        (bangOneCoeff n (p + q) (x (p + q))) := by
  have he := bangComultComponent_evaluate 1 p q n x L β
  rw [he, bangDegreeUnit_eq_act p, bangDegreeUnit_eq_act q, β.naturality]
  have hact := L.act_comp
    (β.app (bangDegreeUnitOne p) (bangDegreeUnitOne q))
    (Superoperator.tensor
      (Superoperator.ofEquivalence (finCongr (tensorPowerDimension_one_eq p)))
      (Superoperator.ofEquivalence (finCongr (tensorPowerDimension_one_eq q))))
    ((bangSplitComponent 1 p q).app n x)
  rw [hact, bangSplit_tensor_cast_eq_oneCoeff]

/-- Mixed-partition admissibility for `A = 1`. -/
theorem bangComultComponentsAdmissible_one :
    BangComultComponentsAdmissible 1 := by
  intro n x L β
  have hrect := bangOne_degreeUnit_rectangle_hasSum L β
  have hre :
      (L.obj (1 * 1)).HasSum
        (fun p : Σ t : ℕ, DegreePartition t =>
          β.app (bangDegreeUnitOne (degreePartitionToPair p.1 p.2).1)
            (bangDegreeUnitOne (degreePartitionToPair p.1 p.2).2))
        (β.app bangOneDegreeUnits bangOneDegreeUnits) :=
    ((L.obj (1 * 1)).summation.reindex degreePartitionEquiv.symm
      (fun pq =>
        β.app (bangDegreeUnitOne pq.1) (bangDegreeUnitOne pq.2))
      (β.app bangOneDegreeUnits bangOneDegreeUnits)).mpr hrect
  obtain ⟨row, hrows, hrowSum⟩ :=
    ((L.obj (1 * 1)).summation.flatten
      (fun t (part : DegreePartition t) =>
        β.app (bangDegreeUnitOne (degreePartitionToPair t part).1)
          (bangDegreeUnitOne (degreePartitionToPair t part).2))
      (β.app bangOneDegreeUnits bangOneDegreeUnits)).mp hre
  obtain ⟨Z, hZ⟩ :=
    bangComultSeriesActHasSum_holds n x L
      (fun k => row k) (β.app bangOneDegreeUnits bangOneDegreeUnits) hrowSum
  refine ⟨Z, ?_⟩
  have hfam :
      (fun pq : ℕ × ℕ =>
          DayCoend.evaluate L β (bangComultComponentFamily 1 n x pq)) =
        fun pq : ℕ × ℕ =>
          L.act (β.app (bangDegreeUnitOne pq.1) (bangDegreeUnitOne pq.2))
            (bangOneCoeff n (pq.1 + pq.2) (x (pq.1 + pq.2))) := by
    funext pq
    simpa [bangComultComponentFamily] using
      bangComultComponent_evaluate_one pq.1 pq.2 n x L β
  rw [hfam]
  have hflat :
      (L.obj n).HasSum
        (fun p : Σ t : ℕ, DegreePartition t =>
          L.act
            (β.app (bangDegreeUnitOne (degreePartitionToPair p.1 p.2).1)
              (bangDegreeUnitOne (degreePartitionToPair p.1 p.2).2))
            (bangOneCoeff n p.1 (x p.1)))
        Z :=
    ((L.obj n).summation.flatten
        (fun t (part : DegreePartition t) =>
          L.act
            (β.app (bangDegreeUnitOne (degreePartitionToPair t part).1)
              (bangDegreeUnitOne (degreePartitionToPair t part).2))
            (bangOneCoeff n t (x t)))
        Z).mpr
      ⟨fun t => L.act (row t) (bangOneCoeff n t (x t)),
        fun t => L.act_sum_element (bangOneCoeff n t (x t)) (hrows t),
        hZ⟩
  have hflat' :
      (L.obj n).HasSum
        (fun p : Σ t : ℕ, DegreePartition t =>
          L.act
            (β.app (bangDegreeUnitOne (degreePartitionToPair p.1 p.2).1)
              (bangDegreeUnitOne (degreePartitionToPair p.1 p.2).2))
            (bangOneCoeff n
              ((degreePartitionToPair p.1 p.2).1 +
                (degreePartitionToPair p.1 p.2).2)
              (x
                ((degreePartitionToPair p.1 p.2).1 +
                  (degreePartitionToPair p.1 p.2).2))))
        Z := by
    convert hflat using 1
    funext p
    rw [degreePartitionToPair_snd_add]
  exact
    ((L.obj n).summation.reindex degreePartitionEquiv.symm
      (fun pq =>
        L.act (β.app (bangDegreeUnitOne pq.1) (bangDegreeUnitOne pq.2))
          (bangOneCoeff n (pq.1 + pq.2) (x (pq.1 + pq.2))))
      Z).mp hflat'

/-- Unconditional Day comultiplication for the one-dimensional exponential. -/
noncomputable def bangComult_one :
    Hom (bang 1) (dayTensor (bang 1) (bang 1)) :=
  bangComult 1 bangComultComponentsAdmissible_one

/-! ## Special case `A = 0`: only degree 0 survives -/

/-- There is a unique superoperator into the zero-dimensional system. -/
theorem superoperator_outDim_zero {n : ℕ} (Φ : Superoperator n 0) :
    Φ = 0 := by
  apply Superoperator.ext
  apply CPMap.ext
  ext a b
  exact isEmptyElim a.1

/-- For `A = 0`, every positive symmetric degree is the zero channel. -/
theorem bang_zero_high_degree (n k : ℕ) (hk : 0 < k)
    (x : ((bang 0).obj n).Carrier) :
    (x k).val = 0 := by
  cases k with
  | zero => exact (lt_irrefl _ hk).elim
  | succ k =>
    have hdim : tensorPowerDimension 0 (k + 1) = 0 := by
      simp [tensorPowerDimension]
    apply Superoperator.ext
    apply CPMap.ext
    ext a b
    have : IsEmpty (Fin (tensorPowerDimension 0 (k + 1))) := by
      rw [hdim]; infer_instance
    exact isEmptyElim a.1

/-- Homogeneous Day components vanish off the `(0,0)` slot when `A = 0`. -/
theorem bangComultComponentFamily_zero_of_pos_degree
    (n : ℕ) (x : ((bang 0).obj n).Carrier) (pq : ℕ × ℕ)
    (hpq : pq ≠ (0, 0)) :
    bangComultComponentFamily 0 n x pq = 0 := by
  have hpos : 0 < pq.1 + pq.2 := by
    rcases pq with ⟨p, q⟩
    change (p, q) ≠ (0, 0) at hpq
    cases p with
    | zero =>
      cases q with
      | zero => exact (hpq rfl).elim
      | succ q => exact Nat.succ_pos _
    | succ p => exact Nat.add_pos_left (Nat.succ_pos _) _
  have hsplit :
      (bangSplitComponent 0 pq.1 pq.2).app n x = 0 := by
    change
        Superoperator.comp
          (Superoperator.ofEquivalence
            (tensorSplitEquiv 0 pq.1 pq.2))
          (x (pq.1 + pq.2)).val =
          0
    rw [bang_zero_high_degree n (pq.1 + pq.2) hpos x]
    exact Superoperator.comp_zero_right _
  change
      (bangComultComponent 0 pq.1 pq.2).app n x = 0
  simp only [bangComultComponent, Hom.comp_app]
  rw [hsplit, (bangSplitToRepDay 0 pq.1 pq.2).map_zero,
    (bangRepDayToSeriesDay 0 pq.1 pq.2).map_zero]

/-- Mixed-partition admissibility holds for `A = 0`: only the `(0,0)`
component can be nonzero, so the Day family is a singleton sum. -/
theorem bangComultComponentsAdmissible_zero :
    BangComultComponentsAdmissible 0 := by
  intro n x L β
  refine
    ⟨DayCoend.evaluate L β (bangComultComponentFamily 0 n x (0, 0)), ?_⟩
  have hfam :
      (fun pq : ℕ × ℕ =>
          DayCoend.evaluate L β (bangComultComponentFamily 0 n x pq)) =
        fun pq : ℕ × ℕ =>
          if pq = (0, 0) then
            DayCoend.evaluate L β (bangComultComponentFamily 0 n x (0, 0))
          else 0 := by
    funext pq
    by_cases hpq : pq = (0, 0)
    · subst hpq; simp
    · rw [bangComultComponentFamily_zero_of_pos_degree n x pq hpq,
        if_neg hpq]
      exact DayCoend.evaluate_zero β
  rw [hfam]
  exact Fiber.hasSum_singleAt (L.obj n) (0, 0)
    (DayCoend.evaluate L β (bangComultComponentFamily 0 n x (0, 0)))

/-- Unconditional Day comultiplication for the zero-dimensional exponential. -/
noncomputable def bangComult_zero :
    Hom (bang 0) (dayTensor (bang 0) (bang 0)) :=
  bangComult 0 bangComultComponentsAdmissible_zero

/-- For `A = 0` the Day comultiplication is exactly the `(0,0)` homogeneous
component (singleton coend sum). -/
theorem bangComult_zero_eq_component (n : ℕ)
    (x : ((bang 0).obj n).Carrier) :
    bangComult_zero.app n x =
      (bangComultComponent 0 0 0).app n x := by
  have hsum :
      DayCoend.HasSum (bangComultComponentFamily 0 n x)
        ((bangComultComponent 0 0 0).app n x) := by
    intro L β
    have hfam :
        (fun pq : ℕ × ℕ =>
            DayCoend.evaluate L β (bangComultComponentFamily 0 n x pq)) =
          fun pq : ℕ × ℕ =>
            if pq = (0, 0) then
              DayCoend.evaluate L β
                ((bangComultComponent 0 0 0).app n x)
            else 0 := by
      funext pq
      by_cases hpq : pq = (0, 0)
      · subst hpq; rfl
      · rw [bangComultComponentFamily_zero_of_pos_degree n x pq hpq,
          if_neg hpq]
        exact DayCoend.evaluate_zero β
    rw [hfam]
    exact Fiber.hasSum_singleAt (L.obj n) (0, 0) _
  exact ((dayTensor (bang 0) (bang 0)).obj n).summation.unique
    (bangComultApp_hasSum 0 bangComultComponentsAdmissible_zero n x) hsum


/-- Admissibility for the two fibers where the acted outer series lands in
fiber `1` (so `Module.act_sum_from_one` applies). -/
theorem bangComultComponentsAdmissible_of_le_one (A : ℕ) (hA : A ≤ 1) :
    BangComultComponentsAdmissible A := by
  interval_cases A
  · exact bangComultComponentsAdmissible_zero
  · exact bangComultComponentsAdmissible_one

/-- Unconditional Day comultiplication when `A ≤ 1`. -/
noncomputable def bangComult_of_le_one (A : ℕ) (hA : A ≤ 1) :
    Hom (bang A) (dayTensor (bang A) (bang A)) :=
  bangComult A (bangComultComponentsAdmissible_of_le_one A hA)

/-! ## Day factorization of contraction for `A ≤ 1` -/

/-- For `A = 1`, every tensor-factor permutation is the identity equivalence. -/
theorem factorPermutationEquiv_one (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    factorPermutationEquiv 1 k σ = Equiv.refl _ := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  have hd := tensorPowerDimension_one_eq k
  exact (fin_val_eq_zero_of_card_one hd _).trans
    (fin_val_eq_zero_of_card_one hd _).symm

/-- For `A = 1`, every tensor-factor permutation channel is the identity. -/
theorem factorPermutation_one (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    factorPermutation 1 k σ =
      Superoperator.identity (tensorPowerDimension 1 k) := by
  change Superoperator.ofEquivalence (factorPermutationEquiv 1 k σ) = _
  rw [factorPermutationEquiv_one, Superoperator.ofEquivalence_refl]

/-- Symmetric averaging is trivial on one-dimensional tensor powers. -/
theorem symmetricAverage_one (k : ℕ) :
    symmetricAverage 1 k =
      Superoperator.identity (tensorPowerDimension 1 k) := by
  apply Superoperator.ext
  apply CPMap.ext_apply
  intro ρ
  rw [symmetricAverage_applyMat]
  simp_rw [factorPermutation_one]
  have hid :
      (Superoperator.identity (tensorPowerDimension 1 k)).cp.applyMat ρ = ρ := by
    change (CPMap.identity _).applyMat ρ = ρ
    exact CPMap.applyMat_identity ρ
  simp_rw [hid]
  rw [Finset.sum_const]
  have hcard :
      (Finset.univ : Finset (Equiv.Perm (Fin k))).card = Nat.factorial k := by
    simp [Fintype.card_perm]
  rw [hcard, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hk : ((Nat.factorial k : ℝ)⁻¹ : ℂ) * (Nat.factorial k : ℂ) = 1 := by
    rw [← Complex.ofReal_natCast (Nat.factorial k), ← Complex.ofReal_inv,
      ← Complex.ofReal_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)),
      Complex.ofReal_one]
  rw [hk, one_smul]

/-- Symmetric averaging is trivial on the unique degree-zero zero-dimensional
fiber. -/
theorem symmetricAverage_zero_zero :
    symmetricAverage 0 0 = Superoperator.identity (tensorPowerDimension 0 0) := by
  have hdim : tensorPowerDimension 0 0 = 1 := by simp [tensorPowerDimension]
  apply Superoperator.ext
  apply CPMap.ext_apply
  intro ρ
  rw [symmetricAverage_applyMat]
  have hperm (σ : Equiv.Perm (Fin 0)) :
      factorPermutation 0 0 σ =
        Superoperator.identity (tensorPowerDimension 0 0) := by
    change Superoperator.ofEquivalence (factorPermutationEquiv 0 0 σ) = _
    have : factorPermutationEquiv 0 0 σ = Equiv.refl _ := by
      apply Equiv.ext
      intro i
      apply Fin.ext
      exact (fin_val_eq_zero_of_card_one hdim _).trans
        (fin_val_eq_zero_of_card_one hdim _).symm
    rw [this, Superoperator.ofEquivalence_refl]
  simp_rw [hperm]
  have hid :
      (Superoperator.identity (tensorPowerDimension 0 0)).cp.applyMat ρ = ρ := by
    change (CPMap.identity _).applyMat ρ = ρ
    exact CPMap.applyMat_identity ρ
  simp_rw [hid]
  rw [Finset.sum_const]
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin 0))).card = 1 := by decide
  rw [hcard, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num

/-- For `A ≤ 1`, symmetric averaging coincides with the identity channel. -/
theorem symmetricAverage_of_le_one (A k : ℕ) (hA : A ≤ 1) :
    symmetricAverage A k =
      Superoperator.identity (tensorPowerDimension A k) := by
  interval_cases A
  · cases k with
    | zero => exact symmetricAverage_zero_zero
    | succ k =>
      apply Superoperator.ext
      apply CPMap.ext
      ext a b
      have : IsEmpty (Fin (tensorPowerDimension 0 (k + 1))) := by
        simp [tensorPowerDimension]; infer_instance
      exact isEmptyElim a.1
  · exact symmetricAverage_one k

/-- Coordinate form of the Yoneda degree unit in the series. -/
theorem bangDegreeUnit_apply (A k j : ℕ) :
    bangDegreeUnit A k j =
      if h : j = k then
        h.symm ▸
          (symmetricPowerProjection A k).app
            (tensorPowerDimension A k)
            (Superoperator.identity (tensorPowerDimension A k))
      else 0 :=
  rfl

/-- Diagonal slot of a square injection recovers the injected channel. -/
theorem injection_square_eq_slot (A p q n : ℕ)
    (Φ : Superoperator n
      (tensorPowerDimension A p * tensorPowerDimension A q)) :
    (countableRepresentableDayTensorInjection
        (tensorPowerDimension A) (tensorPowerDimension A) p q).app n Φ p q =
      Φ := by
  dsimp [countableRepresentableDayTensorInjection, Hom.comp,
    countableProductInjection]
  simp only [↓reduceDIte]

/-- Off-row slots of a square injection vanish. -/
theorem injection_square_eq_zero_left (A p q n i j : ℕ) (hi : i ≠ p)
    (Φ : Superoperator n
      (tensorPowerDimension A p * tensorPowerDimension A q)) :
    (countableRepresentableDayTensorInjection
        (tensorPowerDimension A) (tensorPowerDimension A) p q).app n Φ i j =
      0 := by
  dsimp [countableRepresentableDayTensorInjection, Hom.comp,
    countableProductInjection]
  simp only [hi, ↓reduceDIte]
  rfl

/-- Off-column slots of a square injection vanish. -/
theorem injection_square_eq_zero_right (A p q n j : ℕ) (hj : j ≠ q)
    (Φ : Superoperator n
      (tensorPowerDimension A p * tensorPowerDimension A q)) :
    (countableRepresentableDayTensorInjection
        (tensorPowerDimension A) (tensorPowerDimension A) p q).app n Φ p j =
      0 := by
  dsimp [countableRepresentableDayTensorInjection, Hom.comp,
    countableProductInjection]
  simp only [↓reduceDIte, hj]
  rfl

/-- For `A ≤ 1`, Day compare on a homogeneous comult component is the
corresponding square injection of the contraction slot. -/
theorem compare_bangComultComponent_of_le_one (A : ℕ) (hA : A ≤ 1)
    (p q n : ℕ) (x : ((bang A).obj n).Carrier) :
    (symmetricSeriesDayCompare A).app n
        ((bangComultComponent A p q).app n x) =
      (countableRepresentableDayTensorInjection
          (tensorPowerDimension A) (tensorPowerDimension A) p q).app n
        ((bangSplitComponent A p q).app n x) := by
  have he :=
    bangComultComponent_evaluate A p q n x
      (symmetricFormalTensorSquare A) (symmetricSeriesDayBilinear A)
  have he' :
      (symmetricSeriesDayCompare A).app n
          ((bangComultComponent A p q).app n x) =
        (symmetricFormalTensorSquare A).act
          ((symmetricSeriesDayBilinear A).app
            (bangDegreeUnit A p) (bangDegreeUnit A q))
          ((bangSplitComponent A p q).app n x) := by
    simpa [symmetricSeriesDayCompare, DayCoend.lift] using he
  rw [he']
  funext i j
  change
      Superoperator.comp
          (Superoperator.tensor
            (bangDegreeUnit A p i).val
            (bangDegreeUnit A q j).val)
          ((bangSplitComponent A p q).app n x) =
        (countableRepresentableDayTensorInjection
            (tensorPowerDimension A) (tensorPowerDimension A) p q).app n
          ((bangSplitComponent A p q).app n x) i j
  let Φ : Superoperator n
      (tensorPowerDimension A p * tensorPowerDimension A q) :=
    (bangSplitComponent A p q).app n x
  by_cases hi : i = p
  · subst i
    by_cases hj : j = q
    · subst j
      have hup :
          bangDegreeUnit A p p =
            (symmetricPowerProjection A p).app
              (tensorPowerDimension A p)
              (Superoperator.identity (tensorPowerDimension A p)) := by
        simp [bangDegreeUnit_apply]
      have huq :
          bangDegreeUnit A q q =
            (symmetricPowerProjection A q).app
              (tensorPowerDimension A q)
              (Superoperator.identity (tensorPowerDimension A q)) := by
        simp [bangDegreeUnit_apply]
      rw [hup, huq]
      change Superoperator.comp
          (Superoperator.tensor
            (Superoperator.comp (symmetricAverage A p)
              (Superoperator.identity _))
            (Superoperator.comp (symmetricAverage A q)
              (Superoperator.identity _)))
          Φ =
        (countableRepresentableDayTensorInjection
            (tensorPowerDimension A) (tensorPowerDimension A) p q).app n Φ p q
      rw [Superoperator.comp_identity, Superoperator.comp_identity,
        symmetricAverage_of_le_one A p hA,
        symmetricAverage_of_le_one A q hA,
        Superoperator.tensor_identity, Superoperator.identity_comp,
        injection_square_eq_slot]
    · have huq : bangDegreeUnit A q j =
          (0 : SymmetricElement A j (tensorPowerDimension A q)) := by
        simp [bangDegreeUnit_apply, hj]; rfl
      have hten :
          Superoperator.tensor (bangDegreeUnit A p p).val
              (bangDegreeUnit A q j).val =
            (0 : Superoperator
              (tensorPowerDimension A p * tensorPowerDimension A q)
              (tensorPowerDimension A p * tensorPowerDimension A j)) := by
        have hz : (bangDegreeUnit A q j).val =
            (0 : Superoperator (tensorPowerDimension A q)
              (tensorPowerDimension A j)) := by
          rw [huq, SymmetricElement.zero_val]
        rw [hz]
        exact Superoperator.tensor_zero_right _
      have hL :
          Superoperator.comp
            (Superoperator.tensor (bangDegreeUnit A p p).val
              (bangDegreeUnit A q j).val) Φ =
          (0 : Superoperator n
            (tensorPowerDimension A p * tensorPowerDimension A j)) := by
        rw [hten]
        exact Superoperator.comp_zero_left
          (ℓ := tensorPowerDimension A p * tensorPowerDimension A j) Φ
      have hR :
          (countableRepresentableDayTensorInjection
              (tensorPowerDimension A) (tensorPowerDimension A) p q).app n Φ p j =
          (0 : Superoperator n
            (tensorPowerDimension A p * tensorPowerDimension A j)) :=
        injection_square_eq_zero_right A p q n j hj Φ
      exact hL.trans hR.symm
  · have hup : bangDegreeUnit A p i =
        (0 : SymmetricElement A i (tensorPowerDimension A p)) := by
      simp [bangDegreeUnit_apply, hi]; rfl
    have hten :
        Superoperator.tensor (bangDegreeUnit A p i).val
            (bangDegreeUnit A q j).val =
          (0 : Superoperator
            (tensorPowerDimension A p * tensorPowerDimension A q)
            (tensorPowerDimension A i * tensorPowerDimension A j)) := by
      have hz : (bangDegreeUnit A p i).val =
          (0 : Superoperator (tensorPowerDimension A p)
            (tensorPowerDimension A i)) := by
        rw [hup, SymmetricElement.zero_val]
      rw [hz]
      exact Superoperator.tensor_zero_left _
    have hL :
        Superoperator.comp
          (Superoperator.tensor (bangDegreeUnit A p i).val
            (bangDegreeUnit A q j).val) Φ =
        (0 : Superoperator n
          (tensorPowerDimension A i * tensorPowerDimension A j)) := by
      rw [hten]
      exact Superoperator.comp_zero_left
        (ℓ := tensorPowerDimension A i * tensorPowerDimension A j) Φ
    have hR :
        (countableRepresentableDayTensorInjection
            (tensorPowerDimension A) (tensorPowerDimension A) p q).app n Φ i j =
        (0 : Superoperator n
          (tensorPowerDimension A i * tensorPowerDimension A j)) :=
      injection_square_eq_zero_left A p q n i j hi Φ
    exact hL.trans hR.symm

/-- For `A ≤ 1`, Day comultiplication factors coefficientwise contraction
through the Day comparison. -/
theorem bangComult_factors_contraction_of_le_one (A : ℕ) (hA : A ≤ 1)
    (h : BangComultComponentsAdmissible A) :
    Hom.comp (symmetricSeriesDayCompare A) (bangComult A h) =
      symmetricContraction A := by
  ext n x
  have hsum :
      (symmetricFormalTensorSquare A).obj n |>.HasSum
        (fun pq : ℕ × ℕ =>
          (countableRepresentableDayTensorInjection
              (tensorPowerDimension A) (tensorPowerDimension A)
              pq.1 pq.2).app n
            ((symmetricContraction A).app n x pq.1 pq.2))
        ((symmetricContraction A).app n x) :=
    countableRepresentableDayTensor_hasSum_coordinates
      (tensorPowerDimension A) (tensorPowerDimension A) n
      ((symmetricContraction A).app n x)
  have hfam :
      (fun pq : ℕ × ℕ =>
          (symmetricSeriesDayCompare A).app n
            (bangComultComponentFamily A n x pq)) =
        fun pq : ℕ × ℕ =>
          (countableRepresentableDayTensorInjection
              (tensorPowerDimension A) (tensorPowerDimension A)
              pq.1 pq.2).app n
            ((symmetricContraction A).app n x pq.1 pq.2) := by
    funext pq
    simpa [bangComultComponentFamily, bangSplitComponent_eq_contraction_slot]
      using compare_bangComultComponent_of_le_one A hA pq.1 pq.2 n x
  have hcmp :
      (symmetricFormalTensorSquare A).obj n |>.HasSum
        (fun pq : ℕ × ℕ =>
          (symmetricSeriesDayCompare A).app n
            (bangComultComponentFamily A n x pq))
        ((symmetricSeriesDayCompare A).app n (bangComultApp A h n x)) := by
    simpa [symmetricSeriesDayCompare, DayCoend.lift] using
      bangComultApp_hasSum A h n x
        (symmetricFormalTensorSquare A) (symmetricSeriesDayBilinear A)
  rw [hfam] at hcmp
  exact
    ((symmetricFormalTensorSquare A).obj n).summation.unique hcmp hsum

/-- Unconditional Day factorization of contraction when `A ≤ 1`. -/
theorem bangComult_factors_contraction_le_one (A : ℕ) (hA : A ≤ 1) :
    Hom.comp (symmetricSeriesDayCompare A) (bangComult_of_le_one A hA) =
      symmetricContraction A :=
  bangComult_factors_contraction_of_le_one A hA
    (bangComultComponentsAdmissible_of_le_one A hA)

/-- Day factorization residual closed for `A ≤ 1`. -/
theorem symmetricContractionDayFactorization_of_le_one (A : ℕ) (hA : A ≤ 1) :
    SymmetricContractionDayFactorization A :=
  ⟨bangComult_of_le_one A hA, bangComult_factors_contraction_le_one A hA⟩

/-- Day comonoid package for `A ≤ 1`: admissibility plus factorization. -/
theorem bangDayComonoid_of_le_one (A : ℕ) (hA : A ≤ 1) :
    BangDayComonoid A :=
  ⟨bangComultComponentsAdmissible_of_le_one A hA,
    symmetricContractionDayFactorization_of_le_one A hA⟩

/-! ## Day left-counit ingredients for `A ≤ 1` -/

theorem ofEquivalence_dim_one {m n : ℕ} (_hm : m = 1) (hn : n = 1)
    (e f : Fin m ≃ Fin n) :
    Superoperator.ofEquivalence e = Superoperator.ofEquivalence f := by
  congr 1
  apply Equiv.ext
  intro i
  apply Fin.ext
  exact (fin_val_eq_zero_of_card_one hn (e i)).trans
    (fin_val_eq_zero_of_card_one hn (f i)).symm

theorem tensorLeftUnitor_comp_split_one (q : ℕ) :
    Superoperator.comp
        (Superoperator.tensorLeftUnitor (tensorPowerDimension 1 q))
        (Superoperator.ofEquivalence (tensorSplitEquiv 1 0 q)) =
      Superoperator.comp
        (Superoperator.ofEquivalence (homogeneousLeftUnitorEquiv 1 q))
        (Superoperator.ofEquivalence (tensorSplitEquiv 1 0 q)) := by
  have hsrc : tensorPowerDimension 1 (0 + q) = 1 := by
    rw [Nat.zero_add]; exact tensorPowerDimension_one_eq q
  have htgt : tensorPowerDimension 1 q = 1 := tensorPowerDimension_one_eq q
  have hmid : tensorPowerDimension 1 0 * tensorPowerDimension 1 q = 1 := by
    simp [tensorPowerDimension]
  have hR :
      Superoperator.comp
          (Superoperator.ofEquivalence (homogeneousLeftUnitorEquiv 1 q))
          (Superoperator.ofEquivalence (tensorSplitEquiv 1 0 q)) =
        Superoperator.ofEquivalence
          ((tensorSplitEquiv 1 0 q).trans (homogeneousLeftUnitorEquiv 1 q)) :=
    Superoperator.ofEquivalence_comp _ _
  let eU : Fin (tensorPowerDimension 1 0 * tensorPowerDimension 1 q) ≃
      Fin (tensorPowerDimension 1 q) :=
    finCongr (hmid.trans htgt.symm)
  have hU :
      Superoperator.tensorLeftUnitor (tensorPowerDimension 1 q) =
        Superoperator.ofEquivalence eU := by
    change Superoperator.ofEquivalence
        (Superoperator.tensorLeftUnitorEquiv (tensorPowerDimension 1 q)) =
      Superoperator.ofEquivalence eU
    refine ofEquivalence_dim_one (by simp [Nat.one_mul, htgt]) htgt _ _
  have hL :
      Superoperator.comp
          (Superoperator.tensorLeftUnitor (tensorPowerDimension 1 q))
          (Superoperator.ofEquivalence (tensorSplitEquiv 1 0 q)) =
        Superoperator.ofEquivalence ((tensorSplitEquiv 1 0 q).trans eU) := by
    rw [hU]
    exact Superoperator.ofEquivalence_comp (tensorSplitEquiv 1 0 q) eU
  rw [hL, hR]
  exact ofEquivalence_dim_one hsrc htgt _ _

theorem tensorLeftUnitor_comp_split_zero :
    Superoperator.comp
        (Superoperator.tensorLeftUnitor (tensorPowerDimension 0 0))
        (Superoperator.ofEquivalence (tensorSplitEquiv 0 0 0)) =
      Superoperator.comp
        (Superoperator.ofEquivalence (homogeneousLeftUnitorEquiv 0 0))
        (Superoperator.ofEquivalence (tensorSplitEquiv 0 0 0)) := by
  have h1 : tensorPowerDimension 0 0 = 1 := rfl
  have hmid : tensorPowerDimension 0 0 * tensorPowerDimension 0 0 = 1 := by
    simp [tensorPowerDimension]
  have hR :
      Superoperator.comp
          (Superoperator.ofEquivalence (homogeneousLeftUnitorEquiv 0 0))
          (Superoperator.ofEquivalence (tensorSplitEquiv 0 0 0)) =
        Superoperator.ofEquivalence
          ((tensorSplitEquiv 0 0 0).trans (homogeneousLeftUnitorEquiv 0 0)) :=
    Superoperator.ofEquivalence_comp _ _
  let eU : Fin (tensorPowerDimension 0 0 * tensorPowerDimension 0 0) ≃
      Fin (tensorPowerDimension 0 0) :=
    finCongr (hmid.trans h1.symm)
  have hU :
      Superoperator.tensorLeftUnitor (tensorPowerDimension 0 0) =
        Superoperator.ofEquivalence eU := by
    change Superoperator.ofEquivalence
        (Superoperator.tensorLeftUnitorEquiv (tensorPowerDimension 0 0)) =
      Superoperator.ofEquivalence eU
    exact ofEquivalence_dim_one (by simp [Nat.one_mul, h1]) h1 _ _
  have hL :
      Superoperator.comp
          (Superoperator.tensorLeftUnitor (tensorPowerDimension 0 0))
          (Superoperator.ofEquivalence (tensorSplitEquiv 0 0 0)) =
        Superoperator.ofEquivalence ((tensorSplitEquiv 0 0 0).trans eU) := by
    rw [hU]
    exact Superoperator.ofEquivalence_comp (tensorSplitEquiv 0 0 0) eU
  rw [hL, hR]
  exact ofEquivalence_dim_one h1 h1 _ _

theorem tensorLeftUnitor_comp_split_of_le_one (A : ℕ) (hA : A ≤ 1) (q : ℕ) :
    Superoperator.comp
        (Superoperator.tensorLeftUnitor (tensorPowerDimension A q))
        (Superoperator.ofEquivalence (tensorSplitEquiv A 0 q)) =
      Superoperator.comp
        (Superoperator.ofEquivalence (homogeneousLeftUnitorEquiv A q))
        (Superoperator.ofEquivalence (tensorSplitEquiv A 0 q)) := by
  interval_cases A
  · cases q with
    | zero => exact tensorLeftUnitor_comp_split_zero
    | succ q =>
      apply Superoperator.ext
      apply CPMap.ext
      ext a b
      have hdim : tensorPowerDimension 0 (q + 1) = 0 := by
        simp [tensorPowerDimension]
      exact isEmptyElim (show Fin 0 from hdim ▸ a.1)
  · exact tensorLeftUnitor_comp_split_one q


theorem dayLeftUnitor_tensor_id_comp_split_of_le_one (A : ℕ) (hA : A ≤ 1) (q : ℕ) :
    Superoperator.comp
        (Superoperator.comp
          (Superoperator.tensorLeftUnitor (tensorPowerDimension A q))
          (Superoperator.tensor
            (Superoperator.identity 1 :
              Superoperator (tensorPowerDimension A 0) 1)
            (Superoperator.identity (tensorPowerDimension A q))))
        (Superoperator.ofEquivalence (tensorSplitEquiv A 0 q)) =
      Superoperator.comp
        (Superoperator.ofEquivalence (homogeneousLeftUnitorEquiv A q))
        (Superoperator.ofEquivalence (tensorSplitEquiv A 0 q)) := by
  have hten :
      Superoperator.tensor
          (Superoperator.identity 1 :
            Superoperator (tensorPowerDimension A 0) 1)
          (Superoperator.identity (tensorPowerDimension A q)) =
        Superoperator.identity
          (tensorPowerDimension A 0 * tensorPowerDimension A q) := by
    convert Superoperator.tensor_identity (n := 1)
      (ℓ := tensorPowerDimension A q)
    · rfl
  have hmid :
      Superoperator.comp
          (Superoperator.comp
            (Superoperator.tensorLeftUnitor (tensorPowerDimension A q))
            (Superoperator.tensor
              (Superoperator.identity 1 :
                Superoperator (tensorPowerDimension A 0) 1)
              (Superoperator.identity (tensorPowerDimension A q))))
          (Superoperator.ofEquivalence (tensorSplitEquiv A 0 q)) =
        Superoperator.comp
          (Superoperator.comp
            (Superoperator.tensorLeftUnitor (tensorPowerDimension A q))
            (Superoperator.identity
              (tensorPowerDimension A 0 * tensorPowerDimension A q)))
          (Superoperator.ofEquivalence (tensorSplitEquiv A 0 q)) :=
    congrArg
      (fun t => Superoperator.comp
        (Superoperator.comp
          (Superoperator.tensorLeftUnitor (tensorPowerDimension A q)) t)
        (Superoperator.ofEquivalence (tensorSplitEquiv A 0 q)))
      hten
  refine hmid.trans ?_
  have hid :
      Superoperator.comp
          (Superoperator.tensorLeftUnitor (tensorPowerDimension A q))
          (Superoperator.identity
            (tensorPowerDimension A 0 * tensorPowerDimension A q)) =
        Superoperator.tensorLeftUnitor (tensorPowerDimension A q) := by
    convert Superoperator.comp_identity
      (Superoperator.tensorLeftUnitor (tensorPowerDimension A q))
    simp [tensorPowerDimension]
  have houter := congrArg
    (fun t => Superoperator.comp t
      (Superoperator.ofEquivalence (tensorSplitEquiv A 0 q)))
    hid
  exact houter.trans (tensorLeftUnitor_comp_split_of_le_one A hA q)


theorem bangCounit_degreeUnit_of_pos (A p : ℕ) (hp : p ≠ 0) :
    (bangCounit A).app (tensorPowerDimension A p) (bangDegreeUnit A p) =
      (0 : Superoperator (tensorPowerDimension A p) 1) := by
  change (bangDegreeUnit A p 0).val =
    (0 : Superoperator (tensorPowerDimension A p) 1)
  have h0 : bangDegreeUnit A p 0 =
      (0 : SymmetricElement A 0 (tensorPowerDimension A p)) := by
    rw [bangDegreeUnit_apply]
    simp only [show ¬(0 = p) from fun h => hp h.symm, ↓reduceDIte]
    rfl
  rw [h0]
  exact SymmetricElement.zero_val A 0 (tensorPowerDimension A p)

theorem bangCounit_degreeUnit_zero (A : ℕ) :
    (bangCounit A).app (tensorPowerDimension A 0) (bangDegreeUnit A 0) =
      (Superoperator.identity 1 :
        Superoperator (tensorPowerDimension A 0) 1) := by
  change (bangDegreeUnit A 0 0).val =
    (Superoperator.identity 1 : Superoperator (tensorPowerDimension A 0) 1)
  have h :
      bangDegreeUnit A 0 0 =
        (symmetricPowerProjection A 0).app
          (tensorPowerDimension A 0)
          (Superoperator.identity (tensorPowerDimension A 0)) := by
    simp [bangDegreeUnit_apply]
  rw [h]
  change Superoperator.comp (symmetricAverage A 0)
      (Superoperator.identity (tensorPowerDimension A 0)) =
    (Superoperator.identity 1 : Superoperator (tensorPowerDimension A 0) 1)
  rw [Superoperator.comp_identity]
  apply Superoperator.ext
  apply CPMap.ext_apply
  intro ρ
  rw [symmetricAverage_applyMat]
  have hperm (σ : Equiv.Perm (Fin 0)) :
      factorPermutation A 0 σ =
        Superoperator.identity (tensorPowerDimension A 0) := by
    change Superoperator.ofEquivalence (factorPermutationEquiv A 0 σ) = _
    have : factorPermutationEquiv A 0 σ = Equiv.refl _ := by
      apply Equiv.ext
      intro i
      apply Fin.ext
      exact (fin_val_eq_zero_of_card_one (rfl : tensorPowerDimension A 0 = 1) _).trans
        (fin_val_eq_zero_of_card_one rfl _).symm
    rw [this, Superoperator.ofEquivalence_refl]
  simp_rw [hperm]
  have hid :
      (Superoperator.identity (tensorPowerDimension A 0)).cp.applyMat ρ = ρ := by
    change (CPMap.identity _).applyMat ρ = ρ
    exact CPMap.applyMat_identity ρ
  simp_rw [hid]
  rw [Finset.sum_const]
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin 0))).card = 1 := by decide
  rw [hcard, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num
  change ρ = (CPMap.identity 1).applyMat ρ
  exact (CPMap.applyMat_identity ρ).symm

theorem leftCounit_bangComultComponent (A p q n : ℕ)
    (x : ((bang A).obj n).Carrier) :
    (Hom.comp (DayTensor.leftUnitor (bang A))
        (Hom.comp (DayTensor.map (bangCounit A) (Hom.id (bang A)))
          (bangComultComponent A p q))).app n x =
      (bang A).act (bangDegreeUnit A q)
        (Superoperator.comp
          (Superoperator.comp
            (Superoperator.tensorLeftUnitor (tensorPowerDimension A q))
            (Superoperator.tensor
              ((bangCounit A).app (tensorPowerDimension A p) (bangDegreeUnit A p))
              (Superoperator.identity (tensorPowerDimension A q))))
          ((bangSplitComponent A p q).app n x)) := by
  have he := bangComultComponent_evaluate A p q n x
      (dayTensor dayTensorUnit (bang A))
      (DayTensor.mapBilinear (bangCounit A) (Hom.id (bang A)))
  have hmap :
      (DayTensor.map (bangCounit A) (Hom.id (bang A))).app n
          ((bangComultComponent A p q).app n x) =
        (dayTensor dayTensorUnit (bang A)).act
          ((DayTensor.mapBilinear (bangCounit A) (Hom.id (bang A))).app
            (bangDegreeUnit A p) (bangDegreeUnit A q))
          ((bangSplitComponent A p q).app n x) := by
    simpa [DayTensor.map, DayCoend.lift] using he
  let Φ : Superoperator n
      (tensorPowerDimension A p * tensorPowerDimension A q) :=
    (bangSplitComponent A p q).app n x
  let q0 : Superoperator (tensorPowerDimension A p) 1 :=
    (bangCounit A).app (tensorPowerDimension A p) (bangDegreeUnit A p)
  let uq := bangDegreeUnit A q
  have hmap' :
      (DayTensor.map (bangCounit A) (Hom.id (bang A))).app n
          ((bangComultComponent A p q).app n x) =
        (dayTensor dayTensorUnit (bang A)).act
          ((DayCoend.intro dayTensorUnit (bang A)).app q0 uq) Φ := by
    simpa [DayTensor.mapBilinear, Hom.id_app] using hmap
  change
    (DayTensor.leftUnitor (bang A)).app n
        ((DayTensor.map (bangCounit A) (Hom.id (bang A))).app n
          ((bangComultComponent A p q).app n x)) =
      (bang A).act uq
        (Superoperator.comp
          (Superoperator.comp
            (Superoperator.tensorLeftUnitor (tensorPowerDimension A q))
            (Superoperator.tensor q0
              (Superoperator.identity (tensorPowerDimension A q))))
          Φ)
  rw [hmap']
  have hnat :=
    (DayTensor.leftUnitor (bang A)).naturality
      ((DayCoend.intro dayTensorUnit (bang A)).app q0 uq) Φ
  rw [hnat, DayTensor.leftUnitor_intro q0 uq, (bang A).act_comp]

theorem leftCounit_bangComultComponent_zero_of_le_one (A : ℕ) (hA : A ≤ 1)
    (q n : ℕ) (x : ((bang A).obj n).Carrier) :
    (Hom.comp (DayTensor.leftUnitor (bang A))
        (Hom.comp (DayTensor.map (bangCounit A) (Hom.id (bang A)))
          (bangComultComponent A 0 q))).app n x =
      (bangInjection A q).app n (x q) := by
  rw [leftCounit_bangComultComponent, bangCounit_degreeUnit_zero]
  funext j
  by_cases hj : j = q
  · subst j
    apply SymmetricElement.ext
    have hu :
        bangDegreeUnit A q q =
          (symmetricPowerProjection A q).app
            (tensorPowerDimension A q)
            (Superoperator.identity (tensorPowerDimension A q)) := by
      simp [bangDegreeUnit_apply]
    simp only [bangInjection, countableProductInjection, ↓reduceDIte]
    let U : Superoperator (1 * tensorPowerDimension A q)
        (tensorPowerDimension A q) :=
      Superoperator.tensorLeftUnitor (tensorPowerDimension A q)
    let T : Superoperator
        (tensorPowerDimension A 0 * tensorPowerDimension A q)
        (1 * tensorPowerDimension A q) :=
      Superoperator.tensor
        (Superoperator.identity 1 :
          Superoperator (tensorPowerDimension A 0) 1)
        (Superoperator.identity (tensorPowerDimension A q))
    let S : Superoperator (tensorPowerDimension A (0 + q))
        (tensorPowerDimension A 0 * tensorPowerDimension A q) :=
      Superoperator.ofEquivalence (tensorSplitEquiv A 0 q)
    change Superoperator.comp (bangDegreeUnit A q q).val
        (Superoperator.comp (Superoperator.comp U T)
          ((bangSplitComponent A 0 q).app n x)) =
      (x q).val
    rw [hu]
    change Superoperator.comp
        (Superoperator.comp (symmetricAverage A q) (Superoperator.identity _))
        (Superoperator.comp (Superoperator.comp U T)
          (Superoperator.comp S (x (0 + q)).val)) =
      (x q).val
    rw [Superoperator.comp_identity, symmetricAverage_of_le_one A q hA,
      Superoperator.identity_comp]
    -- After the above, goal is (U.comp T).comp (S.comp x.val) = (x q).val
    let H := Superoperator.ofEquivalence (homogeneousLeftUnitorEquiv A q)
    calc
      Superoperator.comp (Superoperator.comp U T)
          (Superoperator.comp S (x (0 + q)).val) =
          Superoperator.comp
            (Superoperator.comp (Superoperator.comp U T) S)
            (x (0 + q)).val :=
        Superoperator.comp_assoc (Superoperator.comp U T) S (x (0 + q)).val
      _ = Superoperator.comp (Superoperator.comp H S) (x (0 + q)).val :=
        congrArg (fun t => Superoperator.comp t (x (0 + q)).val)
          (dayLeftUnitor_tensor_id_comp_split_of_le_one A hA q)
      _ = Superoperator.comp H (Superoperator.comp S (x (0 + q)).val) :=
        (Superoperator.comp_assoc H S (x (0 + q)).val).symm
      _ = (x q).val :=
        SymmetricElement.left_counit x
  · apply SymmetricElement.ext
    have hu : bangDegreeUnit A q j =
        (0 : SymmetricElement A j (tensorPowerDimension A q)) := by
      rw [bangDegreeUnit_apply]
      simp only [show ¬(j = q) from hj, ↓reduceDIte]
      rfl
    have hz : (bangDegreeUnit A q j).val =
        (0 : Superoperator (tensorPowerDimension A q)
          (tensorPowerDimension A j)) := by
      rw [hu, SymmetricElement.zero_val]
    change Superoperator.comp (bangDegreeUnit A q j).val _ =
      ((bangInjection A q).app n (x q) j).val
    rw [hz, Superoperator.comp_zero_left]
    simp only [bangInjection, countableProductInjection, hj, ↓reduceDIte]
    rfl


theorem leftCounit_bangComultComponent_of_pos (A p q n : ℕ) (hp : p ≠ 0)
    (x : ((bang A).obj n).Carrier) :
    (Hom.comp (DayTensor.leftUnitor (bang A))
        (Hom.comp (DayTensor.map (bangCounit A) (Hom.id (bang A)))
          (bangComultComponent A p q))).app n x = 0 := by
  rw [leftCounit_bangComultComponent, bangCounit_degreeUnit_of_pos A p hp]
  let Φ : Superoperator n
      (tensorPowerDimension A p * tensorPowerDimension A q) :=
    (bangSplitComponent A p q).app n x
  change
    (bang A).act (bangDegreeUnit A q)
      (Superoperator.comp
        (Superoperator.comp
          (Superoperator.tensorLeftUnitor (tensorPowerDimension A q))
          (Superoperator.tensor
            (0 : Superoperator (tensorPowerDimension A p) 1)
            (Superoperator.identity (tensorPowerDimension A q))))
        Φ) = 0
  rw [Superoperator.tensor_zero_left, Superoperator.comp_zero_right,
    Superoperator.comp_zero_left, (bang A).act_zero_map]

/-- The Day left-counit composite equals the identity for `A ≤ 1`. -/
theorem bang_left_counit_of_le_one (A : ℕ) (hA : A ≤ 1) :
    Hom.comp (DayTensor.leftUnitor (bang A))
        (Hom.comp (DayTensor.map (bangCounit A) (Hom.id (bang A)))
          (bangComult_of_le_one A hA)) =
      Hom.id (bang A) := by
  ext n x
  let hAd := bangComultComponentsAdmissible_of_le_one A hA
  change
    (DayTensor.leftUnitor (bang A)).app n
      ((DayTensor.map (bangCounit A) (Hom.id (bang A))).app n
        (bangComultApp A hAd n x)) =
      x
  have hmap_sum :
      ((dayTensor dayTensorUnit (bang A)).obj n).HasSum
        (fun pq : ℕ × ℕ =>
          (DayTensor.map (bangCounit A) (Hom.id (bang A))).app n
            (bangComultComponentFamily A n x pq))
        ((DayTensor.map (bangCounit A) (Hom.id (bang A))).app n
          (bangComultApp A hAd n x)) := by
    simpa [DayTensor.map, DayCoend.lift] using
      bangComultApp_hasSum A hAd n x
        (dayTensor dayTensorUnit (bang A))
        (DayTensor.mapBilinear (bangCounit A) (Hom.id (bang A)))
  have hsum' :
      ((bang A).obj n).HasSum
        (fun pq : ℕ × ℕ =>
          (Hom.comp (DayTensor.leftUnitor (bang A))
            (Hom.comp (DayTensor.map (bangCounit A) (Hom.id (bang A)))
              (bangComultComponent A pq.1 pq.2))).app n x)
        ((DayTensor.leftUnitor (bang A)).app n
          ((DayTensor.map (bangCounit A) (Hom.id (bang A))).app n
            (bangComultApp A hAd n x))) :=
    (DayTensor.leftUnitor (bang A)).map_sum hmap_sum
  have hfam :
      (fun pq : ℕ × ℕ =>
          (Hom.comp (DayTensor.leftUnitor (bang A))
            (Hom.comp (DayTensor.map (bangCounit A) (Hom.id (bang A)))
              (bangComultComponent A pq.1 pq.2))).app n x) =
        fun pq : ℕ × ℕ =>
          if h : pq.1 = 0 then
            (bangInjection A pq.2).app n (x pq.2)
          else 0 := by
    funext pq
    by_cases hp : pq.1 = 0
    · simp only [hp, ↓reduceDIte]
      exact leftCounit_bangComultComponent_zero_of_le_one A hA pq.2 n x
    · simp only [hp, ↓reduceDIte]
      exact leftCounit_bangComultComponent_of_pos A pq.1 pq.2 n hp x
  rw [hfam] at hsum'
  have hcoord :=
    countableProduct_hasSum_coordinates
      (fun j => symmetricPower A j) n x
  have hid :
      ((bang A).obj n).HasSum
        (fun pq : ℕ × ℕ =>
          if h : pq.1 = 0 then (bangInjection A pq.2).app n (x pq.2) else 0)
        x := by
    have hflat :
        ((bang A).obj n).HasSum
          (fun p : Σ _ : ℕ, ℕ =>
            if h : p.1 = 0 then (bangInjection A p.2).app n (x p.2) else 0)
          x := by
      refine
        ((bang A).obj n).summation.flatten
          (fun p q =>
            if h : p = 0 then (bangInjection A q).app n (x q) else 0)
          x |>.mpr ⟨fun p => if h : p = 0 then x else 0, ?_, ?_⟩
      · intro p
        by_cases hp : p = 0
        · simp only [hp, ↓reduceDIte]
          exact hcoord
        · simp only [hp, ↓reduceDIte]
          exact Fiber.hasSum_zero _
      · convert Fiber.hasSum_singleAt ((bang A).obj n) (0 : ℕ) x using 1
        funext p
        by_cases hp : p = 0 <;> simp [hp]
    exact
      ((bang A).obj n).summation.reindex (Equiv.sigmaEquivProd ℕ ℕ)
        (fun pq =>
          if h : pq.1 = 0 then (bangInjection A pq.2).app n (x pq.2) else 0)
        x |>.mp hflat
  exact ((bang A).obj n).summation.unique hsum' hid


/-! ## Day right-counit ingredients for `A ≤ 1` -/

theorem tensorRightUnitor_comp_split_one (p : ℕ) :
    Superoperator.comp
        (Superoperator.tensorRightUnitor (tensorPowerDimension 1 p))
        (Superoperator.ofEquivalence (tensorSplitEquiv 1 p 0)) =
      Superoperator.comp
        (Superoperator.ofEquivalence (homogeneousRightUnitorEquiv 1 p))
        (Superoperator.ofEquivalence (tensorSplitEquiv 1 p 0)) := by
  have hsrc : tensorPowerDimension 1 (p + 0) = 1 := by
    rw [Nat.add_zero]; exact tensorPowerDimension_one_eq p
  have htgt : tensorPowerDimension 1 p = 1 := tensorPowerDimension_one_eq p
  have hmid : tensorPowerDimension 1 p * tensorPowerDimension 1 0 = 1 := by
    simp [tensorPowerDimension]
  have hR :
      Superoperator.comp
          (Superoperator.ofEquivalence (homogeneousRightUnitorEquiv 1 p))
          (Superoperator.ofEquivalence (tensorSplitEquiv 1 p 0)) =
        Superoperator.ofEquivalence
          ((tensorSplitEquiv 1 p 0).trans (homogeneousRightUnitorEquiv 1 p)) :=
    Superoperator.ofEquivalence_comp _ _
  let eU : Fin (tensorPowerDimension 1 p * tensorPowerDimension 1 0) ≃
      Fin (tensorPowerDimension 1 p) :=
    finCongr (hmid.trans htgt.symm)
  have hU :
      Superoperator.tensorRightUnitor (tensorPowerDimension 1 p) =
        Superoperator.ofEquivalence eU := by
    change Superoperator.ofEquivalence
        (Superoperator.tensorRightUnitorEquiv (tensorPowerDimension 1 p)) =
      Superoperator.ofEquivalence eU
    refine ofEquivalence_dim_one ?_ htgt _ _
    simp [tensorPowerDimension, htgt]
  have hL :
      Superoperator.comp
          (Superoperator.tensorRightUnitor (tensorPowerDimension 1 p))
          (Superoperator.ofEquivalence (tensorSplitEquiv 1 p 0)) =
        Superoperator.ofEquivalence ((tensorSplitEquiv 1 p 0).trans eU) := by
    rw [hU]
    exact Superoperator.ofEquivalence_comp (tensorSplitEquiv 1 p 0) eU
  rw [hL, hR]
  exact ofEquivalence_dim_one hsrc htgt _ _

theorem tensorRightUnitor_comp_split_zero :
    Superoperator.comp
        (Superoperator.tensorRightUnitor (tensorPowerDimension 0 0))
        (Superoperator.ofEquivalence (tensorSplitEquiv 0 0 0)) =
      Superoperator.comp
        (Superoperator.ofEquivalence (homogeneousRightUnitorEquiv 0 0))
        (Superoperator.ofEquivalence (tensorSplitEquiv 0 0 0)) := by
  have h1 : tensorPowerDimension 0 0 = 1 := rfl
  have hmid : tensorPowerDimension 0 0 * tensorPowerDimension 0 0 = 1 := by
    simp [tensorPowerDimension]
  have hR :
      Superoperator.comp
          (Superoperator.ofEquivalence (homogeneousRightUnitorEquiv 0 0))
          (Superoperator.ofEquivalence (tensorSplitEquiv 0 0 0)) =
        Superoperator.ofEquivalence
          ((tensorSplitEquiv 0 0 0).trans (homogeneousRightUnitorEquiv 0 0)) :=
    Superoperator.ofEquivalence_comp _ _
  let eU : Fin (tensorPowerDimension 0 0 * tensorPowerDimension 0 0) ≃
      Fin (tensorPowerDimension 0 0) :=
    finCongr (hmid.trans h1.symm)
  have hU :
      Superoperator.tensorRightUnitor (tensorPowerDimension 0 0) =
        Superoperator.ofEquivalence eU := by
    change Superoperator.ofEquivalence
        (Superoperator.tensorRightUnitorEquiv (tensorPowerDimension 0 0)) =
      Superoperator.ofEquivalence eU
    exact ofEquivalence_dim_one (by simp [Nat.mul_one, h1]) h1 _ _
  have hL :
      Superoperator.comp
          (Superoperator.tensorRightUnitor (tensorPowerDimension 0 0))
          (Superoperator.ofEquivalence (tensorSplitEquiv 0 0 0)) =
        Superoperator.ofEquivalence ((tensorSplitEquiv 0 0 0).trans eU) := by
    rw [hU]
    exact Superoperator.ofEquivalence_comp (tensorSplitEquiv 0 0 0) eU
  rw [hL, hR]
  exact ofEquivalence_dim_one h1 h1 _ _

theorem tensorRightUnitor_comp_split_of_le_one (A : ℕ) (hA : A ≤ 1) (p : ℕ) :
    Superoperator.comp
        (Superoperator.tensorRightUnitor (tensorPowerDimension A p))
        (Superoperator.ofEquivalence (tensorSplitEquiv A p 0)) =
      Superoperator.comp
        (Superoperator.ofEquivalence (homogeneousRightUnitorEquiv A p))
        (Superoperator.ofEquivalence (tensorSplitEquiv A p 0)) := by
  interval_cases A
  · cases p with
    | zero => exact tensorRightUnitor_comp_split_zero
    | succ p =>
      apply Superoperator.ext
      apply CPMap.ext
      ext a b
      have hdim : tensorPowerDimension 0 (p + 1) = 0 := by
        simp [tensorPowerDimension]
      exact isEmptyElim (show Fin 0 from hdim ▸ a.1)
  · exact tensorRightUnitor_comp_split_one p

theorem dayRightUnitor_id_tensor_comp_split_of_le_one (A : ℕ) (hA : A ≤ 1) (p : ℕ) :
    Superoperator.comp
        (Superoperator.comp
          (Superoperator.tensorRightUnitor (tensorPowerDimension A p))
          (Superoperator.tensor
            (Superoperator.identity (tensorPowerDimension A p))
            (Superoperator.identity 1 :
              Superoperator (tensorPowerDimension A 0) 1)))
        (Superoperator.ofEquivalence (tensorSplitEquiv A p 0)) =
      Superoperator.comp
        (Superoperator.ofEquivalence (homogeneousRightUnitorEquiv A p))
        (Superoperator.ofEquivalence (tensorSplitEquiv A p 0)) := by
  have hten :
      Superoperator.tensor
          (Superoperator.identity (tensorPowerDimension A p))
          (Superoperator.identity 1 :
            Superoperator (tensorPowerDimension A 0) 1) =
        Superoperator.identity
          (tensorPowerDimension A p * tensorPowerDimension A 0) := by
    convert Superoperator.tensor_identity
      (n := tensorPowerDimension A p) (ℓ := 1) using 1
    · simp [tensorPowerDimension]
  have hmid :
      Superoperator.comp
          (Superoperator.comp
            (Superoperator.tensorRightUnitor (tensorPowerDimension A p))
            (Superoperator.tensor
              (Superoperator.identity (tensorPowerDimension A p))
              (Superoperator.identity 1 :
                Superoperator (tensorPowerDimension A 0) 1)))
          (Superoperator.ofEquivalence (tensorSplitEquiv A p 0)) =
        Superoperator.comp
          (Superoperator.comp
            (Superoperator.tensorRightUnitor (tensorPowerDimension A p))
            (Superoperator.identity
              (tensorPowerDimension A p * tensorPowerDimension A 0)))
          (Superoperator.ofEquivalence (tensorSplitEquiv A p 0)) :=
    congrArg
      (fun t => Superoperator.comp
        (Superoperator.comp
          (Superoperator.tensorRightUnitor (tensorPowerDimension A p)) t)
        (Superoperator.ofEquivalence (tensorSplitEquiv A p 0)))
      hten
  refine hmid.trans ?_
  have hid :
      Superoperator.comp
          (Superoperator.tensorRightUnitor (tensorPowerDimension A p))
          (Superoperator.identity
            (tensorPowerDimension A p * tensorPowerDimension A 0)) =
        Superoperator.tensorRightUnitor (tensorPowerDimension A p) := by
    convert Superoperator.comp_identity
      (Superoperator.tensorRightUnitor (tensorPowerDimension A p))
    simp [tensorPowerDimension]
  have houter := congrArg
    (fun t => Superoperator.comp t
      (Superoperator.ofEquivalence (tensorSplitEquiv A p 0)))
    hid
  exact houter.trans (tensorRightUnitor_comp_split_of_le_one A hA p)

theorem rightCounit_bangComultComponent (A p q n : ℕ)
    (x : ((bang A).obj n).Carrier) :
    (Hom.comp (DayTensor.rightUnitor (bang A))
        (Hom.comp (DayTensor.map (Hom.id (bang A)) (bangCounit A))
          (bangComultComponent A p q))).app n x =
      (bang A).act (bangDegreeUnit A p)
        (Superoperator.comp
          (Superoperator.comp
            (Superoperator.tensorRightUnitor (tensorPowerDimension A p))
            (Superoperator.tensor
              (Superoperator.identity (tensorPowerDimension A p))
              ((bangCounit A).app (tensorPowerDimension A q) (bangDegreeUnit A q))))
          ((bangSplitComponent A p q).app n x)) := by
  have he := bangComultComponent_evaluate A p q n x
      (dayTensor (bang A) dayTensorUnit)
      (DayTensor.mapBilinear (Hom.id (bang A)) (bangCounit A))
  have hmap :
      (DayTensor.map (Hom.id (bang A)) (bangCounit A)).app n
          ((bangComultComponent A p q).app n x) =
        (dayTensor (bang A) dayTensorUnit).act
          ((DayTensor.mapBilinear (Hom.id (bang A)) (bangCounit A)).app
            (bangDegreeUnit A p) (bangDegreeUnit A q))
          ((bangSplitComponent A p q).app n x) := by
    simpa [DayTensor.map, DayCoend.lift] using he
  let Φ : Superoperator n
      (tensorPowerDimension A p * tensorPowerDimension A q) :=
    (bangSplitComponent A p q).app n x
  let q0 : Superoperator (tensorPowerDimension A q) 1 :=
    (bangCounit A).app (tensorPowerDimension A q) (bangDegreeUnit A q)
  let up := bangDegreeUnit A p
  have hmap' :
      (DayTensor.map (Hom.id (bang A)) (bangCounit A)).app n
          ((bangComultComponent A p q).app n x) =
        (dayTensor (bang A) dayTensorUnit).act
          ((DayCoend.intro (bang A) dayTensorUnit).app up q0) Φ := by
    simpa [DayTensor.mapBilinear, Hom.id_app] using hmap
  change
    (DayTensor.rightUnitor (bang A)).app n
        ((DayTensor.map (Hom.id (bang A)) (bangCounit A)).app n
          ((bangComultComponent A p q).app n x)) =
      (bang A).act up
        (Superoperator.comp
          (Superoperator.comp
            (Superoperator.tensorRightUnitor (tensorPowerDimension A p))
            (Superoperator.tensor
              (Superoperator.identity (tensorPowerDimension A p)) q0))
          Φ)
  rw [hmap']
  have hnat :=
    (DayTensor.rightUnitor (bang A)).naturality
      ((DayCoend.intro (bang A) dayTensorUnit).app up q0) Φ
  rw [hnat, DayTensor.rightUnitor_intro up q0, (bang A).act_comp]

theorem rightCounit_bangComultComponent_zero_of_le_one (A : ℕ) (hA : A ≤ 1)
    (p n : ℕ) (x : ((bang A).obj n).Carrier) :
    (Hom.comp (DayTensor.rightUnitor (bang A))
        (Hom.comp (DayTensor.map (Hom.id (bang A)) (bangCounit A))
          (bangComultComponent A p 0))).app n x =
      (bangInjection A p).app n (x p) := by
  rw [rightCounit_bangComultComponent, bangCounit_degreeUnit_zero]
  funext j
  by_cases hj : j = p
  · subst j
    apply SymmetricElement.ext
    have hu :
        bangDegreeUnit A p p =
          (symmetricPowerProjection A p).app
            (tensorPowerDimension A p)
            (Superoperator.identity (tensorPowerDimension A p)) := by
      simp [bangDegreeUnit_apply]
    simp only [bangInjection, countableProductInjection, ↓reduceDIte]
    let U : Superoperator (tensorPowerDimension A p * 1)
        (tensorPowerDimension A p) :=
      Superoperator.tensorRightUnitor (tensorPowerDimension A p)
    let T : Superoperator
        (tensorPowerDimension A p * tensorPowerDimension A 0)
        (tensorPowerDimension A p * 1) :=
      Superoperator.tensor
        (Superoperator.identity (tensorPowerDimension A p))
        (Superoperator.identity 1 :
          Superoperator (tensorPowerDimension A 0) 1)
    let S : Superoperator (tensorPowerDimension A (p + 0))
        (tensorPowerDimension A p * tensorPowerDimension A 0) :=
      Superoperator.ofEquivalence (tensorSplitEquiv A p 0)
    change Superoperator.comp (bangDegreeUnit A p p).val
        (Superoperator.comp (Superoperator.comp U T)
          ((bangSplitComponent A p 0).app n x)) =
      (x p).val
    rw [hu]
    change Superoperator.comp
        (Superoperator.comp (symmetricAverage A p) (Superoperator.identity _))
        (Superoperator.comp (Superoperator.comp U T)
          (Superoperator.comp S (x (p + 0)).val)) =
      (x p).val
    rw [Superoperator.comp_identity, symmetricAverage_of_le_one A p hA,
      Superoperator.identity_comp]
    let H := Superoperator.ofEquivalence (homogeneousRightUnitorEquiv A p)
    calc
      Superoperator.comp (Superoperator.comp U T)
          (Superoperator.comp S (x (p + 0)).val) =
          Superoperator.comp
            (Superoperator.comp (Superoperator.comp U T) S)
            (x (p + 0)).val :=
        Superoperator.comp_assoc (Superoperator.comp U T) S (x (p + 0)).val
      _ = Superoperator.comp (Superoperator.comp H S) (x (p + 0)).val :=
        congrArg (fun t => Superoperator.comp t (x (p + 0)).val)
          (dayRightUnitor_id_tensor_comp_split_of_le_one A hA p)
      _ = Superoperator.comp H (Superoperator.comp S (x (p + 0)).val) :=
        (Superoperator.comp_assoc H S (x (p + 0)).val).symm
      _ = (x p).val :=
        SymmetricElement.right_counit x
  · apply SymmetricElement.ext
    have hu : bangDegreeUnit A p j =
        (0 : SymmetricElement A j (tensorPowerDimension A p)) := by
      rw [bangDegreeUnit_apply]
      simp only [show ¬(j = p) from hj, ↓reduceDIte]
      rfl
    have hz : (bangDegreeUnit A p j).val =
        (0 : Superoperator (tensorPowerDimension A p)
          (tensorPowerDimension A j)) := by
      rw [hu, SymmetricElement.zero_val]
    change Superoperator.comp (bangDegreeUnit A p j).val _ =
      ((bangInjection A p).app n (x p) j).val
    rw [hz, Superoperator.comp_zero_left]
    simp only [bangInjection, countableProductInjection, hj, ↓reduceDIte]
    rfl

theorem rightCounit_bangComultComponent_of_pos (A p q n : ℕ) (hq : q ≠ 0)
    (x : ((bang A).obj n).Carrier) :
    (Hom.comp (DayTensor.rightUnitor (bang A))
        (Hom.comp (DayTensor.map (Hom.id (bang A)) (bangCounit A))
          (bangComultComponent A p q))).app n x = 0 := by
  rw [rightCounit_bangComultComponent, bangCounit_degreeUnit_of_pos A q hq]
  let Φ : Superoperator n
      (tensorPowerDimension A p * tensorPowerDimension A q) :=
    (bangSplitComponent A p q).app n x
  change
    (bang A).act (bangDegreeUnit A p)
      (Superoperator.comp
        (Superoperator.comp
          (Superoperator.tensorRightUnitor (tensorPowerDimension A p))
          (Superoperator.tensor
            (Superoperator.identity (tensorPowerDimension A p))
            (0 : Superoperator (tensorPowerDimension A q) 1)))
        Φ) = 0
  rw [Superoperator.tensor_zero_right, Superoperator.comp_zero_right,
    Superoperator.comp_zero_left, (bang A).act_zero_map]

/-! ### Counit forces degree-one boundary weights to remain `1`

Left (resp. right) counit recovers the full degree-one coefficient from the
unscaled `(0,1)` (resp. `(1,0)`) bang-split component.  Uniform `1/2`
scaling of those boundary components is therefore incompatible with the
counit laws, even though the same scale repairs the raw Route A joint-effect
matrix inequality at `(A,k)=(2,1)`.
-/

/-- Left counit on the unscaled `(0,1)` component recovers the full degree-one
coefficient (`A ≤ 1`). -/
theorem leftCounit_forces_zero_one_weight_one_of_le_one
    (A : ℕ) (hA : A ≤ 1) (n : ℕ) (x : ((bang A).obj n).Carrier) :
    (Hom.comp (DayTensor.leftUnitor (bang A))
        (Hom.comp (DayTensor.map (bangCounit A) (Hom.id (bang A)))
          (bangComultComponent A 0 1))).app n x =
      (bangInjection A 1).app n (x 1) :=
  leftCounit_bangComultComponent_zero_of_le_one A hA 1 n x

/-- Right counit on the unscaled `(1,0)` component recovers the full degree-one
coefficient (`A ≤ 1`). -/
theorem rightCounit_forces_one_zero_weight_one_of_le_one
    (A : ℕ) (hA : A ≤ 1) (n : ℕ) (x : ((bang A).obj n).Carrier) :
    (Hom.comp (DayTensor.rightUnitor (bang A))
        (Hom.comp (DayTensor.map (Hom.id (bang A)) (bangCounit A))
          (bangComultComponent A 1 0))).app n x =
      (bangInjection A 1).app n (x 1) :=
  rightCounit_bangComultComponent_zero_of_le_one A hA 1 n x

/-- On the degree-one identity series, left counit of the `(0,1)` component
recovers the identity Superoperator at degree one — the boundary weight is
exactly `1`, not `1/2`. -/
theorem leftCounit_zero_one_identity_coeff_of_le_one (A : ℕ) (hA : A ≤ 1) :
    (((Hom.comp (DayTensor.leftUnitor (bang A))
        (Hom.comp (DayTensor.map (bangCounit A) (Hom.id (bang A)))
          (bangComultComponent A 0 1))).app
        (tensorPowerDimension A 1) (bangIdentityDegreeOne A)) 1).val =
      Superoperator.identity (tensorPowerDimension A 1) := by
  have h :=
    leftCounit_forces_zero_one_weight_one_of_le_one A hA
      (tensorPowerDimension A 1) (bangIdentityDegreeOne A)
  have h1 := congrArg (fun y => y 1) h
  simp only [bangInjection, countableProductInjection, ↓reduceDIte] at h1
  change
      (((Hom.comp (DayTensor.leftUnitor (bang A))
          (Hom.comp (DayTensor.map (bangCounit A) (Hom.id (bang A)))
            (bangComultComponent A 0 1))).app
          (tensorPowerDimension A 1) (bangIdentityDegreeOne A)) 1).val =
        (bangIdentityDegreeOne A 1).val
  rw [h1, bangIdentityDegreeOne_coeff]

/-- On the degree-one identity series, right counit of the `(1,0)` component
likewise recovers the identity Superoperator. -/
theorem rightCounit_one_zero_identity_coeff_of_le_one (A : ℕ) (hA : A ≤ 1) :
    (((Hom.comp (DayTensor.rightUnitor (bang A))
        (Hom.comp (DayTensor.map (Hom.id (bang A)) (bangCounit A))
          (bangComultComponent A 1 0))).app
        (tensorPowerDimension A 1) (bangIdentityDegreeOne A)) 1).val =
      Superoperator.identity (tensorPowerDimension A 1) := by
  have h :=
    rightCounit_forces_one_zero_weight_one_of_le_one A hA
      (tensorPowerDimension A 1) (bangIdentityDegreeOne A)
  have h1 := congrArg (fun y => y 1) h
  simp only [bangInjection, countableProductInjection, ↓reduceDIte] at h1
  change
      (((Hom.comp (DayTensor.rightUnitor (bang A))
          (Hom.comp (DayTensor.map (Hom.id (bang A)) (bangCounit A))
            (bangComultComponent A 1 0))).app
          (tensorPowerDimension A 1) (bangIdentityDegreeOne A)) 1).val =
        (bangIdentityDegreeOne A 1).val
  rw [h1, bangIdentityDegreeOne_coeff]

/-- Uniform `1/2` scaling repairs the `(2,1)` joint-effect matrix bound, but
is not a counital repair of bang comultiplication: left/right counit force
the `(0,1)` and `(1,0)` boundary weights to remain `1` (full identity
recovery), and half of the identity matrix is not the identity. -/
theorem half_scale_not_counital_bang_repair :
    bangNormalizedSplitFamilyEffect_two_one =
        (1 : Matrix (Fin (tensorPowerDimension 2 1))
          (Fin (tensorPowerDimension 2 1)) ℂ) ∧
      (∀ (A : ℕ) (hA : A ≤ 1),
        (((Hom.comp (DayTensor.leftUnitor (bang A))
            (Hom.comp (DayTensor.map (bangCounit A) (Hom.id (bang A)))
              (bangComultComponent A 0 1))).app
            (tensorPowerDimension A 1) (bangIdentityDegreeOne A)) 1).val =
          Superoperator.identity (tensorPowerDimension A 1)) ∧
      (∀ (A : ℕ) (hA : A ≤ 1),
        (((Hom.comp (DayTensor.rightUnitor (bang A))
            (Hom.comp (DayTensor.map (Hom.id (bang A)) (bangCounit A))
              (bangComultComponent A 1 0))).app
            (tensorPowerDimension A 1) (bangIdentityDegreeOne A)) 1).val =
          Superoperator.identity (tensorPowerDimension A 1)) ∧
      ((2 : ℕ) : ℂ)⁻¹ •
          (1 : Matrix (Fin (tensorPowerDimension 2 1))
            (Fin (tensorPowerDimension 2 1)) ℂ) ≠
        (1 : Matrix (Fin (tensorPowerDimension 2 1))
          (Fin (tensorPowerDimension 2 1)) ℂ) :=
  ⟨bangNormalizedSplitFamilyEffect_two_one_eq_one,
    fun A hA => leftCounit_zero_one_identity_coeff_of_le_one A hA,
    fun A hA => rightCounit_one_zero_identity_coeff_of_le_one A hA,
    half_one_ne_one (Nat.pos_of_ne_zero (by
      simp [tensorPowerDimension_eq_pow]))⟩

/-- The Day right-counit composite equals the identity for `A ≤ 1`. -/
theorem bang_right_counit_of_le_one (A : ℕ) (hA : A ≤ 1) :
    Hom.comp (DayTensor.rightUnitor (bang A))
        (Hom.comp (DayTensor.map (Hom.id (bang A)) (bangCounit A))
          (bangComult_of_le_one A hA)) =
      Hom.id (bang A) := by
  ext n x
  let hAd := bangComultComponentsAdmissible_of_le_one A hA
  change
    (DayTensor.rightUnitor (bang A)).app n
      ((DayTensor.map (Hom.id (bang A)) (bangCounit A)).app n
        (bangComultApp A hAd n x)) =
      x
  have hmap_sum :
      ((dayTensor (bang A) dayTensorUnit).obj n).HasSum
        (fun pq : ℕ × ℕ =>
          (DayTensor.map (Hom.id (bang A)) (bangCounit A)).app n
            (bangComultComponentFamily A n x pq))
        ((DayTensor.map (Hom.id (bang A)) (bangCounit A)).app n
          (bangComultApp A hAd n x)) := by
    simpa [DayTensor.map, DayCoend.lift] using
      bangComultApp_hasSum A hAd n x
        (dayTensor (bang A) dayTensorUnit)
        (DayTensor.mapBilinear (Hom.id (bang A)) (bangCounit A))
  have hsum' :
      ((bang A).obj n).HasSum
        (fun pq : ℕ × ℕ =>
          (Hom.comp (DayTensor.rightUnitor (bang A))
            (Hom.comp (DayTensor.map (Hom.id (bang A)) (bangCounit A))
              (bangComultComponent A pq.1 pq.2))).app n x)
        ((DayTensor.rightUnitor (bang A)).app n
          ((DayTensor.map (Hom.id (bang A)) (bangCounit A)).app n
            (bangComultApp A hAd n x))) :=
    (DayTensor.rightUnitor (bang A)).map_sum hmap_sum
  have hfam :
      (fun pq : ℕ × ℕ =>
          (Hom.comp (DayTensor.rightUnitor (bang A))
            (Hom.comp (DayTensor.map (Hom.id (bang A)) (bangCounit A))
              (bangComultComponent A pq.1 pq.2))).app n x) =
        fun pq : ℕ × ℕ =>
          if h : pq.2 = 0 then
            (bangInjection A pq.1).app n (x pq.1)
          else 0 := by
    funext pq
    by_cases hq : pq.2 = 0
    · simp only [hq, ↓reduceDIte]
      exact rightCounit_bangComultComponent_zero_of_le_one A hA pq.1 n x
    · simp only [hq, ↓reduceDIte]
      exact rightCounit_bangComultComponent_of_pos A pq.1 pq.2 n hq x
  rw [hfam] at hsum'
  have hcoord :=
    countableProduct_hasSum_coordinates
      (fun j => symmetricPower A j) n x
  have hid :
      ((bang A).obj n).HasSum
        (fun pq : ℕ × ℕ =>
          if h : pq.2 = 0 then (bangInjection A pq.1).app n (x pq.1) else 0)
        x := by
    have hflat :
        ((bang A).obj n).HasSum
          (fun s : Σ _ : ℕ, ℕ =>
            if h : s.2 = 0 then (bangInjection A s.1).app n (x s.1) else 0)
          x := by
      refine
        ((bang A).obj n).summation.flatten
          (fun p q =>
            if h : q = 0 then (bangInjection A p).app n (x p) else 0)
          x |>.mpr ⟨fun p => (bangInjection A p).app n (x p), ?_, ?_⟩
      · intro p
        convert Fiber.hasSum_singleAt ((bang A).obj n) (0 : ℕ)
          ((bangInjection A p).app n (x p)) using 1
        funext q
        by_cases hq : q = 0 <;> simp [hq]
      · exact hcoord
    exact
      ((bang A).obj n).summation.reindex (Equiv.sigmaEquivProd ℕ ℕ)
        (fun pq =>
          if h : pq.2 = 0 then (bangInjection A pq.1).app n (x pq.1) else 0)
        x |>.mp hflat
  exact ((bang A).obj n).summation.unique hsum' hid


/-! ## Day braiding / cocommutativity for `A ≤ 1` -/

theorem bangComultComponent_eq_act (A p q n : ℕ)
    (x : ((bang A).obj n).Carrier) :
    (bangComultComponent A p q).app n x =
      (dayTensor (bang A) (bang A)).act
        ((DayCoend.intro (bang A) (bang A)).app
          (bangDegreeUnit A p) (bangDegreeUnit A q))
        ((bangSplitComponent A p q).app n x :
          Superoperator n
            (tensorPowerDimension A p * tensorPowerDimension A q)) := by
  have h := bangComultComponent_evaluate A p q n x
    (dayTensor (bang A) (bang A)) (DayCoend.intro (bang A) (bang A))
  have hs := DayCoend.evaluate_self
    ((bangComultComponent A p q).app n x)
  change DayCoend.evaluate (DayCoend.module (bang A) (bang A))
      (DayCoend.intro (bang A) (bang A))
      ((bangComultComponent A p q).app n x) =
    _ at h
  rw [hs] at h
  exact h

theorem braiding_bangComultComponent (A p q n : ℕ)
    (x : ((bang A).obj n).Carrier) :
    (DayTensor.braiding (bang A) (bang A)).app n
        ((bangComultComponent A p q).app n x) =
      (dayTensor (bang A) (bang A)).act
        ((DayCoend.intro (bang A) (bang A)).app
          (bangDegreeUnit A q) (bangDegreeUnit A p))
        (Superoperator.comp
          (Superoperator.tensorSwap
            (tensorPowerDimension A p) (tensorPowerDimension A q))
          ((bangSplitComponent A p q).app n x :
            Superoperator n
              (tensorPowerDimension A p * tensorPowerDimension A q))) := by
  rw [bangComultComponent_eq_act]
  set Φ : Superoperator n
      (tensorPowerDimension A p * tensorPowerDimension A q) :=
    (bangSplitComponent A p q).app n x
  set gen := (DayCoend.intro (bang A) (bang A)).app
    (bangDegreeUnit A p) (bangDegreeUnit A q)
  rw [(DayTensor.braiding (bang A) (bang A)).naturality gen Φ,
    DayTensor.braiding_intro, (dayTensor (bang A) (bang A)).act_comp]

theorem tensorSwap_eq_ofEquivalence_of_dims_one {a b : ℕ}
    (ha : a = 1) (hb : b = 1) :
    Superoperator.tensorSwap a b =
      Superoperator.ofEquivalence
        (finCongr (by rw [ha, hb]) :
          Fin (a * b) ≃ Fin (b * a)) := by
  change Superoperator.ofEquivalence (Superoperator.tensorSwapEquiv a b) =
    Superoperator.ofEquivalence _
  refine ofEquivalence_dim_one (by simp [ha, hb]) (by simp [ha, hb]) _ _

theorem Superoperator.eq_of_codim_zero {n m : ℕ} (hm : m = 0)
    (f g : Superoperator n m) : f = g := by
  apply Superoperator.ext
  apply CPMap.ext
  ext a b
  exact isEmptyElim (show Fin 0 from hm ▸ a.1)

theorem dim_eq_one_of_le_one_ne_zero (A : ℕ) (hA : A ≤ 1) (k : ℕ)
    (h : ¬tensorPowerDimension A k = 0) :
    tensorPowerDimension A k = 1 := by
  interval_cases A
  · cases k with
    | zero => rfl
    | succ k => simp [tensorPowerDimension] at h
  · exact tensorPowerDimension_one_eq k

theorem bangSplit_swap_of_le_one (A : ℕ) (hA : A ≤ 1) (p q n : ℕ)
    (x : ((bang A).obj n).Carrier) :
    Superoperator.comp
        (Superoperator.tensorSwap
          (tensorPowerDimension A p) (tensorPowerDimension A q))
        ((bangSplitComponent A p q).app n x :
          Superoperator n
            (tensorPowerDimension A p * tensorPowerDimension A q)) =
      ((bangSplitComponent A q p).app n x :
        Superoperator n
          (tensorPowerDimension A q * tensorPowerDimension A p)) := by
  by_cases hzero :
      tensorPowerDimension A q * tensorPowerDimension A p = 0
  · exact Superoperator.eq_of_codim_zero hzero _ _
  have hp0 : tensorPowerDimension A p ≠ 0 := fun h => hzero (by rw [h, Nat.mul_zero])
  have hq0 : tensorPowerDimension A q ≠ 0 := fun h => hzero (by rw [h, Nat.zero_mul])
  have hp := dim_eq_one_of_le_one_ne_zero A hA p hp0
  have hq := dim_eq_one_of_le_one_ne_zero A hA q hq0
  have hsw := tensorSwap_eq_ofEquivalence_of_dims_one hp hq
  have hsrc : tensorPowerDimension A (p + q) = 1 := by
    rw [tensorPowerDimension_eq_pow, pow_add, ← tensorPowerDimension_eq_pow,
      ← tensorPowerDimension_eq_pow, hp, hq, one_mul]
  have htgt : tensorPowerDimension A q * tensorPowerDimension A p = 1 := by
    rw [hp, hq, one_mul]
  have hcomm : p + q = q + p := Nat.add_comm p q
  let eDeg := finCongr (congrArg (tensorPowerDimension A) hcomm)
  have hx :
      (x (p + q)).val =
        Superoperator.comp
          (Superoperator.ofEquivalence eDeg.symm)
          (x (q + p)).val := by
    have hfwd :
        Superoperator.comp
            (Superoperator.ofEquivalence eDeg)
            (x (p + q)).val =
          (x (q + p)).val :=
      (SymmetricElement.val_degreeCast hcomm (x (p + q))).trans
        (congrArg SymmetricElement.val
          (SymmetricElement.family_degreeCast x hcomm))
    have hcancel :
        Superoperator.comp
            (Superoperator.ofEquivalence eDeg.symm)
            (Superoperator.ofEquivalence eDeg) =
          Superoperator.identity (tensorPowerDimension A (p + q)) := by
      rw [Superoperator.ofEquivalence_comp]
      convert Superoperator.ofEquivalence_refl _
      exact Equiv.symm_trans_self _
    calc
      (x (p + q)).val =
          Superoperator.comp
            (Superoperator.identity (tensorPowerDimension A (p + q)))
            (x (p + q)).val :=
        (Superoperator.identity_comp _).symm
      _ = Superoperator.comp
            (Superoperator.comp
              (Superoperator.ofEquivalence eDeg.symm)
              (Superoperator.ofEquivalence eDeg))
            (x (p + q)).val := by rw [← hcancel]
      _ = Superoperator.comp
            (Superoperator.ofEquivalence eDeg.symm)
            (Superoperator.comp
              (Superoperator.ofEquivalence eDeg)
              (x (p + q)).val) :=
        (Superoperator.comp_assoc _ _ _).symm
      _ = Superoperator.comp
            (Superoperator.ofEquivalence eDeg.symm)
            (x (q + p)).val :=
        congrArg _ hfwd
  let eMul : Fin (tensorPowerDimension A p * tensorPowerDimension A q) ≃
      Fin (tensorPowerDimension A q * tensorPowerDimension A p) :=
    finCongr (by rw [hp, hq])
  simp only [bangSplitComponent]
  rw [hsw, hx]
  change
    Superoperator.comp (Superoperator.ofEquivalence eMul)
        (Superoperator.comp
          (Superoperator.ofEquivalence (tensorSplitEquiv A p q))
          (Superoperator.comp
            (Superoperator.ofEquivalence eDeg.symm)
            (x (q + p)).val)) =
      Superoperator.comp
        (Superoperator.ofEquivalence (tensorSplitEquiv A q p))
        (x (q + p)).val
  -- Target: eMul ∘ split ∘ eDeg⁻¹ ∘ x(q+p) = split(q,p) ∘ x(q+p)
  -- Collapse the three ofEquivalences, then use Fin-1 uniqueness.
  have hcollapse :
      Superoperator.comp (Superoperator.ofEquivalence eMul)
          (Superoperator.comp
            (Superoperator.ofEquivalence (tensorSplitEquiv A p q))
            (Superoperator.ofEquivalence eDeg.symm)) =
        Superoperator.ofEquivalence
          ((eDeg.symm.trans (tensorSplitEquiv A p q)).trans eMul) := by
    rw [Superoperator.ofEquivalence_comp, Superoperator.ofEquivalence_comp]
  -- Reassociate the application onto x
  have hreassoc :
      Superoperator.comp (Superoperator.ofEquivalence eMul)
          (Superoperator.comp
            (Superoperator.ofEquivalence (tensorSplitEquiv A p q))
            (Superoperator.comp
              (Superoperator.ofEquivalence eDeg.symm)
              (x (q + p)).val)) =
        Superoperator.comp
          (Superoperator.comp (Superoperator.ofEquivalence eMul)
            (Superoperator.comp
              (Superoperator.ofEquivalence (tensorSplitEquiv A p q))
              (Superoperator.ofEquivalence eDeg.symm)))
          (x (q + p)).val := by
    rw [Superoperator.comp_assoc
      (Ψ := Superoperator.ofEquivalence eDeg.symm)]
    rw [Superoperator.comp_assoc]
  rw [hreassoc, hcollapse]
  exact congrArg (fun t => Superoperator.comp t (x (q + p)).val)
    (ofEquivalence_dim_one (by rw [← hcomm]; exact hsrc) htgt _ _)

theorem braiding_bangComultComponent_eq_of_le_one
    (A : ℕ) (hA : A ≤ 1) (p q n : ℕ)
    (x : ((bang A).obj n).Carrier) :
    (DayTensor.braiding (bang A) (bang A)).app n
        ((bangComultComponent A p q).app n x) =
      (bangComultComponent A q p).app n x := by
  rw [braiding_bangComultComponent, bangSplit_swap_of_le_one A hA p q n x,
    ← bangComultComponent_eq_act]


theorem bang_cocommutative_of_le_one (A : ℕ) (hA : A ≤ 1) :
    Hom.comp (DayTensor.braiding (bang A) (bang A))
        (bangComult_of_le_one A hA) =
      bangComult_of_le_one A hA := by
  ext n x
  let hAd := bangComultComponentsAdmissible_of_le_one A hA
  change
    (DayTensor.braiding (bang A) (bang A)).app n
      (bangComultApp A hAd n x) =
      bangComultApp A hAd n x
  have hfib :
      ((dayTensor (bang A) (bang A)).obj n).HasSum
        (bangComultComponentFamily A n x)
        (bangComultApp A hAd n x) := by
    have h := bangComultApp_hasSum A hAd n x
      (dayTensor (bang A) (bang A)) (DayCoend.intro (bang A) (bang A))
    have hfun :
        (fun pq : ℕ × ℕ =>
            DayCoend.evaluate (dayTensor (bang A) (bang A))
              (DayCoend.intro (bang A) (bang A))
              (bangComultComponentFamily A n x pq)) =
          bangComultComponentFamily A n x := by
      funext pq
      exact DayCoend.evaluate_self _
    have hs := DayCoend.evaluate_self (bangComultApp A hAd n x)
    change ((dayTensor (bang A) (bang A)).obj n).HasSum
        (fun pq => DayCoend.evaluate (DayCoend.module (bang A) (bang A))
          (DayCoend.intro (bang A) (bang A))
          (bangComultComponentFamily A n x pq))
        (DayCoend.evaluate (DayCoend.module (bang A) (bang A))
          (DayCoend.intro (bang A) (bang A))
          (bangComultApp A hAd n x)) at h
    rwa [hfun, hs] at h
  have hbraid :
      ((dayTensor (bang A) (bang A)).obj n).HasSum
        (fun pq : ℕ × ℕ =>
          (DayTensor.braiding (bang A) (bang A)).app n
            (bangComultComponentFamily A n x pq))
        ((DayTensor.braiding (bang A) (bang A)).app n
          (bangComultApp A hAd n x)) :=
    (DayTensor.braiding (bang A) (bang A)).map_sum hfib
  have hfam :
      (fun pq : ℕ × ℕ =>
          (DayTensor.braiding (bang A) (bang A)).app n
            (bangComultComponentFamily A n x pq)) =
        fun pq : ℕ × ℕ =>
          bangComultComponentFamily A n x (pq.2, pq.1) := by
    funext pq
    exact braiding_bangComultComponent_eq_of_le_one A hA pq.1 pq.2 n x
  rw [hfam] at hbraid
  have hswap :
      ((dayTensor (bang A) (bang A)).obj n).HasSum
        (fun pq : ℕ × ℕ =>
          bangComultComponentFamily A n x (pq.2, pq.1))
        (bangComultApp A hAd n x) := by
    exact
      (((dayTensor (bang A) (bang A)).obj n).summation.reindex
        (Equiv.prodComm ℕ ℕ)
        (bangComultComponentFamily A n x)
        (bangComultApp A hAd n x)).mpr hfib
  exact ((dayTensor (bang A) (bang A)).obj n).summation.unique hbraid hswap



/-! ## Day coassociativity for `A = 0` -/

theorem bangDegreeUnit_zero_zero_val :
    (bangDegreeUnit 0 0 0).val =
      Superoperator.identity (tensorPowerDimension 0 0) := by
  simp only [bangDegreeUnit_apply, ↓reduceDIte]
  change Superoperator.comp (symmetricAverage 0 0)
      (Superoperator.identity (tensorPowerDimension 0 0)) =
    Superoperator.identity (tensorPowerDimension 0 0)
  rw [Superoperator.comp_identity, symmetricAverage_of_le_one 0 0 (by decide)]

theorem bangComult_degreeUnit_zero :
    bangComult_zero.app (tensorPowerDimension 0 0) (bangDegreeUnit 0 0) =
      (DayCoend.intro (bang 0) (bang 0)).app
        (bangDegreeUnit 0 0) (bangDegreeUnit 0 0) := by
  rw [bangComult_zero_eq_component, bangComultComponent_eq_act]
  simp only [bangSplitComponent]
  rw [bangDegreeUnit_zero_zero_val, Superoperator.comp_identity]
  have hsplit :
      Superoperator.ofEquivalence (tensorSplitEquiv 0 0 0) =
        Superoperator.ofEquivalence
          (Equiv.refl (Fin (tensorPowerDimension 0 0 * tensorPowerDimension 0 0))) :=
    ofEquivalence_dim_one rfl rfl _ _
  rw [hsplit, Superoperator.ofEquivalence_refl]
  exact (dayTensor (bang 0) (bang 0)).act_id _

theorem bang_coassociative_zero :
    Hom.comp (DayTensor.associator (bang 0) (bang 0) (bang 0))
        (Hom.comp (DayTensor.map bangComult_zero (Hom.id (bang 0)))
          bangComult_zero) =
      Hom.comp (DayTensor.map (Hom.id (bang 0)) bangComult_zero)
        bangComult_zero := by
  ext n x
  set Φ : Superoperator n
      (tensorPowerDimension 0 0 * tensorPowerDimension 0 0) :=
    (bangSplitComponent 0 0 0).app n x with hΦ
  have hδx : bangComult_zero.app n x =
      (dayTensor (bang 0) (bang 0)).act
        ((DayCoend.intro (bang 0) (bang 0)).app
          (bangDegreeUnit 0 0) (bangDegreeUnit 0 0)) Φ := by
    rw [bangComult_zero_eq_component, bangComultComponent_eq_act]
  have hR :
      (DayTensor.map (Hom.id (bang 0)) bangComult_zero).app n
          (bangComult_zero.app n x) =
        (dayTensor (bang 0) (dayTensor (bang 0) (bang 0))).act
          ((DayCoend.intro (bang 0) (dayTensor (bang 0) (bang 0))).app
            (bangDegreeUnit 0 0)
            ((DayCoend.intro (bang 0) (bang 0)).app
              (bangDegreeUnit 0 0) (bangDegreeUnit 0 0))) Φ := by
    rw [hδx,
      (DayTensor.map (Hom.id (bang 0)) bangComult_zero).naturality]
    change
      (dayTensor (bang 0) (dayTensor (bang 0) (bang 0))).act
          ((DayTensor.map (Hom.id (bang 0)) bangComult_zero).app _
            ((DayCoend.intro (bang 0) (bang 0)).app
              (bangDegreeUnit 0 0) (bangDegreeUnit 0 0))) Φ =
        _
    rw [DayTensor.map_intro, Hom.id_app, bangComult_degreeUnit_zero]
    rfl
  have hL_map :
      (DayTensor.map bangComult_zero (Hom.id (bang 0))).app n
          (bangComult_zero.app n x) =
        (dayTensor (dayTensor (bang 0) (bang 0)) (bang 0)).act
          ((DayCoend.intro (dayTensor (bang 0) (bang 0)) (bang 0)).app
            ((DayCoend.intro (bang 0) (bang 0)).app
              (bangDegreeUnit 0 0) (bangDegreeUnit 0 0))
            (bangDegreeUnit 0 0)) Φ := by
    rw [hδx,
      (DayTensor.map bangComult_zero (Hom.id (bang 0))).naturality]
    change
      (dayTensor (dayTensor (bang 0) (bang 0)) (bang 0)).act
          ((DayTensor.map bangComult_zero (Hom.id (bang 0))).app _
            ((DayCoend.intro (bang 0) (bang 0)).app
              (bangDegreeUnit 0 0) (bangDegreeUnit 0 0))) Φ =
        _
    rw [DayTensor.map_intro, Hom.id_app, bangComult_degreeUnit_zero]
    rfl
  have hL :
      (DayTensor.associator (bang 0) (bang 0) (bang 0)).app n
          ((DayTensor.map bangComult_zero (Hom.id (bang 0))).app n
            (bangComult_zero.app n x)) =
        (dayTensor (bang 0) (dayTensor (bang 0) (bang 0))).act
          ((DayCoend.intro (bang 0) (dayTensor (bang 0) (bang 0))).app
            (bangDegreeUnit 0 0)
            ((DayCoend.intro (bang 0) (bang 0)).app
              (bangDegreeUnit 0 0) (bangDegreeUnit 0 0)))
          (Superoperator.comp
            (Superoperator.tensorAssociator
              (tensorPowerDimension 0 0) (tensorPowerDimension 0 0)
              (tensorPowerDimension 0 0)) Φ) := by
    rw [hL_map]
    set gen :=
      (DayCoend.intro (dayTensor (bang 0) (bang 0)) (bang 0)).app
        ((DayCoend.intro (bang 0) (bang 0)).app
          (bangDegreeUnit 0 0) (bangDegreeUnit 0 0))
        (bangDegreeUnit 0 0)
    change
      (DayTensor.associator (bang 0) (bang 0) (bang 0)).app n
          ((dayTensor (dayTensor (bang 0) (bang 0)) (bang 0)).act gen Φ) =
        _
    rw [(DayTensor.associator (bang 0) (bang 0) (bang 0)).naturality gen Φ]
    rw [DayTensor.associator_intro_intro]
    exact (dayTensor (bang 0) (dayTensor (bang 0) (bang 0))).act_comp _ _ _
  change
    (DayTensor.associator (bang 0) (bang 0) (bang 0)).app n
        ((DayTensor.map bangComult_zero (Hom.id (bang 0))).app n
          (bangComult_zero.app n x)) =
      (DayTensor.map (Hom.id (bang 0)) bangComult_zero).app n
        (bangComult_zero.app n x)
  rw [hL, hR]
  congr 1
  have hA :
      Superoperator.tensorAssociator
          (tensorPowerDimension 0 0) (tensorPowerDimension 0 0)
          (tensorPowerDimension 0 0) =
        Superoperator.ofEquivalence
          (Equiv.refl
            (Fin (tensorPowerDimension 0 0 * tensorPowerDimension 0 0))) :=
    ofEquivalence_dim_one rfl rfl _ _
  rw [hA, Superoperator.ofEquivalence_refl]
  exact Superoperator.identity_comp Φ


/-! ## Day coassociativity for `A = 1` -/

theorem eq_rec_act_ofEquivalence {M : Module} {a b : ℕ}
    (h : a = b) (x : (M.obj a).Carrier) :
    (h ▸ x : (M.obj b).Carrier) =
      M.act x (Superoperator.ofEquivalence (finCongr h.symm)) := by
  induction h
  change x = M.act x (Superoperator.ofEquivalence (finCongr (Eq.refl a)).symm)
  rw [finCongr_refl, Equiv.refl_symm, Superoperator.ofEquivalence_refl,
    M.act_id]

theorem bangComultComponent_degreeUnit_one (p q : ℕ) :
    (bangComultComponent 1 p q).app (tensorPowerDimension 1 (p + q))
        (bangDegreeUnit 1 (p + q)) =
      (tensorPowerDimension_mul_add 1 p q) ▸
        ((DayCoend.intro (bang 1) (bang 1)).app
          (bangDegreeUnit 1 p) (bangDegreeUnit 1 q)) := by
  have hp := tensorPowerDimension_one_eq p
  have hq := tensorPowerDimension_one_eq q
  have hpq := tensorPowerDimension_one_eq (p + q)
  have hmul := tensorPowerDimension_mul_add 1 p q
  rw [eq_rec_act_ofEquivalence, bangComultComponent_eq_act]
  simp only [bangSplitComponent]
  have hval :
      (bangDegreeUnit 1 (p + q) (p + q)).val =
        Superoperator.identity (tensorPowerDimension 1 (p + q)) := by
    simp only [bangDegreeUnit_apply, ↓reduceDIte]
    change Superoperator.comp (symmetricAverage 1 (p + q))
        (Superoperator.identity _) = Superoperator.identity _
    rw [Superoperator.comp_identity,
      symmetricAverage_of_le_one 1 (p + q) (by decide)]
  rw [hval, Superoperator.comp_identity]
  have hsplit :
      Superoperator.ofEquivalence (tensorSplitEquiv 1 p q) =
        Superoperator.ofEquivalence (finCongr hmul.symm) :=
    ofEquivalence_dim_one hpq (by simp [hp, hq]) _ _
  rw [hsplit]

theorem bangSplit_coassoc_channel_one (p q r n : ℕ)
    (x : ((bang 1).obj n).Carrier) :
    Superoperator.comp
        (Superoperator.tensorAssociator
          (tensorPowerDimension 1 p) (tensorPowerDimension 1 q)
          (tensorPowerDimension 1 r))
        (Superoperator.comp
          (Superoperator.tensor
            (Superoperator.ofEquivalence
              (finCongr (tensorPowerDimension_mul_add 1 p q).symm))
            (Superoperator.identity (tensorPowerDimension 1 r)))
          ((bangSplitComponent 1 (p + q) r).app n x)) =
      Superoperator.comp
        (Superoperator.tensor
          (Superoperator.identity (tensorPowerDimension 1 p))
          (Superoperator.ofEquivalence
            (finCongr (tensorPowerDimension_mul_add 1 q r).symm)))
        ((bangSplitComponent 1 p (q + r)).app n x) := by
  have hp := tensorPowerDimension_one_eq p
  have hq := tensorPowerDimension_one_eq q
  have hr := tensorPowerDimension_one_eq r
  have hsrc : tensorPowerDimension 1 (p + (q + r)) = 1 :=
    tensorPowerDimension_one_eq _
  have htgt : tensorPowerDimension 1 p *
      (tensorPowerDimension 1 q * tensorPowerDimension 1 r) = 1 := by
    simp [hp, hq, hr]
  have hassoc : (p + q) + r = p + (q + r) := Nat.add_assoc p q r
  let eDeg := finCongr (congrArg (tensorPowerDimension 1) hassoc)
  have hx :
      (x ((p + q) + r)).val =
        Superoperator.comp
          (Superoperator.ofEquivalence eDeg.symm)
          (x (p + (q + r))).val := by
    have hfwd :
        Superoperator.comp
            (Superoperator.ofEquivalence eDeg)
            (x ((p + q) + r)).val =
          (x (p + (q + r))).val :=
      (SymmetricElement.val_degreeCast hassoc (x ((p + q) + r))).trans
        (congrArg SymmetricElement.val
          (SymmetricElement.family_degreeCast x hassoc))
    have hcancel :
        Superoperator.comp
            (Superoperator.ofEquivalence eDeg.symm)
            (Superoperator.ofEquivalence eDeg) =
          Superoperator.identity (tensorPowerDimension 1 ((p + q) + r)) := by
      rw [Superoperator.ofEquivalence_comp]
      convert Superoperator.ofEquivalence_refl _
      exact Equiv.symm_trans_self _
    calc
      (x ((p + q) + r)).val =
          Superoperator.comp
            (Superoperator.identity (tensorPowerDimension 1 ((p + q) + r)))
            (x ((p + q) + r)).val :=
        (Superoperator.identity_comp _).symm
      _ = Superoperator.comp
            (Superoperator.comp
              (Superoperator.ofEquivalence eDeg.symm)
              (Superoperator.ofEquivalence eDeg))
            (x ((p + q) + r)).val := by rw [← hcancel]
      _ = Superoperator.comp
            (Superoperator.ofEquivalence eDeg.symm)
            (Superoperator.comp
              (Superoperator.ofEquivalence eDeg)
              (x ((p + q) + r)).val) :=
        (Superoperator.comp_assoc _ _ _).symm
      _ = Superoperator.comp
            (Superoperator.ofEquivalence eDeg.symm)
            (x (p + (q + r))).val :=
        congrArg _ hfwd
  let e_pq := finCongr (tensorPowerDimension_mul_add 1 p q).symm
  let e_qr := finCongr (tensorPowerDimension_mul_add 1 q r).symm
  let e_splitL := tensorSplitEquiv 1 (p + q) r
  let e_splitR := tensorSplitEquiv 1 p (q + r)
  let e_Assoc := Superoperator.tensorAssociatorEquiv
    (tensorPowerDimension 1 p) (tensorPowerDimension 1 q)
    (tensorPowerDimension 1 r)
  simp only [bangSplitComponent]
  rw [hx]
  have hidr :
      Superoperator.identity (tensorPowerDimension 1 r) =
        Superoperator.ofEquivalence (Equiv.refl _) :=
    (Superoperator.ofEquivalence_refl _).symm
  have hidp :
      Superoperator.identity (tensorPowerDimension 1 p) =
        Superoperator.ofEquivalence (Equiv.refl _) :=
    (Superoperator.ofEquivalence_refl _).symm
  have htenL :
      Superoperator.tensor
          (Superoperator.ofEquivalence e_pq)
          (Superoperator.identity (tensorPowerDimension 1 r)) =
        Superoperator.ofEquivalence
          (Superoperator.tensorEquiv e_pq (Equiv.refl _)) := by
    rw [hidr, Superoperator.tensor_ofEquivalence]
  have htenR :
      Superoperator.tensor
          (Superoperator.identity (tensorPowerDimension 1 p))
          (Superoperator.ofEquivalence e_qr) =
        Superoperator.ofEquivalence
          (Superoperator.tensorEquiv (Equiv.refl _) e_qr) := by
    rw [hidp, Superoperator.tensor_ofEquivalence]
  rw [htenL, htenR]
  change
    Superoperator.comp (Superoperator.ofEquivalence e_Assoc)
        (Superoperator.comp
          (Superoperator.ofEquivalence
            (Superoperator.tensorEquiv e_pq (Equiv.refl _)))
          (Superoperator.comp
            (Superoperator.ofEquivalence e_splitL)
            (Superoperator.comp
              (Superoperator.ofEquivalence eDeg.symm)
              (x (p + (q + r))).val))) =
      Superoperator.comp
        (Superoperator.ofEquivalence
          (Superoperator.tensorEquiv (Equiv.refl _) e_qr))
        (Superoperator.comp
          (Superoperator.ofEquivalence e_splitR)
          (x (p + (q + r))).val)
  have hcollapseL :
      Superoperator.comp (Superoperator.ofEquivalence e_Assoc)
          (Superoperator.comp
            (Superoperator.ofEquivalence
              (Superoperator.tensorEquiv e_pq (Equiv.refl _)))
            (Superoperator.comp
              (Superoperator.ofEquivalence e_splitL)
              (Superoperator.ofEquivalence eDeg.symm))) =
        Superoperator.ofEquivalence
          ((((eDeg.symm.trans e_splitL).trans
              (Superoperator.tensorEquiv e_pq (Equiv.refl _))).trans
            e_Assoc)) := by
    rw [Superoperator.ofEquivalence_comp, Superoperator.ofEquivalence_comp,
      Superoperator.ofEquivalence_comp]
  have hcollapseR :
      Superoperator.comp
          (Superoperator.ofEquivalence
            (Superoperator.tensorEquiv (Equiv.refl _) e_qr))
          (Superoperator.ofEquivalence e_splitR) =
        Superoperator.ofEquivalence
          (e_splitR.trans
            (Superoperator.tensorEquiv (Equiv.refl _) e_qr)) :=
    Superoperator.ofEquivalence_comp _ _
  have hreL :
      Superoperator.comp (Superoperator.ofEquivalence e_Assoc)
          (Superoperator.comp
            (Superoperator.ofEquivalence
              (Superoperator.tensorEquiv e_pq (Equiv.refl _)))
            (Superoperator.comp
              (Superoperator.ofEquivalence e_splitL)
              (Superoperator.comp
                (Superoperator.ofEquivalence eDeg.symm)
                (x (p + (q + r))).val))) =
        Superoperator.comp
          (Superoperator.comp (Superoperator.ofEquivalence e_Assoc)
            (Superoperator.comp
              (Superoperator.ofEquivalence
                (Superoperator.tensorEquiv e_pq (Equiv.refl _)))
              (Superoperator.comp
                (Superoperator.ofEquivalence e_splitL)
                (Superoperator.ofEquivalence eDeg.symm))))
          (x (p + (q + r))).val := by
    simp only [Superoperator.comp_assoc]
  have hreR :
      Superoperator.comp
          (Superoperator.ofEquivalence
            (Superoperator.tensorEquiv (Equiv.refl _) e_qr))
          (Superoperator.comp
            (Superoperator.ofEquivalence e_splitR)
            (x (p + (q + r))).val) =
        Superoperator.comp
          (Superoperator.comp
            (Superoperator.ofEquivalence
              (Superoperator.tensorEquiv (Equiv.refl _) e_qr))
            (Superoperator.ofEquivalence e_splitR))
          (x (p + (q + r))).val := by
    simp only [Superoperator.comp_assoc]
  rw [hreL, hreR, hcollapseL, hcollapseR]
  exact congrArg (fun t => Superoperator.comp t (x (p + (q + r))).val)
    (ofEquivalence_dim_one hsrc htgt _ _)

theorem bangComultComponent_coassoc_one (p q r n : ℕ)
    (x : ((bang 1).obj n).Carrier) :
    (DayTensor.associator (bang 1) (bang 1) (bang 1)).app n
        ((DayTensor.map (bangComultComponent 1 p q) (Hom.id (bang 1))).app n
          ((bangComultComponent 1 (p + q) r).app n x)) =
      (DayTensor.map (Hom.id (bang 1)) (bangComultComponent 1 q r)).app n
        ((bangComultComponent 1 p (q + r)).app n x) := by
  set up := bangDegreeUnit 1 p
  set uq := bangDegreeUnit 1 q
  set ur := bangDegreeUnit 1 r
  set upq := bangDegreeUnit 1 (p + q)
  set uqr := bangDegreeUnit 1 (q + r)
  set gen_pq := (DayCoend.intro (bang 1) (bang 1)).app up uq
  set gen_qr := (DayCoend.intro (bang 1) (bang 1)).app uq ur
  set gen_final :=
    (DayCoend.intro (bang 1) (dayTensor (bang 1) (bang 1))).app up gen_qr
  set e_pq := Superoperator.ofEquivalence
    (finCongr (tensorPowerDimension_mul_add 1 p q).symm)
  set e_qr := Superoperator.ofEquivalence
    (finCongr (tensorPowerDimension_mul_add 1 q r).symm)
  set Assoc := Superoperator.tensorAssociator
    (tensorPowerDimension 1 p) (tensorPowerDimension 1 q)
    (tensorPowerDimension 1 r)
  set ΦL : Superoperator n
      (tensorPowerDimension 1 (p + q) * tensorPowerDimension 1 r) :=
    (bangSplitComponent 1 (p + q) r).app n x
  set ΦR : Superoperator n
      (tensorPowerDimension 1 p * tensorPowerDimension 1 (q + r)) :=
    (bangSplitComponent 1 p (q + r)).app n x
  set ΦL' := Superoperator.comp
    (Superoperator.tensor e_pq
      (Superoperator.identity (tensorPowerDimension 1 r))) ΦL
  set ΦR' := Superoperator.comp
    (Superoperator.tensor
      (Superoperator.identity (tensorPowerDimension 1 p)) e_qr) ΦR
  have hch : Superoperator.comp Assoc ΦL' = ΦR' :=
    bangSplit_coassoc_channel_one p q r n x
  have hL :
      (DayTensor.associator (bang 1) (bang 1) (bang 1)).app n
          ((DayTensor.map (bangComultComponent 1 p q) (Hom.id (bang 1))).app n
            ((bangComultComponent 1 (p + q) r).app n x)) =
        (dayTensor (bang 1) (dayTensor (bang 1) (bang 1))).act gen_final
          (Superoperator.comp Assoc ΦL') := by
    rw [bangComultComponent_eq_act 1 (p + q) r n x]
    change
      (DayTensor.associator (bang 1) (bang 1) (bang 1)).app n
          ((DayTensor.map (bangComultComponent 1 p q) (Hom.id (bang 1))).app n
            ((dayTensor (bang 1) (bang 1)).act
              ((DayCoend.intro (bang 1) (bang 1)).app upq ur) ΦL)) =
        _
    rw [(DayTensor.map (bangComultComponent 1 p q) (Hom.id (bang 1))).naturality
      ((DayCoend.intro (bang 1) (bang 1)).app upq ur) ΦL]
    rw [DayTensor.map_intro, Hom.id_app]
    have hdu := bangComultComponent_degreeUnit_one p q
    change
      (DayTensor.associator (bang 1) (bang 1) (bang 1)).app n
          ((dayTensor (dayTensor (bang 1) (bang 1)) (bang 1)).act
            ((DayCoend.intro (dayTensor (bang 1) (bang 1)) (bang 1)).app
              ((bangComultComponent 1 p q).app
                (tensorPowerDimension 1 (p + q))
                (bangDegreeUnit 1 (p + q)))
              ur) ΦL) =
        _
    rw [hdu, eq_rec_act_ofEquivalence]
    rw [show ur = (bang 1).act ur (Superoperator.identity _)
      from ((bang 1).act_id _).symm]
    rw [(DayCoend.intro (dayTensor (bang 1) (bang 1)) (bang 1)).naturality
      gen_pq ur e_pq (Superoperator.identity _)]
    rw [(dayTensor (dayTensor (bang 1) (bang 1)) (bang 1)).act_comp]
    set gen3 :=
      (DayCoend.intro (dayTensor (bang 1) (bang 1)) (bang 1)).app gen_pq ur
    change
      (DayTensor.associator (bang 1) (bang 1) (bang 1)).app n
          ((dayTensor (dayTensor (bang 1) (bang 1)) (bang 1)).act gen3 ΦL') =
        _
    rw [(DayTensor.associator (bang 1) (bang 1) (bang 1)).naturality gen3 ΦL']
    rw [DayTensor.associator_intro_intro]
    exact (dayTensor (bang 1) (dayTensor (bang 1) (bang 1))).act_comp _ _ _
  have hR :
      (DayTensor.map (Hom.id (bang 1)) (bangComultComponent 1 q r)).app n
          ((bangComultComponent 1 p (q + r)).app n x) =
        (dayTensor (bang 1) (dayTensor (bang 1) (bang 1))).act gen_final
          ΦR' := by
    rw [bangComultComponent_eq_act 1 p (q + r) n x]
    change
      (DayTensor.map (Hom.id (bang 1)) (bangComultComponent 1 q r)).app n
          ((dayTensor (bang 1) (bang 1)).act
            ((DayCoend.intro (bang 1) (bang 1)).app up uqr) ΦR) =
        _
    rw [(DayTensor.map (Hom.id (bang 1)) (bangComultComponent 1 q r)).naturality
      ((DayCoend.intro (bang 1) (bang 1)).app up uqr) ΦR]
    rw [DayTensor.map_intro, Hom.id_app]
    have hdu := bangComultComponent_degreeUnit_one q r
    change
      (dayTensor (bang 1) (dayTensor (bang 1) (bang 1))).act
          ((DayCoend.intro (bang 1) (dayTensor (bang 1) (bang 1))).app
            up
            ((bangComultComponent 1 q r).app
              (tensorPowerDimension 1 (q + r))
              (bangDegreeUnit 1 (q + r)))) ΦR =
        _
    rw [hdu, eq_rec_act_ofEquivalence]
    rw [show up = (bang 1).act up (Superoperator.identity _)
      from ((bang 1).act_id _).symm]
    rw [(DayCoend.intro (bang 1) (dayTensor (bang 1) (bang 1))).naturality
      up gen_qr (Superoperator.identity _) e_qr]
    exact (dayTensor (bang 1) (dayTensor (bang 1) (bang 1))).act_comp _ _ _
  rw [hL, hR, hch]


theorem bangComult_hasSum_components (n : ℕ)
    (x : ((bang 1).obj n).Carrier) :
    ((dayTensor (bang 1) (bang 1)).obj n).HasSum
      (bangComultComponentFamily 1 n x)
      (bangComult_one.app n x) := by
  have h := bangComultApp_hasSum 1 bangComultComponentsAdmissible_one n x
    (dayTensor (bang 1) (bang 1)) (DayCoend.intro (bang 1) (bang 1))
  have hfun :
      (fun pq : ℕ × ℕ =>
          DayCoend.evaluate (dayTensor (bang 1) (bang 1))
            (DayCoend.intro (bang 1) (bang 1))
            (bangComultComponentFamily 1 n x pq)) =
        bangComultComponentFamily 1 n x := by
    funext pq; exact DayCoend.evaluate_self _
  have hs := DayCoend.evaluate_self (bangComultApp 1 bangComultComponentsAdmissible_one n x)
  change ((dayTensor (bang 1) (bang 1)).obj n).HasSum
      (fun pq => DayCoend.evaluate (DayCoend.module (bang 1) (bang 1))
        (DayCoend.intro (bang 1) (bang 1))
        (bangComultComponentFamily 1 n x pq))
      (DayCoend.evaluate (DayCoend.module (bang 1) (bang 1))
        (DayCoend.intro (bang 1) (bang 1))
        (bangComultApp 1 bangComultComponentsAdmissible_one n x)) at h
  rw [hfun, hs] at h
  exact h

theorem bangComultComponent_degreeUnit_of_ne (p q a : ℕ) (hne : p + q ≠ a) :
    (bangComultComponent 1 p q).app (tensorPowerDimension 1 a)
        (bangDegreeUnit 1 a) = 0 := by
  rw [bangComultComponent_eq_act]
  simp only [bangSplitComponent]
  have hval : (bangDegreeUnit 1 a (p + q)).val = 0 := by
    simp only [bangDegreeUnit_apply, dif_neg hne]
    rfl
  rw [hval, Superoperator.comp_zero_right]
  exact (dayTensor (bang 1) (bang 1)).act_zero_map _

theorem bangComult_degreeUnit_partition_hasSum (a : ℕ) :
    ((dayTensor (bang 1) (bang 1)).obj (tensorPowerDimension 1 a)).HasSum
      (fun part : DegreePartition a =>
        (bangComultComponent 1
            (degreePartitionToPair a part).1
            (degreePartitionToPair a part).2).app
          (tensorPowerDimension 1 a) (bangDegreeUnit 1 a))
      (bangComult_one.app (tensorPowerDimension 1 a) (bangDegreeUnit 1 a)) := by
  have hall := bangComult_hasSum_components
    (tensorPowerDimension 1 a) (bangDegreeUnit 1 a)
  have hσ :
      ((dayTensor (bang 1) (bang 1)).obj (tensorPowerDimension 1 a)).HasSum
        (fun s : Σ t : ℕ, DegreePartition t =>
          (bangComultComponent 1
              (degreePartitionToPair s.1 s.2).1
              (degreePartitionToPair s.1 s.2).2).app
            (tensorPowerDimension 1 a) (bangDegreeUnit 1 a))
        (bangComult_one.app (tensorPowerDimension 1 a) (bangDegreeUnit 1 a)) :=
    (((dayTensor (bang 1) (bang 1)).obj (tensorPowerDimension 1 a)).summation.reindex
      degreePartitionEquiv.symm
      (bangComultComponentFamily 1 (tensorPowerDimension 1 a) (bangDegreeUnit 1 a))
      (bangComult_one.app (tensorPowerDimension 1 a) (bangDegreeUnit 1 a))).mpr hall
  obtain ⟨row, hrows, hcol⟩ :=
    ((dayTensor (bang 1) (bang 1)).obj (tensorPowerDimension 1 a)).summation.flatten
      (fun t (part : DegreePartition t) =>
        (bangComultComponent 1
            (degreePartitionToPair t part).1
            (degreePartitionToPair t part).2).app
          (tensorPowerDimension 1 a) (bangDegreeUnit 1 a))
      (bangComult_one.app (tensorPowerDimension 1 a) (bangDegreeUnit 1 a)) |>.mp hσ
  have hrow0 (t : ℕ) (hne : t ≠ a) : row t = 0 := by
    have hz :
        ((dayTensor (bang 1) (bang 1)).obj (tensorPowerDimension 1 a)).HasSum
          (fun part : DegreePartition t =>
            (bangComultComponent 1
                (degreePartitionToPair t part).1
                (degreePartitionToPair t part).2).app
              (tensorPowerDimension 1 a) (bangDegreeUnit 1 a))
          0 := by
      have hfam0 :
          (fun part : DegreePartition t =>
              (bangComultComponent 1
                  (degreePartitionToPair t part).1
                  (degreePartitionToPair t part).2).app
                (tensorPowerDimension 1 a) (bangDegreeUnit 1 a)) =
            fun _ => 0 := by
        funext part
        have : (degreePartitionToPair t part).1 +
            (degreePartitionToPair t part).2 ≠ a := by
          rw [degreePartitionToPair_snd_add]; exact hne
        exact bangComultComponent_degreeUnit_of_ne _ _ a this
      rw [hfam0]
      exact Fiber.hasSum_zero _
    exact ((dayTensor (bang 1) (bang 1)).obj _).summation.unique (hrows t) hz
  have hfam :
      (fun t : ℕ => row t) =
        fun t : ℕ => if h : t = a then row a else (0 : _) := by
    funext t
    by_cases ht : t = a <;> simp [ht, hrow0]
  have hcol' :
      ((dayTensor (bang 1) (bang 1)).obj (tensorPowerDimension 1 a)).HasSum
        (fun t : ℕ => if h : t = a then row a else 0)
        (bangComult_one.app (tensorPowerDimension 1 a) (bangDegreeUnit 1 a)) := by
    rwa [← hfam]
  have hsingle :=
    Fiber.hasSum_singleAt
      ((dayTensor (bang 1) (bang 1)).obj (tensorPowerDimension 1 a))
      (a : ℕ) (row a)
  have hsum :=
    ((dayTensor (bang 1) (bang 1)).obj _).summation.unique hcol' hsingle
  rw [hsum]
  exact hrows a



theorem bang_map_comult_id_partition_hasSum (a b n : ℕ)
    (x : ((bang 1).obj n).Carrier) :
    ((dayTensor (dayTensor (bang 1) (bang 1)) (bang 1)).obj n).HasSum
      (fun part : DegreePartition a =>
        (DayTensor.map
            (bangComultComponent 1
              (degreePartitionToPair a part).1
              (degreePartitionToPair a part).2)
            (Hom.id (bang 1))).app n
          ((bangComultComponent 1 a b).app n x))
      ((DayTensor.map bangComult_one (Hom.id (bang 1))).app n
        ((bangComultComponent 1 a b).app n x)) := by
  set Φ : Superoperator n
      (tensorPowerDimension 1 a * tensorPowerDimension 1 b) :=
    (bangSplitComponent 1 a b).app n x
  set gen := (DayCoend.intro (bang 1) (bang 1)).app
    (bangDegreeUnit 1 a) (bangDegreeUnit 1 b)
  have hx := bangComultComponent_eq_act 1 a b n x
  have hδua := bangComult_degreeUnit_partition_hasSum a
  have hintro :=
    (DayCoend.intro (dayTensor (bang 1) (bang 1)) (bang 1)).map_sum_left
      (bangDegreeUnit 1 b) hδua
  have hact :=
    (dayTensor (dayTensor (bang 1) (bang 1)) (bang 1)).act_sum_element Φ hintro
  have hfam :
      (fun part : DegreePartition a =>
          (dayTensor (dayTensor (bang 1) (bang 1)) (bang 1)).act
            ((DayCoend.intro (dayTensor (bang 1) (bang 1)) (bang 1)).app
              ((bangComultComponent 1
                  (degreePartitionToPair a part).1
                  (degreePartitionToPair a part).2).app
                (tensorPowerDimension 1 a) (bangDegreeUnit 1 a))
              (bangDegreeUnit 1 b)) Φ) =
        fun part : DegreePartition a =>
          (DayTensor.map
              (bangComultComponent 1
                (degreePartitionToPair a part).1
                (degreePartitionToPair a part).2)
              (Hom.id (bang 1))).app n
            ((bangComultComponent 1 a b).app n x) := by
    funext part
    rw [hx]; symm
    rw [(DayTensor.map
        (bangComultComponent 1
          (degreePartitionToPair a part).1
          (degreePartitionToPair a part).2)
        (Hom.id (bang 1))).naturality gen Φ,
      DayTensor.map_intro, Hom.id_app]
  have hsum :
      (DayTensor.map bangComult_one (Hom.id (bang 1))).app n
          ((bangComultComponent 1 a b).app n x) =
        (dayTensor (dayTensor (bang 1) (bang 1)) (bang 1)).act
          ((DayCoend.intro (dayTensor (bang 1) (bang 1)) (bang 1)).app
            (bangComult_one.app (tensorPowerDimension 1 a) (bangDegreeUnit 1 a))
            (bangDegreeUnit 1 b)) Φ := by
    rw [hx, (DayTensor.map bangComult_one (Hom.id (bang 1))).naturality gen Φ,
      DayTensor.map_intro, Hom.id_app]
  rw [hfam] at hact
  rwa [← hsum] at hact

theorem bang_map_id_comult_partition_hasSum (a b n : ℕ)
    (x : ((bang 1).obj n).Carrier) :
    ((dayTensor (bang 1) (dayTensor (bang 1) (bang 1))).obj n).HasSum
      (fun part : DegreePartition b =>
        (DayTensor.map (Hom.id (bang 1))
            (bangComultComponent 1
              (degreePartitionToPair b part).1
              (degreePartitionToPair b part).2)).app n
          ((bangComultComponent 1 a b).app n x))
      ((DayTensor.map (Hom.id (bang 1)) bangComult_one).app n
        ((bangComultComponent 1 a b).app n x)) := by
  set Φ : Superoperator n
      (tensorPowerDimension 1 a * tensorPowerDimension 1 b) :=
    (bangSplitComponent 1 a b).app n x
  set gen := (DayCoend.intro (bang 1) (bang 1)).app
    (bangDegreeUnit 1 a) (bangDegreeUnit 1 b)
  have hx := bangComultComponent_eq_act 1 a b n x
  have hδub := bangComult_degreeUnit_partition_hasSum b
  have hintro :=
    (DayCoend.intro (bang 1) (dayTensor (bang 1) (bang 1))).map_sum_right
      (bangDegreeUnit 1 a) hδub
  have hact :=
    (dayTensor (bang 1) (dayTensor (bang 1) (bang 1))).act_sum_element Φ hintro
  have hfam :
      (fun part : DegreePartition b =>
          (dayTensor (bang 1) (dayTensor (bang 1) (bang 1))).act
            ((DayCoend.intro (bang 1) (dayTensor (bang 1) (bang 1))).app
              (bangDegreeUnit 1 a)
              ((bangComultComponent 1
                  (degreePartitionToPair b part).1
                  (degreePartitionToPair b part).2).app
                (tensorPowerDimension 1 b) (bangDegreeUnit 1 b))) Φ) =
        fun part : DegreePartition b =>
          (DayTensor.map (Hom.id (bang 1))
              (bangComultComponent 1
                (degreePartitionToPair b part).1
                (degreePartitionToPair b part).2)).app n
            ((bangComultComponent 1 a b).app n x) := by
    funext part
    rw [hx]; symm
    rw [(DayTensor.map (Hom.id (bang 1))
        (bangComultComponent 1
          (degreePartitionToPair b part).1
          (degreePartitionToPair b part).2)).naturality gen Φ,
      DayTensor.map_intro, Hom.id_app]
  have hsum :
      (DayTensor.map (Hom.id (bang 1)) bangComult_one).app n
          ((bangComultComponent 1 a b).app n x) =
        (dayTensor (bang 1) (dayTensor (bang 1) (bang 1))).act
          ((DayCoend.intro (bang 1) (dayTensor (bang 1) (bang 1))).app
            (bangDegreeUnit 1 a)
            (bangComult_one.app (tensorPowerDimension 1 b) (bangDegreeUnit 1 b))) Φ := by
    rw [hx, (DayTensor.map (Hom.id (bang 1)) bangComult_one).naturality gen Φ,
      DayTensor.map_intro, Hom.id_app]
  rw [hfam] at hact
  rwa [← hsum] at hact





def leftCoassocIndexEquiv :
    (Σ ab : ℕ × ℕ, DegreePartition ab.1) ≃ ℕ × ℕ × ℕ where
  toFun s :=
    ((degreePartitionToPair s.1.1 s.2).1,
      (degreePartitionToPair s.1.1 s.2).2, s.1.2)
  invFun pqr :=
    ⟨(pqr.1 + pqr.2.1, pqr.2.2), (pairToDegreePartition (pqr.1, pqr.2.1)).2⟩
  left_inv := by
    intro s
    rcases s with ⟨⟨a, b⟩, part⟩
    have hr := degreePartitionEquiv.right_inv ⟨a, part⟩
    -- hr : pairToDegreePartition (toPair a part) = ⟨a, part⟩
    refine Eq.trans ?_ (congrArg (fun σ : (t : ℕ) × DegreePartition t =>
      (⟨(σ.1, b), σ.2⟩ : (Σ ab : ℕ × ℕ, DegreePartition ab.1))) hr)
    -- LHS after toFun∘invFun vs ⟨((p+q),b), part'⟩ where part' = pair....2
    -- and middle is ⟨(a,b), part⟩ from hr
    -- Need: invFun(toFun s) = ⟨(p+q, b), pair(toPair).2⟩ equal to
    --        ⟨((pair toPair).1, b), (pair toPair).2⟩
    apply Sigma.ext
    · apply Prod.ext
      · -- p+q = (pairToDegreePartition (p,q)).1
        rfl
      · rfl
    · rfl
  right_inv := by
    intro pqr
    rcases pqr with ⟨p, q, r⟩
    have hl := pairToDegreePartition_toPair (p, q)
    exact congrArg (fun pq : ℕ × ℕ => (pq.1, pq.2, r)) hl

def rightCoassocIndexEquiv :
    (Σ ab : ℕ × ℕ, DegreePartition ab.2) ≃ ℕ × ℕ × ℕ where
  toFun s :=
    (s.1.1, (degreePartitionToPair s.1.2 s.2).1,
      (degreePartitionToPair s.1.2 s.2).2)
  invFun pqr :=
    ⟨(pqr.1, pqr.2.1 + pqr.2.2), (pairToDegreePartition (pqr.2.1, pqr.2.2)).2⟩
  left_inv := by
    intro s
    rcases s with ⟨⟨a, b⟩, part⟩
    have hr := degreePartitionEquiv.right_inv ⟨b, part⟩
    refine Eq.trans ?_ (congrArg (fun σ : (t : ℕ) × DegreePartition t =>
      (⟨(a, σ.1), σ.2⟩ : (Σ ab : ℕ × ℕ, DegreePartition ab.2))) hr)
    apply Sigma.ext
    · apply Prod.ext <;> rfl
    · rfl
  right_inv := by
    intro pqr
    rcases pqr with ⟨p, q, r⟩
    have hl := pairToDegreePartition_toPair (q, r)
    exact congrArg (fun qr : ℕ × ℕ => (p, qr.1, qr.2)) hl




theorem leftCoassocIndexEquiv_symm_apply (p q r : ℕ) :
    leftCoassocIndexEquiv.symm (p, q, r) =
      ⟨(p + q, r), (pairToDegreePartition (p, q)).2⟩ :=
  rfl

theorem rightCoassocIndexEquiv_symm_apply (p q r : ℕ) :
    rightCoassocIndexEquiv.symm (p, q, r) =
      ⟨(p, q + r), (pairToDegreePartition (q, r)).2⟩ :=
  rfl

theorem degreePartitionToPair_pairToDegreePartition (p q : ℕ) :
    degreePartitionToPair (p + q) (pairToDegreePartition (p, q)).2 = (p, q) := by
  have h := pairToDegreePartition_toPair (p, q)
  -- h : toPair (pair (p,q)).1 (pair (p,q)).2 = (p,q)
  -- (pair (p,q)).1 = p+q definitionally
  exact h


theorem bang_coassociative_one :
    Hom.comp (DayTensor.associator (bang 1) (bang 1) (bang 1))
        (Hom.comp (DayTensor.map bangComult_one (Hom.id (bang 1)))
          bangComult_one) =
      Hom.comp (DayTensor.map (Hom.id (bang 1)) bangComult_one)
        bangComult_one := by
  ext n x
  let Assoc := DayTensor.associator (bang 1) (bang 1) (bang 1)
  let M3 := dayTensor (bang 1) (dayTensor (bang 1) (bang 1))
  have hδ := bangComult_hasSum_components n x
  have hmapL := (DayTensor.map bangComult_one (Hom.id (bang 1))).map_sum hδ
  have hAssocL := Assoc.map_sum hmapL
  have hmapR := (DayTensor.map (Hom.id (bang 1)) bangComult_one).map_sum hδ
  have hinnerL (a b : ℕ) :=
    Assoc.map_sum (bang_map_comult_id_partition_hasSum a b n x)
  let flatL : (Σ ab : ℕ × ℕ, DegreePartition ab.1) → (M3.obj n).Carrier :=
    fun s =>
      Assoc.app n
        ((DayTensor.map
            (bangComultComponent 1
              (degreePartitionToPair s.1.1 s.2).1
              (degreePartitionToPair s.1.1 s.2).2)
            (Hom.id (bang 1))).app n
          ((bangComultComponent 1 s.1.1 s.1.2).app n x))
  have hflatL : (M3.obj n).HasSum flatL
      (Assoc.app n
        ((DayTensor.map bangComult_one (Hom.id (bang 1))).app n
          (bangComult_one.app n x))) := by
    refine (M3.obj n).summation.flatten
      (fun (ab : ℕ × ℕ) (part : DegreePartition ab.1) =>
        Assoc.app n
          ((DayTensor.map
              (bangComultComponent 1
                (degreePartitionToPair ab.1 part).1
                (degreePartitionToPair ab.1 part).2)
              (Hom.id (bang 1))).app n
            ((bangComultComponent 1 ab.1 ab.2).app n x)))
      _ |>.mpr ⟨?_, ?_, ?_⟩
    · exact fun ab =>
        Assoc.app n
          ((DayTensor.map bangComult_one (Hom.id (bang 1))).app n
            (bangComultComponentFamily 1 n x ab))
    · intro ab; exact hinnerL ab.1 ab.2
    · exact hAssocL
  let flatR : (Σ ab : ℕ × ℕ, DegreePartition ab.2) → (M3.obj n).Carrier :=
    fun s =>
      (DayTensor.map (Hom.id (bang 1))
          (bangComultComponent 1
            (degreePartitionToPair s.1.2 s.2).1
            (degreePartitionToPair s.1.2 s.2).2)).app n
        ((bangComultComponent 1 s.1.1 s.1.2).app n x)
  have hinnerR (a b : ℕ) := bang_map_id_comult_partition_hasSum a b n x
  have hflatR : (M3.obj n).HasSum flatR
      ((DayTensor.map (Hom.id (bang 1)) bangComult_one).app n
        (bangComult_one.app n x)) := by
    refine (M3.obj n).summation.flatten
      (fun (ab : ℕ × ℕ) (part : DegreePartition ab.2) =>
        (DayTensor.map (Hom.id (bang 1))
            (bangComultComponent 1
              (degreePartitionToPair ab.2 part).1
              (degreePartitionToPair ab.2 part).2)).app n
          ((bangComultComponent 1 ab.1 ab.2).app n x))
      _ |>.mpr ⟨?_, ?_, ?_⟩
    · exact fun ab =>
        (DayTensor.map (Hom.id (bang 1)) bangComult_one).app n
          (bangComultComponentFamily 1 n x ab)
    · intro ab; exact hinnerR ab.1 ab.2
    · exact hmapR
  have hL_comp :
      (M3.obj n).HasSum (flatL ∘ leftCoassocIndexEquiv.symm)
        (Assoc.app n
          ((DayTensor.map bangComult_one (Hom.id (bang 1))).app n
            (bangComult_one.app n x))) :=
    ((M3.obj n).summation.reindex leftCoassocIndexEquiv.symm flatL _).mpr hflatL
  have hL :
      (M3.obj n).HasSum
        (fun pqr : ℕ × ℕ × ℕ =>
          Assoc.app n
            ((DayTensor.map (bangComultComponent 1 pqr.1 pqr.2.1)
                (Hom.id (bang 1))).app n
              ((bangComultComponent 1 (pqr.1 + pqr.2.1) pqr.2.2).app n x)))
        (Assoc.app n
          ((DayTensor.map bangComult_one (Hom.id (bang 1))).app n
            (bangComult_one.app n x))) := by
    convert hL_comp using 1
    funext pqr
    rcases pqr with ⟨p, q, r⟩
    rw [Function.comp_apply, leftCoassocIndexEquiv_symm_apply]
    dsimp only [flatL]
    rw [degreePartitionToPair_pairToDegreePartition]
  have hR_comp :
      (M3.obj n).HasSum (flatR ∘ rightCoassocIndexEquiv.symm)
        ((DayTensor.map (Hom.id (bang 1)) bangComult_one).app n
          (bangComult_one.app n x)) :=
    ((M3.obj n).summation.reindex rightCoassocIndexEquiv.symm flatR _).mpr hflatR
  have hR :
      (M3.obj n).HasSum
        (fun pqr : ℕ × ℕ × ℕ =>
          (DayTensor.map (Hom.id (bang 1))
              (bangComultComponent 1 pqr.2.1 pqr.2.2)).app n
            ((bangComultComponent 1 pqr.1 (pqr.2.1 + pqr.2.2)).app n x))
        ((DayTensor.map (Hom.id (bang 1)) bangComult_one).app n
          (bangComult_one.app n x)) := by
    convert hR_comp using 1
    funext pqr
    rcases pqr with ⟨p, q, r⟩
    rw [Function.comp_apply, rightCoassocIndexEquiv_symm_apply]
    dsimp only [flatR]
    rw [degreePartitionToPair_pairToDegreePartition]
  have heq :
      (fun pqr : ℕ × ℕ × ℕ =>
          Assoc.app n
            ((DayTensor.map (bangComultComponent 1 pqr.1 pqr.2.1)
                (Hom.id (bang 1))).app n
              ((bangComultComponent 1 (pqr.1 + pqr.2.1) pqr.2.2).app n x))) =
        fun pqr : ℕ × ℕ × ℕ =>
          (DayTensor.map (Hom.id (bang 1))
              (bangComultComponent 1 pqr.2.1 pqr.2.2)).app n
            ((bangComultComponent 1 pqr.1 (pqr.2.1 + pqr.2.2)).app n x) := by
    funext pqr
    exact bangComultComponent_coassoc_one pqr.1 pqr.2.1 pqr.2.2 n x
  rw [heq] at hL
  exact (M3.obj n).summation.unique hL hR



theorem bang_coassociative_of_le_one (A : ℕ) (hA : A ≤ 1) :
    Hom.comp (DayTensor.associator (bang A) (bang A) (bang A))
        (Hom.comp (DayTensor.map (bangComult_of_le_one A hA) (Hom.id (bang A)))
          (bangComult_of_le_one A hA)) =
      Hom.comp (DayTensor.map (Hom.id (bang A)) (bangComult_of_le_one A hA))
        (bangComult_of_le_one A hA) := by
  interval_cases A
  · -- Reduce to bang_coassociative_zero via bangComult_zero_eq
    have h0 : bangComult_of_le_one 0 (by decide) = bangComult_zero := rfl
    simpa [h0] using bang_coassociative_zero
  · have h1 : bangComult_of_le_one 1 (by decide) = bangComult_one := rfl
    simpa [h1] using bang_coassociative_one

/-- Day comonoid structure on `bang A` for `A ≤ 1`.
Marked `abbrev` so `(bangComonoid A hA).carrier` reduces to `bang A`. -/
noncomputable abbrev bangComonoid (A : ℕ) (hA : A ≤ 1) : Comonoid where
  carrier := bang A
  counit := bangCounit A
  comult := bangComult_of_le_one A hA
  left_counit := bang_left_counit_of_le_one A hA
  right_counit := bang_right_counit_of_le_one A hA
  coassociative := bang_coassociative_of_le_one A hA
  cocommutative := bang_cocommutative_of_le_one A hA

/-- Dereliction direction of the prospective cofree UP. -/
noncomputable def bangCofreeForget (A : ℕ) (C : Module)
    (f : Hom C (bang A)) : Hom C (representable A) :=
  Hom.comp (bangDereliction A) f

/-! ## Cofree UP for `A ≤ 1` (forgetful direction) -/

/-- Forgetful map from comonoid homs into `bangComonoid` to module homs into
the representable. -/
noncomputable def bangCofreeForgetComonoid (A : ℕ) (hA : A ≤ 1)
    (C : Comonoid)
    (f : ComonoidHom C (bangComonoid A hA)) :
    Hom C.carrier (representable A) :=
  bangCofreeForget A C.carrier f.hom


/-! ## Cofree UP for `A = 0`

The forgetful map `bangCofreeForgetComonoid` has an inverse for `A = 0`:
every comonoid admits a unique comonoid morphism into `bangComonoid 0`,
given by promoting the counit along `representableToBang 0 0`.  Hom-sets into
`representable 0` are fiberwise unique, so the cofree equivalence is a
propositional equivalence of singletons.
-/

/-- There is only one CP map into the zero-dimensional output. -/
theorem cpMap_to_zero_subsingleton (n : ℕ) :
    Subsingleton (CPMap n 0) where
  allEq _Φ _Ψ := by
    apply CPMap.ext
    ext i
    exact Fin.elim0 i.1

/-- Consequently every superoperator into dimension zero is the zero map. -/
theorem superoperator_to_zero_subsingleton (n : ℕ) :
    Subsingleton (Superoperator n 0) where
  allEq _Φ _Ψ :=
    Superoperator.ext ((cpMap_to_zero_subsingleton n).allEq _ _)

/-- Every fiber of the zero-dimensional representable is a singleton. -/
theorem representableZero_subsingleton (n : ℕ) :
    Subsingleton (((representable 0).obj n).Carrier) :=
  superoperator_to_zero_subsingleton n

theorem hom_to_representable_zero_unique (M : Module)
    (f g : Hom M (representable 0)) : f = g := by
  ext n x
  exact (representableZero_subsingleton n).allEq _ _

theorem comonoid_map_counit_id_comult (C : Comonoid) :
    Hom.comp (DayTensor.map C.counit (Hom.id C.carrier)) C.comult =
      DayTensor.leftUnitorInv C.carrier := by
  have hinv := (DayTensor.leftUnitorIso C.carrier).inv_hom
  have h := C.left_counit
  refine Eq.trans ?_ (Eq.trans (congrArg
    (fun g => Hom.comp (DayTensor.leftUnitorInv C.carrier) g) h)
    (Hom.comp_id _))
  refine Eq.trans (Eq.symm (Hom.id_comp _)) ?_
  refine Eq.trans (congrArg (fun g => Hom.comp g
    (Hom.comp (DayTensor.map C.counit (Hom.id C.carrier)) C.comult))
    hinv.symm) ?_
  ext n x; rfl

theorem leftUnitor_natural {M N : Module} (f : Hom M N) :
    Hom.comp (DayTensor.leftUnitor N)
        (DayTensor.map (Hom.id dayTensorUnit) f) =
      Hom.comp f (DayTensor.leftUnitor M) := by
  apply DayTensor.hom_ext
  intro m n q x
  simp only [DayTensor.map_intro, Hom.comp_app, Hom.id_app]
  have hL := DayTensor.leftUnitor_intro (M := N) q (f.app n x)
  have hR := DayTensor.leftUnitor_intro (M := M) q x
  change
    (DayTensor.leftUnitor N).app (m * n)
        ((DayCoend.intro dayTensorUnit N).app q (f.app n x)) =
      f.app (m * n)
        ((DayTensor.leftUnitor M).app (m * n)
          ((DayCoend.intro dayTensorUnit M).app q x))
  rw [hL, hR, f.naturality]

theorem leftUnitorInv_natural {M N : Module} (f : Hom M N) :
    Hom.comp (DayTensor.map (Hom.id dayTensorUnit) f)
        (DayTensor.leftUnitorInv M) =
      Hom.comp (DayTensor.leftUnitorInv N) f := by
  have hcancel :
      Hom.comp (DayTensor.leftUnitor N)
          (Hom.comp (DayTensor.map (Hom.id dayTensorUnit) f)
            (DayTensor.leftUnitorInv M)) =
        f := by
    refine Eq.trans ?_ (Hom.comp_id f)
    refine Eq.trans ?_
      (congrArg (fun g => Hom.comp f g)
        (DayTensor.leftUnitorIso M).hom_inv)
    have hnat := leftUnitor_natural f
    refine Eq.trans (Eq.symm (by ext; rfl :
        Hom.comp (DayTensor.leftUnitor N)
            (Hom.comp (DayTensor.map (Hom.id dayTensorUnit) f)
              (DayTensor.leftUnitorInv M)) =
          Hom.comp
            (Hom.comp (DayTensor.leftUnitor N)
              (DayTensor.map (Hom.id dayTensorUnit) f))
            (DayTensor.leftUnitorInv M))) ?_
    refine Eq.trans (congrArg (fun g => Hom.comp g
        (DayTensor.leftUnitorInv M)) hnat) ?_
    ext; rfl
  refine Eq.trans ?_ (congrArg
    (fun g => Hom.comp (DayTensor.leftUnitorInv N) g) hcancel)
  have hinv := (DayTensor.leftUnitorIso N).inv_hom
  refine Eq.trans (Eq.symm (Hom.id_comp _)) ?_
  refine Eq.trans (congrArg (fun g => Hom.comp g
      (Hom.comp (DayTensor.map (Hom.id dayTensorUnit) f)
        (DayTensor.leftUnitorInv M))) hinv.symm) ?_
  ext; rfl

/-- Any Day comonoid satisfies `(ε ⊗ ε) ∘ Δ = λ_I⁻¹ ∘ ε`. -/
theorem comonoid_counit_tensor (C : Comonoid) :
    Hom.comp (DayTensor.map C.counit C.counit) C.comult =
      Hom.comp (DayTensor.leftUnitorInv dayTensorUnit) C.counit := by
  have hfactor :
      DayTensor.map C.counit C.counit =
        Hom.comp (DayTensor.map (Hom.id dayTensorUnit) C.counit)
          (DayTensor.map C.counit (Hom.id C.carrier)) := by
    have h :=
      DayTensor.map_comp (Hom.id dayTensorUnit) C.counit
        C.counit (Hom.id C.carrier)
    simp only [Hom.id_comp, Hom.comp_id] at h
    exact h
  refine Eq.trans (congrArg (fun g => Hom.comp g C.comult) hfactor) ?_
  refine Eq.trans (by ext; rfl :
      Hom.comp
          (Hom.comp (DayTensor.map (Hom.id dayTensorUnit) C.counit)
            (DayTensor.map C.counit (Hom.id C.carrier)))
          C.comult =
        Hom.comp (DayTensor.map (Hom.id dayTensorUnit) C.counit)
          (Hom.comp (DayTensor.map C.counit (Hom.id C.carrier))
            C.comult)) ?_
  rw [comonoid_map_counit_id_comult C, leftUnitorInv_natural C.counit]

theorem bangCounit_comp_representableToBang_zero :
    Hom.comp (bangCounit 0) (representableToBang 0 0) =
      Hom.id dayTensorUnit := by
  ext n Φ
  change ((representableToBang 0 0).app n Φ 0).val = Φ
  change ((symmetricPowerProjection 0 0).app n Φ).val = Φ
  show Superoperator.comp (symmetricAverage 0 0)
      (Φ : Superoperator n (tensorPowerDimension 0 0)) = Φ
  rw [symmetricAverage_of_le_one 0 0 (by decide)]
  exact Superoperator.identity_comp _

theorem symmetricElement_zero_of_pos_subsingleton (k n : ℕ) (hk : k ≠ 0) :
    Subsingleton (SymmetricElement 0 k n) where
  allEq x y := by
    apply SymmetricElement.ext
    have hdim : tensorPowerDimension 0 k = 0 := by
      cases k with
      | zero => exact (hk rfl).elim
      | succ k => simp [tensorPowerDimension]
    have : Subsingleton (Superoperator n (tensorPowerDimension 0 k)) := by
      rw [hdim]; exact superoperator_to_zero_subsingleton n
    exact Subsingleton.elim _ _

theorem bang_zero_eq_of_counit (n : ℕ)
    (x : ((bang 0).obj n).Carrier) :
    (representableToBang 0 0).app n ((bangCounit 0).app n x) = x := by
  funext k
  by_cases hk : k = 0
  · subst hk
    apply SymmetricElement.ext
    change Superoperator.comp (symmetricAverage 0 0) (x 0).val = (x 0).val
    rw [symmetricAverage_of_le_one 0 0 (by decide)]
    exact Superoperator.identity_comp _
  · exact (symmetricElement_zero_of_pos_subsingleton k n hk).allEq _ _

theorem representableToBang_comp_bangCounit_zero :
    Hom.comp (representableToBang 0 0) (bangCounit 0) =
      Hom.id (bang 0) := by
  ext n x; exact bang_zero_eq_of_counit n x

theorem bangSplit_representableToBang_zero (n : ℕ)
    (Φ : ((representable (tensorPowerDimension 0 0)).obj n).Carrier) :
    (bangSplitComponent 0 0 0).app n
        ((representableToBang 0 0).app n Φ) =
      (Φ : Superoperator n
        (tensorPowerDimension 0 0 * tensorPowerDimension 0 0)) := by
  unfold bangSplitComponent representableToBang
  simp only [Hom.comp_app]
  change Superoperator.comp
      (Superoperator.ofEquivalence (tensorSplitEquiv 0 0 0))
      ((countableProductInjection (fun j => symmetricPower 0 j) 0).app n
        ((symmetricPowerProjection 0 0).app n Φ) 0).val = _
  change Superoperator.comp
      (Superoperator.ofEquivalence (tensorSplitEquiv 0 0 0))
      ((symmetricPowerProjection 0 0).app n Φ).val = _
  change Superoperator.comp
      (Superoperator.ofEquivalence (tensorSplitEquiv 0 0 0))
      (Superoperator.comp (symmetricAverage 0 0)
        (Φ : Superoperator n (tensorPowerDimension 0 0))) = _
  have havg := symmetricAverage_of_le_one 0 0 (Nat.zero_le 1)
  rw [havg]
  have hΦ :
      Superoperator.comp
          (Superoperator.identity (tensorPowerDimension 0 0))
          (Φ : Superoperator n (tensorPowerDimension 0 0)) =
        (Φ : Superoperator n (tensorPowerDimension 0 0)) :=
    Superoperator.identity_comp _
  rw [hΦ]
  have hsplit :
      Superoperator.ofEquivalence (tensorSplitEquiv 0 0 0) =
        Superoperator.ofEquivalence
          (Equiv.refl
            (Fin (tensorPowerDimension 0 0 * tensorPowerDimension 0 0))) :=
    ofEquivalence_dim_one rfl rfl _ _
  rw [hsplit, Superoperator.ofEquivalence_refl]
  exact Superoperator.identity_comp _

theorem tensorLeftUnitorInv_one :
    Superoperator.tensorLeftUnitorInv 1 =
      Superoperator.identity (1 * 1) := by
  change Superoperator.ofEquivalence
      (Superoperator.tensorLeftUnitorEquiv 1).symm =
    Superoperator.identity (1 * 1)
  have h :
      Superoperator.tensorLeftUnitorEquiv 1 =
        Equiv.refl (Fin (1 * 1)) := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    exact (fin_val_eq_zero_of_card_one (rfl : 1 * 1 = 1)
        (Superoperator.tensorLeftUnitorEquiv 1 i)).trans
      (fin_val_eq_zero_of_card_one (rfl : 1 * 1 = 1)
        ((Equiv.refl (Fin (1 * 1))) i)).symm
  rw [h, Equiv.refl_symm, Superoperator.ofEquivalence_refl]

theorem bangSplitToRepDay_eq_leftUnitorInv (n : ℕ)
    (Φ : ((representable
        (tensorPowerDimension 0 0 * tensorPowerDimension 0 0)).obj n).Carrier) :
    (bangSplitToRepDay 0 0 0).app n Φ =
      (DayTensor.leftUnitorInv dayTensorUnit).app n
        (Φ : (dayTensorUnit.obj n).Carrier) := by
  rw [bangSplitToRepDay_app]
  set Φ1 : Superoperator n 1 := Φ
  set id1 : (dayTensorUnit.obj 1).Carrier := Superoperator.identity 1
  have hnat :=
    (DayCoend.intro dayTensorUnit dayTensorUnit).naturality
      id1 id1 (Superoperator.identity 1) Φ1
  have hid : dayTensorUnit.act id1 (Superoperator.identity 1) = id1 :=
    dayTensorUnit.act_id id1
  have hΦact : dayTensorUnit.act id1 Φ1 = Φ1 := by
    change Superoperator.comp (id1 : Superoperator 1 1) Φ1 = Φ1
    exact Superoperator.identity_comp Φ1
  have hnat' :
      (DayCoend.intro dayTensorUnit dayTensorUnit).app id1 Φ1 =
        (dayTensor dayTensorUnit dayTensorUnit).act
          ((DayCoend.intro dayTensorUnit dayTensorUnit).app id1 id1)
          (Superoperator.tensor (Superoperator.identity 1) Φ1) := by
    rw [hid, hΦact] at hnat; exact hnat
  have hcomp :
      Superoperator.comp
          (Superoperator.tensor (Superoperator.identity 1) Φ1)
          (Superoperator.tensorLeftUnitorInv n) =
        Φ1 := by
    rw [Superoperator.tensorLeftUnitorInv_naturality Φ1,
      tensorLeftUnitorInv_one]
    exact Superoperator.identity_comp Φ1
  have hEq :
      (dayTensor dayTensorUnit dayTensorUnit).act
          ((DayCoend.intro dayTensorUnit dayTensorUnit).app id1 Φ1)
          (Superoperator.tensorLeftUnitorInv n) =
        (dayTensor dayTensorUnit dayTensorUnit).act
          ((DayCoend.intro dayTensorUnit dayTensorUnit).app id1 id1) Φ1 := by
    rw [hnat', (dayTensor dayTensorUnit dayTensorUnit).act_comp, hcomp]
  change
    (dayTensor
        (representable (tensorPowerDimension 0 0))
        (representable (tensorPowerDimension 0 0))).act
      ((DayCoend.intro
          (representable (tensorPowerDimension 0 0))
          (representable (tensorPowerDimension 0 0))).app
        (Superoperator.identity (tensorPowerDimension 0 0))
        (Superoperator.identity (tensorPowerDimension 0 0)))
      Φ =
    (DayTensor.leftUnitorInv dayTensorUnit).app n
      (Φ1 : (dayTensorUnit.obj n).Carrier)
  change _ =
    (dayTensor dayTensorUnit dayTensorUnit).act
      ((DayCoend.intro dayTensorUnit dayTensorUnit).app id1 Φ1)
      (Superoperator.tensorLeftUnitorInv n)
  rw [hEq]; rfl

/-- Typed left-unitor inverse at the Mid fiber `tensorPowerDimension 0 0`. -/
noncomputable abbrev leftUnitorInv0 :
    Hom dayTensorUnit
      (dayTensor (representable (tensorPowerDimension 0 0))
        (representable (tensorPowerDimension 0 0))) :=
  DayTensor.leftUnitorInv dayTensorUnit

theorem bangComult_zero_comp_representableToBang :
    Hom.comp bangComult_zero (representableToBang 0 0) =
      Hom.comp
        (DayTensor.map (representableToBang 0 0) (representableToBang 0 0))
        leftUnitorInv0 := by
  apply Hom.ext
  intro n Φ
  have hL := bangComult_zero_eq_component n
    ((representableToBang 0 0).app n Φ)
  have hs := bangSplit_representableToBang_zero n Φ
  change
    bangComult_zero.app n ((representableToBang 0 0).app n Φ) =
      (DayTensor.map (representableToBang 0 0)
          (representableToBang 0 0)).app n
        ((DayTensor.leftUnitorInv dayTensorUnit).app n Φ)
  rw [hL]
  change
    (DayTensor.map (representableToBang 0 0)
        (representableToBang 0 0)).app n
      ((bangSplitToRepDay 0 0 0).app n
        ((bangSplitComponent 0 0 0).app n
          ((representableToBang 0 0).app n Φ))) = _
  rw [hs]
  exact congrArg
    ((DayTensor.map (representableToBang 0 0)
        (representableToBang 0 0)).app n)
    (bangSplitToRepDay_eq_leftUnitorInv n
      (Φ : Superoperator n
        (tensorPowerDimension 0 0 * tensorPowerDimension 0 0)))

/-- Cofree lift of the unique map into `representable 0`. -/
noncomputable def bangCofreeLiftZero (C : Comonoid) :
    Hom C.carrier (bang 0) :=
  Hom.comp (representableToBang 0 0) C.counit

theorem bangCofreeLiftZero_preserves_counit (C : Comonoid) :
    Hom.comp (bangCounit 0) (bangCofreeLiftZero C) = C.counit := by
  ext n x
  change (bangCounit 0).app n
      ((representableToBang 0 0).app n (C.counit.app n x)) =
    C.counit.app n x
  have h :=
    congrArg (fun (f : Hom dayTensorUnit dayTensorUnit) =>
      f.app n (C.counit.app n x))
      bangCounit_comp_representableToBang_zero
  change (bangCounit 0).app n
      ((representableToBang 0 0).app n (C.counit.app n x)) = _ at h
  simpa [Hom.id_app] using h

theorem bangCofreeLiftZero_preserves_comult (C : Comonoid) :
    Hom.comp bangComult_zero (bangCofreeLiftZero C) =
      Hom.comp (DayTensor.map (bangCofreeLiftZero C) (bangCofreeLiftZero C))
        C.comult := by
  have hL :
      Hom.comp bangComult_zero (bangCofreeLiftZero C) =
        Hom.comp
          (DayTensor.map (representableToBang 0 0) (representableToBang 0 0))
          (Hom.comp leftUnitorInv0 C.counit) := by
    change Hom.comp bangComult_zero
        (Hom.comp (representableToBang 0 0) C.counit) = _
    refine Eq.trans (by ext; rfl :
        Hom.comp bangComult_zero
            (Hom.comp (representableToBang 0 0) C.counit) =
          Hom.comp
            (Hom.comp bangComult_zero (representableToBang 0 0)) C.counit) ?_
    refine Eq.trans (congrArg (fun g => Hom.comp g C.counit)
      bangComult_zero_comp_representableToBang) ?_
    ext; rfl
  have hCT :
      Hom.comp leftUnitorInv0 C.counit =
        Hom.comp (DayTensor.map C.counit C.counit) C.comult := by
    have h := comonoid_counit_tensor C
    refine Eq.trans ?_ h.symm
    rfl
  have hR :
      Hom.comp (DayTensor.map (bangCofreeLiftZero C) (bangCofreeLiftZero C))
          C.comult =
        Hom.comp
          (DayTensor.map (representableToBang 0 0) (representableToBang 0 0))
          (Hom.comp (DayTensor.map C.counit C.counit) C.comult) := by
    have hmap := DayTensor.map_comp (representableToBang 0 0) C.counit
      (representableToBang 0 0) C.counit
    change Hom.comp
        (DayTensor.map
          (Hom.comp (representableToBang 0 0) C.counit)
          (Hom.comp (representableToBang 0 0) C.counit))
        C.comult = _
    refine Eq.trans (congrArg (fun g => Hom.comp g C.comult) hmap) ?_
    ext; rfl
  rw [hL, hCT]; exact hR.symm

noncomputable def bangCofreeLiftZeroComonoidHom (C : Comonoid) :
    ComonoidHom C (bangComonoid 0 (by decide)) where
  hom := bangCofreeLiftZero C
  preserves_counit := bangCofreeLiftZero_preserves_counit C
  preserves_comult := by
    change Hom.comp (bangComult_of_le_one 0 (by decide)) (bangCofreeLiftZero C) = _
    have h0 : bangComult_of_le_one 0 (by decide) = bangComult_zero := rfl
    rw [h0]
    exact bangCofreeLiftZero_preserves_comult C

theorem bangCofreeLiftZero_unique (C : Comonoid)
    (f : ComonoidHom C (bangComonoid 0 (by decide))) :
    f = bangCofreeLiftZeroComonoidHom C := by
  apply ComonoidHom.ext
  ext n x
  have hε :
      (bangCounit 0).app n (f.hom.app n x) = C.counit.app n x := by
    have h := congrArg (fun g : Hom C.carrier dayTensorUnit => g.app n x)
      f.preserves_counit
    simpa [bangComonoid, Hom.comp_app] using h
  have hret := bang_zero_eq_of_counit n (f.hom.app n x)
  -- f.hom x = repToBang (bangCounit (f.hom x)) = repToBang (C.counit x)
  change f.hom.app n x = (representableToBang 0 0).app n (C.counit.app n x)
  rw [← hret, hε]

/-- Cofree UP equivalence for `A = 0`. -/
noncomputable def bangCofreeEquiv_zero (C : Comonoid) :
    Hom C.carrier (representable 0) ≃
      ComonoidHom C (bangComonoid 0 (by decide)) where
  toFun _ := bangCofreeLiftZeroComonoidHom C
  invFun f := bangCofreeForgetComonoid 0 (by decide) C f
  left_inv f := hom_to_representable_zero_unique _ _ _
  right_inv f := (bangCofreeLiftZero_unique C f).symm

/-- Alias matching the gate-3 naming for the `A = 0` case of the prospective
`comonoidHomEquiv`. -/
noncomputable def comonoidHomEquiv_zero (C : Comonoid) :=
  bangCofreeEquiv_zero C


/-! ## Cofree UP for `A = 1`

Homogeneous coefficients `φ₀ = ε`, `φₙ₊₁ = λ ∘ (φₙ ⊗ f) ∘ Δ` assemble by
`countableProductLift` into `bang 1`.  The tensor-power law
`(φ_p ⊗ φ_q) ∘ Δ = λ⁻¹ ∘ φ_{p+q}` is proved by induction on `q`.
-/

/-- Day tensor elements are determined by all bilinear evaluations. -/
theorem dayTensor_ext {M N : Module} {n : ℕ}
    {x y : ((dayTensor M N).obj n).Carrier}
    (h : ∀ (L : Module) (β : Bilinear M N L),
      DayCoend.evaluate L β x = DayCoend.evaluate L β y) : x = y :=
  (DayCoend.evaluate_self x).symm.trans
    ((h (dayTensor M N) (DayCoend.intro M N)).trans (DayCoend.evaluate_self y))

/-- Transport `ofEquivalence (finCongr h.symm) ∘ ψ` along `h : d = 1`. -/
theorem ofEquiv_comp_eq_rec {n d : ℕ} (hd : d = 1)
    (ψ : Superoperator n 1) :
    Superoperator.comp
        (Superoperator.ofEquivalence (finCongr hd.symm))
        ψ =
      hd.symm ▸ ψ := by
  subst hd
  change Superoperator.comp
      (Superoperator.ofEquivalence (finCongr (Eq.symm rfl))) ψ =
    (Eq.symm (rfl : (1:ℕ)=1)) ▸ ψ
  have he : finCongr (Eq.symm (rfl : (1:ℕ)=1)) = Equiv.refl (Fin 1) := by
    apply Equiv.ext; intro; apply Fin.ext; rfl
  rw [he, Superoperator.ofEquivalence_refl, Superoperator.identity_comp]

theorem ofEquiv_comp_tpd {n k : ℕ} (ψ : Superoperator n 1) :
    Superoperator.comp
        (Superoperator.ofEquivalence
          (finCongr (tensorPowerDimension_one_eq k).symm))
        ψ =
      (tensorPowerDimension_one_eq k).symm ▸ ψ :=
  ofEquiv_comp_eq_rec (tensorPowerDimension_one_eq k) ψ

/-!
`PartialCountableSum` axioms (empty / singleton / remove_zero / reindex /
flatten) do **not** give free finite HasSum of arbitrary multi-term families:
flatten only regroups.  `Fiber.hasSum_singleAt` covers one-supported families.
Thus the finite inner sum over `p+q=k` is **not** automatic for a general
`Module` fiber — A≥2 `BangDegreeUnitRectangleHasSum` remains blocked without
additional structure.  The candidate `Module.act_sum_from_dim` (joint action
at fiber `A^k`) is **unsound** for representable/TNI modules when `d ≥ 2`;
`act_sum_tensor_from_one` and `CPMapSum.comp_from_dim` do not close the gap.
-/

/-- Precompose a bilinear map along a pair of module morphisms. -/
noncomputable def Bilinear.precomp
    {M M' N N' L : Module}
    (β : Bilinear M' N' L) (f : Hom M M') (g : Hom N N') :
    Bilinear M N L where
  app := fun x y => β.app (f.app _ x) (g.app _ y)
  map_zero_left := by
    intro m n y
    rw [f.map_zero, β.map_zero_left]
  map_zero_right := by
    intro m n x
    rw [g.map_zero, β.map_zero_right]
  map_sum_left := by
    intro ι _ m n xs s y h
    exact β.map_sum_left (g.app _ y) (f.map_sum h)
  map_sum_right := by
    intro ι _ m n x ys s h
    exact β.map_sum_right (f.app _ x) (g.map_sum h)
  naturality := by
    intro m' m n' n x y p q
    rw [f.naturality, g.naturality, β.naturality]

theorem DayTensor.evaluate_map {M M' N N' L : Module}
    (β : Bilinear M' N' L) (f : Hom M M') (g : Hom N N')
    {n : ℕ} (z : ((dayTensor M N).obj n).Carrier) :
    DayCoend.evaluate L β ((DayTensor.map f g).app n z) =
      DayCoend.evaluate L (Bilinear.precomp β f g) z := by
  have h :
      Hom.comp (DayCoend.lift β) (DayTensor.map f g) =
        DayCoend.lift (Bilinear.precomp β f g) := by
    apply DayTensor.hom_ext
    intro m k x y
    simp only [Hom.comp_app, DayTensor.map_intro]
    change DayCoend.evaluate L β
        ((DayCoend.intro M' N').app (f.app m x) (g.app k y)) =
      DayCoend.evaluate L (Bilinear.precomp β f g)
        ((DayCoend.intro M N).app x y)
    rw [DayCoend.evaluate_intro, DayCoend.evaluate_intro]
    rfl
  exact congrArg (fun η : Hom (dayTensor M N) L => η.app n z) h

theorem DayCoend.raw_value_hasSum_bilinear
    {M N L : Module} {n : ℕ} {ι : Type} [Countable ι]
    (βs : ι → Bilinear M N L) (γ : Bilinear M N L)
    (hpt : ∀ {m k : ℕ} (x : (M.obj m).Carrier) (y : (N.obj k).Carrier),
      (L.obj (m * k)).HasSum (fun i => (βs i).app x y) (γ.app x y))
    (t : DayCoend.Raw M N n) (ht : t.Admissible) (hh : t.Hereditary) :
    (L.obj n).HasSum
      (fun i => DayCoend.Raw.value t ht L (βs i))
      (DayCoend.Raw.value t ht L γ) := by
  induction t with
  | zero =>
    have h0 : DayCoend.Raw.value (.zero : DayCoend.Raw M N n) ht L γ = 0 :=
      (DayCoend.Raw.eval_unique _ ht L γ DayCoend.Raw.Eval.zero).symm
    have hi (i : ι) :
        DayCoend.Raw.value (.zero : DayCoend.Raw M N n) ht L (βs i) = 0 :=
      (DayCoend.Raw.eval_unique _ ht L (βs i) DayCoend.Raw.Eval.zero).symm
    have hfun :
        (fun i => DayCoend.Raw.value (.zero : DayCoend.Raw M N n) ht L (βs i)) =
          fun _ => (0 : (L.obj n).Carrier) := funext hi
    rw [h0, hfun]
    exact Fiber.hasSum_zero (L.obj n)
  | generator x y f =>
    have hγ : DayCoend.Raw.value (.generator x y f) ht L γ =
        L.act (γ.app x y) f :=
      (DayCoend.Raw.eval_unique _ ht L γ (DayCoend.Raw.Eval.generator x y f)).symm
    have hi (i : ι) :
        DayCoend.Raw.value (.generator x y f) ht L (βs i) =
          L.act ((βs i).app x y) f :=
      (DayCoend.Raw.eval_unique _ ht L (βs i)
        (DayCoend.Raw.Eval.generator x y f)).symm
    have hfun :
        (fun i => DayCoend.Raw.value (.generator x y f) ht L (βs i)) =
          fun i => L.act ((βs i).app x y) f := funext hi
    rw [hγ, hfun]
    exact L.act_sum_element f (hpt x y)
  | sum f ih =>
    have hγeval := DayCoend.Raw.eval_value (.sum f) ht L γ
    obtain ⟨vγ, hvγ, hsγ⟩ := DayCoend.Raw.eval_sum_cases γ f hγeval
    have hγval : vγ = fun j =>
        DayCoend.Raw.value (f j) (hh j).2 L γ := by
      funext j
      exact DayCoend.Raw.eval_unique (f j) (hh j).2 L γ (hvγ j)
    have hsumγ :
        (L.obj n).HasSum
          (fun j => DayCoend.Raw.value (f j) (hh j).2 L γ)
          (DayCoend.Raw.value (.sum f) ht L γ) := by
      rwa [hγval] at hsγ
    have hrow (j : ℕ) :
        (L.obj n).HasSum
          (fun i => DayCoend.Raw.value (f j) (hh j).2 L (βs i))
          (DayCoend.Raw.value (f j) (hh j).2 L γ) :=
      ih j (hh j).2 (hh j).1
    let φ : ℕ → ι → (L.obj n).Carrier :=
      fun j i => DayCoend.Raw.value (f j) (hh j).2 L (βs i)
    have hflat :
        (L.obj n).HasSum
          (fun p : Σ _ : ℕ, ι => φ p.1 p.2)
          (DayCoend.Raw.value (.sum f) ht L γ) :=
      ((L.obj n).summation.flatten φ
        (DayCoend.Raw.value (.sum f) ht L γ)).mpr
        ⟨fun j => DayCoend.Raw.value (f j) (hh j).2 L γ, hrow, hsumγ⟩
    have hswap :
        (L.obj n).HasSum
          (fun p : Σ _ : ι, ℕ => φ p.2 p.1)
          (DayCoend.Raw.value (.sum f) ht L γ) :=
      ((L.obj n).summation.reindex (sigmaSwapEquiv ι ℕ)
        (fun p : Σ _ : ℕ, ι => φ p.1 p.2)
        (DayCoend.Raw.value (.sum f) ht L γ)).mpr hflat
    obtain ⟨g, hrows, hsumg⟩ :=
      ((L.obj n).summation.flatten
        (fun i j => φ j i)
        (DayCoend.Raw.value (.sum f) ht L γ)).mp hswap
    have hg : g = fun i => DayCoend.Raw.value (.sum f) ht L (βs i) := by
      funext i
      have he := DayCoend.Raw.eval_value (.sum f) ht L (βs i)
      obtain ⟨vi, hvi, hsi⟩ := DayCoend.Raw.eval_sum_cases (βs i) f he
      have : vi = fun j => DayCoend.Raw.value (f j) (hh j).2 L (βs i) := by
        funext j
        exact DayCoend.Raw.eval_unique (f j) (hh j).2 L (βs i) (hvi j)
      have : (L.obj n).HasSum
          (fun j => DayCoend.Raw.value (f j) (hh j).2 L (βs i))
          (DayCoend.Raw.value (.sum f) ht L (βs i)) := by
        rwa [this] at hsi
      exact (L.obj n).summation.unique (hrows i) this
    rwa [hg] at hsumg

theorem DayCoend.evaluate_hasSum_bilinear
    {M N L : Module} {n : ℕ} {ι : Type} [Countable ι]
    (βs : ι → Bilinear M N L) (γ : Bilinear M N L)
    (hpt : ∀ {m k : ℕ} (x : (M.obj m).Carrier) (y : (N.obj k).Carrier),
      (L.obj (m * k)).HasSum (fun i => (βs i).app x y) (γ.app x y))
    (z : DayCoend.Carrier M N n) :
    (L.obj n).HasSum
      (fun i => DayCoend.evaluate L (βs i) z)
      (DayCoend.evaluate L γ z) := by
  induction z using Quotient.inductionOn with
  | _ t =>
    change (L.obj n).HasSum
      (fun i => DayCoend.Term.value t L (βs i))
      (DayCoend.Term.value t L γ)
    exact DayCoend.raw_value_hasSum_bilinear βs γ hpt t.1 t.2.1 t.2.2


theorem tensorRightUnitorInv_one :
    Superoperator.tensorRightUnitorInv 1 =
      Superoperator.identity (1 * 1) := by
  change Superoperator.ofEquivalence
      (Superoperator.tensorRightUnitorEquiv 1).symm =
    Superoperator.identity (1 * 1)
  have h :
      Superoperator.tensorRightUnitorEquiv 1 =
        Equiv.refl (Fin (1 * 1)) := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    exact (fin_val_eq_zero_of_card_one (rfl : 1 * 1 = 1)
        (Superoperator.tensorRightUnitorEquiv 1 i)).trans
      (fin_val_eq_zero_of_card_one (rfl : 1 * 1 = 1)
        ((Equiv.refl (Fin (1 * 1))) i)).symm
  rw [h, Equiv.refl_symm, Superoperator.ofEquivalence_refl]

theorem leftUnitorInv_unit_eq_rightUnitorInv_unit :
    DayTensor.leftUnitorInv dayTensorUnit =
      DayTensor.rightUnitorInv dayTensorUnit := by
  apply Hom.ext
  intro n x
  change
    (dayTensor dayTensorUnit dayTensorUnit).act
      ((DayCoend.intro dayTensorUnit dayTensorUnit).app
        (Superoperator.identity 1) x)
      (Superoperator.tensorLeftUnitorInv n) =
    (dayTensor dayTensorUnit dayTensorUnit).act
      ((DayCoend.intro dayTensorUnit dayTensorUnit).app
        x (Superoperator.identity 1))
      (Superoperator.tensorRightUnitorInv n)
  have hid1 : dayTensorUnit.act (Superoperator.identity 1) (Superoperator.identity 1) =
      (Superoperator.identity 1 : (dayTensorUnit.obj 1).Carrier) :=
    dayTensorUnit.act_id _
  have hx : dayTensorUnit.act (Superoperator.identity 1) x = x := by
    change Superoperator.comp (Superoperator.identity 1) x = x
    exact Superoperator.identity_comp x
  have hL :
      (DayCoend.intro dayTensorUnit dayTensorUnit).app
        (Superoperator.identity 1) x =
      (dayTensor dayTensorUnit dayTensorUnit).act
        ((DayCoend.intro dayTensorUnit dayTensorUnit).app
          (Superoperator.identity 1) (Superoperator.identity 1))
        (Superoperator.tensor (Superoperator.identity 1) x) := by
    have h := (DayCoend.intro dayTensorUnit dayTensorUnit).naturality
      (Superoperator.identity 1) (Superoperator.identity 1)
      (Superoperator.identity 1) x
    simpa [hid1, hx] using h
  have hR :
      (DayCoend.intro dayTensorUnit dayTensorUnit).app
        x (Superoperator.identity 1) =
      (dayTensor dayTensorUnit dayTensorUnit).act
        ((DayCoend.intro dayTensorUnit dayTensorUnit).app
          (Superoperator.identity 1) (Superoperator.identity 1))
        (Superoperator.tensor x (Superoperator.identity 1)) := by
    have h := (DayCoend.intro dayTensorUnit dayTensorUnit).naturality
      (Superoperator.identity 1) (Superoperator.identity 1)
      x (Superoperator.identity 1)
    simpa [hid1, hx] using h
  rw [hL, hR, (dayTensor dayTensorUnit dayTensorUnit).act_comp,
    (dayTensor dayTensorUnit dayTensorUnit).act_comp]
  have hEq :
      Superoperator.comp
          (Superoperator.tensor (Superoperator.identity 1) x)
          (Superoperator.tensorLeftUnitorInv n) =
        Superoperator.comp
          (Superoperator.tensor x (Superoperator.identity 1))
          (Superoperator.tensorRightUnitorInv n) := by
    rw [Superoperator.tensorLeftUnitorInv_naturality x,
      Superoperator.tensorRightUnitorInv_naturality x,
      tensorLeftUnitorInv_one, tensorRightUnitorInv_one]
  exact congrArg
    ((dayTensor dayTensorUnit dayTensorUnit).act
      ((DayCoend.intro dayTensorUnit dayTensorUnit).app
        (Superoperator.identity 1) (Superoperator.identity 1)))
    hEq

theorem leftUnitor_unit_eq_rightUnitor_unit :
    DayTensor.leftUnitor dayTensorUnit =
      DayTensor.rightUnitor dayTensorUnit := by
  have hinv := leftUnitorInv_unit_eq_rightUnitorInv_unit
  -- λ ∘ λ⁻¹ = ρ ∘ λ⁻¹, then cancel λ⁻¹ by composing with λ on the right
  have hcomp :
      Hom.comp (DayTensor.leftUnitor dayTensorUnit)
          (DayTensor.leftUnitorInv dayTensorUnit) =
        Hom.comp (DayTensor.rightUnitor dayTensorUnit)
          (DayTensor.leftUnitorInv dayTensorUnit) := by
    have hl := (DayTensor.leftUnitorIso dayTensorUnit).hom_inv
    have hr := (DayTensor.rightUnitorIso dayTensorUnit).hom_inv
    -- λ∘λ⁻¹ = id = ρ∘ρ⁻¹ = ρ∘λ⁻¹
    refine Eq.trans hl ?_
    refine Eq.trans hr.symm ?_
    exact congrArg (Hom.comp (DayTensor.rightUnitor dayTensorUnit)) hinv.symm
  -- compose both sides on the right with λ
  have h := congrArg (fun g => Hom.comp g (DayTensor.leftUnitor dayTensorUnit)) hcomp
  -- (λ∘λ⁻¹)∘λ = (ρ∘λ⁻¹)∘λ
  have hL : Hom.comp
      (Hom.comp (DayTensor.leftUnitor dayTensorUnit)
        (DayTensor.leftUnitorInv dayTensorUnit))
      (DayTensor.leftUnitor dayTensorUnit) =
      DayTensor.leftUnitor dayTensorUnit := by
    have hl := (DayTensor.leftUnitorIso dayTensorUnit).hom_inv
    refine Eq.trans (congrArg (fun g => Hom.comp g
        (DayTensor.leftUnitor dayTensorUnit)) hl) ?_
    exact Hom.id_comp _
  have hR : Hom.comp
      (Hom.comp (DayTensor.rightUnitor dayTensorUnit)
        (DayTensor.leftUnitorInv dayTensorUnit))
      (DayTensor.leftUnitor dayTensorUnit) =
      DayTensor.rightUnitor dayTensorUnit := by
    -- (ρ ∘ λ⁻¹) ∘ λ = ρ ∘ (λ⁻¹ ∘ λ) = ρ ∘ id = ρ
    refine Eq.trans (by ext; rfl) ?_
    refine Eq.trans (congrArg (Hom.comp (DayTensor.rightUnitor dayTensorUnit))
      (DayTensor.leftUnitorIso dayTensorUnit).inv_hom) ?_
    exact Hom.comp_id _
  exact Eq.trans hL.symm (Eq.trans h hR)

/-- Coherence: (id ⊗ λ) ∘ α ∘ (λ⁻¹ ⊗ id) = id on I⊗I. -/
theorem leftUnitor_associator_coherence :
    Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor dayTensorUnit))
      (Hom.comp (DayTensor.associator dayTensorUnit dayTensorUnit dayTensorUnit)
        (DayTensor.map (DayTensor.leftUnitorInv dayTensorUnit) (Hom.id dayTensorUnit))) =
      Hom.id (dayTensor dayTensorUnit dayTensorUnit) := by
  -- triangle: map(id,λ)∘α = map(ρ,id)
  have htri := DayTensor.triangle dayTensorUnit dayTensorUnit
  refine Eq.trans (congrArg (fun g => Hom.comp g
      (DayTensor.map (DayTensor.leftUnitorInv dayTensorUnit)
        (Hom.id dayTensorUnit))) htri) ?_
  -- map(ρ,id) ∘ map(λ⁻¹,id) = map(ρ∘λ⁻¹, id)
  have hmap := DayTensor.map_comp (DayTensor.rightUnitor dayTensorUnit)
      (DayTensor.leftUnitorInv dayTensorUnit)
      (Hom.id dayTensorUnit) (Hom.id dayTensorUnit)
  refine Eq.trans hmap.symm ?_
  -- ρ ∘ λ⁻¹ = ρ ∘ ρ⁻¹ = id (using λ⁻¹=ρ⁻¹)
  have hcancel :
      Hom.comp (DayTensor.rightUnitor dayTensorUnit)
          (DayTensor.leftUnitorInv dayTensorUnit) =
        Hom.id dayTensorUnit := by
    rw [leftUnitorInv_unit_eq_rightUnitorInv_unit]
    exact (DayTensor.rightUnitorIso dayTensorUnit).hom_inv
  refine Eq.trans (congrArg (fun g => DayTensor.map g (Hom.comp (Hom.id dayTensorUnit) (Hom.id dayTensorUnit)))
      hcancel) ?_
  simp only [Hom.id_comp, DayTensor.map_id]

theorem comonoid_map_id_counit_comult (C : Comonoid) :
    Hom.comp (DayTensor.map (Hom.id C.carrier) C.counit) C.comult =
      DayTensor.rightUnitorInv C.carrier := by
  have hinv := (DayTensor.rightUnitorIso C.carrier).inv_hom
  have h := C.right_counit
  refine Eq.trans ?_ (Eq.trans (congrArg
    (fun g => Hom.comp (DayTensor.rightUnitorInv C.carrier) g) h)
    (Hom.comp_id _))
  refine Eq.trans (Eq.symm (Hom.id_comp _)) ?_
  refine Eq.trans (congrArg (fun g => Hom.comp g
    (Hom.comp (DayTensor.map (Hom.id C.carrier) C.counit) C.comult))
    hinv.symm) ?_
  ext n x; rfl

theorem rightUnitor_natural {M N : Module} (f : Hom M N) :
    Hom.comp (DayTensor.rightUnitor N)
        (DayTensor.map f (Hom.id dayTensorUnit)) =
      Hom.comp f (DayTensor.rightUnitor M) := by
  apply DayTensor.hom_ext
  intro m n x y
  simp only [DayTensor.map_intro, Hom.comp_app, Hom.id_app]
  have hL := DayTensor.rightUnitor_intro (M := N) (f.app m x) y
  have hR := DayTensor.rightUnitor_intro (M := M) x y
  change
    (DayTensor.rightUnitor N).app (m * n)
        ((DayCoend.intro N dayTensorUnit).app (f.app m x) y) =
      f.app (m * n)
        ((DayTensor.rightUnitor M).app (m * n)
          ((DayCoend.intro M dayTensorUnit).app x y))
  rw [hL, hR, f.naturality]

theorem rightUnitorInv_natural {M N : Module} (f : Hom M N) :
    Hom.comp (DayTensor.map f (Hom.id dayTensorUnit))
        (DayTensor.rightUnitorInv M) =
      Hom.comp (DayTensor.rightUnitorInv N) f := by
  have hcancel :
      Hom.comp (DayTensor.rightUnitor N)
          (Hom.comp (DayTensor.map f (Hom.id dayTensorUnit))
            (DayTensor.rightUnitorInv M)) =
        f := by
    refine Eq.trans ?_ (Hom.comp_id f)
    refine Eq.trans ?_
      (congrArg (fun g => Hom.comp f g)
        (DayTensor.rightUnitorIso M).hom_inv)
    have hnat := rightUnitor_natural f
    refine Eq.trans (Eq.symm (by ext; rfl :
        Hom.comp (DayTensor.rightUnitor N)
            (Hom.comp (DayTensor.map f (Hom.id dayTensorUnit))
              (DayTensor.rightUnitorInv M)) =
          Hom.comp
            (Hom.comp (DayTensor.rightUnitor N)
              (DayTensor.map f (Hom.id dayTensorUnit)))
            (DayTensor.rightUnitorInv M))) ?_
    refine Eq.trans (congrArg (fun g => Hom.comp g
        (DayTensor.rightUnitorInv M)) hnat) ?_
    ext; rfl
  refine Eq.trans ?_ (congrArg
    (fun g => Hom.comp (DayTensor.rightUnitorInv N) g) hcancel)
  have hinv := (DayTensor.rightUnitorIso N).inv_hom
  refine Eq.trans (Eq.symm (Hom.id_comp _)) ?_
  refine Eq.trans (congrArg (fun g => Hom.comp g
      (Hom.comp (DayTensor.map f (Hom.id dayTensorUnit))
        (DayTensor.rightUnitorInv M))) hinv.symm) ?_
  ext; rfl

noncomputable def bangCofreeCoeffOne (C : Comonoid)
    (f : Hom C.carrier dayTensorUnit) :
    ℕ → Hom C.carrier dayTensorUnit
  | 0 => C.counit
  | n + 1 =>
      Hom.comp (DayTensor.leftUnitor dayTensorUnit)
        (Hom.comp (DayTensor.map (bangCofreeCoeffOne C f n) f) C.comult)

theorem bangCofreeCoeffOne_one (C : Comonoid)
    (f : Hom C.carrier dayTensorUnit) :
    bangCofreeCoeffOne C f 1 = f := by
  change Hom.comp (DayTensor.leftUnitor dayTensorUnit)
      (Hom.comp (DayTensor.map C.counit f) C.comult) = f
  have hfactor :
      DayTensor.map C.counit f =
        Hom.comp (DayTensor.map (Hom.id dayTensorUnit) f)
          (DayTensor.map C.counit (Hom.id C.carrier)) := by
    have h := DayTensor.map_comp (Hom.id dayTensorUnit) C.counit
      f (Hom.id C.carrier)
    simp only [Hom.id_comp, Hom.comp_id] at h
    exact h
  have hleft := comonoid_map_counit_id_comult C
  refine Eq.trans (congrArg (fun g => Hom.comp (DayTensor.leftUnitor dayTensorUnit)
      (Hom.comp g C.comult)) hfactor) ?_
  refine Eq.trans (by ext; rfl :
      Hom.comp (DayTensor.leftUnitor dayTensorUnit)
          (Hom.comp
            (Hom.comp (DayTensor.map (Hom.id dayTensorUnit) f)
              (DayTensor.map C.counit (Hom.id C.carrier)))
            C.comult) =
        Hom.comp (DayTensor.leftUnitor dayTensorUnit)
          (Hom.comp (DayTensor.map (Hom.id dayTensorUnit) f)
            (Hom.comp (DayTensor.map C.counit (Hom.id C.carrier))
              C.comult))) ?_
  rw [hleft]
  have hnatU := leftUnitor_natural f
  refine Eq.trans (by ext; rfl :
      Hom.comp (DayTensor.leftUnitor dayTensorUnit)
          (Hom.comp (DayTensor.map (Hom.id dayTensorUnit) f)
            (DayTensor.leftUnitorInv C.carrier)) =
        Hom.comp
          (Hom.comp (DayTensor.leftUnitor dayTensorUnit)
            (DayTensor.map (Hom.id dayTensorUnit) f))
          (DayTensor.leftUnitorInv C.carrier)) ?_
  refine Eq.trans (congrArg (fun g => Hom.comp g
      (DayTensor.leftUnitorInv C.carrier)) hnatU) ?_
  refine Eq.trans (by ext; rfl :
      Hom.comp (Hom.comp f (DayTensor.leftUnitor C.carrier))
          (DayTensor.leftUnitorInv C.carrier) =
        Hom.comp f (Hom.comp (DayTensor.leftUnitor C.carrier)
          (DayTensor.leftUnitorInv C.carrier))) ?_
  refine Eq.trans (congrArg (Hom.comp f)
      (DayTensor.leftUnitorIso C.carrier).hom_inv) ?_
  exact Hom.comp_id f

theorem bangCofreeCoeffOne_comult (C : Comonoid)
    (f : Hom C.carrier dayTensorUnit) (p q : ℕ) :
    Hom.comp
        (DayTensor.map (bangCofreeCoeffOne C f p) (bangCofreeCoeffOne C f q))
        C.comult =
      Hom.comp (DayTensor.leftUnitorInv dayTensorUnit)
        (bangCofreeCoeffOne C f (p + q)) := by
  induction q generalizing p with
  | zero =>
    change Hom.comp (DayTensor.map (bangCofreeCoeffOne C f p) C.counit) C.comult =
      Hom.comp (DayTensor.leftUnitorInv dayTensorUnit) (bangCofreeCoeffOne C f (p + 0))
    rw [Nat.add_zero]
    have hfactor :
        DayTensor.map (bangCofreeCoeffOne C f p) C.counit =
          Hom.comp (DayTensor.map (bangCofreeCoeffOne C f p) (Hom.id dayTensorUnit))
            (DayTensor.map (Hom.id C.carrier) C.counit) := by
      have h := DayTensor.map_comp (bangCofreeCoeffOne C f p) (Hom.id C.carrier)
        (Hom.id dayTensorUnit) C.counit
      simp only [Hom.comp_id, Hom.id_comp] at h
      exact h
    refine Eq.trans (congrArg (fun g => Hom.comp g C.comult) hfactor) ?_
    refine Eq.trans (by ext; rfl :
        Hom.comp
            (Hom.comp (DayTensor.map (bangCofreeCoeffOne C f p) (Hom.id dayTensorUnit))
              (DayTensor.map (Hom.id C.carrier) C.counit))
            C.comult =
          Hom.comp (DayTensor.map (bangCofreeCoeffOne C f p) (Hom.id dayTensorUnit))
            (Hom.comp (DayTensor.map (Hom.id C.carrier) C.counit) C.comult)) ?_
    rw [comonoid_map_id_counit_comult C]
    refine Eq.trans (rightUnitorInv_natural (bangCofreeCoeffOne C f p)) ?_
    exact congrArg (fun g => Hom.comp g (bangCofreeCoeffOne C f p))
      leftUnitorInv_unit_eq_rightUnitorInv_unit.symm
  | succ q ih =>
    let φ := bangCofreeCoeffOne C f
    let Δ := C.comult
    -- Unfold φ(q+1)
    have hφq1 : φ (q + 1) =
        Hom.comp (DayTensor.leftUnitor dayTensorUnit)
          (Hom.comp (DayTensor.map (φ q) f) Δ) := rfl
    -- LHS rewrite chain
    have hL :
        Hom.comp (DayTensor.map (φ p) (φ (q + 1))) Δ =
          Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor dayTensorUnit))
            (Hom.comp (DayTensor.associator dayTensorUnit dayTensorUnit dayTensorUnit)
              (Hom.comp
                (DayTensor.map (DayTensor.leftUnitorInv dayTensorUnit) (Hom.id dayTensorUnit))
                (Hom.comp (DayTensor.map (φ (p + q)) f) Δ))) := by
      -- Step through the calculation
      rw [hφq1]
      -- map(φp, λ ∘ mid) = map(id,λ) ∘ map(φp, mid)
      have hf1 :
          DayTensor.map (φ p)
              (Hom.comp (DayTensor.leftUnitor dayTensorUnit)
                (Hom.comp (DayTensor.map (φ q) f) Δ)) =
            Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor dayTensorUnit))
              (DayTensor.map (φ p) (Hom.comp (DayTensor.map (φ q) f) Δ)) := by
        have h := DayTensor.map_comp (Hom.id dayTensorUnit) (φ p)
          (DayTensor.leftUnitor dayTensorUnit)
          (Hom.comp (DayTensor.map (φ q) f) Δ)
        simpa only [Hom.id_comp] using h
      refine Eq.trans (congrArg (fun g => Hom.comp g Δ) hf1) ?_
      refine Eq.trans (by ext; rfl) ?_
      -- map(φp, map(φq,f)∘Δ) = map(id, map(φq,f)) ∘ map(φp, Δ)
      have hf2 :
          DayTensor.map (φ p) (Hom.comp (DayTensor.map (φ q) f) Δ) =
            Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.map (φ q) f))
              (DayTensor.map (φ p) Δ) := by
        have h := DayTensor.map_comp (Hom.id dayTensorUnit) (φ p)
          (DayTensor.map (φ q) f) Δ
        simpa only [Hom.id_comp] using h
      refine Eq.trans (congrArg (fun g =>
          Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor dayTensorUnit))
            (Hom.comp g Δ)) hf2) ?_
      refine Eq.trans (by ext; rfl) ?_
      -- map(φp, Δ) = map(φp, id) ∘ map(id, Δ)
      have hf3 :
          DayTensor.map (φ p) Δ =
            Hom.comp (DayTensor.map (φ p) (Hom.id (dayTensor C.carrier C.carrier)))
              (DayTensor.map (Hom.id C.carrier) Δ) := by
        have h := DayTensor.map_comp (φ p) (Hom.id C.carrier)
          (Hom.id (dayTensor C.carrier C.carrier)) Δ
        simpa only [Hom.comp_id, Hom.id_comp] using h
      refine Eq.trans (congrArg (fun g =>
          Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor dayTensorUnit))
            (Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.map (φ q) f))
              (Hom.comp g Δ))) hf3) ?_
      refine Eq.trans (by ext; rfl) ?_
      -- coassoc: map(id,Δ)∘Δ = α ∘ map(Δ,id)∘Δ
      have hco := C.coassociative.symm
      refine Eq.trans (congrArg (fun g =>
          Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor dayTensorUnit))
            (Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.map (φ q) f))
              (Hom.comp (DayTensor.map (φ p) (Hom.id (dayTensor C.carrier C.carrier))) g)))
        hco) ?_
      refine Eq.trans (by ext; rfl) ?_
      -- map(id, map(φq,f)) ∘ map(φp, id) = map(φp, map(φq,f))
      have hf4 :
          Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.map (φ q) f))
              (DayTensor.map (φ p) (Hom.id (dayTensor C.carrier C.carrier))) =
            DayTensor.map (φ p) (DayTensor.map (φ q) f) := by
        have h := DayTensor.map_comp (Hom.id dayTensorUnit) (φ p)
          (DayTensor.map (φ q) f) (Hom.id (dayTensor C.carrier C.carrier))
        simpa only [Hom.comp_id, Hom.id_comp] using h.symm
      -- Reassociate to apply hf4 before α
      refine Eq.trans (by ext; rfl :
          Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor dayTensorUnit))
              (Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.map (φ q) f))
                (Hom.comp (DayTensor.map (φ p) (Hom.id (dayTensor C.carrier C.carrier)))
                  (Hom.comp (DayTensor.associator C.carrier C.carrier C.carrier)
                    (Hom.comp (DayTensor.map Δ (Hom.id C.carrier)) Δ)))) =
            Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor dayTensorUnit))
              (Hom.comp
                (Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.map (φ q) f))
                  (DayTensor.map (φ p) (Hom.id (dayTensor C.carrier C.carrier))))
                (Hom.comp (DayTensor.associator C.carrier C.carrier C.carrier)
                  (Hom.comp (DayTensor.map Δ (Hom.id C.carrier)) Δ)))) ?_
      refine Eq.trans (congrArg (fun g =>
          Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor dayTensorUnit))
            (Hom.comp g
              (Hom.comp (DayTensor.associator C.carrier C.carrier C.carrier)
                (Hom.comp (DayTensor.map Δ (Hom.id C.carrier)) Δ)))) hf4) ?_
      -- associator naturality: map(φp, map(φq,f)) ∘ α = α' ∘ map(map(φp,φq), f)
      have hnat := DayTensor.associator_naturality (φ p) (φ q) f
      -- hnat: α' ∘ map(map φp φq, f) = map(φp, map(φq,f)) ∘ α
      -- so map(φp, map(φq,f)) ∘ α = α' ∘ map(map(φp,φq), f)
      refine Eq.trans (by ext; rfl :
          Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor dayTensorUnit))
              (Hom.comp (DayTensor.map (φ p) (DayTensor.map (φ q) f))
                (Hom.comp (DayTensor.associator C.carrier C.carrier C.carrier)
                  (Hom.comp (DayTensor.map Δ (Hom.id C.carrier)) Δ))) =
            Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor dayTensorUnit))
              (Hom.comp
                (Hom.comp (DayTensor.map (φ p) (DayTensor.map (φ q) f))
                  (DayTensor.associator C.carrier C.carrier C.carrier))
                (Hom.comp (DayTensor.map Δ (Hom.id C.carrier)) Δ))) ?_
      refine Eq.trans (congrArg (fun g =>
          Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor dayTensorUnit))
            (Hom.comp g (Hom.comp (DayTensor.map Δ (Hom.id C.carrier)) Δ)))
        hnat.symm) ?_
      refine Eq.trans (by ext; rfl) ?_
      -- map(map(φp,φq), f) ∘ map(Δ, id) = map(map(φp,φq)∘Δ, f)
      have hf5 :
          Hom.comp (DayTensor.map (DayTensor.map (φ p) (φ q)) f)
              (DayTensor.map Δ (Hom.id C.carrier)) =
            DayTensor.map (Hom.comp (DayTensor.map (φ p) (φ q)) Δ) f := by
        have h := DayTensor.map_comp (DayTensor.map (φ p) (φ q)) Δ
          f (Hom.id C.carrier)
        simpa only [Hom.comp_id] using h.symm
      refine Eq.trans (congrArg (fun g =>
          Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor dayTensorUnit))
            (Hom.comp (DayTensor.associator dayTensorUnit dayTensorUnit dayTensorUnit)
              (Hom.comp g Δ))) hf5) ?_
      -- IH: map(φp,φq)∘Δ = λ⁻¹ ∘ φ(p+q)
      have hih := ih p
      -- hih: map(φp, φq)∘Δ = λ⁻¹ ∘ φ(p+q)
      refine Eq.trans (congrArg (fun g =>
          Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor dayTensorUnit))
            (Hom.comp (DayTensor.associator dayTensorUnit dayTensorUnit dayTensorUnit)
              (Hom.comp (DayTensor.map g f) Δ))) hih) ?_
      -- map(λ⁻¹ ∘ φ(p+q), f) = map(λ⁻¹, id) ∘ map(φ(p+q), f)
      have hf6 :
          DayTensor.map
              (Hom.comp (DayTensor.leftUnitorInv dayTensorUnit) (φ (p + q))) f =
            Hom.comp
              (DayTensor.map (DayTensor.leftUnitorInv dayTensorUnit) (Hom.id dayTensorUnit))
              (DayTensor.map (φ (p + q)) f) := by
        have h := DayTensor.map_comp (DayTensor.leftUnitorInv dayTensorUnit) (φ (p + q))
          (Hom.id dayTensorUnit) f
        simpa only [Hom.id_comp] using h
      refine Eq.trans (congrArg (fun g =>
          Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor dayTensorUnit))
            (Hom.comp (DayTensor.associator dayTensorUnit dayTensorUnit dayTensorUnit)
              (Hom.comp g Δ))) hf6) ?_
      ext; rfl
    -- Now apply coherence to collapse (id⊗λ)∘α∘(λ⁻¹⊗id)
    have hcoh := leftUnitor_associator_coherence
    have hL2 :
        Hom.comp (DayTensor.map (φ p) (φ (q + 1))) Δ =
          Hom.comp (DayTensor.map (φ (p + q)) f) Δ := by
      refine Eq.trans hL ?_
      refine Eq.trans (by ext; rfl :
          Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor dayTensorUnit))
              (Hom.comp (DayTensor.associator dayTensorUnit dayTensorUnit dayTensorUnit)
                (Hom.comp
                  (DayTensor.map (DayTensor.leftUnitorInv dayTensorUnit) (Hom.id dayTensorUnit))
                  (Hom.comp (DayTensor.map (φ (p + q)) f) Δ))) =
            Hom.comp
              (Hom.comp (DayTensor.map (Hom.id dayTensorUnit) (DayTensor.leftUnitor dayTensorUnit))
                (Hom.comp (DayTensor.associator dayTensorUnit dayTensorUnit dayTensorUnit)
                  (DayTensor.map (DayTensor.leftUnitorInv dayTensorUnit) (Hom.id dayTensorUnit))))
              (Hom.comp (DayTensor.map (φ (p + q)) f) Δ)) ?_
      refine Eq.trans (congrArg (fun g => Hom.comp g
          (Hom.comp (DayTensor.map (φ (p + q)) f) Δ)) hcoh) ?_
      exact Hom.id_comp _
    -- RHS: λ⁻¹ ∘ φ(p+q+1) = λ⁻¹ ∘ λ ∘ map(φ(p+q), f) ∘ Δ = map(φ(p+q), f) ∘ Δ
    have hR :
        Hom.comp (DayTensor.leftUnitorInv dayTensorUnit) (φ (p + (q + 1))) =
          Hom.comp (DayTensor.map (φ (p + q)) f) Δ := by
      have hadd : p + (q + 1) = (p + q) + 1 := by omega
      rw [hadd]
      change Hom.comp (DayTensor.leftUnitorInv dayTensorUnit)
          (Hom.comp (DayTensor.leftUnitor dayTensorUnit)
            (Hom.comp (DayTensor.map (φ (p + q)) f) Δ)) = _
      refine Eq.trans (by ext; rfl) ?_
      refine Eq.trans (congrArg (fun g => Hom.comp g
          (Hom.comp (DayTensor.map (φ (p + q)) f) Δ))
        (DayTensor.leftUnitorIso dayTensorUnit).inv_hom) ?_
      exact Hom.id_comp _
    exact Eq.trans hL2 hR.symm

noncomputable def bangCofreeLiftOne (C : Comonoid)
    (f : Hom C.carrier (representable 1)) :
    Hom C.carrier (bang 1) :=
  countableProductLift (fun j => symmetricPower 1 j)
    (fun k =>
      Hom.comp (symmetricPowerProjection 1 k)
        (Hom.comp
          (yonedaMap
            (Superoperator.ofEquivalence
              (finCongr (tensorPowerDimension_one_eq k).symm)))
          (bangCofreeCoeffOne C f k)))

private theorem ofEquiv_cast_one_zero :
    Superoperator.ofEquivalence
        (finCongr (tensorPowerDimension_one_eq 0).symm) =
      Superoperator.identity 1 := by
  have h := ofEquivalence_dim_one
    (show 1 = 1 from rfl)
    (show tensorPowerDimension 1 0 = 1 from rfl)
    (finCongr (tensorPowerDimension_one_eq 0).symm)
    (Equiv.refl (Fin 1))
  exact h.trans (Superoperator.ofEquivalence_refl 1)

private theorem ofEquiv_cast_one_one_fwd :
    Superoperator.ofEquivalence
        (finCongr (tensorPowerDimension_one 1)) =
      Superoperator.identity 1 := by
  have h := ofEquivalence_dim_one
    (show tensorPowerDimension 1 1 = 1 from rfl)
    (show 1 = 1 from rfl)
    (finCongr (tensorPowerDimension_one 1))
    (Equiv.refl (Fin 1))
  exact h.trans (Superoperator.ofEquivalence_refl 1)

private theorem ofEquiv_cast_one_one_bwd :
    Superoperator.ofEquivalence
        (finCongr (tensorPowerDimension_one_eq 1).symm) =
      Superoperator.identity 1 := by
  have h := ofEquivalence_dim_one
    (show 1 = 1 from rfl)
    (show tensorPowerDimension 1 1 = 1 from rfl)
    (finCongr (tensorPowerDimension_one_eq 1).symm)
    (Equiv.refl (Fin 1))
  exact h.trans (Superoperator.ofEquivalence_refl 1)

theorem bangCofreeLiftOne_preserves_counit (C : Comonoid)
    (f : Hom C.carrier (representable 1)) :
    Hom.comp (bangCounit 1) (bangCofreeLiftOne C f) = C.counit := by
  ext n x
  change
    Superoperator.comp (symmetricAverage 1 0)
      (Superoperator.comp
        (Superoperator.ofEquivalence
          (finCongr (tensorPowerDimension_one_eq 0).symm))
        (C.counit.app n x)) =
      C.counit.app n x
  have havg := symmetricAverage_of_le_one 1 0 (Nat.le_refl 1)
  -- Rewrite both to identity 1 explicitly
  rw [havg, ofEquiv_cast_one_zero]
  -- goal: identity(tpd).comp (identity 1 .comp counit) = counit
  -- tpd = 1 defeq, so identity(tpd) = identity 1
  change Superoperator.comp (Superoperator.identity 1)
      (Superoperator.comp (Superoperator.identity 1)
        (C.counit.app n x)) = C.counit.app n x
  simp only [Superoperator.identity_comp]
  exact Superoperator.identity_comp _

theorem bangCofreeLiftOne_forget (C : Comonoid)
    (f : Hom C.carrier (representable 1)) :
    Hom.comp (bangDereliction 1) (bangCofreeLiftOne C f) = f := by
  ext n x
  change Superoperator.comp
      (Superoperator.ofEquivalence
        (finCongr (tensorPowerDimension_one 1)))
      (Superoperator.comp (symmetricAverage 1 1)
        (Superoperator.comp
          (Superoperator.ofEquivalence
            (finCongr (tensorPowerDimension_one_eq 1).symm))
          ((bangCofreeCoeffOne C f 1).app n x))) =
    f.app n x
  rw [bangCofreeCoeffOne_one, symmetricAverage_of_le_one 1 1 (Nat.le_refl 1),
    ofEquiv_cast_one_one_fwd, ofEquiv_cast_one_one_bwd]
  change Superoperator.comp (Superoperator.identity 1)
      (Superoperator.comp (Superoperator.identity 1)
        (Superoperator.comp (Superoperator.identity 1)
          (f.app n x))) = f.app n x
  simp only [Superoperator.identity_comp]
  exact Superoperator.identity_comp _

theorem bangCofreeLiftOne_val (C : Comonoid)
    (f : Hom C.carrier (representable 1)) (k n : ℕ)
    (x : (C.carrier.obj n).Carrier) :
    (((bangCofreeLiftOne C f).app n x) k).val =
      Superoperator.comp
        (symmetricAverage 1 k)
        (Superoperator.comp
          (Superoperator.ofEquivalence
            (finCongr (tensorPowerDimension_one_eq k).symm))
          ((bangCofreeCoeffOne C f k).app n x)) :=
  rfl

private theorem eq_rec_symm_cancel {α : Sort*} {a b : α} (h : a = b)
    {β : α → Sort*} (x : β b) : h ▸ (h.symm ▸ x) = x := by
  cases h; rfl

/-- Cast alignment: `bangOneCoeff` of the lifted series recovers the
cofree coefficient morphisms. -/
theorem bangOneCoeff_liftOne (C : Comonoid)
    (f : Hom C.carrier (representable 1)) (k n : ℕ)
    (x : (C.carrier.obj n).Carrier) :
    bangOneCoeff n k (((bangCofreeLiftOne C f).app n x) k) =
      (bangCofreeCoeffOne C f k).app n x := by
  dsimp only [bangOneCoeff]
  rw [bangCofreeLiftOne_val, symmetricAverage_of_le_one 1 k (by omega),
    Superoperator.identity_comp]
  have h := ofEquiv_comp_tpd (k := k) ((bangCofreeCoeffOne C f k).app n x)
  refine Eq.trans (congrArg
      (fun ψ : Superoperator n (tensorPowerDimension 1 k) =>
        (tensorPowerDimension_one_eq k) ▸ ψ) h) ?_
  exact eq_rec_symm_cancel (tensorPowerDimension_one_eq k) _

theorem bangComultComponent_liftOne_evaluate (C : Comonoid)
    (f : Hom C.carrier (representable 1)) (p q n : ℕ)
    (x : (C.carrier.obj n).Carrier)
    (L : Module) (β : Bilinear (bang 1) (bang 1) L) :
    DayCoend.evaluate L β
        ((bangComultComponent 1 p q).app n
          ((bangCofreeLiftOne C f).app n x)) =
      L.act (β.app (bangDegreeUnitOne p) (bangDegreeUnitOne q))
        ((bangCofreeCoeffOne C f (p + q)).app n x) := by
  rw [bangComultComponent_evaluate_one, bangOneCoeff_liftOne]

/-! ## Remaining gate-3 obligations -//-! ## A = 1 cofree packaging -/

noncomputable def bangOneCast (k : ℕ) :
    Hom (representable 1) (representable (tensorPowerDimension 1 k)) :=
  yonedaMap
    (Superoperator.ofEquivalence
      (finCongr (tensorPowerDimension_one_eq k).symm))

noncomputable def bangCofreeFactorOne (C : Comonoid)
    (f : Hom C.carrier (representable 1)) (k : ℕ) :
    Hom C.carrier (bang 1) :=
  Hom.comp (representableToBang 1 k)
    (Hom.comp (bangOneCast k) (bangCofreeCoeffOne C f k))

theorem bangOneCoeff_repToBang_cast (k n : ℕ) (Φ : Superoperator n 1) :
    bangOneCoeff n k
        (((representableToBang 1 k).app n ((bangOneCast k).app n Φ)) k) =
      Φ := by
  let Ψ : Superoperator n (tensorPowerDimension 1 k) :=
    (bangOneCast k).app n Φ
  have hslot :
      ((representableToBang 1 k).app n Ψ) k =
        (symmetricPowerProjection 1 k).app n Ψ := by
    change (if h : k = k then
        h.symm ▸ (symmetricPowerProjection 1 k).app n Ψ else 0) = _
    simp only [↓reduceDIte]
  rw [hslot]
  dsimp only [bangOneCoeff]
  have hval :
      ((symmetricPowerProjection 1 k).app n Ψ).val =
        Superoperator.comp (symmetricAverage 1 k) Ψ := rfl
  rw [hval, symmetricAverage_of_le_one 1 k (by omega),
    Superoperator.identity_comp]
  have hΨ : Ψ =
      Superoperator.comp
        (Superoperator.ofEquivalence
          (finCongr (tensorPowerDimension_one_eq k).symm))
        Φ := rfl
  rw [hΨ]
  have h := ofEquiv_comp_tpd (k := k) Φ
  refine Eq.trans (congrArg
      (fun ψ : Superoperator n (tensorPowerDimension 1 k) =>
        (tensorPowerDimension_one_eq k) ▸ ψ) h) ?_
  exact eq_rec_symm_cancel (tensorPowerDimension_one_eq k) Φ

theorem bangDegreeUnitOne_eq_factor (k : ℕ) :
    bangDegreeUnitOne k =
      (representableToBang 1 k).app 1
        ((bangOneCast k).app 1 (Superoperator.identity 1)) := by
  change
    (bangInjection 1 k).app 1 (bangOneDegreeUnits k) =
      (bangInjection 1 k).app 1
        ((symmetricPowerProjection 1 k).app 1
          ((bangOneCast k).app 1 (Superoperator.identity 1)))
  congr 1
  change
    (symmetricPowerProjection 1 k).app 1
        (cast (congrArg (Superoperator 1)
          (tensorPowerDimension_one_eq k).symm)
          (Superoperator.identity 1)) =
      (symmetricPowerProjection 1 k).app 1
        (Superoperator.comp
          (Superoperator.ofEquivalence
            (finCongr (tensorPowerDimension_one_eq k).symm))
          (Superoperator.identity 1))
  congr 1
  rw [Superoperator.comp_identity]
  exact cast_identity_eq_ofEquivalence (tensorPowerDimension_one_eq k).symm

theorem bangComultComponent_comp_cast_evaluate (p q n : ℕ)
    (Φ : Superoperator n 1)
    (L : Module) (β : Bilinear (bang 1) (bang 1) L) :
    DayCoend.evaluate L β
        ((bangComultComponent 1 p q).app n
          ((representableToBang 1 (p + q)).app n
            ((bangOneCast (p + q)).app n Φ))) =
      DayCoend.evaluate L β
        ((DayTensor.map
            (Hom.comp (representableToBang 1 p) (bangOneCast p))
            (Hom.comp (representableToBang 1 q) (bangOneCast q))).app n
          ((DayTensor.leftUnitorInv dayTensorUnit).app n Φ)) := by
  rw [bangComultComponent_evaluate_one, bangOneCoeff_repToBang_cast,
    DayTensor.evaluate_map]
  let fp : Hom (representable 1) (bang 1) :=
    Hom.comp (representableToBang 1 p) (bangOneCast p)
  let fq : Hom (representable 1) (bang 1) :=
    Hom.comp (representableToBang 1 q) (bangOneCast q)
  let γ : Bilinear (representable 1) (representable 1) L :=
    Bilinear.precomp β fp fq
  set id1 : (dayTensorUnit.obj 1).Carrier := Superoperator.identity 1
  set Φ1 : (dayTensorUnit.obj n).Carrier := Φ
  let gen := (DayCoend.intro dayTensorUnit dayTensorUnit).app id1 Φ1
  let U := Superoperator.tensorLeftUnitorInv n
  have heval :
      DayCoend.evaluate L γ ((DayTensor.leftUnitorInv dayTensorUnit).app n Φ1) =
        L.act (DayCoend.evaluate L γ gen) U := by
    change DayCoend.evaluate L γ (DayCoend.action gen U) = _
    exact DayCoend.evaluate_action γ gen U
  change
      L.act (β.app (bangDegreeUnitOne p) (bangDegreeUnitOne q))
          (Φ1 : Superoperator n 1) =
        DayCoend.evaluate L γ
          ((DayTensor.leftUnitorInv dayTensorUnit).app n Φ1)
  rw [heval, DayCoend.evaluate_intro γ id1 Φ1]
  have hnat :
      γ.app id1 Φ1 =
        L.act (γ.app id1 id1)
          (Superoperator.tensor (Superoperator.identity 1) Φ1) := by
    have h := γ.naturality id1 id1 (Superoperator.identity 1) Φ1
    have hid : dayTensorUnit.act id1 (Superoperator.identity 1) = id1 :=
      dayTensorUnit.act_id id1
    have hΦ : dayTensorUnit.act id1 Φ1 = Φ1 := by
      change Superoperator.comp (id1 : Superoperator 1 1) Φ1 = Φ1
      exact Superoperator.identity_comp _
    rw [hid, hΦ] at h; exact h
  rw [hnat, L.act_comp]
  have hcomp :
      Superoperator.comp
          (Superoperator.tensor (Superoperator.identity 1) Φ1) U =
        (Φ1 : Superoperator n 1) := by
    change Superoperator.comp
        (Superoperator.tensor (Superoperator.identity 1) Φ1)
        (Superoperator.tensorLeftUnitorInv n) = Φ1
    rw [Superoperator.tensorLeftUnitorInv_naturality Φ1,
      tensorLeftUnitorInv_one]
    exact Superoperator.identity_comp Φ1
  rw [hcomp]
  change
      L.act (β.app (bangDegreeUnitOne p) (bangDegreeUnitOne q)) Φ1 =
        L.act (β.app (fp.app 1 id1) (fq.app 1 id1)) Φ1
  congr 1; congr 1
  · exact bangDegreeUnitOne_eq_factor p
  · exact bangDegreeUnitOne_eq_factor q

theorem bangComultComponent_comp_cast (p q : ℕ) :
    Hom.comp (bangComultComponent 1 p q)
        (Hom.comp (representableToBang 1 (p + q)) (bangOneCast (p + q))) =
      Hom.comp
        (DayTensor.map
          (Hom.comp (representableToBang 1 p) (bangOneCast p))
          (Hom.comp (representableToBang 1 q) (bangOneCast q)))
        (DayTensor.leftUnitorInv dayTensorUnit) := by
  apply Hom.ext
  intro n Φ
  apply dayTensor_ext
  intro L β
  exact bangComultComponent_comp_cast_evaluate p q n Φ L β

theorem bangComultComponent_comp_liftOne_eq_coeff (C : Comonoid)
    (f : Hom C.carrier (representable 1)) (p q : ℕ) :
    Hom.comp (bangComultComponent 1 p q) (bangCofreeLiftOne C f) =
      Hom.comp (bangComultComponent 1 p q)
        (bangCofreeFactorOne C f (p + q)) := by
  apply Hom.ext
  intro n x
  apply dayTensor_ext
  intro L β
  change
      DayCoend.evaluate L β
          ((bangComultComponent 1 p q).app n
            ((bangCofreeLiftOne C f).app n x)) =
        DayCoend.evaluate L β
          ((bangComultComponent 1 p q).app n
            ((bangCofreeFactorOne C f (p + q)).app n x))
  rw [bangComultComponent_liftOne_evaluate, bangComultComponent_evaluate_one]
  have hcoeff :
      bangOneCoeff n (p + q)
          (((bangCofreeFactorOne C f (p + q)).app n x) (p + q)) =
        (bangCofreeCoeffOne C f (p + q)).app n x :=
    bangOneCoeff_repToBang_cast (p + q) n
      ((bangCofreeCoeffOne C f (p + q)).app n x)
  rw [hcoeff]

theorem bangComultComponent_comp_liftOne (C : Comonoid)
    (f : Hom C.carrier (representable 1)) (p q : ℕ) :
    Hom.comp (bangComultComponent 1 p q) (bangCofreeLiftOne C f) =
      Hom.comp
        (DayTensor.map
          (bangCofreeFactorOne C f p) (bangCofreeFactorOne C f q))
        C.comult := by
  rw [bangComultComponent_comp_liftOne_eq_coeff]
  change Hom.comp (bangComultComponent 1 p q)
      (Hom.comp (representableToBang 1 (p + q))
        (Hom.comp (bangOneCast (p + q)) (bangCofreeCoeffOne C f (p + q)))) = _
  refine Eq.trans (by ext; rfl) ?_
  refine Eq.trans (congrArg (fun g => Hom.comp g (bangCofreeCoeffOne C f (p + q)))
    (bangComultComponent_comp_cast p q)) ?_
  refine Eq.trans (by ext; rfl) ?_
  refine Eq.trans (congrArg
      (Hom.comp (DayTensor.map
        (Hom.comp (representableToBang 1 p) (bangOneCast p))
        (Hom.comp (representableToBang 1 q) (bangOneCast q))))
      (bangCofreeCoeffOne_comult C f p q).symm) ?_
  have hmap := DayTensor.map_comp
    (Hom.comp (representableToBang 1 p) (bangOneCast p))
    (bangCofreeCoeffOne C f p)
    (Hom.comp (representableToBang 1 q) (bangOneCast q))
    (bangCofreeCoeffOne C f q)
  refine Eq.trans (by ext; rfl) ?_
  exact congrArg (fun g => Hom.comp g C.comult) hmap.symm

theorem bangCofreeLiftOne_hasSum_factors (C : Comonoid)
    (f : Hom C.carrier (representable 1)) :
    Hom.HasSum (bangCofreeFactorOne C f) (bangCofreeLiftOne C f) := by
  intro n x
  have hcoord :=
    countableProduct_hasSum_coordinates
      (fun j => symmetricPower 1 j) n ((bangCofreeLiftOne C f).app n x)
  have hfun :
      (fun k => (bangCofreeFactorOne C f k).app n x) =
        (fun k =>
          (bangInjection 1 k).app n
            (((bangCofreeLiftOne C f).app n x) k)) := by
    funext k
    rfl
  rw [hfun]
  exact hcoord

theorem bangCofreeLiftOne_preserves_comult (C : Comonoid)
    (f : Hom C.carrier (representable 1)) :
    Hom.comp bangComult_one (bangCofreeLiftOne C f) =
      Hom.comp
        (DayTensor.map (bangCofreeLiftOne C f) (bangCofreeLiftOne C f))
        C.comult := by
  let lift := bangCofreeLiftOne C f
  let fac := bangCofreeFactorOne C f
  have hfac : Hom.HasSum fac lift := bangCofreeLiftOne_hasSum_factors C f
  apply Hom.ext
  intro n x
  apply dayTensor_ext
  intro L β
  have hsumL :=
    bangComultApp_hasSum 1 bangComultComponentsAdmissible_one n
      (lift.app n x) L β
  have hfun :
      (fun pq : ℕ × ℕ =>
          DayCoend.evaluate L β
            ((bangComultComponent 1 pq.1 pq.2).app n (lift.app n x))) =
        (fun pq : ℕ × ℕ =>
          DayCoend.evaluate L β
            ((DayTensor.map (fac pq.1) (fac pq.2)).app n
              (C.comult.app n x))) := by
    funext pq
    have heq :=
      congrArg (fun η : Hom C.carrier (dayTensor (bang 1) (bang 1)) =>
        η.app n x)
        (bangComultComponent_comp_liftOne C f pq.1 pq.2)
    simpa [Hom.comp_app] using congrArg (DayCoend.evaluate L β) heq
  have hpt {m k : ℕ} (u : (C.carrier.obj m).Carrier)
      (v : (C.carrier.obj k).Carrier) :
      (L.obj (m * k)).HasSum
        (fun pq : ℕ × ℕ =>
          β.app (fac pq.1 |>.app m u) (fac pq.2 |>.app k v))
        (β.app (lift.app m u) (lift.app k v)) := by
    have hU := hfac m u
    have hV := hfac k v
    have hrows (p : ℕ) :
        (L.obj (m * k)).HasSum
          (fun q : ℕ => β.app (fac p |>.app m u) (fac q |>.app k v))
          (β.app (fac p |>.app m u) (lift.app k v)) :=
      β.map_sum_right (fac p |>.app m u) hV
    have hcol :
        (L.obj (m * k)).HasSum
          (fun p : ℕ => β.app (fac p |>.app m u) (lift.app k v))
          (β.app (lift.app m u) (lift.app k v)) :=
      β.map_sum_left (lift.app k v) hU
    have hflat :=
      ((L.obj (m * k)).summation.flatten
        (fun p q => β.app (fac p |>.app m u) (fac q |>.app k v))
        (β.app (lift.app m u) (lift.app k v))).mpr
          ⟨fun p => β.app (fac p |>.app m u) (lift.app k v),
            hrows, hcol⟩
    exact
      ((L.obj (m * k)).summation.reindex (Equiv.sigmaEquivProd ℕ ℕ)
        (fun pq : ℕ × ℕ =>
          β.app (fac pq.1 |>.app m u) (fac pq.2 |>.app k v))
        (β.app (lift.app m u) (lift.app k v))).mp hflat
  have hβs :
      (L.obj n).HasSum
        (fun pq : ℕ × ℕ =>
          DayCoend.evaluate L β
            ((DayTensor.map (fac pq.1) (fac pq.2)).app n
              (C.comult.app n x)))
        (DayCoend.evaluate L β
          ((DayTensor.map lift lift).app n (C.comult.app n x))) := by
    have hpre := DayCoend.evaluate_hasSum_bilinear
      (fun pq : ℕ × ℕ => Bilinear.precomp β (fac pq.1) (fac pq.2))
      (Bilinear.precomp β lift lift)
      (fun {m k} u v => hpt u v)
      (C.comult.app n x)
    convert hpre using 1
    · funext pq
      exact DayTensor.evaluate_map β (fac pq.1) (fac pq.2)
        (C.comult.app n x)
    · exact DayTensor.evaluate_map β lift lift (C.comult.app n x)
  have hsumL' :
      (L.obj n).HasSum
        (fun pq : ℕ × ℕ =>
          DayCoend.evaluate L β
            ((DayTensor.map (fac pq.1) (fac pq.2)).app n
              (C.comult.app n x)))
        (DayCoend.evaluate L β
          (bangComult_one.app n (lift.app n x))) := by
    have h :
        bangComult_one.app n (lift.app n x) =
          bangComultApp 1 bangComultComponentsAdmissible_one n
            (lift.app n x) := rfl
    rw [h]
    convert hsumL using 1
    exact hfun.symm
  exact (L.obj n).summation.unique hsumL' hβs

noncomputable def bangCofreeLiftOneComonoidHom (C : Comonoid)
    (f : Hom C.carrier (representable 1)) :
    ComonoidHom C (bangComonoid 1 (by decide)) where
  hom := bangCofreeLiftOne C f
  preserves_counit := bangCofreeLiftOne_preserves_counit C f
  preserves_comult := by
    change Hom.comp (bangComult_of_le_one 1 (by decide))
        (bangCofreeLiftOne C f) = _
    have h1 : bangComult_of_le_one 1 (by decide) = bangComult_one := rfl
    rw [h1]
    exact bangCofreeLiftOne_preserves_comult C f

/-! ## Uniqueness of the A=1 cofree lift -/

noncomputable def bangOneCoeffHom (k : ℕ) :
    Hom (bang 1) dayTensorUnit where
  app := fun n x => bangOneCoeff n k (x k)
  map_zero := by
    intro n
    dsimp only [bangOneCoeff]
    have hz : ((0 : ((bang 1).obj n).Carrier) k).val =
        (0 : Superoperator n (tensorPowerDimension 1 k)) := rfl
    rw [hz]
    exact (Superoperator.comp_ofEquivalence_finCongr
        (tensorPowerDimension_one_eq k)
        (0 : Superoperator n (tensorPowerDimension 1 k))).symm.trans
      (Superoperator.comp_zero_right _)
  map_sum := by
    intro ι _ n f s hf
    dsimp only [bangOneCoeff]
    have hk : SigmaMon.ChoiSum.HasSum
        (fun i => ((f i) k).val) (s k).val := hf k
    have hcast :=
      SigmaMon.ChoiSum.comp_left
        (Superoperator.ofEquivalence
          (finCongr (tensorPowerDimension_one_eq k))) hk
    have hfun :
        (fun i => (tensorPowerDimension_one_eq k) ▸ ((f i) k).val) =
          (fun i => Superoperator.comp
            (Superoperator.ofEquivalence
              (finCongr (tensorPowerDimension_one_eq k)))
            ((f i) k).val) := by
      funext i
      exact (Superoperator.comp_ofEquivalence_finCongr
        (tensorPowerDimension_one_eq k) ((f i) k).val).symm
    have hs :
        (tensorPowerDimension_one_eq k) ▸ (s k).val =
          Superoperator.comp
            (Superoperator.ofEquivalence
              (finCongr (tensorPowerDimension_one_eq k)))
            (s k).val :=
      (Superoperator.comp_ofEquivalence_finCongr
        (tensorPowerDimension_one_eq k) (s k).val).symm
    rw [hfun, hs]
    exact hcast
  naturality := by
    intro m n x φ
    dsimp only [bangOneCoeff]
    change
        (tensorPowerDimension_one_eq k) ▸
            Superoperator.comp (x k).val φ =
          Superoperator.comp
            ((tensorPowerDimension_one_eq k) ▸ (x k).val) φ
    have hx := Superoperator.comp_ofEquivalence_finCongr
      (tensorPowerDimension_one_eq k) (Superoperator.comp (x k).val φ)
    have hy := congrArg (fun ψ : Superoperator n 1 => Superoperator.comp ψ φ)
      (Superoperator.comp_ofEquivalence_finCongr
        (tensorPowerDimension_one_eq k) (x k).val)
    rw [← hx, ← hy, Superoperator.comp_assoc]

theorem bangOneCoeffHom_comp_representableToBang_ne (a k : ℕ) (hne : a ≠ k) :
    Hom.comp (bangOneCoeffHom a) (representableToBang 1 k) = 0 := by
  apply Hom.ext
  intro n Φ
  change bangOneCoeff n a
      ((if h : a = k then h.symm ▸
          (symmetricPowerProjection 1 k).app n Φ else 0)) = 0
  simp only [hne, ↓reduceDIte]
  dsimp only [bangOneCoeff]
  exact (Superoperator.comp_ofEquivalence_finCongr
      (tensorPowerDimension_one_eq a)
      (0 : Superoperator n (tensorPowerDimension 1 a))).symm.trans
    (Superoperator.comp_zero_right _)

theorem bangDereliction_comp_representableToBang_ne (k : ℕ) (hne : k ≠ 1) :
    Hom.comp (bangDereliction 1) (representableToBang 1 k) = 0 := by
  apply Hom.ext
  intro n Φ
  dsimp [bangDereliction, symmetricDereliction, representableToBang,
    bangInjection, countableProductInjection, Hom.comp]
  change Superoperator.comp
      (Superoperator.ofEquivalence
        (finCongr (tensorPowerDimension_one 1)))
      ((if h : (1 : ℕ) = k then h.symm ▸
          (symmetricPowerProjection 1 k).app n Φ else 0)).val = 0
  have hne' : ¬((1 : ℕ) = k) := fun h => hne h.symm
  simp only [hne', ↓reduceDIte]
  exact Superoperator.comp_zero_right _

theorem DayTensor.map_comp_zero_left {M M' N N' : Module}
    (g : Hom N N') :
    DayTensor.map (0 : Hom M M') g = 0 := by
  apply DayTensor.hom_ext
  intro m n x y
  have hz : (0 : Hom M M').app m x = 0 := (0 : Hom M M').map_zero m
  simp only [DayTensor.map_intro]
  rw [hz, (DayCoend.intro M' N').map_zero_left]
  rfl

theorem DayTensor.map_comp_zero_right {M M' N N' : Module}
    (f : Hom M M') :
    DayTensor.map f (0 : Hom N N') = 0 := by
  apply DayTensor.hom_ext
  intro m n x y
  have hz : (0 : Hom N N').app n y = 0 := (0 : Hom N N').map_zero n
  simp only [DayTensor.map_intro]
  rw [hz, (DayCoend.intro M' N').map_zero_right]
  rfl

theorem map_coeff_dereliction_comp_bangComultComponent_ne
    (k p q : ℕ) (hne : (p, q) ≠ (k, 1)) :
    Hom.comp
        (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1))
        (bangComultComponent 1 p q) = 0 := by
  simp only [bangComultComponent]
  refine Eq.trans (by ext; rfl) ?_
  have hmap := DayTensor.map_comp (bangOneCoeffHom k) (representableToBang 1 p)
    (bangDereliction 1) (representableToBang 1 q)
  refine Eq.trans (congrArg (fun g => Hom.comp g
      (Hom.comp (bangSplitToRepDay 1 p q) (bangSplitComponent 1 p q)))
    hmap.symm) ?_
  by_cases hp : p = k
  · by_cases hq : q = 1
    · exact (hne (by subst hp; subst hq; rfl)).elim
    · have hz := bangDereliction_comp_representableToBang_ne q hq
      rw [hz, DayTensor.map_comp_zero_right]
      ext; rfl
  · have hz := bangOneCoeffHom_comp_representableToBang_ne k p (Ne.symm hp)
    rw [hz, DayTensor.map_comp_zero_left]
    ext; rfl

private theorem eq_rec_cancel {α : Sort*} {a b : α} (h : a = b)
    {β : α → Sort*} (x : β a) : h.symm ▸ (h ▸ x) = x := by
  cases h; rfl

theorem bangOneCoeff_val_eq {k n : ℕ} (x : SymmetricElement 1 k n) :
    Superoperator.comp
        (Superoperator.ofEquivalence
          (finCongr (tensorPowerDimension_one_eq k).symm))
        (bangOneCoeff n k x) =
      x.val := by
  dsimp only [bangOneCoeff]
  refine (ofEquiv_comp_tpd (k := k)
    ((tensorPowerDimension_one_eq k) ▸ x.val)).trans ?_
  exact eq_rec_cancel (tensorPowerDimension_one_eq k) x.val

theorem symmetricElement_one_ext {k n : ℕ}
    (x y : SymmetricElement 1 k n)
    (h : bangOneCoeff n k x = bangOneCoeff n k y) : x = y := by
  apply SymmetricElement.ext
  have hx := bangOneCoeff_val_eq x
  have hy := bangOneCoeff_val_eq y
  rw [← hx, ← hy, h]

theorem bangOneCoeff_comonoidHom_zero (C : Comonoid)
    (g : ComonoidHom C (bangComonoid 1 (by decide))) (n : ℕ)
    (x : (C.carrier.obj n).Carrier) :
    bangOneCoeff n 0 ((g.hom.app n x) 0) = C.counit.app n x := by
  have hε := congrArg (fun η : Hom C.carrier dayTensorUnit => η.app n x)
    g.preserves_counit
  simpa [bangOneCoeff, bangComonoid, Hom.comp_app, bangCounit,
    symmetricWeakening] using hε

theorem bangOneCoeff_comonoidHom_one (C : Comonoid)
    (g : ComonoidHom C (bangComonoid 1 (by decide))) (n : ℕ)
    (x : (C.carrier.obj n).Carrier) :
    bangOneCoeff n 1 ((g.hom.app n x) 1) =
      (bangCofreeForgetComonoid 1 (by decide) C g).app n x := by
  have hEq :
      finCongr (tensorPowerDimension_one 1) =
        finCongr (tensorPowerDimension_one_eq 1) := by
    congr 1
  change bangOneCoeff n 1 ((g.hom.app n x) 1) =
    Superoperator.comp
      (Superoperator.ofEquivalence
        (finCongr (tensorPowerDimension_one 1)))
      ((g.hom.app n x) 1).val
  rw [hEq]
  exact (Superoperator.comp_ofEquivalence_finCongr
    (tensorPowerDimension_one_eq 1) ((g.hom.app n x) 1).val).symm

theorem bangOneCoeffHom_comp_factor (k : ℕ) :
    Hom.comp (bangOneCoeffHom k)
        (Hom.comp (representableToBang 1 k) (bangOneCast k)) =
      Hom.id dayTensorUnit := by
  apply Hom.ext
  intro n Φ
  exact bangOneCoeff_repToBang_cast k n Φ

theorem bangDereliction_comp_factor :
    Hom.comp (bangDereliction 1)
        (Hom.comp (representableToBang 1 1) (bangOneCast 1)) =
      Hom.id (representable 1) := by
  apply Hom.ext
  intro n Φ
  change Superoperator.comp
      (Superoperator.ofEquivalence
        (finCongr (tensorPowerDimension_one 1)))
      (((representableToBang 1 1).app n ((bangOneCast 1).app n Φ)) 1).val = Φ
  have hfin :
      finCongr (tensorPowerDimension_one 1) =
        finCongr (tensorPowerDimension_one_eq 1) :=
    congrArg finCongr (Subsingleton.elim _ _)
  rw [hfin, Superoperator.comp_ofEquivalence_finCongr]
  exact bangOneCoeff_repToBang_cast 1 n Φ

/-- `(coeff_k ⊗ dereliction) ∘ Δ_bang = λ⁻¹ ∘ coeff_{k+1}` on `bang 1`. -/
theorem map_coeff_dereliction_comp_bangComult (k : ℕ) :
    Hom.comp
        (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1))
        bangComult_one =
      Hom.comp (DayTensor.leftUnitorInv dayTensorUnit)
        (bangOneCoeffHom (k + 1)) := by
  have hsum :
      Hom.HasSum
        (fun pq : ℕ × ℕ => bangComultComponent 1 pq.1 pq.2)
        bangComult_one :=
    fun n x => bangComult_hasSum_components n x
  have hL := Hom.hasSum_comp_left
    (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1)) hsum
  have hfun :
      (fun pq : ℕ × ℕ =>
          Hom.comp
            (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1))
            (bangComultComponent 1 pq.1 pq.2)) =
        fun pq : ℕ × ℕ =>
          if pq = (k, 1) then
            Hom.comp
              (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1))
              (bangComultComponent 1 k 1)
          else 0 := by
    funext pq
    by_cases h : pq = (k, 1)
    · subst h; simp
    · rw [map_coeff_dereliction_comp_bangComultComponent_ne k pq.1 pq.2 h]
      simp [h]
  have hsingle :
      Hom.HasSum
        (fun pq : ℕ × ℕ =>
          if pq = (k, 1) then
            Hom.comp
              (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1))
              (bangComultComponent 1 k 1)
          else 0)
        (Hom.comp
          (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1))
          (bangComultComponent 1 k 1)) := by
    intro n x
    convert Fiber.hasSum_singleAt _
        (k, 1)
        ((Hom.comp
            (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1))
            (bangComultComponent 1 k 1)).app n x) using 1
    funext i
    by_cases h : i = (k, 1)
    · simp [h]
    · simp [h, Hom.zero_app]
  have hL' :
      Hom.comp
          (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1))
          bangComult_one =
        Hom.comp
          (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1))
          (bangComultComponent 1 k 1) :=
    Hom.hasSum_unique (by rwa [hfun] at hL) hsingle
  rw [hL']
  have hcast := bangComultComponent_comp_cast k 1
  have hfactor := DayTensor.map_comp
    (bangOneCoeffHom k) (Hom.comp (representableToBang 1 k) (bangOneCast k))
    (bangDereliction 1) (Hom.comp (representableToBang 1 1) (bangOneCast 1))
  have hid :
      DayTensor.map
          (Hom.comp (bangOneCoeffHom k)
            (Hom.comp (representableToBang 1 k) (bangOneCast k)))
          (Hom.comp (bangDereliction 1)
            (Hom.comp (representableToBang 1 1) (bangOneCast 1))) =
        DayTensor.map (Hom.id dayTensorUnit) (Hom.id (representable 1)) := by
    rw [bangOneCoeffHom_comp_factor, bangDereliction_comp_factor]
  have hmapid : DayTensor.map (Hom.id dayTensorUnit) (Hom.id (representable 1)) =
      Hom.id (dayTensor dayTensorUnit (representable 1)) :=
    DayTensor.map_id _ _
  have hcancel :
      Hom.comp
          (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1))
          (Hom.comp
            (DayTensor.map
              (Hom.comp (representableToBang 1 k) (bangOneCast k))
              (Hom.comp (representableToBang 1 1) (bangOneCast 1)))
            (DayTensor.leftUnitorInv dayTensorUnit)) =
        DayTensor.leftUnitorInv dayTensorUnit := by
    -- associate: map ∘ (map' ∘ λ⁻¹) = (map ∘ map') ∘ λ⁻¹
    refine Eq.trans (Hom.comp_assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun g => Hom.comp g
        (DayTensor.leftUnitorInv dayTensorUnit)) hfactor.symm) ?_
    rw [hid, hmapid, Hom.id_comp]
  apply Hom.ext
  intro n x
  have hslot :
      (bangComultComponent 1 k 1).app n x =
        (bangComultComponent 1 k 1).app n
          ((representableToBang 1 (k + 1)).app n
            ((bangOneCast (k + 1)).app n
              (bangOneCoeff n (k + 1) (x (k + 1))))) := by
    apply dayTensor_ext
    intro L β
    rw [bangComultComponent_evaluate_one, bangComultComponent_evaluate_one,
      bangOneCoeff_repToBang_cast]
  -- map ∘ component ∘ (rep∘cast) = λ⁻¹
  have hpath :
      Hom.comp
          (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1))
          (Hom.comp (bangComultComponent 1 k 1)
            (Hom.comp (representableToBang 1 (k + 1)) (bangOneCast (k + 1)))) =
        DayTensor.leftUnitorInv dayTensorUnit :=
    (congrArg (Hom.comp
        (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1))) hcast).trans
      hcancel
  have happ := congrArg
    (fun η : Hom (representable 1)
        (dayTensor dayTensorUnit (representable 1)) =>
      η.app n (bangOneCoeff n (k + 1) (x (k + 1)))) hpath
  -- Reduce both sides at x via the (k+1)-slot factorization
  change
      (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1)).app n
          ((bangComultComponent 1 k 1).app n x) =
        (DayTensor.leftUnitorInv dayTensorUnit).app n
          ((bangOneCoeffHom (k + 1)).app n x)
  rw [hslot]
  -- Match happ's nested Hom.comp shape
  change
      (Hom.comp
          (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1))
          (Hom.comp (bangComultComponent 1 k 1)
            (Hom.comp (representableToBang 1 (k + 1)) (bangOneCast (k + 1))))).app
        n (bangOneCoeff n (k + 1) (x (k + 1))) =
        (DayTensor.leftUnitorInv dayTensorUnit).app n
          (bangOneCoeff n (k + 1) (x (k + 1)))
  exact happ

theorem bangOneCoeff_comonoidHom (C : Comonoid)
    (g : ComonoidHom C (bangComonoid 1 (by decide))) (k n : ℕ)
    (x : (C.carrier.obj n).Carrier) :
    bangOneCoeff n k ((g.hom.app n x) k) =
      (bangCofreeCoeffOne C
        (bangCofreeForgetComonoid 1 (by decide) C g) k).app n x := by
  let f := bangCofreeForgetComonoid 1 (by decide) C g
  induction k generalizing n x with
  | zero => exact bangOneCoeff_comonoidHom_zero C g n x
  | succ k ih =>
    have hφ :
        bangCofreeCoeffOne C f (k + 1) =
          Hom.comp (DayTensor.leftUnitor dayTensorUnit)
            (Hom.comp (DayTensor.map (bangCofreeCoeffOne C f k) f)
              C.comult) := rfl
    -- (map(coeff,der) ∘ bangComult) ∘ g = (λ⁻¹ ∘ coeffHom(k+1)) ∘ g
    have hsucc :
        Hom.comp
            (Hom.comp
              (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1))
              bangComult_one)
            g.hom =
          Hom.comp
            (Hom.comp (DayTensor.leftUnitorInv dayTensorUnit)
              (bangOneCoeffHom (k + 1)))
            g.hom :=
      congrArg (fun η => Hom.comp η g.hom)
        (map_coeff_dereliction_comp_bangComult k)
    -- bangComult ∘ g = map(g,g) ∘ Δ
    have hpres :
        Hom.comp bangComult_one g.hom =
          Hom.comp (DayTensor.map g.hom g.hom) C.comult := by
      change Hom.comp (bangComonoid 1 (by decide)).comult g.hom = _
      exact g.preserves_comult
    have hreassoc :
        Hom.comp
            (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1))
            (DayTensor.map g.hom g.hom) =
          DayTensor.map
            (Hom.comp (bangOneCoeffHom k) g.hom)
            (Hom.comp (bangDereliction 1) g.hom) :=
      (DayTensor.map_comp (bangOneCoeffHom k) g.hom
        (bangDereliction 1) g.hom).symm
    -- Pointwise: λ⁻¹ (coeffHom(k+1) (g x)) = map(coeff∘g, der∘g) (Δ x)
    have hL :
        (DayTensor.leftUnitorInv dayTensorUnit).app n
            (bangOneCoeff n (k + 1) ((g.hom.app n x) (k + 1))) =
          (DayTensor.map
              (Hom.comp (bangOneCoeffHom k) g.hom)
              (Hom.comp (bangDereliction 1) g.hom)).app n
            (C.comult.app n x) := by
      have hchain :
          Hom.comp
              (Hom.comp (DayTensor.leftUnitorInv dayTensorUnit)
                (bangOneCoeffHom (k + 1)))
              g.hom =
            Hom.comp
              (DayTensor.map
                (Hom.comp (bangOneCoeffHom k) g.hom)
                (Hom.comp (bangDereliction 1) g.hom))
              C.comult := by
        -- start from hsucc RHS = LHS of hsucc
        refine Eq.trans hsucc.symm ?_
        -- map∘bangComult∘g → map∘(map(g,g)∘Δ)
        refine Eq.trans (by
          change Hom.comp
              (Hom.comp
                (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1))
                bangComult_one)
              g.hom =
            Hom.comp
              (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1))
              (Hom.comp bangComult_one g.hom)
          exact (Hom.comp_assoc _ _ _).symm) ?_
        refine Eq.trans (congrArg
            (Hom.comp (DayTensor.map (bangOneCoeffHom k) (bangDereliction 1)))
            hpres) ?_
        -- map ∘ (map(g,g) ∘ Δ) = (map ∘ map(g,g)) ∘ Δ
        refine Eq.trans (Hom.comp_assoc _ _ _) ?_
        exact congrArg (fun η => Hom.comp η C.comult) hreassoc
      exact congrArg
        (fun η : Hom C.carrier
            (dayTensor dayTensorUnit (representable 1)) => η.app n x)
        hchain
    -- cancel λ⁻¹ by applying λ
    have hL2 :
        bangOneCoeff n (k + 1) ((g.hom.app n x) (k + 1)) =
          (DayTensor.leftUnitor dayTensorUnit).app n
            ((DayTensor.map
                (Hom.comp (bangOneCoeffHom k) g.hom)
                (Hom.comp (bangDereliction 1) g.hom)).app n
              (C.comult.app n x)) := by
      have hLU := congrArg
        (fun z => (DayTensor.leftUnitor dayTensorUnit).app n z) hL
      refine Eq.trans ?_ hLU
      let c : (dayTensorUnit.obj n).Carrier :=
        bangOneCoeff n (k + 1) ((g.hom.app n x) (k + 1))
      have h := congrArg (fun η : Hom dayTensorUnit dayTensorUnit => η.app n c)
        (DayTensor.leftUnitor_hom_inv dayTensorUnit)
      exact
        ((Hom.id_app dayTensorUnit n c).symm).trans
          (h.symm.trans
            (Hom.comp_app (DayTensor.leftUnitor dayTensorUnit)
              (DayTensor.leftUnitorInv dayTensorUnit) n c))
    refine Eq.trans hL2 ?_
    rw [hφ]
    have hψ : Hom.comp (bangOneCoeffHom k) g.hom =
        bangCofreeCoeffOne C f k := by
      apply Hom.ext
      intro m y
      exact ih m y
    have hε : Hom.comp (bangDereliction 1) g.hom = f := rfl
    simp only [Hom.comp_app, hψ, hε]
    rfl

theorem bangCofreeLiftOne_unique (C : Comonoid)
    (g : ComonoidHom C (bangComonoid 1 (by decide))) :
    g = bangCofreeLiftOneComonoidHom C
      (bangCofreeForgetComonoid 1 (by decide) C g) := by
  apply ComonoidHom.ext
  apply Hom.ext
  intro n x
  funext k
  apply symmetricElement_one_ext
  exact (bangOneCoeff_comonoidHom C g k n x).trans
    (bangOneCoeff_liftOne C _ k n x).symm

noncomputable def bangCofreeEquiv_one (C : Comonoid) :
    Hom C.carrier (representable 1) ≃
      ComonoidHom C (bangComonoid 1 (by decide)) where
  toFun := bangCofreeLiftOneComonoidHom C
  invFun := bangCofreeForgetComonoid 1 (by decide) C
  left_inv f := bangCofreeLiftOne_forget C f
  right_inv g := (bangCofreeLiftOne_unique C g).symm

noncomputable def comonoidHomEquiv_one (C : Comonoid) :=
  bangCofreeEquiv_one C

noncomputable def bangCofreeLift_of_le_one (A : ℕ) (hA : A ≤ 1)
    (C : Comonoid) (f : Hom C.carrier (representable A)) :
    ComonoidHom C (bangComonoid A hA) :=
  if h : A = 0 then by
    subst h
    exact bangCofreeLiftZeroComonoidHom C
  else by
    have h1 : A = 1 := by omega
    subst h1
    exact bangCofreeLiftOneComonoidHom C f

theorem bangCofreeLift_of_le_one_forget (A : ℕ) (hA : A ≤ 1)
    (C : Comonoid) (f : Hom C.carrier (representable A)) :
    bangCofreeForgetComonoid A hA C (bangCofreeLift_of_le_one A hA C f) = f := by
  unfold bangCofreeLift_of_le_one
  split_ifs with h
  · subst h
    exact hom_to_representable_zero_unique _ _ _
  · have h1 : A = 1 := by omega
    subst h1
    exact bangCofreeLiftOne_forget C f

theorem bangCofreeLift_of_le_one_unique (A : ℕ) (hA : A ≤ 1)
    (C : Comonoid) (g : ComonoidHom C (bangComonoid A hA)) :
    g = bangCofreeLift_of_le_one A hA C
      (bangCofreeForgetComonoid A hA C g) := by
  unfold bangCofreeLift_of_le_one
  split_ifs with h
  · subst h
    exact bangCofreeLiftZero_unique C g
  · have h1 : A = 1 := by omega
    subst h1
    exact bangCofreeLiftOne_unique C g

noncomputable def bangCofreeEquiv_of_le_one (A : ℕ) (hA : A ≤ 1)
    (C : Comonoid) :
    Hom C.carrier (representable A) ≃
      ComonoidHom C (bangComonoid A hA) where
  toFun := bangCofreeLift_of_le_one A hA C
  invFun := bangCofreeForgetComonoid A hA C
  left_inv := bangCofreeLift_of_le_one_forget A hA C
  right_inv g := (bangCofreeLift_of_le_one_unique A hA C g).symm

/-! ## Cofree co-Kleisli / bang comonad interface (`A ≤ 1`)

The cofree UP `bangCofreeEquiv_of_le_one` induces the standard co-Kleisli
promotion `Hom(!B, A) → Hom(!B, !A)` and the functorial action of bang on
maps between representables.  Counit of the comonad is dereliction; the
comonoid counit/comult are `bangCounit` / `bangComult_of_le_one`.  Digging
`!A → !!A` is not packaged here: `bang` is indexed by dimension `ℕ`, not by
arbitrary modules.  Comonad/co-Kleisli laws below are the ones that follow
from the UP alone (standard cofree diagrams).
-/

/-- Co-Kleisli promotion via the cofree UP:
`Hom(!B, A) → ComonoidHom(!B, !A)` for `A,B ≤ 1`. -/
noncomputable def bangPromote {A B : ℕ} (hA : A ≤ 1) (hB : B ≤ 1)
    (f : Hom (bang B) (representable A)) :
    ComonoidHom (bangComonoid B hB) (bangComonoid A hA) :=
  bangCofreeLift_of_le_one A hA (bangComonoid B hB) f

/-- Underlying module map of co-Kleisli promotion. -/
noncomputable def bangPromoteHom {A B : ℕ} (hA : A ≤ 1) (hB : B ≤ 1)
    (f : Hom (bang B) (representable A)) :
    Hom (bang B) (bang A) :=
  (bangPromote hA hB f).hom

/-- Functorial action of bang on maps of representables (`A,B ≤ 1`). -/
noncomputable def bangMap {A B : ℕ} (hA : A ≤ 1) (hB : B ≤ 1)
    (f : Hom (representable A) (representable B)) :
    Hom (bang A) (bang B) :=
  bangPromoteHom hB hA (Hom.comp f (bangDereliction A))

/-- Comonoid morphism induced by a map of representables. -/
noncomputable def bangMapComonoidHom {A B : ℕ} (hA : A ≤ 1) (hB : B ≤ 1)
    (f : Hom (representable A) (representable B)) :
    ComonoidHom (bangComonoid A hA) (bangComonoid B hB) :=
  bangPromote hB hA (Hom.comp f (bangDereliction A))

/-- Comonad counit: dereliction `!A → y(A)`. -/
noncomputable abbrev bangComonadCounit (A : ℕ) : Hom (bang A) (representable A) :=
  bangDereliction A

/-- Comonoid counit / weakening `!A → I` (Day tensor unit). -/
noncomputable abbrev bangComonadWeakening (A : ℕ) : Hom (bang A) dayTensorUnit :=
  bangCounit A

/-- Comonoid comultiplication `!A → !A ⊗ !A` for `A ≤ 1`. -/
noncomputable abbrev bangComonadComult (A : ℕ) (hA : A ≤ 1) :
    Hom (bang A) (dayTensor (bang A) (bang A)) :=
  bangComult_of_le_one A hA

/-- UP left inverse: dereliction after promotion recovers the generator. -/
theorem bangPromote_dereliction {A B : ℕ} (hA : A ≤ 1) (hB : B ≤ 1)
    (f : Hom (bang B) (representable A)) :
    Hom.comp (bangDereliction A) (bangPromoteHom hA hB f) = f :=
  bangCofreeLift_of_le_one_forget A hA (bangComonoid B hB) f

/-- UP right inverse on the identity comonoid endomorphism: promoting
dereliction is the identity. -/
theorem bangPromote_dereliction_id {A : ℕ} (hA : A ≤ 1) :
    bangPromote hA hA (bangDereliction A) =
      ComonoidHom.id (bangComonoid A hA) := by
  have hforget :
      bangCofreeForgetComonoid A hA (bangComonoid A hA)
          (ComonoidHom.id (bangComonoid A hA)) =
        bangDereliction A := by
    simp [bangCofreeForgetComonoid, bangCofreeForget, ComonoidHom.id_hom]
  have h :=
    bangCofreeLift_of_le_one_unique A hA (bangComonoid A hA)
      (ComonoidHom.id (bangComonoid A hA))
  rw [hforget] at h
  exact h.symm

@[simp]
theorem bangPromoteHom_dereliction_id {A : ℕ} (hA : A ≤ 1) :
    bangPromoteHom hA hA (bangDereliction A) = Hom.id (bang A) :=
  congrArg ComonoidHom.hom (bangPromote_dereliction_id hA)

/-- Co-Kleisli associativity from uniqueness of cofree lifts. -/
theorem bangPromote_comp {A B C : ℕ} (hA : A ≤ 1) (hB : B ≤ 1) (hC : C ≤ 1)
    (g : Hom (bang B) (representable A))
    (f : Hom (bang C) (representable B)) :
    ComonoidHom.comp (bangPromote hA hB g) (bangPromote hB hC f) =
      bangPromote hA hC (Hom.comp g (bangPromoteHom hB hC f)) := by
  let φ := ComonoidHom.comp (bangPromote hA hB g) (bangPromote hB hC f)
  have hforget :
      bangCofreeForgetComonoid A hA (bangComonoid C hC) φ =
        Hom.comp g (bangPromoteHom hB hC f) := by
    simp only [φ, bangCofreeForgetComonoid, bangCofreeForget,
      ComonoidHom.comp_hom, bangPromoteHom]
    have hg := bangPromote_dereliction hA hB g
    simp only [bangPromoteHom] at hg
    rw [Hom.comp_assoc, hg]
  have h :=
    bangCofreeLift_of_le_one_unique A hA (bangComonoid C hC) φ
  rw [hforget] at h
  exact h

@[simp]
theorem bangMap_id {A : ℕ} (hA : A ≤ 1) :
    bangMap hA hA (Hom.id (representable A)) = Hom.id (bang A) := by
  simp [bangMap]

theorem bangDereliction_bangMap {A B : ℕ} (hA : A ≤ 1) (hB : B ≤ 1)
    (f : Hom (representable A) (representable B)) :
    Hom.comp (bangDereliction B) (bangMap hA hB f) =
      Hom.comp f (bangDereliction A) :=
  bangPromote_dereliction hB hA (Hom.comp f (bangDereliction A))

theorem bangMap_comp {A B C : ℕ} (hA : A ≤ 1) (hB : B ≤ 1) (hC : C ≤ 1)
    (g : Hom (representable B) (representable C))
    (f : Hom (representable A) (representable B)) :
    bangMap hA hC (Hom.comp g f) =
      Hom.comp (bangMap hB hC g) (bangMap hA hB f) := by
  dsimp only [bangMap]
  have hassoc :=
    congrArg ComonoidHom.hom
      (bangPromote_comp hC hB hA
        (Hom.comp g (bangDereliction B))
        (Hom.comp f (bangDereliction A)))
  have hgen :
      Hom.comp (Hom.comp g (bangDereliction B))
          (bangPromoteHom hB hA (Hom.comp f (bangDereliction A))) =
        Hom.comp (Hom.comp g f) (bangDereliction A) := by
    have hf := bangDereliction_bangMap hA hB f
    simp only [bangMap, bangPromoteHom] at hf ⊢
    rw [← Hom.comp_assoc, hf, Hom.comp_assoc]
  exact (congrArg (bangPromoteHom hC hA) hgen.symm).trans hassoc.symm

/-- Promoted maps preserve the Day comonoid counit (weakening). -/
theorem bangMap_preserves_counit {A B : ℕ} (hA : A ≤ 1) (hB : B ≤ 1)
    (f : Hom (representable A) (representable B)) :
    Hom.comp (bangCounit B) (bangMap hA hB f) = bangCounit A :=
  (bangMapComonoidHom hA hB f).preserves_counit

/-- Promoted maps preserve Day comultiplication. -/
theorem bangMap_preserves_comult {A B : ℕ} (hA : A ≤ 1) (hB : B ≤ 1)
    (f : Hom (representable A) (representable B)) :
    Hom.comp (bangComult_of_le_one B hB) (bangMap hA hB f) =
      Hom.comp (DayTensor.map (bangMap hA hB f) (bangMap hA hB f))
        (bangComult_of_le_one A hA) :=
  (bangMapComonoidHom hA hB f).preserves_comult

end SuperoperatorModule

end QLambda.Domain.Presheaf
