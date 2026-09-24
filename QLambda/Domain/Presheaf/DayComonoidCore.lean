/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.ComonoidHom

/-!
# Bang carrier and Day comultiplication components
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


end SuperoperatorModule

end QLambda.Domain.Presheaf
