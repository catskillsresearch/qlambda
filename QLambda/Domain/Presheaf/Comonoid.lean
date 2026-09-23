/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Exponential
import QLambda.Domain.Presheaf.DayCoend

/-!
# Commutative comonoids over the genuine Day tensor (plan gate 3)

Gate progress (`cofree-exponential`): **blocked at `BangComultComponentsAdmissible` for `A ≥ 1`**.

## Fiber support (critical)

`bang A = symmetricFormalPowerSeries A = countableProduct (symmetricPower A)`.
Fibers are pointwise products `∀ k, SymmetricElement A k n` — **not**
finite-support / eventually-zero series.  The finite-subfamily Choi shortcut
therefore does **not** apply to `BangComultComponentsAdmissible`: a general
series element can load every degree, so infinitely many `(p,q)` split
components may be nonzero.

## Constructed (kernel-checked)

* Abstract `Comonoid` / `ComonoidHom` over `dayTensor`
* `bang`, `bangCounit`, `bangDereliction`
* `symmetricSeriesDayCompare : dayTensor(!A,!A) → square` (not an iso)
* Per-degree Day components
  `bangComultComponent A p q : Hom (!A) (dayTensor (!A) (!A))`
* Conditional fiberwise sum `bangComultApp` and Hom promotion
  `bangComult` under `BangComultComponentsAdmissible` (map_sum via
  `PartialCountableSum.flatten`)
* Degree reindexing: `DegreePartition`, `bangComultComponent_eq_of_injection`,
  `bangComultComponent_evaluate`, `bangOne_degreeUnit_rectangle_hasSum`

## Blocker

`BangComultComponentsAdmissible A`: every bilinear interpretation of the
family `bangComultComponentFamily` must admit a joint sum.  This is the
Day-side form of the mixed-partition TNI gate recorded in `Exponential.lean`.

**Proved for `A = 0`** (only the `(0,0)` slot survives).

**Degree reindexing (`A ≥ 1`):** evaluate identity and the `A = 1` degree-unit
rectangle are in place.  Homogeneous diagonal rows reduce to flatten of that
rectangle acted by a single channel; the residual outer gate is
`BangComultSeriesActHasSum` (joint `L.act d_k Φ_k` with summable `(d_k)`).
Assembly of unconditional `bangComult` / `Comonoid` waits on that gate.

Ambient obstruction `factorPermutationEquiv_swap_ne_refl` remains.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

/-! ## Abstract commutative comonoids -/

/-- A commutative comonoid in specialized modules, with comultiplication
landing in the genuine Day tensor. -/
structure Comonoid where
  carrier : Module
  counit : Hom carrier dayTensorUnit
  comult : Hom carrier (dayTensor carrier carrier)
  left_counit :
    Hom.comp (DayTensor.leftUnitor carrier)
        (Hom.comp (DayTensor.map counit (Hom.id carrier)) comult) =
      Hom.id carrier
  right_counit :
    Hom.comp (DayTensor.rightUnitor carrier)
        (Hom.comp (DayTensor.map (Hom.id carrier) counit) comult) =
      Hom.id carrier
  coassociative :
    Hom.comp (DayTensor.associator carrier carrier carrier)
        (Hom.comp (DayTensor.map comult (Hom.id carrier)) comult) =
      Hom.comp (DayTensor.map (Hom.id carrier) comult) comult
  cocommutative :
    Hom.comp (DayTensor.braiding carrier carrier) comult = comult

/-- Morphisms of commutative comonoids: underlying module maps preserving
counit and comultiplication. -/
structure ComonoidHom (C D : Comonoid) where
  hom : Hom C.carrier D.carrier
  preserves_counit :
    Hom.comp D.counit hom = C.counit
  preserves_comult :
    Hom.comp D.comult hom =
      Hom.comp (DayTensor.map hom hom) C.comult

namespace ComonoidHom

@[ext]
theorem ext {C D : Comonoid} {f g : ComonoidHom C D}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (C : Comonoid) : ComonoidHom C C where
  hom := Hom.id C.carrier
  preserves_counit := by simp
  preserves_comult := by simp [DayTensor.map_id]

def comp {C D E : Comonoid}
    (g : ComonoidHom D E) (f : ComonoidHom C D) :
    ComonoidHom C E where
  hom := Hom.comp g.hom f.hom
  preserves_counit := by
    rw [Hom.comp_assoc, g.preserves_counit, f.preserves_counit]
  preserves_comult := by
    rw [Hom.comp_assoc, g.preserves_comult, ← Hom.comp_assoc,
      f.preserves_comult, Hom.comp_assoc, DayTensor.map_comp]

@[simp]
theorem id_hom (C : Comonoid) : (id C).hom = Hom.id C.carrier :=
  rfl

@[simp]
theorem comp_hom {C D E : Comonoid}
    (g : ComonoidHom D E) (f : ComonoidHom C D) :
    (comp g f).hom = Hom.comp g.hom f.hom :=
  rfl

end ComonoidHom

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

/-- Open residual: existence of a Day-valued comultiplication factoring the
coefficientwise `symmetricContraction` through `symmetricSeriesDayCompare`.
Not claimed. -/
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

/-- Cast of an `A = 1` homogeneous coefficient to fiber dimension `1`. -/
noncomputable def bangOneCoeff (n k : ℕ)
    (x : SymmetricElement 1 k n) : Superoperator n 1 :=
  cast (by rw [tensorPowerDimension_eq_pow, one_pow]) x.val

/-- For `A = 1` every tensor-power dimension is `1`. -/
theorem tensorPowerDimension_one_eq (k : ℕ) :
    tensorPowerDimension 1 k = 1 := by
  simp [tensorPowerDimension_eq_pow, one_pow]

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

/-- Outer series gate for assembling general `A = 1` admissibility from
homogeneous diagonal rows: joint `L.act d_k Φ_k` with summable `(d_k)`. -/
def BangComultSeriesActHasSum : Prop :=
  ∀ (n : ℕ) (x : ((bang 1).obj n).Carrier)
    (L : Module.{0}) (d : ℕ → (L.obj 1).Carrier) (D : (L.obj 1).Carrier),
    (L.obj 1).HasSum d D →
      ∃ z : (L.obj n).Carrier,
        (L.obj n).HasSum (fun k => L.act (d k) (bangOneCoeff n k (x k))) z

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

end SuperoperatorModule

end QLambda.Domain.Presheaf
