/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.DayComonoidCoassoc

/-!
# Cofree UP and bang co-Kleisli (`bangPromote` / `bangMap`)
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

set_option maxHeartbeats 8000000

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

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
