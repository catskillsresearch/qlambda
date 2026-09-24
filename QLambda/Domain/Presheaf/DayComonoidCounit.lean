/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.DayComonoidAdmissible

/-!
# Day counit and cocommutativity for bang (`A ≤ 1`)
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

set_option maxHeartbeats 8000000

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

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
    refine ofEquivalence_dim_one (by simp) htgt _ _
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
    exact ofEquivalence_dim_one (by simp) h1 _ _
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
    simp
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
    refine ofEquivalence_dim_one (by simp) htgt _ _
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
    exact ofEquivalence_dim_one (by simp) h1 _ _
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
    · simp
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
    simp
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
      (∀ (A : ℕ) (_hA : A ≤ 1),
        (((Hom.comp (DayTensor.leftUnitor (bang A))
            (Hom.comp (DayTensor.map (bangCounit A) (Hom.id (bang A)))
              (bangComultComponent A 0 1))).app
            (tensorPowerDimension A 1) (bangIdentityDegreeOne A)) 1).val =
          Superoperator.identity (tensorPowerDimension A 1)) ∧
      (∀ (A : ℕ) (_hA : A ≤ 1),
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




end SuperoperatorModule

end QLambda.Domain.Presheaf
