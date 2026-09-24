/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.DayComonoidCounit

/-!
# Day coassociativity and `bangComonoid`
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

set_option maxHeartbeats 8000000

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

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
    ofEquivalence_dim_one hpq (by simp) _ _
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
  have hsrc : tensorPowerDimension 1 (p + (q + r)) = 1 :=
    tensorPowerDimension_one_eq _
  have htgt : tensorPowerDimension 1 p *
      (tensorPowerDimension 1 q * tensorPowerDimension 1 r) = 1 := by
    simp
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


end SuperoperatorModule

end QLambda.Domain.Presheaf
