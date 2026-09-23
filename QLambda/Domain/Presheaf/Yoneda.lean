/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Module

/-!
# Representable superoperator modules and Yoneda

The proofs are elementary and use the concrete Choi-sum preservation of
composition.  Thus the Yoneda correspondence below has no categorical
existence premise.
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SuperoperatorModule

universe u
/-- The representable module `Q(-, A)`. -/
noncomputable def representable (A : ℕ) : Module where
  obj n :=
    { Carrier := Superoperator n A
      zero := 0
      summation := SigmaMon.superoperatorPartialCountableSum }
  act := fun x f => Superoperator.comp x f
  act_zero_element := by
    intro m n f
    exact Superoperator.comp_zero_left f
  act_zero_map := by
    intro m n x
    exact Superoperator.comp_zero_right x
  act_id := by
    intro n x
    exact Superoperator.comp_identity x
  act_comp := by
    intro ℓ m n x f g
    exact (Superoperator.comp_assoc x f g).symm
  act_sum_element := by
    intro ι _ m n x s f h
    exact SigmaMon.ChoiSum.comp_right f h
  act_sum_map := by
    intro ι _ m n x f s h
    exact SigmaMon.ChoiSum.comp_left x h
  act_sum_from_one := by
    intro ι _ m x s f h
    obtain ⟨Χ, hΧ⟩ := SigmaMon.ChoiSum.comp_from_one f h
    exact ⟨Χ, hΧ⟩
  act_sum_tensor_from_one := by
    intro ι _ m B x s f h
    match B with
    | 0 =>
      refine ⟨0, ?_⟩
      have hz : ∀ i,
          Superoperator.comp (x i)
              (Superoperator.tensor (f i) (Superoperator.identity 0)) =
            0 := by
        intro i
        have hT :
            Superoperator.tensor (f i) (Superoperator.identity 0) =
              (0 : Superoperator (m * 0) (1 * 0)) := by
          apply Superoperator.ext
          apply CPMap.ext
          ext a b
          have : IsEmpty (Fin (1 * 0)) := by
            simp only [Nat.mul_zero]; infer_instance
          exact isEmptyElim (a.1 : Fin (1 * 0))
        rw [hT]
        exact Superoperator.comp_zero_right _
      exact
        (Fiber.hasSum_congr
            { Carrier := Superoperator (m * 0) A
              zero := 0
              summation := SigmaMon.superoperatorPartialCountableSum }
            hz).mpr
          (Fiber.hasSum_zero _)
    | 1 =>
      -- `1 * 1 = 1` definitionally (numeral); `m * 1 = m` only propositionally.
      have hx1 : SigmaMon.ChoiSum.HasSum
          (fun i => (x i : Superoperator 1 A))
          (s : Superoperator 1 A) := h
      obtain ⟨Χ, hΧ⟩ := SigmaMon.ChoiSum.comp_from_one f hx1
      -- `Χ ∘ ρₘ` lives at fiber `m * 1`.
      refine
        ⟨Superoperator.comp Χ (Superoperator.tensorRightUnitor m), ?_⟩
      have hrunitor1 :
          Superoperator.tensorRightUnitorInv 1 =
            Superoperator.identity 1 := by
        rw [show Superoperator.tensorRightUnitorInv 1 =
          Superoperator.ofEquivalence
            (Superoperator.tensorRightUnitorEquiv 1).symm from rfl]
        have hEq :
            (Superoperator.tensorRightUnitorEquiv 1).symm =
              Equiv.refl (Fin 1) := by
          apply Equiv.ext
          intro i
          apply Fin.ext
          omega
        rw [hEq, Superoperator.ofEquivalence_refl]
      have htensor (g : Superoperator m 1) :
          Superoperator.tensor g (Superoperator.identity 1) =
            Superoperator.comp (Superoperator.tensorRightUnitorInv 1)
              (Superoperator.comp g
                (Superoperator.tensorRightUnitor m)) := by
        have hnat := Superoperator.tensorRightUnitor_naturality g
        have h :=
          congrArg
            (Superoperator.comp (Superoperator.tensorRightUnitorInv 1)) hnat
        simpa [Superoperator.comp_assoc,
          Superoperator.tensorRightUnitor_inv_hom,
          Superoperator.identity_comp] using h
      have hfam :
          (fun i =>
            Superoperator.comp (x i)
              (Superoperator.tensor (f i) (Superoperator.identity 1))) =
            fun i =>
              Superoperator.comp
                (Superoperator.comp (x i) (f i))
                (Superoperator.tensorRightUnitor m) := by
        funext i
        rw [htensor, hrunitor1, Superoperator.identity_comp,
          Superoperator.comp_assoc]
      have hΧρ :
          SigmaMon.ChoiSum.HasSum
            (fun i =>
              Superoperator.comp (Superoperator.comp (x i) (f i))
                (Superoperator.tensorRightUnitor m))
            (Superoperator.comp Χ
              (Superoperator.tensorRightUnitor m)) :=
        SigmaMon.ChoiSum.comp_right
          (Superoperator.tensorRightUnitor m) hΧ
      rw [hfam]
      exact hΧρ
    | n + 2 =>
      -- Discard majorant `δ` (effect `I`), residual effects `I - E_i`, then
      -- extract the target family as a Bool-subfamily of a flat Choi sum.
      let δ : Superoperator m 1 := by
        let C : Matrix (Fin 1 × Fin m) (Fin 1 × Fin m) ℂ :=
          fun p q => (1 : Matrix (Fin m) (Fin m) ℂ) q.2 p.2
        have hC : C.PosSemidef :=
          (Matrix.PosSemidef.one (n := Fin m)).transpose.submatrix
            (Prod.snd : Fin 1 × Fin m → Fin m)
        exact
          ⟨{ choi := C, choi_pos := hC },
            (traceNonincreasing_iff_effect_le_one _).mpr (by
              have hE : (⟨C, hC⟩ : CPMap m 1).effect = 1 := by
                ext i j
                simp [CPMap.effect, C, Finset.card_fin, nsmul_eq_mul,
                  Nat.cast_one, one_mul]
              simpa [hE] using
                (le_refl (1 : Matrix (Fin m) (Fin m) ℂ)))⟩
      have hδE : δ.cp.effect = (1 : Matrix (Fin m) (Fin m) ℂ) := by
        ext i j
        simp [δ, CPMap.effect, Finset.card_fin, nsmul_eq_mul, Nat.cast_one,
          one_mul]
      have hchoi_form (Ψ : Superoperator m 1)
          (p q : Fin 1 × Fin m) :
          Ψ.cp.choi p q = Ψ.cp.effect q.2 p.2 := by
        simp only [CPMap.effect, Fin.sum_univ_one]
        congr 1
        · exact Prod.ext (Subsingleton.elim _ _) rfl
        · exact Prod.ext (Subsingleton.elim _ _) rfl
      have hf_le (i : ι) : (f i).cp ≤ δ.cp := by
        change (f i).cp.choi ≤ δ.cp.choi
        rw [Matrix.le_iff]
        have hE :
            ((1 : Matrix (Fin m) (Fin m) ℂ) - (f i).cp.effect).PosSemidef :=
          Matrix.le_iff.mp
            (CPMap.effect_le_one_of_trace_nonincreasing (f i).cp
              (f i).trace_nonincreasing)
        have hdiff :
            δ.cp.choi - (f i).cp.choi =
              ((1 : Matrix (Fin m) (Fin m) ℂ) -
                  (f i).cp.effect)ᵀ.submatrix
                (Prod.snd : Fin 1 × Fin m → Fin m)
                (Prod.snd : Fin 1 × Fin m → Fin m) := by
          ext p q
          simp only [Matrix.sub_apply, Matrix.submatrix_apply,
            Matrix.transpose_apply, hchoi_form, hδE]
        rw [hdiff]
        exact hE.transpose.submatrix _
      let r (i : ι) : Superoperator m 1 := by
        let R := CPMap.residualOfLE (hf_le i)
        refine ⟨R, (traceNonincreasing_iff_effect_le_one _).mpr ?_⟩
        -- Residual effect is `I - effect(f i) ≤ I`.
        have hRchoi (p q : Fin 1 × Fin m) :
            R.choi p q =
              ((1 : Matrix (Fin m) (Fin m) ℂ) - (f i).cp.effect) q.2 p.2 := by
          change (δ.cp.choi - (f i).cp.choi) p q = _
          simp [Matrix.sub_apply, hchoi_form, hδE]
        have hRe :
            R.effect =
              (1 : Matrix (Fin m) (Fin m) ℂ) - (f i).cp.effect := by
          ext a b
          simp only [CPMap.effect, Fin.sum_univ_one, hRchoi]
        have hIE :
            ((1 : Matrix (Fin m) (Fin m) ℂ) - (f i).cp.effect) ≤ 1 := by
          rw [Matrix.le_iff]
          have hEpos := CPMap.effect_posSemidef (f i).cp
          simpa [sub_sub_cancel] using hEpos
        simpa [hRe] using hIE
      have hadd_cp (i : ι) :
          (f i).cp + (r i).cp = δ.cp := by
        simpa [r] using CPMap.add_residualOfLE (hf_le i)
      have hten_cp (i : ι) :
          CPMap.tensor (f i).cp (CPMap.identity (n + 2)) +
              CPMap.tensor (r i).cp (CPMap.identity (n + 2)) =
            CPMap.tensor δ.cp (CPMap.identity (n + 2)) := by
        rw [← CPMap.tensor_add_left, hadd_cp]
      have hten (i : ι) :
          (Superoperator.tensor (f i)
                (Superoperator.identity (n + 2))).cp +
              (Superoperator.tensor (r i)
                (Superoperator.identity (n + 2))).cp =
            (Superoperator.tensor δ
              (Superoperator.identity (n + 2))).cp := by
        simpa [Superoperator.cp_tensor, show
            (Superoperator.identity (n + 2)).cp =
              CPMap.identity (n + 2) from rfl] using hten_cp i
      have hcomp_add (i : ι) :
          (Superoperator.comp (x i)
                (Superoperator.tensor (f i)
                  (Superoperator.identity (n + 2)))).cp +
              (Superoperator.comp (x i)
                (Superoperator.tensor (r i)
                  (Superoperator.identity (n + 2)))).cp =
            (Superoperator.comp (x i)
              (Superoperator.tensor δ
                (Superoperator.identity (n + 2)))).cp := by
        simp only [Superoperator.cp_comp]
        rw [← CPMap.comp_add_left, hten]
      let F : (Σ _ : ι, Bool) → Superoperator (m * (n + 2)) A :=
        fun p =>
          if p.2 then
            Superoperator.comp (x p.1)
              (Superoperator.tensor (f p.1)
                (Superoperator.identity (n + 2)))
          else
            Superoperator.comp (x p.1)
              (Superoperator.tensor (r p.1)
                (Superoperator.identity (n + 2)))
      have hrow (i : ι) :
          SigmaMon.ChoiSum.HasSum (fun b : Bool => F ⟨i, b⟩)
            (Superoperator.comp (x i)
              (Superoperator.tensor δ
                (Superoperator.identity (n + 2)))) := by
        change SigmaMon.ChoiSum.HasSum
            (fun b : Bool =>
              if b then
                Superoperator.comp (x i)
                  (Superoperator.tensor (f i)
                    (Superoperator.identity (n + 2)))
              else
                Superoperator.comp (x i)
                  (Superoperator.tensor (r i)
                    (Superoperator.identity (n + 2))))
            _
        have hsum :
            _root_.HasSum
              (fun b : Bool =>
                (if b then
                    Superoperator.comp (x i)
                      (Superoperator.tensor (f i)
                        (Superoperator.identity (n + 2)))
                  else
                    Superoperator.comp (x i)
                      (Superoperator.tensor (r i)
                        (Superoperator.identity (n + 2)))).cp.choi)
              ((Superoperator.comp (x i)
                  (Superoperator.tensor δ
                    (Superoperator.identity (n + 2)))).cp.choi) := by
          let Tf :=
            Superoperator.comp (x i)
              (Superoperator.tensor (f i)
                (Superoperator.identity (n + 2)))
          let Tr :=
            Superoperator.comp (x i)
              (Superoperator.tensor (r i)
                (Superoperator.identity (n + 2)))
          let Tδ :=
            Superoperator.comp (x i)
              (Superoperator.tensor δ
                (Superoperator.identity (n + 2)))
          have hfin :
              _root_.HasSum
                (fun b : Bool => (if b then Tf else Tr).cp.choi)
                (∑ b : Bool, (if b then Tf else Tr).cp.choi) :=
            hasSum_fintype _
          have htot :
              (∑ b : Bool, (if b then Tf else Tr).cp.choi) = Tδ.cp.choi := by
            calc
              (∑ b : Bool, (if b then Tf else Tr).cp.choi)
                  = (if true then Tf else Tr).cp.choi +
                      (if false then Tf else Tr).cp.choi :=
                    Fintype.sum_bool _
              _ = Tf.cp.choi + Tr.cp.choi := by simp
              _ = (Tf.cp + Tr.cp).choi := (CPMap.choi_add Tf.cp Tr.cp).symm
              _ = Tδ.cp.choi := congrArg CPMap.choi (hcomp_add i)
          exact htot ▸ hfin
        exact hsum
      have hmaj :
          SigmaMon.ChoiSum.HasSum
            (fun i =>
              Superoperator.comp (x i)
                (Superoperator.tensor δ
                  (Superoperator.identity (n + 2))))
            (Superoperator.comp s
              (Superoperator.tensor δ
                (Superoperator.identity (n + 2)))) :=
        SigmaMon.ChoiSum.comp_right
          (Superoperator.tensor δ (Superoperator.identity (n + 2))) h
      have hflat :
          SigmaMon.ChoiSum.HasSum F
            (Superoperator.comp s
              (Superoperator.tensor δ
                (Superoperator.identity (n + 2)))) := by
        exact
          (SigmaMon.superoperatorPartialCountableSum.flatten
              (fun i b => F ⟨i, b⟩)
              (Superoperator.comp s
                (Superoperator.tensor δ
                  (Superoperator.identity (n + 2))))).mpr
            ⟨fun i =>
              Superoperator.comp (x i)
                (Superoperator.tensor δ
                  (Superoperator.identity (n + 2))),
              hrow, hmaj⟩
      -- Target family is the `true` Bool-slice.
      let S : Set (Σ _ : ι, Bool) := {p | p.2 = true}
      obtain ⟨Ψ, hΨ⟩ := SigmaMon.ChoiSum.subfamily_hasSum hflat S
      let e : ι ≃ S :=
        { toFun := fun i => ⟨⟨i, true⟩, rfl⟩
          invFun := fun p => p.1.1
          left_inv := fun i => rfl
          right_inv := by
            rintro ⟨⟨i, b⟩, hb⟩
            -- `hb : (⟨i, b⟩ : Σ _, Bool).2 = true`
            change b = true at hb
            subst hb
            rfl }
      have hre :
          SigmaMon.ChoiSum.HasSum
            (fun i => F (e i)) Ψ :=
        (SigmaMon.ChoiSum.reindex e (fun p : S => F p) Ψ).mpr hΨ
      refine ⟨Ψ, ?_⟩
      change SigmaMon.ChoiSum.HasSum
          (fun i =>
            Superoperator.comp (x i)
              (Superoperator.tensor (f i)
                (Superoperator.identity (n + 2))))
          Ψ
      convert hre using 1
      funext i
      rfl

@[simp]
theorem representable_obj (A n : ℕ) :
    ((representable A).obj n).Carrier = Superoperator n A :=
  rfl

@[simp]
theorem representable_act {A m n : ℕ}
    (x : Superoperator n A) (f : Superoperator m n) :
    (representable A).act x f = Superoperator.comp x f :=
  rfl

/-- Yoneda sends a base superoperator to postcomposition by that map. -/
noncomputable def yonedaMap {A B : ℕ} (f : Superoperator A B) :
    Hom (representable A) (representable B) where
  app := fun _ x => Superoperator.comp f x
  map_zero := fun _ => Superoperator.comp_zero_right f
  map_sum := by
    intro ι _ n x s h
    exact SigmaMon.ChoiSum.comp_left f h
  naturality := by
    intro m n x g
    exact Superoperator.comp_assoc f x g

@[simp]
theorem yonedaMap_app {A B n : ℕ} (f : Superoperator A B)
    (x : Superoperator n A) :
    (yonedaMap f).app n x = Superoperator.comp f x :=
  rfl

@[simp]
theorem yonedaMap_id (A : ℕ) :
    yonedaMap (Superoperator.identity A) = Hom.id (representable A) := by
  ext n x
  exact Superoperator.identity_comp x

@[simp]
theorem yonedaMap_comp {A B C : ℕ}
    (g : Superoperator B C) (f : Superoperator A B) :
    yonedaMap (Superoperator.comp g f) =
      Hom.comp (yonedaMap g) (yonedaMap f) := by
  ext n x
  exact (Superoperator.comp_assoc g f x).symm

/-- A module element determines a natural map out of a representable. -/
def fromElement (M : Module.{u}) {A : ℕ} (x : (M.obj A).Carrier) :
    Hom (representable A) M where
  app := fun _ f => M.act x f
  map_zero := fun _ => M.act_zero_map x
  map_sum := by
    intro ι _ n f s h
    exact M.act_sum_map x h
  naturality := by
    intro m n f g
    exact (M.act_comp x f g).symm

/-- Evaluation of a natural map at the identity element. -/
def toElement (M : Module.{u}) {A : ℕ}
    (η : Hom (representable A) M) : (M.obj A).Carrier :=
  η.app A (Superoperator.identity A)

@[simp]
theorem toElement_fromElement (M : Module.{u}) {A : ℕ}
    (x : (M.obj A).Carrier) :
    toElement M (fromElement M x) = x :=
  M.act_id x

@[simp]
theorem fromElement_toElement (M : Module.{u}) {A : ℕ}
    (η : Hom (representable A) M) :
    fromElement M (toElement M η) = η := by
  ext n f
  change M.act (η.app A (Superoperator.identity A)) f = η.app n f
  rw [show M.act (η.app A (Superoperator.identity A)) f =
      η.app n
        ((representable A).act (Superoperator.identity A) f) from
        (η.naturality (Superoperator.identity A) f).symm]
  have hf :
      (representable A).act (Superoperator.identity A) f = f :=
    Superoperator.identity_comp f
  exact congrArg (η.app n) hf

/-- The concrete enriched Yoneda correspondence. -/
def yonedaEquiv (M : Module.{u}) (A : ℕ) :
    Hom (representable A) M ≃ (M.obj A).Carrier where
  toFun := toElement M
  invFun := fromElement M
  left_inv := fromElement_toElement M
  right_inv := toElement_fromElement M

@[simp]
theorem yonedaEquiv_apply (M : Module.{u}) (A : ℕ)
    (η : Hom (representable A) M) :
    yonedaEquiv M A η = η.app A (Superoperator.identity A) :=
  rfl

@[simp]
theorem yonedaEquiv_symm_apply (M : Module.{u}) (A : ℕ)
    (x : (M.obj A).Carrier) (n : ℕ) (f : Superoperator n A) :
    ((yonedaEquiv M A).symm x).app n f = M.act x f :=
  rfl

end SuperoperatorModule

end QLambda.Domain.Presheaf
