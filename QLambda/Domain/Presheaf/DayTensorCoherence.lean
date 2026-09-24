/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.DayInternalHom

/-!
# Day tensor associators and coherence
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule
open Classical

namespace DayTensor

/-- The nested universal map underlying Day tensor reassociation. -/
noncomputable def associatorBilinear (M N P : Module) :
    Bilinear M N
      (dayInternalHom P (dayTensor M (dayTensor N P))) where
  app := fun {m n} x y =>
    { app := fun {k p} r z =>
        (dayTensor M (dayTensor N P)).act
          ((DayCoend.intro M (dayTensor N P)).app x
            ((DayCoend.intro N P).app y z))
          (Superoperator.comp (Superoperator.tensorAssociator m n p)
            (Superoperator.tensor r (Superoperator.identity p)))
      map_zero_left := by
        intro k p z
        change
          (dayTensor M (dayTensor N P)).act
            ((DayCoend.intro M (dayTensor N P)).app x
              ((DayCoend.intro N P).app y z))
            (Superoperator.comp (Superoperator.tensorAssociator m n p)
              (Superoperator.tensor (0 : Superoperator k (m * n))
                (Superoperator.identity p))) = 0
        rw [Superoperator.tensor_zero_left,
          Superoperator.comp_zero_right,
          (dayTensor M (dayTensor N P)).act_zero_map]
      map_zero_right := by
        intro k p r
        rw [(DayCoend.intro N P).map_zero_right,
          (DayCoend.intro M (dayTensor N P)).map_zero_right,
          (dayTensor M (dayTensor N P)).act_zero_element]
      map_sum_left := by
        intro ι _ k p r s z h
        apply (dayTensor M (dayTensor N P)).act_sum_map _
        exact SigmaMon.ChoiSum.comp_left _ <|
          SigmaMon.ChoiSum.tensor_hasSum_left h
            (Superoperator.identity p)
      map_sum_right := by
        intro ι _ k p r z s h
        exact (dayTensor M (dayTensor N P)).act_sum_element _ <|
          (DayCoend.intro M (dayTensor N P)).map_sum_right x <|
            (DayCoend.intro N P).map_sum_right y h
      naturality := by
        intro k' k p' p r z f g
        change Superoperator k (m * n) at r
        change
          (dayTensor M (dayTensor N P)).act
              ((DayCoend.intro M (dayTensor N P)).app x
                ((DayCoend.intro N P).app y (P.act z g)))
              (Superoperator.comp
                (Superoperator.tensorAssociator m n p')
                (Superoperator.tensor (Superoperator.comp r f)
                  (Superoperator.identity p'))) =
            (dayTensor M (dayTensor N P)).act
              ((dayTensor M (dayTensor N P)).act
                ((DayCoend.intro M (dayTensor N P)).app x
                  ((DayCoend.intro N P).app y z))
                (Superoperator.comp
                  (Superoperator.tensorAssociator m n p)
                  (Superoperator.tensor r (Superoperator.identity p))))
              (Superoperator.tensor f g)
        have hn := (DayCoend.intro N P).naturality y z
          (Superoperator.identity n) g
        simp only [N.act_id] at hn
        rw [hn]
        have hm := (DayCoend.intro M (dayTensor N P)).naturality x
          ((DayCoend.intro N P).app y z)
          (Superoperator.identity m)
          (Superoperator.tensor (Superoperator.identity n) g)
        simp only [M.act_id] at hm
        rw [hm,
          (dayTensor M (dayTensor N P)).act_comp,
          (dayTensor M (dayTensor N P)).act_comp]
        congr 1
        rw [Superoperator.comp_assoc,
          ← Superoperator.tensorAssociator_naturality
            (Superoperator.identity m) (Superoperator.identity n) g,
          ← Superoperator.comp_assoc]
        rw [← Superoperator.tensor_comp]
        simp
        rw [← Superoperator.comp_assoc,
          ← Superoperator.tensor_comp]
        simp }
  map_zero_left := by
    intro m n y
    apply Bilinear.ext
    intro k p r z
    change Superoperator k (m * n) at r
    change
      (dayTensor M (dayTensor N P)).act
          ((DayCoend.intro M (dayTensor N P)).app
            (0 : (M.obj m).Carrier)
            ((DayCoend.intro N P).app y z))
          (Superoperator.comp (Superoperator.tensorAssociator m n p)
            (Superoperator.tensor r (Superoperator.identity p))) = 0
    rw [(DayCoend.intro M (dayTensor N P)).map_zero_left,
      (dayTensor M (dayTensor N P)).act_zero_element]
  map_zero_right := by
    intro m n x
    apply Bilinear.ext
    intro k p r z
    change Superoperator k (m * n) at r
    change
      (dayTensor M (dayTensor N P)).act
          ((DayCoend.intro M (dayTensor N P)).app x
            ((DayCoend.intro N P).app
              (0 : (N.obj n).Carrier) z))
          (Superoperator.comp (Superoperator.tensorAssociator m n p)
            (Superoperator.tensor r (Superoperator.identity p))) = 0
    rw [(DayCoend.intro N P).map_zero_left,
      (DayCoend.intro M (dayTensor N P)).map_zero_right,
      (dayTensor M (dayTensor N P)).act_zero_element]
  map_sum_left := by
    intro ι _ m n x s y h
    intro k p r z
    exact (dayTensor M (dayTensor N P)).act_sum_element _ <|
      (DayCoend.intro M (dayTensor N P)).map_sum_left _ h
  map_sum_right := by
    intro ι _ m n x y s h
    intro k p r z
    exact (dayTensor M (dayTensor N P)).act_sum_element _ <|
      (DayCoend.intro M (dayTensor N P)).map_sum_right x <|
        (DayCoend.intro N P).map_sum_left z h
  naturality := by
    intro m' m n' n x y f g
    apply Bilinear.ext
    intro k p r z
    change Superoperator k (m' * n') at r
    simp only [dayInternalHom, DayInternalHom.module,
      DayInternalHom.precompose]
    have hn := (DayCoend.intro N P).naturality y z g
      (Superoperator.identity p)
    simp only [P.act_id] at hn
    rw [hn]
    have hm := (DayCoend.intro M (dayTensor N P)).naturality x
      ((DayCoend.intro N P).app y z) f
      (Superoperator.tensor g (Superoperator.identity p))
    rw [hm, (dayTensor M (dayTensor N P)).act_comp]
    congr 1
    rw [Superoperator.comp_assoc,
      ← Superoperator.tensorAssociator_naturality f g
        (Superoperator.identity p),
      ← Superoperator.comp_assoc]
    rw [← Superoperator.tensor_comp]
    simp

/-- Associator of the genuine Day tensor, obtained by two applications of
the coend universal property and currying. -/
noncomputable def associator (M N P : Module) :
    Hom (dayTensor (dayTensor M N) P)
      (dayTensor M (dayTensor N P)) :=
  DayCoend.lift
    (DayInternalHom.uncurry
      (DayCoend.lift (associatorBilinear M N P)))

@[simp]
theorem associator_intro_intro {M N P : Module}
    {m n p : ℕ} (x : (M.obj m).Carrier)
    (y : (N.obj n).Carrier) (z : (P.obj p).Carrier) :
    (associator M N P).app ((m * n) * p)
        ((DayCoend.intro (dayTensor M N) P).app
          ((DayCoend.intro M N).app x y) z) =
      (dayTensor M (dayTensor N P)).act
        ((DayCoend.intro M (dayTensor N P)).app x
          ((DayCoend.intro N P).app y z))
        (Superoperator.tensorAssociator m n p) := by
  change
    DayCoend.evaluate (dayTensor M (dayTensor N P))
      (DayInternalHom.uncurry
        (DayCoend.lift (associatorBilinear M N P)))
      ((DayCoend.intro (dayTensor M N) P).app
        ((DayCoend.intro M N).app x y) z) = _
  rw [DayCoend.evaluate_intro]
  change
    ((DayCoend.lift (associatorBilinear M N P)).app (m * n)
      ((DayCoend.intro M N).app x y)).app
        (Superoperator.identity (m * n)) z = _
  change
    (DayCoend.evaluate
      (dayInternalHom P (dayTensor M (dayTensor N P)))
      (associatorBilinear M N P)
      ((DayCoend.intro M N).app x y)).app
        (Superoperator.identity (m * n)) z = _
  rw [DayCoend.evaluate_intro]
  change
    (dayTensor M (dayTensor N P)).act
      ((DayCoend.intro M (dayTensor N P)).app x
        ((DayCoend.intro N P).app y z))
      (Superoperator.comp (Superoperator.tensorAssociator m n p)
        (Superoperator.tensor (Superoperator.identity (m * n))
          (Superoperator.identity p))) =
    _
  rw [Superoperator.tensor_identity, Superoperator.comp_identity]

/-- Inverse Day associator, expressed by the canonical symmetric-braided
path using forward associators. -/
noncomputable def associatorInv (M N P : Module) :
    Hom (dayTensor M (dayTensor N P))
      (dayTensor (dayTensor M N) P) :=
  Hom.comp (braiding P (dayTensor M N))
    (Hom.comp (associator P M N)
      (Hom.comp (braiding N (dayTensor P M))
        (Hom.comp (associator N P M)
          (braiding M (dayTensor N P)))))

@[simp]
theorem associatorInv_intro_intro {M N P : Module}
    {m n p : ℕ} (x : (M.obj m).Carrier)
    (y : (N.obj n).Carrier) (z : (P.obj p).Carrier) :
    (associatorInv M N P).app (m * (n * p))
        ((DayCoend.intro M (dayTensor N P)).app x
          ((DayCoend.intro N P).app y z)) =
      (dayTensor (dayTensor M N) P).act
        ((DayCoend.intro (dayTensor M N) P).app
          ((DayCoend.intro M N).app x y) z)
        (Superoperator.tensorAssociatorInv m n p) := by
  rw [associatorInv, Hom.comp_app, Hom.comp_app, Hom.comp_app,
    Hom.comp_app, braiding_intro,
    (associator N P M).naturality, associator_intro_intro,
    (dayTensor N (dayTensor P M)).act_comp,
    (braiding N (dayTensor P M)).naturality, braiding_intro,
    (dayTensor (dayTensor P M) N).act_comp,
    (associator P M N).naturality, associator_intro_intro,
    (dayTensor P (dayTensor M N)).act_comp,
    (braiding P (dayTensor M N)).naturality, braiding_intro,
    (dayTensor (dayTensor M N) P).act_comp,
    Superoperator.tensorAssociatorInv_braiding]

@[simp]
theorem braiding_involutive (M N : Module) :
    Hom.comp (braiding N M) (braiding M N) =
      Hom.id (dayTensor M N) := by
  apply hom_ext
  intro m n x y
  rw [Hom.comp_app, braiding_intro,
    (braiding N M).naturality, braiding_intro,
    (dayTensor M N).act_comp,
    Superoperator.tensorSwap_involutive,
    (dayTensor M N).act_id]
  rfl

/-- Extensionality for maps out of a left-associated triple Day tensor. -/
theorem hom_ext_nested_left {M N P L : Module.{0}}
    {f g : Hom (dayTensor (dayTensor M N) P) L}
    (h : ∀ m n p (x : (M.obj m).Carrier)
      (y : (N.obj n).Carrier) (z : (P.obj p).Carrier),
      f.app ((m * n) * p)
          ((DayCoend.intro (dayTensor M N) P).app
            ((DayCoend.intro M N).app x y) z) =
        g.app ((m * n) * p)
          ((DayCoend.intro (dayTensor M N) P).app
            ((DayCoend.intro M N).app x y) z)) :
    f = g := by
  apply (DayCoend.universalEquiv (dayTensor M N) P L).injective
  apply (DayInternalHom.curryEquiv (dayTensor M N) P L).injective
  apply hom_ext
  intro m n x y
  apply Bilinear.ext
  intro k p r z
  change Superoperator k (m * n) at r
  change
    f.app (k * p)
        ((DayCoend.intro (dayTensor M N) P).app
          ((dayTensor M N).act ((DayCoend.intro M N).app x y) r) z) =
      g.app (k * p)
        ((DayCoend.intro (dayTensor M N) P).app
          ((dayTensor M N).act ((DayCoend.intro M N).app x y) r) z)
  have hi := (DayCoend.intro (dayTensor M N) P).naturality
    ((DayCoend.intro M N).app x y) z r
    (Superoperator.identity p)
  simp only [P.act_id] at hi
  rw [hi, f.naturality, g.naturality, h]

/-- Extensionality for maps out of a right-associated triple Day tensor. -/
theorem hom_ext_nested_right {M N P L : Module.{0}}
    {f g : Hom (dayTensor M (dayTensor N P)) L}
    (h : ∀ m n p (x : (M.obj m).Carrier)
      (y : (N.obj n).Carrier) (z : (P.obj p).Carrier),
      f.app (m * (n * p))
          ((DayCoend.intro M (dayTensor N P)).app x
            ((DayCoend.intro N P).app y z)) =
        g.app (m * (n * p))
          ((DayCoend.intro M (dayTensor N P)).app x
            ((DayCoend.intro N P).app y z))) :
    f = g := by
  have hs :
      Hom.comp f (braiding (dayTensor N P) M) =
        Hom.comp g (braiding (dayTensor N P) M) := by
    apply hom_ext_nested_left
    intro n p m y z x
    rw [Hom.comp_app, Hom.comp_app, braiding_intro,
      f.naturality, g.naturality, h]
  have hs' := congrArg
    (fun q => Hom.comp q (braiding M (dayTensor N P))) hs
  rw [← Hom.comp_assoc, braiding_involutive, Hom.comp_id] at hs'
  rw [← Hom.comp_assoc, braiding_involutive, Hom.comp_id] at hs'
  exact hs'

/-- Extensionality for maps out of a fully left-associated fourfold Day
tensor. -/
theorem hom_ext_nested_four {M N P Q L : Module.{0}}
    {f g : Hom
      (dayTensor (dayTensor (dayTensor M N) P) Q) L}
    (h : ∀ m n p q (x : (M.obj m).Carrier)
      (y : (N.obj n).Carrier) (z : (P.obj p).Carrier)
      (w : (Q.obj q).Carrier),
      f.app (((m * n) * p) * q)
          ((DayCoend.intro (dayTensor (dayTensor M N) P) Q).app
            ((DayCoend.intro (dayTensor M N) P).app
              ((DayCoend.intro M N).app x y) z) w) =
        g.app (((m * n) * p) * q)
          ((DayCoend.intro (dayTensor (dayTensor M N) P) Q).app
            ((DayCoend.intro (dayTensor M N) P).app
              ((DayCoend.intro M N).app x y) z) w)) :
    f = g := by
  apply (DayCoend.universalEquiv
    (dayTensor (dayTensor M N) P) Q L).injective
  apply (DayInternalHom.curryEquiv
    (dayTensor (dayTensor M N) P) Q L).injective
  apply hom_ext_nested_left
  intro m n p x y z
  apply Bilinear.ext
  intro k q r w
  change Superoperator k ((m * n) * p) at r
  change
    f.app (k * q)
        ((DayCoend.intro (dayTensor (dayTensor M N) P) Q).app
          ((dayTensor (dayTensor M N) P).act
            ((DayCoend.intro (dayTensor M N) P).app
              ((DayCoend.intro M N).app x y) z) r) w) =
      g.app (k * q)
        ((DayCoend.intro (dayTensor (dayTensor M N) P) Q).app
          ((dayTensor (dayTensor M N) P).act
            ((DayCoend.intro (dayTensor M N) P).app
              ((DayCoend.intro M N).app x y) z) r) w)
  have hi :=
    (DayCoend.intro (dayTensor (dayTensor M N) P) Q).naturality
      ((DayCoend.intro (dayTensor M N) P).app
        ((DayCoend.intro M N).app x y) z) w r
      (Superoperator.identity q)
  simp only [Q.act_id] at hi
  rw [hi, f.naturality, g.naturality, h]

@[simp]
theorem associator_hom_inv (M N P : Module) :
    Hom.comp (associator M N P) (associatorInv M N P) =
      Hom.id (dayTensor M (dayTensor N P)) := by
  apply hom_ext_nested_right
  intro m n p x y z
  rw [Hom.comp_app, associatorInv_intro_intro,
    (associator M N P).naturality, associator_intro_intro,
    (dayTensor M (dayTensor N P)).act_comp,
    Superoperator.tensorAssociator_hom_inv,
    (dayTensor M (dayTensor N P)).act_id]
  rfl

@[simp]
theorem associator_inv_hom (M N P : Module) :
    Hom.comp (associatorInv M N P) (associator M N P) =
      Hom.id (dayTensor (dayTensor M N) P) := by
  apply hom_ext_nested_left
  intro m n p x y z
  rw [Hom.comp_app, associator_intro_intro,
    (associatorInv M N P).naturality, associatorInv_intro_intro,
    (dayTensor (dayTensor M N) P).act_comp,
    Superoperator.tensorAssociator_inv_hom,
    (dayTensor (dayTensor M N) P).act_id]
  rfl

/-- Associator isomorphism for Day convolution. -/
noncomputable def associatorIso (M N P : Module) :
    Iso (dayTensor (dayTensor M N) P)
      (dayTensor M (dayTensor N P)) where
  hom := associator M N P
  inv := associatorInv M N P
  hom_inv := associator_hom_inv M N P
  inv_hom := associator_inv_hom M N P

theorem associator_naturality
    {M M' N N' P P' : Module}
    (f : Hom M M') (g : Hom N N') (h : Hom P P') :
    Hom.comp (associator M' N' P')
        (map (map f g) h) =
      Hom.comp (map f (map g h))
        (associator M N P) := by
  apply hom_ext_nested_left
  intro m n p x y z
  rw [Hom.comp_app, Hom.comp_app, map_intro, map_intro,
    associator_intro_intro, associator_intro_intro,
    (map f (map g h)).naturality, map_intro, map_intro]

theorem braiding_naturality
    {M M' N N' : Module} (f : Hom M M') (g : Hom N N') :
    Hom.comp (braiding M' N') (map f g) =
      Hom.comp (map g f) (braiding M N) := by
  apply hom_ext
  intro m n x y
  rw [Hom.comp_app, Hom.comp_app, map_intro, braiding_intro,
    braiding_intro, (map g f).naturality, map_intro]

theorem pentagon (M N P Q : Module) :
    Hom.comp (associator M N (dayTensor P Q))
        (associator (dayTensor M N) P Q) =
      Hom.comp (map (Hom.id M) (associator N P Q))
        (Hom.comp (associator M (dayTensor N P) Q)
          (map (associator M N P) (Hom.id Q))) := by
  apply hom_ext_nested_four
  intro m n p q x y z w
  rw [Hom.comp_app,
    associator_intro_intro,
    (associator M N (dayTensor P Q)).naturality,
    associator_intro_intro,
    (dayTensor M (dayTensor N (dayTensor P Q))).act_comp,
    Hom.comp_app, Hom.comp_app, map_intro, associator_intro_intro,
    Hom.id_app]
  have hi :=
    (DayCoend.intro (dayTensor M (dayTensor N P)) Q).naturality
      ((DayCoend.intro M (dayTensor N P)).app x
        ((DayCoend.intro N P).app y z)) w
      (Superoperator.tensorAssociator m n p)
      (Superoperator.identity q)
  simp only [Q.act_id] at hi
  rw [hi,
    (associator M (dayTensor N P) Q).naturality,
    associator_intro_intro,
    (dayTensor M (dayTensor (dayTensor N P) Q)).act_comp,
    (map (Hom.id M) (associator N P Q)).naturality,
    map_intro, associator_intro_intro, Hom.id_app]
  have hj :=
    (DayCoend.intro M (dayTensor N (dayTensor P Q))).naturality
      x ((DayCoend.intro N (dayTensor P Q)).app y
        ((DayCoend.intro P Q).app z w))
      (Superoperator.identity m)
      (Superoperator.tensorAssociator n p q)
  simp only [M.act_id] at hj
  rw [hj,
    (dayTensor M (dayTensor N (dayTensor P Q))).act_comp,
    Superoperator.tensor_pentagon]

theorem triangle (M N : Module) :
    Hom.comp (map (Hom.id M) (leftUnitor N))
        (associator M dayTensorUnit N) =
      map (rightUnitor M) (Hom.id N) := by
  apply hom_ext_nested_left
  intro m u n x q z
  rw [Hom.comp_app, associator_intro_intro,
    (map (Hom.id M) (leftUnitor N)).naturality,
    map_intro]
  change Superoperator u 1 at q
  rw [leftUnitor_intro, Hom.id_app,
    map_intro, rightUnitor_intro, Hom.id_app]
  have hl :=
    (DayCoend.intro M N).naturality x z
      (Superoperator.identity m)
      (Superoperator.comp (Superoperator.tensorLeftUnitor n)
        (Superoperator.tensor q (Superoperator.identity n)))
  simp only [M.act_id] at hl
  rw [hl, (dayTensor M N).act_comp]
  have hr :=
    (DayCoend.intro M N).naturality x z
      (Superoperator.comp (Superoperator.tensorRightUnitor m)
        (Superoperator.tensor (Superoperator.identity m) q))
      (Superoperator.identity n)
  simp only [N.act_id] at hr
  rw [hr, Superoperator.tensor_triangle_naturality]

/-- Right-unitor / associator coherence: `(id ⊗ ρ) ∘ α = ρ`. -/
theorem rightUnitor_associator (M N : Module) :
    Hom.comp (map (Hom.id M) (rightUnitor N))
        (associator M N dayTensorUnit) =
      rightUnitor (dayTensor M N) := by
  apply hom_ext_nested_left
  intro m n u x y q
  rw [Hom.comp_app, associator_intro_intro,
    (map (Hom.id M) (rightUnitor N)).naturality, map_intro]
  change Superoperator u 1 at q
  rw [rightUnitor_intro, Hom.id_app, rightUnitor_intro]
  have hl :=
    (DayCoend.intro M N).naturality x y
      (Superoperator.identity m)
      (Superoperator.comp (Superoperator.tensorRightUnitor n)
        (Superoperator.tensor (Superoperator.identity n) q))
  simp only [M.act_id] at hl
  rw [hl, (dayTensor M N).act_comp]
  congr 1
  exact Superoperator.tensor_rightUnitor_associator_naturality m n q

/-- Inverse form: `ρ ∘ α⁻¹ = id ⊗ ρ`. -/
theorem rightUnitor_associatorInv (M N : Module) :
    Hom.comp (rightUnitor (dayTensor M N))
        (associatorInv M N dayTensorUnit) =
      map (Hom.id M) (rightUnitor N) := by
  have h :=
    congrArg (fun g => Hom.comp g (associatorInv M N dayTensorUnit))
      (rightUnitor_associator M N)
  -- From `(id ⊗ ρ) ∘ α ∘ α⁻¹ = ρ ∘ α⁻¹`, reverse to start from `ρ ∘ α⁻¹`.
  refine Eq.trans h.symm ?_
  refine Eq.trans (Hom.comp_assoc _ _ _) ?_
  refine Eq.trans
    (congrArg (Hom.comp (map (Hom.id M) (rightUnitor N)))
      (associator_hom_inv M N dayTensorUnit)) ?_
  exact Hom.comp_id _

theorem hexagon (M N P : Module) :
    Hom.comp (braiding M (dayTensor N P))
        (associator M N P) =
      Hom.comp (associatorInv N P M)
        (Hom.comp (map (Hom.id N) (braiding M P))
          (Hom.comp (associator N M P)
            (map (braiding M N) (Hom.id P)))) := by
  apply hom_ext_nested_left
  intro m n p x y z
  rw [Hom.comp_app, associator_intro_intro,
    (braiding M (dayTensor N P)).naturality, braiding_intro,
    (dayTensor (dayTensor N P) M).act_comp,
    Hom.comp_app, Hom.comp_app, Hom.comp_app,
    map_intro, braiding_intro, Hom.id_app]
  have h₁ :=
    (DayCoend.intro (dayTensor N M) P).naturality
      ((DayCoend.intro N M).app y x) z
      (Superoperator.tensorSwap m n)
      (Superoperator.identity p)
  simp only [P.act_id] at h₁
  rw [h₁, (associator N M P).naturality,
    associator_intro_intro,
    (dayTensor N (dayTensor M P)).act_comp,
    (map (Hom.id N) (braiding M P)).naturality,
    map_intro, braiding_intro, Hom.id_app]
  have h₂ :=
    (DayCoend.intro N (dayTensor P M)).naturality y
      ((DayCoend.intro P M).app z x)
      (Superoperator.identity n)
      (Superoperator.tensorSwap m p)
  simp only [N.act_id] at h₂
  rw [h₂, (dayTensor N (dayTensor P M)).act_comp,
    (associatorInv N P M).naturality,
    associatorInv_intro_intro,
    (dayTensor (dayTensor N P) M).act_comp,
    Superoperator.tensor_hexagon]

/-- Inverse to the left Day unitor. -/
noncomputable def leftUnitorInv (M : Module) :
    Hom M (dayTensor dayTensorUnit M) where
  app := fun n x =>
    (dayTensor dayTensorUnit M).act
      ((DayCoend.intro dayTensorUnit M).app
        (Superoperator.identity 1) x)
      (Superoperator.tensorLeftUnitorInv n)
  map_zero := by
    intro n
    change
      (dayTensor dayTensorUnit M).act
        ((DayCoend.intro dayTensorUnit M).app
          (show (dayTensorUnit.obj 1).Carrier from
            Superoperator.identity 1)
          (0 : (M.obj n).Carrier))
        (Superoperator.tensorLeftUnitorInv n) = 0
    rw [(DayCoend.intro dayTensorUnit M).map_zero_right,
      (dayTensor dayTensorUnit M).act_zero_element]
  map_sum := by
    intro ι _ n x s h
    exact (dayTensor dayTensorUnit M).act_sum_element _ <|
      (DayCoend.intro dayTensorUnit M).map_sum_right
        (Superoperator.identity 1) h
  naturality := by
    intro m n x f
    have hi := (DayCoend.intro dayTensorUnit M).naturality
      (Superoperator.identity 1) x
      (Superoperator.identity 1) f
    change
      (DayCoend.intro dayTensorUnit M).app
          (Superoperator.comp (Superoperator.identity 1)
            (Superoperator.identity 1)) (M.act x f) =
        (dayTensor dayTensorUnit M).act
          ((DayCoend.intro dayTensorUnit M).app
            (Superoperator.identity 1) x)
          (Superoperator.tensor (Superoperator.identity 1) f) at hi
    rw [Superoperator.identity_comp] at hi
    rw [hi, (dayTensor dayTensorUnit M).act_comp,
      (dayTensor dayTensorUnit M).act_comp,
      Superoperator.tensorLeftUnitorInv_naturality]

/-- Inverse to the right Day unitor. -/
noncomputable def rightUnitorInv (M : Module) :
    Hom M (dayTensor M dayTensorUnit) where
  app := fun n x =>
    (dayTensor M dayTensorUnit).act
      ((DayCoend.intro M dayTensorUnit).app x
        (Superoperator.identity 1))
      (Superoperator.tensorRightUnitorInv n)
  map_zero := by
    intro n
    change
      (dayTensor M dayTensorUnit).act
        ((DayCoend.intro M dayTensorUnit).app
          (0 : (M.obj n).Carrier)
          (show (dayTensorUnit.obj 1).Carrier from
            Superoperator.identity 1))
        (Superoperator.tensorRightUnitorInv n) = 0
    rw [(DayCoend.intro M dayTensorUnit).map_zero_left,
      (dayTensor M dayTensorUnit).act_zero_element]
  map_sum := by
    intro ι _ n x s h
    exact (dayTensor M dayTensorUnit).act_sum_element _ <|
      (DayCoend.intro M dayTensorUnit).map_sum_left
        (Superoperator.identity 1) h
  naturality := by
    intro m n x f
    have hi := (DayCoend.intro M dayTensorUnit).naturality x
      (Superoperator.identity 1) f
      (Superoperator.identity 1)
    change
      (DayCoend.intro M dayTensorUnit).app (M.act x f)
          (Superoperator.comp (Superoperator.identity 1)
            (Superoperator.identity 1)) =
        (dayTensor M dayTensorUnit).act
          ((DayCoend.intro M dayTensorUnit).app x
            (Superoperator.identity 1))
          (Superoperator.tensor f (Superoperator.identity 1)) at hi
    rw [Superoperator.identity_comp] at hi
    rw [hi, (dayTensor M dayTensorUnit).act_comp,
      (dayTensor M dayTensorUnit).act_comp,
      Superoperator.tensorRightUnitorInv_naturality]

@[simp]
theorem leftUnitor_hom_inv (M : Module) :
    Hom.comp (leftUnitor M) (leftUnitorInv M) = Hom.id M := by
  apply Hom.ext
  intro n x
  rw [Hom.comp_app, leftUnitorInv, (leftUnitor M).naturality,
    leftUnitor_intro, M.act_comp]
  simp only [Superoperator.tensor_identity,
    Superoperator.comp_identity,
    Superoperator.tensorLeftUnitor_hom_inv, M.act_id]
  rfl

@[simp]
theorem rightUnitor_hom_inv (M : Module) :
    Hom.comp (rightUnitor M) (rightUnitorInv M) = Hom.id M := by
  apply Hom.ext
  intro n x
  rw [Hom.comp_app, rightUnitorInv, (rightUnitor M).naturality,
    rightUnitor_intro, M.act_comp]
  simp only [Superoperator.tensor_identity,
    Superoperator.comp_identity,
    Superoperator.tensorRightUnitor_hom_inv, M.act_id]
  rfl

/-- Left-unitor isomorphism for Day convolution. -/
noncomputable def leftUnitorIso (M : Module) :
    Iso (dayTensor dayTensorUnit M) M where
  hom := leftUnitor M
  inv := leftUnitorInv M
  hom_inv := leftUnitor_hom_inv M
  inv_hom := by
    apply hom_ext
    intro m n q x
    change Superoperator m 1 at q
    rw [Hom.comp_app, leftUnitor_intro,
      (leftUnitorInv M).naturality]
    change Superoperator m 1 at q
    rw [leftUnitorInv, (dayTensor dayTensorUnit M).act_comp]
    rw [Superoperator.comp_assoc,
      Superoperator.tensorLeftUnitor_inv_hom,
      Superoperator.identity_comp]
    have hi := (DayCoend.intro dayTensorUnit M).naturality
      (Superoperator.identity 1) x q (Superoperator.identity n)
    change
      (DayCoend.intro dayTensorUnit M).app
          (Superoperator.comp (Superoperator.identity 1) q)
          (M.act x (Superoperator.identity n)) =
        (dayTensor dayTensorUnit M).act
          ((DayCoend.intro dayTensorUnit M).app
            (Superoperator.identity 1) x)
          (Superoperator.tensor q (Superoperator.identity n)) at hi
    simpa only [Superoperator.identity_comp, M.act_id,
      Hom.id_app] using hi.symm

/-- Right-unitor isomorphism for Day convolution. -/
noncomputable def rightUnitorIso (M : Module) :
    Iso (dayTensor M dayTensorUnit) M where
  hom := rightUnitor M
  inv := rightUnitorInv M
  hom_inv := rightUnitor_hom_inv M
  inv_hom := by
    apply hom_ext
    intro m n x q
    change Superoperator n 1 at q
    rw [Hom.comp_app, rightUnitor_intro,
      (rightUnitorInv M).naturality]
    change Superoperator n 1 at q
    rw [rightUnitorInv, (dayTensor M dayTensorUnit).act_comp]
    rw [Superoperator.comp_assoc,
      Superoperator.tensorRightUnitor_inv_hom,
      Superoperator.identity_comp]
    have hi := (DayCoend.intro M dayTensorUnit).naturality x
      (Superoperator.identity 1) (Superoperator.identity m) q
    change
      (DayCoend.intro M dayTensorUnit).app
          (M.act x (Superoperator.identity m))
          (Superoperator.comp (Superoperator.identity 1) q) =
        (dayTensor M dayTensorUnit).act
          ((DayCoend.intro M dayTensorUnit).app x
            (Superoperator.identity 1))
          (Superoperator.tensor (Superoperator.identity m) q) at hi
    simpa only [Superoperator.identity_comp, M.act_id,
      Hom.id_app] using hi.symm

/-- Braiding isomorphism for Day convolution. -/
noncomputable def braidingIso (M N : Module) :
    Iso (dayTensor M N) (dayTensor N M) where
  hom := braiding M N
  inv := braiding N M
  hom_inv := braiding_involutive N M
  inv_hom := braiding_involutive M N


end DayTensor

/-- Every index of a one-element `Fin` is zero. -/
theorem fin_val_eq_zero_of_card_one {d : ℕ} (hd : d = 1) (i : Fin d) :
    (i : ℕ) = 0 := by
  have : (i : ℕ) < 1 := hd ▸ i.isLt
  exact Nat.lt_one_iff.mp this

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

end SuperoperatorModule
end QLambda.Domain.Presheaf
