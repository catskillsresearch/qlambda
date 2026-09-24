/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.DayCoendSum

/-!
# Day tensor bifunctor, braiding, and unitors
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule
open Classical

namespace DayTensor

/-- Extensionality for maps out of a Day tensor: it is enough to check
coend generators. -/
theorem hom_ext {M N L : Module.{0}}
    {f g : Hom (dayTensor M N) L}
    (h : ∀ m n (x : (M.obj m).Carrier) (y : (N.obj n).Carrier),
      f.app (m * n) ((DayCoend.intro M N).app x y) =
        g.app (m * n) ((DayCoend.intro M N).app x y)) :
    f = g := by
  apply (DayCoend.universalEquiv M N L).injective
  apply Bilinear.ext
  intro m n x y
  exact h m n x y

/-- Bilinear map on generators induced by maps in both variables. -/
noncomputable def mapBilinear {M M' N N' : Module}
    (f : Hom M M') (g : Hom N N') :
    Bilinear M N (dayTensor M' N') where
  app := fun x y => (DayCoend.intro M' N').app (f.app _ x) (g.app _ y)
  map_zero_left := by
    intro m n y
    rw [f.map_zero]
    exact (DayCoend.intro M' N').map_zero_left _
  map_zero_right := by
    intro m n x
    rw [g.map_zero]
    exact (DayCoend.intro M' N').map_zero_right _
  map_sum_left := by
    intro ι _ m n x s y h
    exact (DayCoend.intro M' N').map_sum_left _
      (f.map_sum h)
  map_sum_right := by
    intro ι _ m n x y s h
    exact (DayCoend.intro M' N').map_sum_right _
      (g.map_sum h)
  naturality := by
    intro m' m n' n x y p q
    rw [f.naturality, g.naturality]
    exact (DayCoend.intro M' N').naturality
      (f.app m x) (g.app n y) p q

/-- Day tensor is a bifunctor on module morphisms. -/
noncomputable def map {M M' N N' : Module}
    (f : Hom M M') (g : Hom N N') :
    Hom (dayTensor M N) (dayTensor M' N') :=
  DayCoend.lift (mapBilinear f g)

@[simp]
theorem map_intro {M M' N N' : Module}
    (f : Hom M M') (g : Hom N N') {m n : ℕ}
    (x : (M.obj m).Carrier) (y : (N.obj n).Carrier) :
    (map f g).app (m * n) ((DayCoend.intro M N).app x y) =
      (DayCoend.intro M' N').app (f.app m x) (g.app n y) :=
  DayCoend.evaluate_intro (mapBilinear f g) x y

@[simp]
theorem map_id (M N : Module) :
    map (Hom.id M) (Hom.id N) = Hom.id (dayTensor M N) := by
  apply hom_ext
  intro m n x y
  rw [map_intro]
  rfl

@[simp]
theorem map_comp {M₀ M₁ M₂ N₀ N₁ N₂ : Module}
    (f₂ : Hom M₁ M₂) (f₁ : Hom M₀ M₁)
    (g₂ : Hom N₁ N₂) (g₁ : Hom N₀ N₁) :
    map (Hom.comp f₂ f₁) (Hom.comp g₂ g₁) =
      Hom.comp (map f₂ g₂) (map f₁ g₁) := by
  apply hom_ext
  intro m n x y
  simp only [map_intro, Hom.comp_app]

end DayTensor

/-- The Day tensor unit is the representable at the multiplicative unit. -/
noncomputable abbrev dayTensorUnit : Module :=
  representable 1

namespace DayTensor

/-- Generator-level bilinear map which exchanges the two Day factors. -/
noncomputable def braidingBilinear (M N : Module) :
    Bilinear M N (dayTensor N M) where
  app := fun {m n} x y =>
    (dayTensor N M).act ((DayCoend.intro N M).app y x)
      (Superoperator.tensorSwap m n)
  map_zero_left := by
    intro m n y
    rw [(DayCoend.intro N M).map_zero_right,
      (dayTensor N M).act_zero_element]
  map_zero_right := by
    intro m n x
    rw [(DayCoend.intro N M).map_zero_left,
      (dayTensor N M).act_zero_element]
  map_sum_left := by
    intro ι _ m n x s y h
    exact (dayTensor N M).act_sum_element _
      ((DayCoend.intro N M).map_sum_right y h)
  map_sum_right := by
    intro ι _ m n x y s h
    exact (dayTensor N M).act_sum_element _
      ((DayCoend.intro N M).map_sum_left x h)
  naturality := by
    intro m' m n' n x y f g
    rw [(DayCoend.intro N M).naturality, (dayTensor N M).act_comp,
      (dayTensor N M).act_comp,
      Superoperator.tensorSwap_naturality]

/-- Braiding of the genuine Day tensor. -/
noncomputable def braiding (M N : Module) :
    Hom (dayTensor M N) (dayTensor N M) :=
  DayCoend.lift (braidingBilinear M N)

@[simp]
theorem braiding_intro {M N : Module} {m n : ℕ}
    (x : (M.obj m).Carrier) (y : (N.obj n).Carrier) :
    (braiding M N).app (m * n) ((DayCoend.intro M N).app x y) =
      (dayTensor N M).act ((DayCoend.intro N M).app y x)
        (Superoperator.tensorSwap m n) :=
  DayCoend.evaluate_intro (braidingBilinear M N) x y

/-- Bilinear evaluation of the left Day unitor. -/
noncomputable def leftUnitorBilinear (M : Module) :
    Bilinear dayTensorUnit M M where
  app := fun {m n} q x =>
    M.act x
      (Superoperator.comp (Superoperator.tensorLeftUnitor n)
        (Superoperator.tensor q (Superoperator.identity n)))
  map_zero_left := by
    intro m n x
    change M.act x
      (Superoperator.comp (Superoperator.tensorLeftUnitor n)
        (Superoperator.tensor (0 : Superoperator m 1)
          (Superoperator.identity n))) = 0
    rw [Superoperator.tensor_zero_left,
      Superoperator.comp_zero_right, M.act_zero_map]
  map_zero_right := by
    intro m n q
    exact M.act_zero_element _
  map_sum_left := by
    intro ι _ m n q s x h
    apply M.act_sum_map x
    exact SigmaMon.ChoiSum.comp_left _ <|
      SigmaMon.ChoiSum.tensor_hasSum_left h (Superoperator.identity n)
  map_sum_right := by
    intro ι _ m n q x s h
    exact M.act_sum_element _ h
  naturality := by
    intro m' m n' n q x f g
    change Superoperator m 1 at q
    change
      M.act (M.act x g)
          (Superoperator.comp (Superoperator.tensorLeftUnitor n')
            (Superoperator.tensor (Superoperator.comp q f)
              (Superoperator.identity n'))) =
        M.act
          (M.act x
            (Superoperator.comp (Superoperator.tensorLeftUnitor n)
              (Superoperator.tensor q (Superoperator.identity n))))
          (Superoperator.tensor f g)
    rw [M.act_comp, M.act_comp]
    congr 1
    calc
      Superoperator.comp g
          (Superoperator.comp (Superoperator.tensorLeftUnitor n')
            (Superoperator.tensor (Superoperator.comp q f)
              (Superoperator.identity n'))) =
        Superoperator.comp (Superoperator.tensorLeftUnitor n)
          (Superoperator.tensor (Superoperator.comp q f) g) := by
            rw [Superoperator.comp_assoc,
              ← Superoperator.tensorLeftUnitor_naturality g,
              ← Superoperator.comp_assoc,
              ← Superoperator.tensor_comp]
            simp
      _ = Superoperator.comp
          (Superoperator.comp (Superoperator.tensorLeftUnitor n)
            (Superoperator.tensor q (Superoperator.identity n)))
          (Superoperator.tensor f g) := by
            rw [← Superoperator.comp_assoc,
              ← Superoperator.tensor_comp]
            simp

/-- Left unitor of the genuine Day tensor. -/
noncomputable def leftUnitor (M : Module) :
    Hom (dayTensor dayTensorUnit M) M :=
  DayCoend.lift (leftUnitorBilinear M)

@[simp]
theorem leftUnitor_intro {M : Module} {m n : ℕ}
    (q : Superoperator m 1) (x : (M.obj n).Carrier) :
    (leftUnitor M).app (m * n)
        ((DayCoend.intro dayTensorUnit M).app q x) =
      M.act x
        (Superoperator.comp (Superoperator.tensorLeftUnitor n)
          (Superoperator.tensor q (Superoperator.identity n))) :=
  DayCoend.evaluate_intro (leftUnitorBilinear M) q x

/-- Bilinear evaluation of the right Day unitor. -/
noncomputable def rightUnitorBilinear (M : Module) :
    Bilinear M dayTensorUnit M where
  app := fun {m n} x q =>
    M.act x
      (Superoperator.comp (Superoperator.tensorRightUnitor m)
        (Superoperator.tensor (Superoperator.identity m) q))
  map_zero_left := by
    intro m n q
    exact M.act_zero_element _
  map_zero_right := by
    intro m n x
    change M.act x
      (Superoperator.comp (Superoperator.tensorRightUnitor m)
        (Superoperator.tensor (Superoperator.identity m)
          (0 : Superoperator n 1))) = 0
    rw [Superoperator.tensor_zero_right,
      Superoperator.comp_zero_right, M.act_zero_map]
  map_sum_left := by
    intro ι _ m n x s q h
    exact M.act_sum_element _ h
  map_sum_right := by
    intro ι _ m n x q s h
    apply M.act_sum_map x
    exact SigmaMon.ChoiSum.comp_left _ <|
      SigmaMon.ChoiSum.tensor_hasSum_right (Superoperator.identity m) h
  naturality := by
    intro m' m n' n x q f g
    change Superoperator n 1 at q
    change
      M.act (M.act x f)
          (Superoperator.comp (Superoperator.tensorRightUnitor m')
            (Superoperator.tensor (Superoperator.identity m')
              (Superoperator.comp q g))) =
        M.act
          (M.act x
            (Superoperator.comp (Superoperator.tensorRightUnitor m)
              (Superoperator.tensor (Superoperator.identity m) q)))
          (Superoperator.tensor f g)
    rw [M.act_comp, M.act_comp]
    congr 1
    calc
      Superoperator.comp f
          (Superoperator.comp (Superoperator.tensorRightUnitor m')
            (Superoperator.tensor (Superoperator.identity m')
              (Superoperator.comp q g))) =
        Superoperator.comp (Superoperator.tensorRightUnitor m)
          (Superoperator.tensor f (Superoperator.comp q g)) := by
            rw [Superoperator.comp_assoc,
              ← Superoperator.tensorRightUnitor_naturality f,
              ← Superoperator.comp_assoc,
              ← Superoperator.tensor_comp]
            simp
      _ = Superoperator.comp
          (Superoperator.comp (Superoperator.tensorRightUnitor m)
            (Superoperator.tensor (Superoperator.identity m) q))
          (Superoperator.tensor f g) := by
            rw [← Superoperator.comp_assoc,
              ← Superoperator.tensor_comp]
            simp

/-- Right unitor of the genuine Day tensor. -/
noncomputable def rightUnitor (M : Module) :
    Hom (dayTensor M dayTensorUnit) M :=
  DayCoend.lift (rightUnitorBilinear M)

@[simp]
theorem rightUnitor_intro {M : Module} {m n : ℕ}
    (x : (M.obj m).Carrier) (q : Superoperator n 1) :
    (rightUnitor M).app (m * n)
        ((DayCoend.intro M dayTensorUnit).app x q) =
      M.act x
        (Superoperator.comp (Superoperator.tensorRightUnitor m)
          (Superoperator.tensor (Superoperator.identity m) q)) :=
  DayCoend.evaluate_intro (rightUnitorBilinear M) x q

end DayTensor

end SuperoperatorModule
end QLambda.Domain.Presheaf
