/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Generated

/-!
# Bilinear maps of specialized modules
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u v w

/-- A bilinear, action-preserving map of specialized modules. -/
structure Bilinear (M : Module.{u}) (N : Module.{v}) (L : Module.{w}) where
  app :
    {m n : ℕ} →
      (M.obj m).Carrier → (N.obj n).Carrier → (L.obj (m * n)).Carrier
  map_zero_left :
    ∀ {m n} (y : (N.obj n).Carrier), app (0 : (M.obj m).Carrier) y = 0
  map_zero_right :
    ∀ {m n} (x : (M.obj m).Carrier), app x (0 : (N.obj n).Carrier) = 0
  map_sum_left :
    ∀ {ι : Type} [Countable ι] {m n}
      {x : ι → (M.obj m).Carrier} {s : (M.obj m).Carrier}
      (y : (N.obj n).Carrier),
      (M.obj m).HasSum x s →
        (L.obj (m * n)).HasSum (fun i => app (x i) y) (app s y)
  map_sum_right :
    ∀ {ι : Type} [Countable ι] {m n}
      (x : (M.obj m).Carrier)
      {y : ι → (N.obj n).Carrier} {s : (N.obj n).Carrier},
      (N.obj n).HasSum y s →
        (L.obj (m * n)).HasSum (fun i => app x (y i)) (app x s)
  naturality :
    ∀ {m' m n' n}
      (x : (M.obj m).Carrier) (y : (N.obj n).Carrier)
      (f : Superoperator m' m) (g : Superoperator n' n),
      app (M.act x f) (N.act y g) =
        L.act (app x y) (Superoperator.tensor f g)

namespace Bilinear

@[ext]
theorem ext {M : Module.{u}} {N : Module.{v}} {L : Module.{w}}
    {b c : Bilinear M N L}
    (h : ∀ m n x y, @b.app m n x y = @c.app m n x y) :
    b = c := by
  cases b
  cases c
  congr
  funext m n x y
  exact h m n x y

end Bilinear

/-- Postcomposition of a bilinear map by a module morphism. -/
def Bilinear.postcomp {M : Module.{u}} {N : Module.{v}}
    {L : Module.{w}} {K : Module.{u}}
    (f : Hom L K) (b : Bilinear M N L) : Bilinear M N K where
  app := fun x y => f.app _ (b.app x y)
  map_zero_left := by
    intro m n y
    rw [b.map_zero_left, f.map_zero]
  map_zero_right := by
    intro m n x
    rw [b.map_zero_right, f.map_zero]
  map_sum_left := by
    intro ι _ m n xs s y h
    exact f.map_sum (b.map_sum_left y h)
  map_sum_right := by
    intro ι _ m n x ys s h
    exact f.map_sum (b.map_sum_right x h)
  naturality := by
    intro m' m n' n x y g h
    rw [b.naturality, f.naturality]

end SuperoperatorModule

end QLambda.Domain.Presheaf
