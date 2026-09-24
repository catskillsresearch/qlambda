/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.SuperoperatorModule

/-!
# Pointwise additive product of specialized modules
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u

/-! ## Additive product -/

/-- Product of partial-countable-sum fibers. -/
noncomputable def additiveProductFiber (X Y : Fiber.{u}) : Fiber.{u} where
  Carrier := X.Carrier × Y.Carrier
  zero := (0, 0)
  summation :=
    { HasSum := fun f s =>
        X.HasSum (fun i => (f i).1) s.1 ∧
          Y.HasSum (fun i => (f i).2) s.2
      unique := by
        intro ι _ f s t hs ht
        apply Prod.ext
        · exact X.summation.unique hs.1 ht.1
        · exact Y.summation.unique hs.2 ht.2
      empty := by
        constructor
        · convert X.summation.empty using 1
          rfl
        · convert Y.summation.empty using 1
          rfl
      singleton := fun s =>
        ⟨X.summation.singleton s.1, Y.summation.singleton s.2⟩
      remove_zero := by
        intro ι _ f a s hz
        constructor
        · intro h
          constructor
          · apply (X.summation.remove_zero
              (fun i => (f i).1) a s.1 ?_).mp h.1
            intro i hi
            exact congrArg Prod.fst (hz i hi)
          · apply (Y.summation.remove_zero
              (fun i => (f i).2) a s.2 ?_).mp h.2
            intro i hi
            exact congrArg Prod.snd (hz i hi)
        · intro h
          constructor
          · apply (X.summation.remove_zero
              (fun i => (f i).1) a s.1 ?_).mpr h.1
            intro i hi
            exact congrArg Prod.fst (hz i hi)
          · apply (Y.summation.remove_zero
              (fun i => (f i).2) a s.2 ?_).mpr h.2
            intro i hi
            exact congrArg Prod.snd (hz i hi)
      reindex := by
        intro ι κ _ _ e f s
        constructor <;> intro h
        · exact
            ⟨(X.summation.reindex e (fun i => (f i).1) s.1).mp h.1,
              (Y.summation.reindex e (fun i => (f i).2) s.2).mp h.2⟩
        · exact
            ⟨(X.summation.reindex e (fun i => (f i).1) s.1).mpr h.1,
              (Y.summation.reindex e (fun i => (f i).2) s.2).mpr h.2⟩
      flatten := by
        intro ι _ κ _ f s
        constructor
        · intro h
          obtain ⟨gx, hgx, hsx⟩ :=
            (X.summation.flatten (fun i j => (f i j).1) s.1).mp h.1
          obtain ⟨gy, hgy, hsy⟩ :=
            (Y.summation.flatten (fun i j => (f i j).2) s.2).mp h.2
          exact
            ⟨fun i => (gx i, gy i),
              fun i => ⟨hgx i, hgy i⟩, ⟨hsx, hsy⟩⟩
        · rintro ⟨g, hg, hs⟩
          exact
            ⟨(X.summation.flatten
                (fun i j => (f i j).1) s.1).mpr
                ⟨fun i => (g i).1, fun i => (hg i).1, hs.1⟩,
              (Y.summation.flatten
                (fun i j => (f i j).2) s.2).mpr
                ⟨fun i => (g i).2, fun i => (hg i).2, hs.2⟩⟩ }

/-- Pointwise additive product of specialized modules. -/
noncomputable def additiveProduct (M N : Module.{u}) : Module.{u} where
  obj n := additiveProductFiber (M.obj n) (N.obj n)
  act := fun x f => (M.act x.1 f, N.act x.2 f)
  act_zero_element := by
    intro m n f
    exact Prod.ext (M.act_zero_element f) (N.act_zero_element f)
  act_zero_map := by
    intro m n x
    exact Prod.ext (M.act_zero_map x.1) (N.act_zero_map x.2)
  act_id := by
    intro n x
    exact Prod.ext (M.act_id x.1) (N.act_id x.2)
  act_comp := by
    intro l m n x f g
    exact Prod.ext (M.act_comp x.1 f g) (N.act_comp x.2 f g)
  act_sum_element := by
    intro ι _ m n x s f h
    exact ⟨M.act_sum_element f h.1, N.act_sum_element f h.2⟩
  act_sum_map := by
    intro ι _ m n x f s h
    exact ⟨M.act_sum_map x.1 h, N.act_sum_map x.2 h⟩
  act_sum_from_one := by
    intro ι _ m x s f h
    obtain ⟨zM, hzM⟩ := M.act_sum_from_one f h.1
    obtain ⟨zN, hzN⟩ := N.act_sum_from_one f h.2
    exact ⟨(zM, zN), ⟨hzM, hzN⟩⟩
  act_sum_tensor_from_one := by
    intro ι _ m B x s f h
    obtain ⟨zM, hzM⟩ := M.act_sum_tensor_from_one f h.1
    obtain ⟨zN, hzN⟩ := N.act_sum_tensor_from_one f h.2
    exact ⟨(zM, zN), ⟨hzM, hzN⟩⟩

/-- First additive projection. -/
noncomputable def additiveFst (M N : Module.{u}) :
    Hom (additiveProduct M N) M where
  app := fun _ x => x.1
  map_zero := fun _ => rfl
  map_sum := fun h => h.1
  naturality := fun _ _ => rfl

/-- Second additive projection. -/
noncomputable def additiveSnd (M N : Module.{u}) :
    Hom (additiveProduct M N) N where
  app := fun _ x => x.2
  map_zero := fun _ => rfl
  map_sum := fun h => h.2
  naturality := fun _ _ => rfl

/-- Pairing into an additive product. -/
noncomputable def additivePair {L M N : Module.{u}}
    (f : Hom L M) (g : Hom L N) :
    Hom L (additiveProduct M N) where
  app := fun n x => (f.app n x, g.app n x)
  map_zero := by
    intro n
    exact Prod.ext (f.map_zero n) (g.map_zero n)
  map_sum := fun h => ⟨f.map_sum h, g.map_sum h⟩
  naturality := by
    intro m n x h
    exact Prod.ext (f.naturality x h) (g.naturality x h)

@[simp]
theorem additiveFst_pair {L M N : Module.{u}}
    (f : Hom L M) (g : Hom L N) :
    Hom.comp (additiveFst M N) (additivePair f g) = f := by
  ext
  rfl

@[simp]
theorem additiveSnd_pair {L M N : Module.{u}}
    (f : Hom L M) (g : Hom L N) :
    Hom.comp (additiveSnd M N) (additivePair f g) = g := by
  ext
  rfl

theorem additivePair_unique {L M N : Module.{u}}
    (h : Hom L (additiveProduct M N))
    (f : Hom L M) (g : Hom L N)
    (hf : Hom.comp (additiveFst M N) h = f)
    (hg : Hom.comp (additiveSnd M N) h = g) :
    h = additivePair f g := by
  ext n x
  apply Prod.ext
  · exact congrArg (fun k => k.app n x) hf
  · exact congrArg (fun k => k.app n x) hg

end SuperoperatorModule

end QLambda.Domain.Presheaf
