/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.OmegaMapFunctionSpaceInstances
import QLambda.Domain.OmegaCompleteInstances

/-!
# Cartesian closed structure on ω-continuous maps
-/

namespace QLambda.Domain

universe u v w

namespace OmegaMap

section ClosedStructure

variable
  {A : Type u} {B : Type v} {X : Type w}
  [PartialOrder A] [OmegaComplete A]
  [PartialOrder B] [OmegaComplete B]
  [PartialOrder X] [OmegaComplete X]

def fst : OmegaMap (A × B) A where
  toFun := Prod.fst
  monotone := fun _ _ h => h.1
  map_ωSup _ _ := rfl

def snd : OmegaMap (A × B) B where
  toFun := Prod.snd
  monotone := fun _ _ h => h.2
  map_ωSup _ _ := rfl

def pair (f : OmegaMap X A) (g : OmegaMap X B) :
    OmegaMap X (A × B) where
  toFun x := (f x, g x)
  monotone := fun h₁ h₂ h => ⟨f.monotone h, g.monotone h⟩
  map_ωSup c hc := by
    apply Prod.ext
    · exact f.map_ωSup c hc
    · exact g.map_ωSup c hc

/-- Evaluation is jointly ω-continuous.  The proof uses the diagonal
cofinality of a pair of increasing chains. -/
noncomputable def eval : OmegaMap (OmegaMap A B × A) B where
  toFun p := p.1 p.2
  monotone := by
    intro p q hpq
    exact (hpq.1 p.2).trans (q.1.monotone hpq.2)
  map_ωSup := by
    intro c hc
    let fs : ℕ → OmegaMap A B := fun n => (c n).1
    let xs : ℕ → A := fun n => (c n).2
    have hfs : Monotone fs := fun _ _ h => (hc h).1
    have hxs : Monotone xs := fun _ _ h => (hc h).2
    change
      OmegaComplete.ωSup
          (fun n => fs n (OmegaComplete.ωSup xs hxs))
          (fun _ _ h => hfs h _) =
        OmegaComplete.ωSup (fun n => fs n (xs n))
          (fun a b hab =>
            (hfs hab (xs a)).trans ((fs b).monotone (hxs hab)))
    apply le_antisymm
    · apply OmegaComplete.ωSup_le
      intro n
      rw [(fs n).map_ωSup xs hxs]
      apply OmegaComplete.ωSup_le
      intro m
      let k := max n m
      have hnk : n ≤ k := Nat.le_max_left _ _
      have hmk : m ≤ k := Nat.le_max_right _ _
      calc
        fs n (xs m) ≤ fs k (xs m) := hfs hnk _
        _ ≤ fs k (xs k) := (fs k).monotone (hxs hmk)
        _ ≤ OmegaComplete.ωSup (fun j => fs j (xs j))
            (fun a b hab =>
              (hfs hab (xs a)).trans ((fs b).monotone (hxs hab))) :=
          OmegaComplete.le_ωSup (fun j => fs j (xs j))
            (fun a b hab =>
              (hfs hab (xs a)).trans ((fs b).monotone (hxs hab))) k
    · apply OmegaComplete.ωSup_le
      intro n
      calc
        fs n (xs n) ≤ fs n (OmegaComplete.ωSup xs hxs) :=
          (fs n).monotone (OmegaComplete.le_ωSup xs hxs n)
        _ ≤ OmegaComplete.ωSup
            (fun j => fs j (OmegaComplete.ωSup xs hxs))
            (fun _ _ h => hfs h _) :=
          OmegaComplete.le_ωSup
            (fun j => fs j (OmegaComplete.ωSup xs hxs))
            (fun _ _ h => hfs h _) n

noncomputable def curry (f : OmegaMap (X × A) B) :
    OmegaMap X (OmegaMap A B) where
  toFun x :=
    { toFun := fun a => f (x, a)
      monotone := fun _ _ h => f.monotone ⟨le_rfl, h⟩
      map_ωSup := by
        intro c hc
        let d : ℕ → X × A := fun n => (x, c n)
        have hd : Monotone d := fun _ _ h => ⟨le_rfl, hc h⟩
        have hs :
            OmegaComplete.ωSup d hd =
              (x, OmegaComplete.ωSup c hc) := by
          apply Prod.ext
          · exact OmegaComplete.ωSup_const x
          · rfl
        rw [← hs, f.map_ωSup d hd]
        }
  monotone := by
    intro x y hxy a
    exact f.monotone ⟨hxy, le_rfl⟩
  map_ωSup := by
    intro c hc
    apply OmegaMap.ext
    intro a
    rw [ωSup_apply]
    let d : ℕ → X × A := fun n => (c n, a)
    have hd : Monotone d := fun _ _ h => ⟨hc h, le_rfl⟩
    have hs :
        OmegaComplete.ωSup d hd =
          (OmegaComplete.ωSup c hc, a) := by
      apply Prod.ext
      · rfl
      · exact OmegaComplete.ωSup_const a
    change f (OmegaComplete.ωSup c hc, a) =
      OmegaComplete.ωSup (fun n => f (c n, a))
        (fun _ _ h => f.monotone ⟨hc h, le_rfl⟩)
    rw [← hs, f.map_ωSup d hd]

noncomputable def uncurry (f : OmegaMap X (OmegaMap A B)) :
    OmegaMap (X × A) B :=
  eval.comp (pair (f.comp fst) snd)

@[simp] theorem curry_apply (f : OmegaMap (X × A) B) (x : X) (a : A) :
    curry f x a = f (x, a) :=
  rfl

@[simp] theorem uncurry_apply (f : OmegaMap X (OmegaMap A B))
    (x : X) (a : A) :
    uncurry f (x, a) = f x a :=
  rfl

@[simp] theorem curry_uncurry (f : OmegaMap X (OmegaMap A B)) :
    curry (uncurry f) = f := by
  ext x a
  rfl

@[simp] theorem uncurry_curry (f : OmegaMap (X × A) B) :
    uncurry (curry f) = f := by
  ext p
  cases p
  rfl

end ClosedStructure

end OmegaMap

end QLambda.Domain
