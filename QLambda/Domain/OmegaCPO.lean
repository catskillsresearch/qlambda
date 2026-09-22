/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints

/-!
# ω-complete partial orders and pointed fixed points

This is the domain-theoretic foundation of the typed linear calculus.  It is
independent of valuation powerdomains, ωQVA, and the Jung--Tix problem.
-/

namespace QLambda.Domain

universe u v w

/-- A partial order with suprema of increasing `ℕ`-chains.  Pointedness is
separate: only least-fixed-point constructions require `OrderBot`. -/
class OmegaComplete (D : Type u) [PartialOrder D] where
  ωSup : (c : ℕ → D) → Monotone c → D
  le_ωSup : ∀ (c : ℕ → D) (hc : Monotone c) (n : ℕ), c n ≤ ωSup c hc
  ωSup_le : ∀ (c : ℕ → D) (hc : Monotone c) (x : D),
    (∀ n, c n ≤ x) → ωSup c hc ≤ x

/-- Complete lattices are, in particular, pointed ωCPOs. -/
noncomputable instance (D : Type u) [CompleteLattice D] : OmegaComplete D where
  ωSup c _ := ⨆ n, c n
  le_ωSup c _ n := le_iSup c n
  ωSup_le _ _ _ h := iSup_le h

namespace OmegaComplete

variable {D : Type u} [PartialOrder D] [OmegaComplete D]

theorem ωSup_unique (c : ℕ → D) (hc : Monotone c) {x : D}
    (hupper : ∀ n, c n ≤ x) (hleast : ∀ y, (∀ n, c n ≤ y) → x ≤ y) :
    OmegaComplete.ωSup c hc = x := by
  apply le_antisymm
  · exact OmegaComplete.ωSup_le c hc x hupper
  · exact hleast _ (OmegaComplete.le_ωSup c hc)

theorem ωSup_mono {c d : ℕ → D} (hc : Monotone c) (hd : Monotone d)
    (hcd : ∀ n, c n ≤ d n) :
    OmegaComplete.ωSup c hc ≤ OmegaComplete.ωSup d hd := by
  apply OmegaComplete.ωSup_le
  intro n
  exact (hcd n).trans (OmegaComplete.le_ωSup d hd n)

theorem ωSup_const (x : D) :
    OmegaComplete.ωSup (fun _ : ℕ => x) monotone_const = x := by
  apply ωSup_unique
  · exact fun _ => le_rfl
  · intro y hy
    exact hy 0

end OmegaComplete

/-- Products of ωCPOs carry the pointwise ωCPO structure. -/
noncomputable instance instOmegaCompleteProd
    {D : Type u} {E : Type v}
    [PartialOrder D] [OmegaComplete D]
    [PartialOrder E] [OmegaComplete E] :
    OmegaComplete (D × E) where
  ωSup c hc :=
    (OmegaComplete.ωSup (fun n => (c n).1)
      (fun _ _ h => (hc h).1),
    OmegaComplete.ωSup (fun n => (c n).2)
      (fun _ _ h => (hc h).2))
  le_ωSup c hc n :=
    ⟨OmegaComplete.le_ωSup (fun k => (c k).1)
        (fun _ _ h => (hc h).1) n,
      OmegaComplete.le_ωSup (fun k => (c k).2)
        (fun _ _ h => (hc h).2) n⟩
  ωSup_le c hc x hx :=
    ⟨OmegaComplete.ωSup_le (fun k => (c k).1)
        (fun _ _ h => (hc h).1) x.1
        (fun n => (hx n).1),
      OmegaComplete.ωSup_le (fun k => (c k).2)
        (fun _ _ h => (hc h).2) x.2
        (fun n => (hx n).2)⟩

/-- Scott/ω-continuous maps between ωCPOs. -/
structure OmegaMap
    (D : Type u) (E : Type v)
    [PartialOrder D] [OmegaComplete D]
    [PartialOrder E] [OmegaComplete E] where
  toFun : D → E
  monotone : Monotone toFun
  map_ωSup : ∀ (c : ℕ → D) (hc : Monotone c),
    toFun (OmegaComplete.ωSup c hc) =
      OmegaComplete.ωSup (fun n => toFun (c n)) (monotone.comp hc)

namespace OmegaMap

variable
  {D : Type u} {E : Type v} {F : Type w} {G : Type u}
  [PartialOrder D] [OmegaComplete D]
  [PartialOrder E] [OmegaComplete E]
  [PartialOrder F] [OmegaComplete F]
  [PartialOrder G] [OmegaComplete G]

instance : CoeFun (OmegaMap D E) (fun _ => D → E) :=
  ⟨OmegaMap.toFun⟩

instance : LE (OmegaMap D E) :=
  ⟨fun f g => ∀ x, f x ≤ g x⟩

instance [OrderBot E] : OrderBot (OmegaMap D E) where
  bot :=
    { toFun := fun _ => ⊥
      monotone := fun _ _ _ => le_rfl
      map_ωSup := fun c hc => by
        apply le_antisymm
        · exact bot_le
        · exact OmegaComplete.ωSup_le (fun _ => ⊥)
            ((monotone_const).comp hc) ⊥ (fun _ => le_rfl) }
  bot_le _ _ := bot_le

@[ext]
theorem ext {f g : OmegaMap D E} (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  simp only [mk.injEq]
  exact funext h

instance : PartialOrder (OmegaMap D E) where
  le_refl _ _ := le_rfl
  le_trans _ _ _ hfg hgh x := (hfg x).trans (hgh x)
  le_antisymm f g hfg hgf := by
    ext x
    exact le_antisymm (hfg x) (hgf x)

def id : OmegaMap D D where
  toFun x := x
  monotone := monotone_id
  map_ωSup _ _ := rfl

def comp (f : OmegaMap E F) (g : OmegaMap D E) : OmegaMap D F where
  toFun x := f (g x)
  monotone := f.monotone.comp g.monotone
  map_ωSup c hc := by
    rw [g.map_ωSup c hc, f.map_ωSup]

@[simp] theorem id_apply (x : D) : id x = x := rfl
@[simp] theorem comp_apply (f : OmegaMap E F) (g : OmegaMap D E) (x : D) :
    f.comp g x = f (g x) := rfl

@[simp] theorem id_comp (f : OmegaMap D E) : id.comp f = f := by
  ext
  rfl

@[simp] theorem comp_id (f : OmegaMap D E) : f.comp id = f := by
  ext
  rfl

theorem comp_assoc (h : OmegaMap F G) (g : OmegaMap E F) (f : OmegaMap D E) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext
  rfl

section Pointed

variable [OrderBot D]

/-- Finite iterates from bottom. -/
def iterateBot (f : OmegaMap D D) : ℕ → D
  | 0 => ⊥
  | n + 1 => f (iterateBot f n)

theorem iterateBot_mono (f : OmegaMap D D) : Monotone (iterateBot f) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih => exact f.monotone ih

/-- Least fixed point of an ω-continuous endomap. -/
noncomputable def fix (f : OmegaMap D D) : D :=
  OmegaComplete.ωSup (iterateBot f) (iterateBot_mono f)

theorem fix_eq (f : OmegaMap D D) : f (fix f) = fix f := by
  unfold fix
  rw [f.map_ωSup]
  apply le_antisymm
  · apply OmegaComplete.ωSup_le
    intro n
    exact OmegaComplete.le_ωSup (iterateBot f) (iterateBot_mono f) (n + 1)
  · apply OmegaComplete.ωSup_le
    intro n
    cases n with
    | zero => exact bot_le
    | succ n =>
        exact OmegaComplete.le_ωSup
          (fun k => f (iterateBot f k))
          (f.monotone.comp (iterateBot_mono f)) n

theorem fix_le_of_prefixed (f : OmegaMap D D) {x : D} (hx : f x ≤ x) :
    fix f ≤ x := by
  apply OmegaComplete.ωSup_le
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih => exact (f.monotone ih).trans hx

/-- Least fixed points are monotone in their defining functional. -/
theorem fix_mono {f g : OmegaMap D D} (hfg : f ≤ g) :
    fix f ≤ fix g := by
  apply fix_le_of_prefixed
  calc
    f (fix g) ≤ g (fix g) := hfg _
    _ = fix g := fix_eq g

/-- A parameter-indexed family of least fixed points. -/
noncomputable def paramFix
    {P : Type w} [PartialOrder P] [OmegaComplete P]
    (f : P → OmegaMap D D) (p : P) : D :=
  fix (f p)

theorem paramFix_mono
    {P : Type w} [PartialOrder P] [OmegaComplete P]
    {f : P → OmegaMap D D} (hf : Monotone f) :
    Monotone (paramFix f) := by
  intro p q hpq
  exact fix_mono (hf hpq)

end Pointed

end OmegaMap

namespace OmegaMap

section FunctionSpace

variable {D : Type u} {E : Type v}
  [PartialOrder D] [OmegaComplete D]
  [PartialOrder E] [OmegaComplete E]

/-- Continuous maps form an ωCPO under the pointwise order. -/
noncomputable instance instOmegaCompleteFunctionSpace :
    OmegaComplete (OmegaMap D E) where
  ωSup c hc :=
    { toFun := fun x =>
        OmegaComplete.ωSup (fun n => c n x)
          (fun _ _ h => hc h x)
      monotone := by
        intro x y hxy
        exact OmegaComplete.ωSup_mono _ _
          (fun n => (c n).monotone hxy)
      map_ωSup := by
        intro x hx
        apply le_antisymm
        · apply OmegaComplete.ωSup_le
          intro n
          rw [(c n).map_ωSup x hx]
          apply OmegaComplete.ωSup_le
          intro m
          let k := max n m
          have hnk : n ≤ k := Nat.le_max_left _ _
          have hmk : m ≤ k := Nat.le_max_right _ _
          calc
            c n (x m) ≤ c k (x m) := hc hnk _
            _ ≤ c k (x k) := (c k).monotone (hx hmk)
            _ ≤ OmegaComplete.ωSup (fun j => c j (x k))
                (fun _ _ h => hc h _) :=
              OmegaComplete.le_ωSup (fun j => c j (x k))
                (fun _ _ h => hc h _) k
            _ ≤ OmegaComplete.ωSup
                (fun r => OmegaComplete.ωSup (fun j => c j (x r))
                  (fun _ _ h => hc h _))
                (fun a b hab =>
                  OmegaComplete.ωSup_mono _ _
                    (fun j => (c j).monotone (hx hab))) :=
              OmegaComplete.le_ωSup
                (fun r => OmegaComplete.ωSup (fun j => c j (x r))
                  (fun _ _ h => hc h _))
                (fun a b hab =>
                  OmegaComplete.ωSup_mono _ _
                    (fun j => (c j).monotone (hx hab))) k
        · apply OmegaComplete.ωSup_le
          intro m
          apply OmegaComplete.ωSup_le
          intro n
          let k := max n m
          have hnk : n ≤ k := Nat.le_max_left _ _
          have hmk : m ≤ k := Nat.le_max_right _ _
          calc
            c n (x m) ≤ c k (x m) := hc hnk _
            _ ≤ c k (x k) := (c k).monotone (hx hmk)
            _ ≤ c k (OmegaComplete.ωSup x hx) :=
              (c k).monotone (OmegaComplete.le_ωSup x hx k)
            _ ≤ OmegaComplete.ωSup
                (fun j => c j (OmegaComplete.ωSup x hx))
                (fun _ _ h => hc h _) :=
              OmegaComplete.le_ωSup
                (fun j => c j (OmegaComplete.ωSup x hx))
                (fun _ _ h => hc h _) k }
  le_ωSup c hc n x :=
    OmegaComplete.le_ωSup (fun k => c k x)
      (fun _ _ h => hc h x) n
  ωSup_le c hc f hf x :=
    OmegaComplete.ωSup_le (fun n => c n x)
      (fun _ _ h => hc h x) (f x) (fun n => hf n x)

@[simp] theorem ωSup_apply (c : ℕ → OmegaMap D E) (hc : Monotone c)
    (x : D) :
    (OmegaComplete.ωSup c hc) x =
      OmegaComplete.ωSup (fun n => c n x)
        (fun _ _ h => hc h x) :=
  rfl

end FunctionSpace

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
