/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints

/-!
# Pointed ω-complete partial orders

This is the domain-theoretic foundation of the typed linear calculus.  It is
independent of valuation powerdomains, ωQVA, and the Jung--Tix problem.
-/

namespace QLambda.Domain

universe u v w

/-- A partial order with a least element and suprema of increasing
`ℕ`-chains. -/
class OmegaComplete (D : Type u) [PartialOrder D] [OrderBot D] where
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

variable {D : Type u} [PartialOrder D] [OrderBot D] [OmegaComplete D]

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

end OmegaComplete

/-- Products of pointed ωCPOs carry the pointwise ωCPO structure. -/
noncomputable instance instOmegaCompleteProd
    {D : Type u} {E : Type v}
    [PartialOrder D] [OrderBot D] [OmegaComplete D]
    [PartialOrder E] [OrderBot E] [OmegaComplete E] :
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

/-- Scott/ω-continuous maps between pointed ωCPOs. -/
structure OmegaMap
    (D : Type u) (E : Type v)
    [PartialOrder D] [OrderBot D] [OmegaComplete D]
    [PartialOrder E] [OrderBot E] [OmegaComplete E] where
  toFun : D → E
  monotone : Monotone toFun
  map_ωSup : ∀ (c : ℕ → D) (hc : Monotone c),
    toFun (OmegaComplete.ωSup c hc) =
      OmegaComplete.ωSup (fun n => toFun (c n)) (monotone.comp hc)

namespace OmegaMap

variable
  {D : Type u} {E : Type v} {F : Type w} {G : Type u}
  [PartialOrder D] [OrderBot D] [OmegaComplete D]
  [PartialOrder E] [OrderBot E] [OmegaComplete E]
  [PartialOrder F] [OrderBot F] [OmegaComplete F]
  [PartialOrder G] [OrderBot G] [OmegaComplete G]

instance : CoeFun (OmegaMap D E) (fun _ => D → E) :=
  ⟨OmegaMap.toFun⟩

instance : LE (OmegaMap D E) :=
  ⟨fun f g => ∀ x, f x ≤ g x⟩

instance : OrderBot (OmegaMap D E) where
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
    {P : Type w} [PartialOrder P] [OrderBot P] [OmegaComplete P]
    (f : P → OmegaMap D D) (p : P) : D :=
  fix (f p)

theorem paramFix_mono
    {P : Type w} [PartialOrder P] [OrderBot P] [OmegaComplete P]
    {f : P → OmegaMap D D} (hf : Monotone f) :
    Monotone (paramFix f) := by
  intro p q hpq
  exact fix_mono (hf hpq)

end OmegaMap

namespace OmegaMap

section FunctionSpace

variable {D : Type u} {E : Type v}
  [PartialOrder D] [OrderBot D] [OmegaComplete D]
  [PartialOrder E] [OrderBot E] [OmegaComplete E]

/-- Continuous maps form a pointed ωCPO under the pointwise order. -/
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

end FunctionSpace

end OmegaMap

end QLambda.Domain
