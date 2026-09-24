/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Monoidal

/-!
# The Day coend for superoperator modules

This file gives the term model of the enriched Day coend.  A term is built
from coend generators and countable sums.  Only terms which have a unique
value under every bilinear interpretation are retained, and two such terms
are identified when all interpretations agree.  This is the usual semantic
construction of the free partial-countable-sum algebra; importantly, the
quantification is over `Prop`, so the construction stays in the same
universe.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

namespace DayCoend

open Classical

/-- Raw terms for the coend at an input dimension `n`.  Arbitrary countable
sums are represented by natural-number sums; `extend` below turns every
countable family into one of these without changing its sum. -/
inductive Raw (M N : Module.{0}) (n : ℕ) where
  | zero
  | generator {a b : ℕ}
      (x : (M.obj a).Carrier) (y : (N.obj b).Carrier)
      (h : Superoperator n (a * b))
  | sum (f : ℕ → Raw M N n)

namespace Raw

/-- Relational evaluation of a raw coend term. -/
inductive Eval {M N L : Module.{0}} (β : Bilinear M N L) {n : ℕ} :
    Raw M N n → (L.obj n).Carrier → Prop where
  | zero : Eval β .zero 0
  | generator {a b} (x : (M.obj a).Carrier) (y : (N.obj b).Carrier)
      (h : Superoperator n (a * b)) :
      Eval β (.generator x y h) (L.act (β.app x y) h)
  | sum (f : ℕ → Raw M N n) (v : ℕ → (L.obj n).Carrier)
      (z : (L.obj n).Carrier) :
      (∀ i, Eval β (f i) (v i)) →
      (L.obj n).HasSum v z →
      Eval β (.sum f) z

/-- Terms retained by the coend are precisely those with a unique value in
every bilinear interpretation. -/
def Admissible {M N : Module.{0}} {n : ℕ} (t : Raw M N n) : Prop :=
  ∀ (L : Module.{0}) (β : Bilinear M N L),
    ∃! z : (L.obj n).Carrier, Eval β t z

/-- Hereditary admissibility ensures that operations defined recursively on
terms (in particular the presheaf action) remain admissible. -/
def Hereditary {M N : Module.{0}} {n : ℕ} : Raw M N n → Prop
  | .zero => True
  | .generator _ _ _ => True
  | .sum f => ∀ i, (f i).Hereditary ∧ (f i).Admissible

theorem admissible_zero {M N : Module} {n : ℕ} :
    Admissible (.zero : Raw M N n) := by
  intro L β
  refine ⟨0, .zero, ?_⟩
  intro z hz
  cases hz
  rfl

theorem admissible_generator {M N : Module} {n a b : ℕ}
    (x : (M.obj a).Carrier) (y : (N.obj b).Carrier)
    (h : Superoperator n (a * b)) :
    Admissible (.generator x y h) := by
  intro L β
  refine ⟨L.act (β.app x y) h, .generator x y h, ?_⟩
  intro z hz
  cases hz
  rfl

/-- The uniquely determined value of an admissible term. -/
noncomputable def value {M N : Module} {n : ℕ}
    (t : Raw M N n) (ht : Admissible t)
    (L : Module) (β : Bilinear M N L) : (L.obj n).Carrier :=
  Classical.choose (ht L β)

theorem eval_value {M N : Module} {n : ℕ}
    (t : Raw M N n) (ht : Admissible t)
    (L : Module) (β : Bilinear M N L) :
    Eval β t (value t ht L β) :=
  (Classical.choose_spec (ht L β)).1

theorem eval_unique {M N : Module} {n : ℕ}
    (t : Raw M N n) (ht : Admissible t)
    (L : Module) (β : Bilinear M N L)
    {z : (L.obj n).Carrier} (hz : Eval β t z) :
    z = value t ht L β :=
  (Classical.choose_spec (ht L β)).2 z hz

theorem eval_sum_cases {M N L : Module} {n : ℕ}
    (β : Bilinear M N L) (f : ℕ → Raw M N n)
    {z : (L.obj n).Carrier} (h : Eval β (.sum f) z) :
    ∃ v, (∀ i, Eval β (f i) (v i)) ∧ (L.obj n).HasSum v z := by
  cases h with
  | sum _ v _ hv hs => exact ⟨v, hv, hs⟩

/-- Contravariant action on raw coend terms. -/
noncomputable def map {M N : Module} {m n : ℕ} (g : Superoperator m n) :
    Raw M N n → Raw M N m
  | .zero => .zero
  | .generator x y h => .generator x y (Superoperator.comp h g)
  | .sum f => .sum (fun i => map g (f i))

theorem eval_map {M N L : Module} {m n : ℕ}
    (β : Bilinear M N L) (g : Superoperator m n)
    {t : Raw M N n} {z : (L.obj n).Carrier}
    (h : Eval β t z) :
    Eval β (map g t) (L.act z g) := by
  induction h with
  | zero =>
      rw [L.act_zero_element]
      exact Eval.zero
  | generator x y h =>
      simpa [map, L.act_comp] using
        (Eval.generator (β := β) x y (Superoperator.comp h g))
  | sum f v z hv hs ih =>
      exact Eval.sum _ (fun i => L.act (v i) g) _ ih
        (L.act_sum_element g hs)

theorem admissible_map {M N : Module} {m n : ℕ}
    (g : Superoperator m n) (t : Raw M N n)
    (ht : t.Admissible) (hh : t.Hereditary) :
    (map g t).Admissible := by
  induction t with
  | zero => simpa [map] using (admissible_zero (M := M) (N := N) (n := m))
  | generator x y h =>
      simpa [map] using admissible_generator x y (Superoperator.comp h g)
  | sum f ih =>
      intro L β
      let z := value (.sum f) ht L β
      refine ⟨L.act z g, eval_map β g (eval_value (.sum f) ht L β), ?_⟩
      intro w hw
      obtain ⟨v, hv, hvs⟩ := eval_sum_cases β _ hw
      have hz := eval_value (.sum f) ht L β
      obtain ⟨u, hu, hus⟩ := eval_sum_cases β f hz
      have hvu : v = fun i => L.act (u i) g := by
        funext i
        exact (ih i (hh i).2 (hh i).1 L β).unique
          (hv i) (eval_map β g (hu i))
      rw [hvu] at hvs
      exact (L.obj m).summation.unique hvs (L.act_sum_element g hus)

theorem hereditary_map {M N : Module} {m n : ℕ}
    (g : Superoperator m n) (t : Raw M N n)
    (hh : t.Hereditary) :
    (map g t).Hereditary := by
  induction t with
  | zero => trivial
  | generator => trivial
  | sum f ih =>
      intro i
      exact ⟨ih i (hh i).1,
        admissible_map g (f i) (hh i).2 (hh i).1⟩

end Raw

/-- An admissible raw term. -/
abbrev Term (M N : Module.{0}) (n : ℕ) :=
  {t : Raw M N n // t.Admissible ∧ t.Hereditary}

namespace Term

noncomputable def value {M N : Module} {n : ℕ}
    (t : Term M N n) (L : Module) (β : Bilinear M N L) :
    (L.obj n).Carrier :=
  t.1.value t.2.1 L β

/-- Semantic equivalence is equality in every bilinear interpretation. -/
def Equivalent {M N : Module} {n : ℕ}
    (s t : Term M N n) : Prop :=
  ∀ (L : Module) (β : Bilinear M N L), s.value L β = t.value L β
end Term

end DayCoend

end SuperoperatorModule

end QLambda.Domain.Presheaf
