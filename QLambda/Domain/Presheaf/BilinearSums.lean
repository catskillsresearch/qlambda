/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.DayTensorBasic

/-!
# Bilinear pointwise sums and Day tensor sum-preservation
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule
open Classical

namespace Bilinear

private theorem fiber_hasSum_zero (X : Fiber) {ι : Type} [Countable ι] :
    X.HasSum (fun _ : ι => (0 : X.Carrier)) 0 := by
  have he :
      X.HasSum (fun i : (∅ : Set ι) => (0 : X.Carrier)) 0 := by
    convert ((X.summation.reindex (Equiv.Set.empty ι)
      (fun i : Empty => nomatch i) 0).mpr X.summation.empty) using 1
    funext i
    exact i.property.elim
  exact (X.summation.remove_zero
    (fun _ : ι => (0 : X.Carrier)) ∅ 0 (by simp)).mp he

/-- Pointwise sums of bilinear maps. -/
def HasSum {M A N : Module} {ι : Type} [Countable ι]
    (f : ι → Bilinear M A N) (s : Bilinear M A N) : Prop :=
  ∀ m n (x : (M.obj m).Carrier) (y : (A.obj n).Carrier),
    (N.obj (m * n)).HasSum
      (fun i => (f i).app x y) (s.app x y)

noncomputable def sumOf {M A N : Module}
    {ι : Type} [Countable ι] (f : ι → Bilinear M A N)
    (h : ∀ m n (x : (M.obj m).Carrier) (y : (A.obj n).Carrier),
      ∃ z, (N.obj (m * n)).HasSum (fun i => (f i).app x y) z) :
    Bilinear M A N where
  app := fun {m n} x y => Classical.choose (h m n x y)
  map_zero_left := by
    intro m n y
    apply (N.obj (m * n)).summation.unique
      (Classical.choose_spec (h m n 0 y))
    simpa only [map_zero_left] using
      (fiber_hasSum_zero (N.obj (m * n)) (ι := ι))
  map_zero_right := by
    intro m n x
    apply (N.obj (m * n)).summation.unique
      (Classical.choose_spec (h m n x 0))
    simpa only [map_zero_right] using
      (fiber_hasSum_zero (N.obj (m * n)) (ι := ι))
  map_sum_left := by
    intro κ _ m n x s y hs
    let F : (i : ι) → κ → (N.obj (m * n)).Carrier :=
      fun i k => (f i).app (x k) y
    have hrows :
        ∀ i, (N.obj (m * n)).HasSum (F i) ((f i).app s y) :=
      fun i => (f i).map_sum_left y hs
    have houter :
        (N.obj (m * n)).HasSum
          (fun i => (f i).app s y)
          (Classical.choose (h m n s y)) :=
      Classical.choose_spec (h m n s y)
    have hflat :=
      ((N.obj (m * n)).summation.flatten F
        (Classical.choose (h m n s y))).2
        ⟨fun i => (f i).app s y, hrows, houter⟩
    let e : (Σ _ : ι, κ) ≃ (Σ _ : κ, ι) :=
      { toFun := fun p => ⟨p.2, p.1⟩
        invFun := fun p => ⟨p.2, p.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hswap :
        (N.obj (m * n)).HasSum
          (fun p : Σ _ : κ, ι => F p.2 p.1)
          (Classical.choose (h m n s y)) := by
      exact ((N.obj (m * n)).summation.reindex e.symm
        (fun p : Σ _ : ι, κ => F p.1 p.2)
        (Classical.choose (h m n s y))).2 hflat
    obtain ⟨g, hg, hgs⟩ :=
      ((N.obj (m * n)).summation.flatten
        (fun k i => F i k) (Classical.choose (h m n s y))).1 hswap
    convert hgs using 1
    funext k
    exact (N.obj (m * n)).summation.unique
      (Classical.choose_spec (h m n (x k) y)) (hg k)
  map_sum_right := by
    intro κ _ m n x y s hs
    let F : (i : ι) → κ → (N.obj (m * n)).Carrier :=
      fun i k => (f i).app x (y k)
    have hrows :
        ∀ i, (N.obj (m * n)).HasSum (F i) ((f i).app x s) :=
      fun i => (f i).map_sum_right x hs
    have houter :
        (N.obj (m * n)).HasSum
          (fun i => (f i).app x s)
          (Classical.choose (h m n x s)) :=
      Classical.choose_spec (h m n x s)
    have hflat :=
      ((N.obj (m * n)).summation.flatten F
        (Classical.choose (h m n x s))).2
        ⟨fun i => (f i).app x s, hrows, houter⟩
    let e : (Σ _ : ι, κ) ≃ (Σ _ : κ, ι) :=
      { toFun := fun p => ⟨p.2, p.1⟩
        invFun := fun p => ⟨p.2, p.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hswap :
        (N.obj (m * n)).HasSum
          (fun p : Σ _ : κ, ι => F p.2 p.1)
          (Classical.choose (h m n x s)) := by
      exact ((N.obj (m * n)).summation.reindex e.symm
        (fun p : Σ _ : ι, κ => F p.1 p.2)
        (Classical.choose (h m n x s))).2 hflat
    obtain ⟨g, hg, hgs⟩ :=
      ((N.obj (m * n)).summation.flatten
        (fun k i => F i k) (Classical.choose (h m n x s))).1 hswap
    convert hgs using 1
    funext k
    exact (N.obj (m * n)).summation.unique
      (Classical.choose_spec (h m n x (y k))) (hg k)
  naturality := by
    intro m' m n' n x y p q
    apply (N.obj (m' * n')).summation.unique
      (Classical.choose_spec
        (h m' n' (M.act x p) (A.act y q)))
    have hs := N.act_sum_element (Superoperator.tensor p q)
      (Classical.choose_spec (h m n x y))
    convert hs using 1
    funext i
    exact (f i).naturality x y p q

theorem sumOf_hasSum {M A N : Module}
    {ι : Type} [Countable ι] (f : ι → Bilinear M A N)
    (h : ∀ m n (x : (M.obj m).Carrier) (y : (A.obj n).Carrier),
      ∃ z, (N.obj (m * n)).HasSum (fun i => (f i).app x y) z) :
    HasSum f (sumOf f h) :=
  fun m n x y => Classical.choose_spec (h m n x y)

noncomputable def zero (M A N : Module) : Bilinear M A N where
  app := fun _ _ => 0
  map_zero_left := fun _ => rfl
  map_zero_right := fun _ => rfl
  map_sum_left := by
    intro ι _ m n x s y h
    exact fiber_hasSum_zero (N.obj (m * n))
  map_sum_right := by
    intro ι _ m n x y s h
    exact fiber_hasSum_zero (N.obj (m * n))
  naturality := by
    intro m' m n' n x y f g
    exact (N.act_zero_element _).symm

noncomputable instance instZeroBilinear (M A N : Module) : Zero (Bilinear M A N) :=
  ⟨zero M A N⟩

noncomputable def partialCountableSum (M A N : Module) :
    @SigmaMon.PartialCountableSum (Bilinear M A N) ⟨zero M A N⟩ where
  HasSum := HasSum
  unique := by
    intro ι _ f s t hs ht
    apply Bilinear.ext
    intro m n x y
    exact (N.obj (m * n)).summation.unique
      (hs m n x y) (ht m n x y)
  empty := by
    intro m n x y
    convert (N.obj (m * n)).summation.empty using 1
    rfl
  singleton := by
    intro b m n x y
    exact (N.obj (m * n)).summation.singleton _
  remove_zero := by
    intro ι _ f u b hz
    constructor <;> intro h m n x y
    · apply ((N.obj (m * n)).summation.remove_zero
        (fun i => (f i).app x y) u (b.app x y) ?_).1
      · exact h m n x y
      · intro i hi
        rw [hz i hi]
        rfl
    · apply ((N.obj (m * n)).summation.remove_zero
        (fun i => (f i).app x y) u (b.app x y) ?_).2
      · exact h m n x y
      · intro i hi
        rw [hz i hi]
        rfl
  reindex := by
    intro ι κ _ _ e f b
    constructor <;> intro h m n x y
    · exact ((N.obj (m * n)).summation.reindex e
        (fun i => (f i).app x y) (b.app x y)).1 (h m n x y)
    · exact ((N.obj (m * n)).summation.reindex e
        (fun i => (f i).app x y) (b.app x y)).2 (h m n x y)
  flatten := by
    intro ι _ κ _ f b
    constructor
    · intro hflat
      have hexists (i : ι) m n
          (x : (M.obj m).Carrier) (y : (A.obj n).Carrier) :
          ∃ z, (N.obj (m * n)).HasSum
            (fun j => (f i j).app x y) z := by
        obtain ⟨v, hv, _⟩ :=
          ((N.obj (m * n)).summation.flatten
            (fun i j => (f i j).app x y) (b.app x y)).1
            (hflat m n x y)
        exact ⟨v i, hv i⟩
      let g : ι → Bilinear M A N :=
        fun i => sumOf (f i) (hexists i)
      have hg : ∀ i, HasSum (f i) (g i) :=
        fun i => sumOf_hasSum (f i) (hexists i)
      refine ⟨g, hg, ?_⟩
      intro m n x y
      obtain ⟨v, hv, hvs⟩ :=
        ((N.obj (m * n)).summation.flatten
          (fun i j => (f i j).app x y) (b.app x y)).1
          (hflat m n x y)
      convert hvs using 1
      funext i
      exact (N.obj (m * n)).summation.unique
        (hg i m n x y) (hv i)
    · rintro ⟨g, hg, hgb⟩ m n x y
      exact ((N.obj (m * n)).summation.flatten
        (fun i j => (f i j).app x y) (b.app x y)).2
        ⟨fun i => (g i).app x y,
          fun i => hg i m n x y, hgb m n x y⟩

/-- Evaluation of an admissible coend term preserves pointwise sums of its
bilinear interpretations. -/
private theorem Raw.value_hasSum {M A N : Module}
    {ι : Type} [Countable ι] {n : ℕ}
    (t : DayCoend.Raw M A n) (ht : t.Admissible) (hh : t.Hereditary)
    (f : ι → Bilinear M A N) (s : Bilinear M A N)
    (h : HasSum f s) :
    (N.obj n).HasSum
      (fun i => DayCoend.Raw.value t ht N (f i))
      (DayCoend.Raw.value t ht N s) := by
  induction t with
  | zero =>
      convert fiber_hasSum_zero (N.obj n) (ι := ι) using 1
      · funext i
        exact (DayCoend.Raw.eval_unique .zero ht N (f i)
          DayCoend.Raw.Eval.zero).symm
      · exact (DayCoend.Raw.eval_unique .zero ht N s
          DayCoend.Raw.Eval.zero).symm
  | @generator a b x y q =>
      have hs := N.act_sum_element q (h a b x y)
      convert hs using 1
      · funext i
        exact (DayCoend.Raw.eval_unique (.generator x y q) ht N (f i)
          (DayCoend.Raw.Eval.generator x y q)).symm
      · exact (DayCoend.Raw.eval_unique (.generator x y q) ht N s
          (DayCoend.Raw.Eval.generator x y q)).symm
  | sum u ih =>
      choose v hv hvs using fun i =>
        DayCoend.Raw.eval_sum_cases (f i) u
          (DayCoend.Raw.eval_value (.sum u) ht N (f i))
      obtain ⟨w, hw, hws⟩ :=
        DayCoend.Raw.eval_sum_cases s u
          (DayCoend.Raw.eval_value (.sum u) ht N s)
      let F : ι → ℕ → (N.obj n).Carrier :=
        fun i k => DayCoend.Raw.value (u k) (hh k).2 N (f i)
      have hrow (i : ι) :
          (N.obj n).HasSum (F i)
            (DayCoend.Raw.value (.sum u) ht N (f i)) := by
        convert hvs i using 1
        funext k
        exact (DayCoend.Raw.eval_unique (u k) (hh k).2
          N (f i) (hv i k)).symm
      have hcol (k : ℕ) :
          (N.obj n).HasSum (fun i => F i k)
            (DayCoend.Raw.value (u k) (hh k).2 N s) :=
        ih k (hh k).2 (hh k).1
      have htarget :
          (N.obj n).HasSum
            (fun k => DayCoend.Raw.value (u k) (hh k).2 N s)
            (DayCoend.Raw.value (.sum u) ht N s) := by
        convert hws using 1
        funext k
        exact (DayCoend.Raw.eval_unique (u k) (hh k).2 N s (hw k)).symm
      have hflatKI :
          (N.obj n).HasSum
            (fun p : Σ _ : ℕ, ι => F p.2 p.1)
            (DayCoend.Raw.value (.sum u) ht N s) :=
        ((N.obj n).summation.flatten
          (fun k i => F i k)
          (DayCoend.Raw.value (.sum u) ht N s)).2
          ⟨fun k => DayCoend.Raw.value (u k) (hh k).2 N s,
            hcol, htarget⟩
      let e : (Σ _ : ι, ℕ) ≃ (Σ _ : ℕ, ι) :=
        { toFun := fun p => ⟨p.2, p.1⟩
          invFun := fun p => ⟨p.2, p.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have hflatIK :
          (N.obj n).HasSum
            (fun p : Σ _ : ι, ℕ => F p.1 p.2)
            (DayCoend.Raw.value (.sum u) ht N s) := by
        exact ((N.obj n).summation.reindex e
          (fun p : Σ _ : ℕ, ι => F p.2 p.1)
          (DayCoend.Raw.value (.sum u) ht N s)).2 hflatKI
      obtain ⟨g, hg, hgs⟩ :=
        ((N.obj n).summation.flatten F
          (DayCoend.Raw.value (.sum u) ht N s)).1 hflatIK
      convert hgs using 1
      funext i
      exact (N.obj n).summation.unique (hrow i) (hg i)

/-- The Day universal map is enriched: pointwise sums of bilinear
interpretations become pointwise sums of module morphisms. -/
theorem lift_hasSum {M A N : Module} {ι : Type} [Countable ι]
    {f : ι → Bilinear M A N} {s : Bilinear M A N}
    (h : HasSum f s) :
    Hom.HasSum (fun i => DayCoend.lift (f i)) (DayCoend.lift s) := by
  intro n x
  induction x using Quotient.inductionOn with
  | _ t => exact Raw.value_hasSum t.1 t.2.1 t.2.2 f s h

end Bilinear

namespace DayTensor

/-- Tensoring on the left preserves every defined sum of module maps. -/
theorem map_hasSum_left {M M' N N' : Module}
    {ι : Type} [Countable ι]
    {f : ι → Hom M M'} {s : Hom M M'} (g : Hom N N')
    (h : Hom.HasSum f s) :
    Hom.HasSum (fun i => map (f i) g) (map s g) := by
  apply Bilinear.lift_hasSum
  intro m n x y
  exact (DayCoend.intro M' N').map_sum_left (g.app n y) (h m x)

/-- Tensoring on the right preserves every defined sum of module maps. -/
theorem map_hasSum_right {M M' N N' : Module}
    {ι : Type} [Countable ι]
    (f : Hom M M') {g : ι → Hom N N'} {s : Hom N N'}
    (h : Hom.HasSum g s) :
    Hom.HasSum (fun i => map f (g i)) (map f s) := by
  apply Bilinear.lift_hasSum
  intro m n x y
  exact (DayCoend.intro M' N').map_sum_right (f.app m x) (h n y)

end DayTensor

end SuperoperatorModule
end QLambda.Domain.Presheaf
