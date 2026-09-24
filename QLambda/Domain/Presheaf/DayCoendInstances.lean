/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.DayCoend
import QLambda.Domain.Presheaf.instZeroDayRaw
import QLambda.Domain.Presheaf.setoid
import QLambda.Domain.Presheaf.instZeroDayCarrier

/-!
# Instances from `DayCoend`
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule
namespace DayCoend

open Classical

@[simp]
theorem evaluate_zero {M N L : Module} {n : ℕ}
    (β : Bilinear M N L) :
    evaluate L β (0 : Carrier M N n) = 0 := by
  change (zeroTerm M N n).value L β = 0
  exact (Raw.eval_unique _ Raw.admissible_zero L β Raw.Eval.zero).symm

/-- A fixed embedding of a countable type into the naturals. -/
noncomputable def countableEmbedding (α : Type) [Countable α] : α ↪ ℕ :=
  ⟨Classical.choose (Countable.exists_injective_nat α),
    Classical.choose_spec (Countable.exists_injective_nat α)⟩

/-- Extend a countable family by zero along a fixed encoding. -/
noncomputable def extend {α : Type} [Countable α] {X : Type} [Zero X]
    (f : α → X) : ℕ → X :=
  fun k => if h : ∃ i, countableEmbedding α i = k
    then f (Classical.choose h) else 0

private theorem extend_encode {α : Type} [Countable α]
    {X : Type} [Zero X] (f : α → X) (i : α) :
    extend f (countableEmbedding α i) = f i := by
  rw [extend]
  simp only [dif_pos
    (show ∃ j : α, countableEmbedding α j = countableEmbedding α i
      from ⟨i, rfl⟩)]
  have hc := Classical.choose_spec
    (show ∃ j, countableEmbedding α j = countableEmbedding α i from ⟨i, rfl⟩)
  have hi := (countableEmbedding α).injective hc
  rw [hi]

private theorem extend_hasSum_iff {α : Type} [Countable α]
    (X : Fiber) (f : α → X.Carrier) (s : X.Carrier) :
    X.HasSum (extend f) s ↔ X.HasSum f s := by
  let e : α ≃ Set.range (countableEmbedding α) :=
    Equiv.ofInjective (countableEmbedding α) (countableEmbedding α).injective
  have hz :
      ∀ k, k ∉ Set.range (countableEmbedding α) →
        extend f k = 0 := by
    intro k hk
    rw [extend, dif_neg]
    intro h
    exact hk h
  have hr :=
    X.summation.remove_zero (extend f)
      (Set.range (countableEmbedding α)) s hz
  have he :
      X.HasSum
          (fun k : Set.range (countableEmbedding α) => extend f k) s ↔
        X.HasSum f s := by
    have hre := X.summation.reindex e
      (fun k : Set.range (countableEmbedding α) => extend f k) s
    have hfun :
        (fun k : Set.range (countableEmbedding α) => extend f k) ∘ e = f := by
      funext i
      exact extend_encode f i
    rw [hfun] at hre
    exact hre.symm
  exact hr.symm.trans he

/-- The partial sum on the semantic quotient is tested in every target.
This is what makes all bilinear interpretations sum preserving by
construction. -/
def HasSum {M N : Module} {ι : Type} [Countable ι] {n : ℕ}
    (f : ι → Carrier M N n) (s : Carrier M N n) : Prop :=
  ∀ (L : Module) (β : Bilinear M N L),
    (L.obj n).HasSum (fun i => evaluate L β (f i)) (evaluate L β s)

private noncomputable def representative {M N : Module} {n : ℕ}
    (x : Carrier M N n) : Term M N n :=
  Quotient.out x

private theorem mk_representative {M N : Module} {n : ℕ}
    (x : Carrier M N n) :
    Quotient.mk _ (representative x) = x :=
  Quotient.out_eq x

private theorem value_representative {M N L : Module} {n : ℕ}
    (β : Bilinear M N L) (x : Carrier M N n) :
    (representative x).value L β = evaluate L β x := by
  have h := congrArg (evaluate L β) (mk_representative x)
  exact h

private theorem eval_extend_representative {M N L : Module}
    {ι : Type} [Countable ι] {n : ℕ}
    (β : Bilinear M N L) (f : ι → Carrier M N n) (k : ℕ) :
    Raw.Eval β
      (extend (fun i => (representative (f i)).1) k)
      (extend (fun i => evaluate L β (f i)) k) := by
  simp only [extend]
  split
  · rename_i h
    have hv := (representative (f (Classical.choose h))).1.eval_value
      (representative (f (Classical.choose h))).2.1 L β
    convert hv using 1
    exact (value_representative β _).symm
  · exact .zero

private noncomputable def sumTerm {M N : Module} {ι : Type} [Countable ι]
    {n : ℕ} (f : ι → Carrier M N n) :
    Raw M N n :=
  .sum (extend (fun i => (representative (f i)).1))

private theorem sumTerm_hereditary {M N : Module}
    {ι : Type} [Countable ι] {n : ℕ}
    (f : ι → Carrier M N n) :
    (sumTerm f).Hereditary := by
  intro k
  simp only [extend]
  split
  · exact ⟨(representative _).2.2, (representative _).2.1⟩
  · exact ⟨trivial, Raw.admissible_zero⟩

private theorem sumTerm_admissible_of {M N : Module}
    {ι : Type} [Countable ι] {n : ℕ}
    (f : ι → Carrier M N n)
    (h : ∀ (L : Module) (β : Bilinear M N L),
      ∃ z, (L.obj n).HasSum
        (fun i => evaluate L β (f i)) z) :
    (sumTerm f).Admissible := by
  intro L β
  obtain ⟨s, hs⟩ := h L β
  refine ⟨s, ?_, ?_⟩
  · apply Raw.Eval.sum _ (extend (fun i => evaluate L β (f i)))
    · exact eval_extend_representative β f
    · exact (extend_hasSum_iff (L.obj n)
        (fun i => evaluate L β (f i)) s).2 hs
  · intro z hz
    have hz' : Raw.Eval β
        (.sum (extend (fun i => (representative (f i)).1))) z := by
      simpa only [sumTerm] using hz
    obtain ⟨v, hv, hvs⟩ := Raw.eval_sum_cases β _ hz'
    have hvext :
        v = extend (fun i => evaluate L β (f i)) := by
      funext k
      specialize hv k
      simp only [extend] at hv ⊢
      by_cases hk : ∃ i, countableEmbedding ι i = k
      · simp only [dif_pos hk] at hv ⊢
        exact (representative (f (Classical.choose hk))).1.eval_unique
          (representative (f (Classical.choose hk))).2.1 L β hv |>.trans
            (value_representative β _)
      · simp only [dif_neg hk] at hv ⊢
        exact (Raw.eval_unique (.zero : Raw M N n) Raw.admissible_zero
          L β hv).trans
            (Raw.eval_unique (.zero : Raw M N n) Raw.admissible_zero
              L β Raw.Eval.zero).symm
    rw [hvext] at hvs
    exact (L.obj n).summation.unique hvs
      ((extend_hasSum_iff (L.obj n)
        (fun i => evaluate L β (f i)) s).2 hs)

private theorem sumTerm_admissible {M N : Module} {ι : Type} [Countable ι]
    {n : ℕ} {f : ι → Carrier M N n} {s : Carrier M N n}
    (h : HasSum f s) :
    (sumTerm f).Admissible :=
  sumTerm_admissible_of f fun L β => ⟨evaluate L β s, h L β⟩

/-- Form the Day-coend sum of a family that admits a sum under every
bilinear interpretation. -/
noncomputable def sumOfAdmissible {M N : Module}
    {ι : Type} [Countable ι] {n : ℕ}
    (f : ι → Carrier M N n)
    (h : ∀ (L : Module) (β : Bilinear M N L),
      ∃ z, (L.obj n).HasSum
        (fun i => evaluate L β (f i)) z) :
    Carrier M N n :=
  Quotient.mk _ ⟨sumTerm f, sumTerm_admissible_of f h,
    sumTerm_hereditary f⟩

theorem evaluate_sumOfAdmissible {M N : Module}
    {ι : Type} [Countable ι] {n : ℕ}
    (f : ι → Carrier M N n)
    (h : ∀ (L : Module) (β : Bilinear M N L),
      ∃ z, (L.obj n).HasSum
        (fun i => evaluate L β (f i)) z)
    (L : Module) (β : Bilinear M N L) (z : (L.obj n).Carrier)
    (hz : (L.obj n).HasSum (fun i => evaluate L β (f i)) z) :
    evaluate L β (sumOfAdmissible f h) = z := by
  change Term.value
    (⟨sumTerm f, sumTerm_admissible_of f h,
      sumTerm_hereditary f⟩ : Term M N n) L β = z
  have he : Raw.Eval β (sumTerm f) z := by
    apply Raw.Eval.sum _ (extend (fun i => evaluate L β (f i)))
    · exact eval_extend_representative β f
    · exact (extend_hasSum_iff (L.obj n)
        (fun i => evaluate L β (f i)) z).2 hz
  exact (Raw.eval_unique (sumTerm f) (sumTerm_admissible_of f h)
    L β he).symm

/-- Specialization: the sum of a family that already has a coend `HasSum`
witness. -/
noncomputable def sumElement {M N : Module}
    {ι : Type} [Countable ι] {n : ℕ}
    {f : ι → Carrier M N n} {s : Carrier M N n}
    (h : HasSum f s) : Carrier M N n :=
  sumOfAdmissible f fun L β => ⟨evaluate L β s, h L β⟩

theorem evaluate_sumElement {M N : Module}
    {ι : Type} [Countable ι] {n : ℕ}
    {f : ι → Carrier M N n} {s : Carrier M N n}
    (h : HasSum f s) (L : Module) (β : Bilinear M N L) :
    evaluate L β (sumElement h) = evaluate L β s :=
  evaluate_sumOfAdmissible f
    (fun L β => ⟨evaluate L β s, h L β⟩)
    L β (evaluate L β s) (h L β)

private theorem quotient_ext {M N : Module} {n : ℕ}
    {x y : Carrier M N n}
    (h : ∀ (L : Module) (β : Bilinear M N L),
      evaluate L β x = evaluate L β y) : x = y := by
  rw [← mk_representative x, ← mk_representative y]
  apply Quotient.sound
  intro L β
  rw [value_representative, value_representative]
  exact h L β

/-- The semantic quotient is a genuine partial countable-sum algebra. -/
noncomputable def partialCountableSum (M N : Module) (n : ℕ) :
    @SigmaMon.PartialCountableSum (Carrier M N n) ⟨zero M N n⟩ where
  HasSum := HasSum
  unique := by
    intro ι _ f a b ha hb
    apply quotient_ext
    intro L β
    exact (L.obj n).summation.unique (ha L β) (hb L β)
  empty := by
    intro L β
    convert (L.obj n).summation.empty using 1
    exact evaluate_zero β
  singleton := by
    intro a L β
    exact (L.obj n).summation.singleton _
  remove_zero := by
    intro ι _ f u a hz
    constructor <;> intro h L β
    · apply ((L.obj n).summation.remove_zero
        (fun i => evaluate L β (f i)) u (evaluate L β a) ?_).mp
      · exact h L β
      · intro i hi
        rw [hz i hi]
        exact evaluate_zero β
    · apply ((L.obj n).summation.remove_zero
        (fun i => evaluate L β (f i)) u (evaluate L β a) ?_).mpr
      · exact h L β
      · intro i hi
        rw [hz i hi]
        exact evaluate_zero β
  reindex := by
    intro ι κ _ _ e f a
    constructor <;> intro h L β
    · exact ((L.obj n).summation.reindex e
        (fun i => evaluate L β (f i)) (evaluate L β a)).mp (h L β)
    · exact ((L.obj n).summation.reindex e
        (fun i => evaluate L β (f i)) (evaluate L β a)).mpr (h L β)
  flatten := by
    intro ι _ κ _ f a
    constructor
    · intro hflat
      have hexists (i : ι) (L : Module) (β : Bilinear M N L) :
          ∃ z, (L.obj n).HasSum
            (fun j => evaluate L β (f i j)) z := by
        obtain ⟨v, hv, _⟩ :=
          ((L.obj n).summation.flatten
            (fun i j => evaluate L β (f i j))
            (evaluate L β a)).mp (hflat L β)
        exact ⟨v i, hv i⟩
      let g : ι → Carrier M N n :=
        fun i => sumOfAdmissible (f i) (hexists i)
      have hrows : ∀ i, HasSum (f i) (g i) := by
        intro i L β
        obtain ⟨v, hv, _⟩ :=
          ((L.obj n).summation.flatten
            (fun i j => evaluate L β (f i j))
            (evaluate L β a)).mp (hflat L β)
        rw [show evaluate L β (g i) = v i from
          evaluate_sumOfAdmissible (f i) (hexists i) L β (v i) (hv i)]
        exact hv i
      refine ⟨g, hrows, ?_⟩
      intro L β
      obtain ⟨v, hv, hva⟩ :=
        ((L.obj n).summation.flatten
          (fun i j => evaluate L β (f i j))
          (evaluate L β a)).mp (hflat L β)
      convert hva using 1
      funext i
      exact (evaluate_sumOfAdmissible (f i) (hexists i)
        L β (v i) (hv i))
    · rintro ⟨g, hrows, hg⟩ L β
      exact ((L.obj n).summation.flatten
        (fun i j => evaluate L β (f i j))
        (evaluate L β a)).mpr
          ⟨fun i => evaluate L β (g i), fun i => hrows i L β, hg L β⟩

private noncomputable def mapTerm {M N : Module} {m n : ℕ}
    (g : Superoperator m n) (t : Term M N n) : Term M N m :=
  ⟨Raw.map g t.1,
    Raw.admissible_map g t.1 t.2.1 t.2.2,
    Raw.hereditary_map g t.1 t.2.2⟩

private theorem value_mapTerm {M N L : Module} {m n : ℕ}
    (β : Bilinear M N L) (g : Superoperator m n)
    (t : Term M N n) :
    (mapTerm g t).value L β = L.act (t.value L β) g := by
  exact (Raw.eval_unique (Raw.map g t.1)
    (Raw.admissible_map g t.1 t.2.1 t.2.2) L β
    (Raw.eval_map β g (Raw.eval_value t.1 t.2.1 L β))).symm

/-- Presheaf action on the semantic coend. -/
noncomputable def action {M N : Module} {m n : ℕ}
    (x : Carrier M N n) (g : Superoperator m n) :
    Carrier M N m :=
  Quotient.map (mapTerm g) (by
    intro s t h
    intro L β
    rw [value_mapTerm, value_mapTerm, h L β]) x

@[simp]
theorem evaluate_action {M N L : Module} {m n : ℕ}
    (β : Bilinear M N L) (x : Carrier M N n)
    (g : Superoperator m n) :
    evaluate L β (action x g) = L.act (evaluate L β x) g := by
  induction x using Quotient.inductionOn with
  | _ t => exact value_mapTerm β g t

/-- The genuine Day coend as a specialized superoperator module. -/
noncomputable def module (M N : Module) : Module where
  obj n :=
    { Carrier := Carrier M N n
      zero := zero M N n
      summation := partialCountableSum M N n }
  act := action
  act_zero_element := by
    intro m n g
    apply quotient_ext
    intro L β
    rw [evaluate_action, evaluate_zero, L.act_zero_element, evaluate_zero]
  act_zero_map := by
    intro m n x
    apply quotient_ext
    intro L β
    rw [evaluate_action, L.act_zero_map, evaluate_zero]
  act_id := by
    intro n x
    apply quotient_ext
    intro L β
    rw [evaluate_action, L.act_id]
  act_comp := by
    intro ℓ m n x f g
    apply quotient_ext
    intro L β
    rw [evaluate_action, evaluate_action, evaluate_action, L.act_comp]
  act_sum_element := by
    intro ι _ m n x s g h
    intro L β
    simp only [evaluate_action]
    exact L.act_sum_element g (h L β)
  act_sum_map := by
    intro ι _ m n x f s h
    intro L β
    simp only [evaluate_action]
    exact L.act_sum_map (evaluate L β x) h
  act_sum_from_one := by
    intro ι _ m x s f hs
    have hadm :
        ∀ (L : Module) (β : Bilinear M N L),
          ∃ z, (L.obj m).HasSum
            (fun i => evaluate L β (action (x i) (f i))) z := by
      intro L β
      obtain ⟨z, hz⟩ := L.act_sum_from_one f (hs L β)
      exact ⟨z, by simpa [evaluate_action] using hz⟩
    refine ⟨sumOfAdmissible (fun i => action (x i) (f i)) hadm, ?_⟩
    intro L β
    obtain ⟨z, hz⟩ := hadm L β
    have he := evaluate_sumOfAdmissible
      (fun i => action (x i) (f i)) hadm L β z hz
    simpa [he] using hz
  act_sum_tensor_from_one := by
    intro ι _ m B x s f hs
    have hadm :
        ∀ (L : Module) (β : Bilinear M N L),
          ∃ z, (L.obj (m * B)).HasSum
            (fun i =>
              evaluate L β
                (action (x i)
                  (Superoperator.tensor (f i)
                    (Superoperator.identity B)))) z := by
      intro L β
      obtain ⟨z, hz⟩ :=
        L.act_sum_tensor_from_one f (hs L β)
      exact ⟨z, by simpa [evaluate_action] using hz⟩
    refine
      ⟨sumOfAdmissible
          (fun i =>
            action (x i)
              (Superoperator.tensor (f i) (Superoperator.identity B)))
          hadm,
        ?_⟩
    intro L β
    obtain ⟨z, hz⟩ := hadm L β
    have he :=
      evaluate_sumOfAdmissible
        (fun i =>
          action (x i)
            (Superoperator.tensor (f i) (Superoperator.identity B)))
        hadm L β z hz
    simpa [he] using hz

/-- A coend generator. -/
noncomputable def generator {M N : Module} {n a b : ℕ}
    (x : (M.obj a).Carrier) (y : (N.obj b).Carrier)
    (h : Superoperator n (a * b)) :
    Carrier M N n :=
  Quotient.mk _ ⟨.generator x y h,
    Raw.admissible_generator x y h, trivial⟩

@[simp]
theorem evaluate_generator {M N L : Module} {n a b : ℕ}
    (β : Bilinear M N L)
    (x : (M.obj a).Carrier) (y : (N.obj b).Carrier)
    (h : Superoperator n (a * b)) :
    evaluate L β (generator x y h) = L.act (β.app x y) h := by
  exact (Raw.eval_unique (.generator x y h)
    (Raw.admissible_generator x y h) L β
    (Raw.Eval.generator x y h)).symm

/-- Universal bilinear insertion into the Day coend. -/
noncomputable def intro (M N : Module) :
    Bilinear M N (module M N) where
  app := fun {m n} x y =>
    generator x y (Superoperator.identity (m * n))
  map_zero_left := by
    intro m n y
    change generator (0 : (M.obj m).Carrier) y
      (Superoperator.identity (m * n)) = zero M N (m * n)
    apply quotient_ext
    intro L β
    rw [evaluate_generator, β.map_zero_left, L.act_zero_element]
    exact (evaluate_zero β).symm
  map_zero_right := by
    intro m n x
    change generator x (0 : (N.obj n).Carrier)
      (Superoperator.identity (m * n)) = zero M N (m * n)
    apply quotient_ext
    intro L β
    rw [evaluate_generator, β.map_zero_right, L.act_zero_element]
    exact (evaluate_zero β).symm
  map_sum_left := by
    intro ι _ m n x s y h L β
    simp only [evaluate_generator]
    simpa only [L.act_id] using β.map_sum_left y h
  map_sum_right := by
    intro ι _ m n x y s h L β
    simp only [evaluate_generator]
    simpa only [L.act_id] using β.map_sum_right x h
  naturality := by
    intro m' m n' n x y f g
    change
      generator (M.act x f) (N.act y g)
          (Superoperator.identity (m' * n')) =
        action (generator x y (Superoperator.identity (m * n)))
          (Superoperator.tensor f g)
    apply quotient_ext
    intro L β
    rw [evaluate_generator, evaluate_action, evaluate_generator,
      L.act_id, L.act_id]
    exact β.naturality x y f g

@[simp]
theorem evaluate_intro {M N L : Module} (β : Bilinear M N L)
    {m n : ℕ} (x : (M.obj m).Carrier) (y : (N.obj n).Carrier) :
    evaluate L β ((intro M N).app x y) = β.app x y := by
  rw [intro, evaluate_generator, L.act_id]

/-- Evaluation of terms is the universal map induced by a bilinear map. -/
noncomputable def lift {M N L : Module} (β : Bilinear M N L) :
    Hom (module M N) L where
  app := fun _ x => evaluate L β x
  map_zero := fun _ => evaluate_zero β
  map_sum := fun h => h L β
  naturality := by
    intro m n x g
    exact evaluate_action β x g

private theorem evaluate_self_raw {M N L : Module} {n : ℕ}
    (t : Raw M N n) (ht : t.Admissible) (hh : t.Hereditary)
    (β : Bilinear M N L) :
    evaluate L β
        (Raw.value t ht (module M N) (intro M N)) =
      Raw.value t ht L β := by
  induction t with
  | zero =>
      have hs := Raw.eval_unique (.zero : Raw M N n) ht
        (module M N) (intro M N) Raw.Eval.zero
      have htgt := Raw.eval_unique (.zero : Raw M N n) ht
        L β Raw.Eval.zero
      rw [← hs, ← htgt]
      exact evaluate_zero β
  | generator x y h =>
      have hs := Raw.eval_unique (.generator x y h) ht
        (module M N) (intro M N) (Raw.Eval.generator x y h)
      have htgt := Raw.eval_unique (.generator x y h) ht
        L β (Raw.Eval.generator x y h)
      rw [← hs, ← htgt]
      change evaluate L β
        (action (generator x y (Superoperator.identity _)) h) =
          L.act (β.app x y) h
      rw [evaluate_action, evaluate_generator, L.act_id]
  | sum f ih =>
      have hs := Raw.eval_value (.sum f) ht (module M N) (intro M N)
      obtain ⟨q, hq, hqs⟩ := Raw.eval_sum_cases (intro M N) f hs
      have hv := Raw.eval_value (.sum f) ht L β
      obtain ⟨v, hv, hvs⟩ := Raw.eval_sum_cases β f hv
      have hqv :
          (fun i => evaluate L β (q i)) = v := by
        funext i
        have hqi := Raw.eval_unique (f i) (hh i).2
          (module M N) (intro M N) (hq i)
        have hvi := Raw.eval_unique (f i) (hh i).2 L β (hv i)
        rw [hqi, ih i (hh i).2 (hh i).1, ← hvi]
      have hsum := hqs L β
      rw [hqv] at hsum
      exact (L.obj n).summation.unique hsum hvs

@[simp]
theorem evaluate_self {M N : Module} {n : ℕ}
    (x : Carrier M N n) :
    evaluate (module M N) (intro M N) x = x := by
  induction x using Quotient.inductionOn with
  | _ t =>
      apply quotient_ext
      intro L β
      exact evaluate_self_raw t.1 t.2.1 t.2.2 β

private theorem Raw.eval_postcomp {M N K L : Module}
    (η : Hom K L) (β : Bilinear M N K) {n : ℕ}
    {t : Raw M N n} {z : (K.obj n).Carrier}
    (h : Raw.Eval β t z) :
    Raw.Eval (Bilinear.postcomp η β) t (η.app n z) := by
  induction h with
  | zero =>
      rw [η.map_zero]
      exact Raw.Eval.zero
  | generator x y h =>
      rw [Bilinear.postcomp, η.naturality]
      exact Raw.Eval.generator x y h
  | sum f v z hv hs ih =>
      exact Raw.Eval.sum f (fun i => η.app n (v i)) _ ih (η.map_sum hs)

private theorem evaluate_postcomp_raw {M N K L : Module}
    (η : Hom K L) (β : Bilinear M N K) {n : ℕ}
    (t : Raw M N n) (ht : t.Admissible) :
    Raw.value t ht L (Bilinear.postcomp η β) =
      η.app n (Raw.value t ht K β) := by
  exact (Raw.eval_unique t ht L (Bilinear.postcomp η β)
    (Raw.eval_postcomp η β (Raw.eval_value t ht K β))).symm

theorem evaluate_postcomp {M N K L : Module}
    (η : Hom K L) (β : Bilinear M N K) {n : ℕ}
    (x : Carrier M N n) :
    evaluate L (Bilinear.postcomp η β) x =
      η.app n (evaluate K β x) := by
  induction x using Quotient.inductionOn with
  | _ t => exact evaluate_postcomp_raw η β t.1 t.2.1

/-- The semantic coend has the required Day universal property. -/
noncomputable def universalEquiv (M N L : Module) :
    Hom (module M N) L ≃ Bilinear M N L where
  toFun := fun η => Bilinear.postcomp η (intro M N)
  invFun := lift
  left_inv := by
    intro η
    apply Hom.ext
    intro n x
    change evaluate L (Bilinear.postcomp η (intro M N))
      (show Carrier M N n from x) =
        η.app n (show Carrier M N n from x)
    rw [evaluate_postcomp, evaluate_self]
  right_inv := by
    intro β
    apply Bilinear.ext
    intro m n x y
    exact evaluate_intro β x y

/-- The general Day tensor presentation. -/
noncomputable def presentation (M N : Module) :
    DayTensorPresentation M N where
  object := module M N
  intro := intro M N
  universal := fun L => universalEquiv M N L
  universal_apply := by
    intro L η
    rfl

end DayCoend

/-- Genuine Day tensor for arbitrary specialized modules. -/
noncomputable abbrev dayTensor (M N : Module) : Module :=
  DayCoend.module M N

/-- Concrete general Day tensor presentation. -/
noncomputable def dayTensorPresentation (M N : Module) :
    DayTensorPresentation M N :=
  DayCoend.presentation M N

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

private noncomputable def sumOf {M A N : Module}
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

private theorem sumOf_hasSum {M A N : Module}
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

namespace DayInternalHom

/-- Precomposition in the representable argument of a bilinear map. -/
noncomputable def precompose {A N : Module} {m n : ℕ}
    (f : Superoperator m n)
    (b : Bilinear (representable n) A N) :
    Bilinear (representable m) A N where
  app := fun x y => b.app (Superoperator.comp f x) y
  map_zero_left := by
    intro p q y
    change b.app (Superoperator.comp f (0 : Superoperator p m)) y = 0
    rw [Superoperator.comp_zero_right]
    exact b.map_zero_left y
  map_zero_right := by
    intro p q x
    exact b.map_zero_right _
  map_sum_left := by
    intro ι _ p q x s y h
    exact b.map_sum_left y (SigmaMon.ChoiSum.comp_left f h)
  map_sum_right := by
    intro ι _ p q x y s h
    exact b.map_sum_right _ h
  naturality := by
    intro p' p q' q x y g h
    change Superoperator p m at x
    change
      b.app (Superoperator.comp f (Superoperator.comp x g)) (A.act y h) =
        N.act (b.app (Superoperator.comp f x) y)
          (Superoperator.tensor g h)
    rw [Superoperator.comp_assoc]
    exact b.naturality (Superoperator.comp f x) y g h

/-- The closed object `[A,N]`, represented pointwise by bilinear maps out of
a representable. -/
noncomputable def module (A N : Module) : Module where
  obj n :=
    { Carrier := Bilinear (representable n) A N
      zero := Bilinear.zero _ _ _
      summation := Bilinear.partialCountableSum _ _ _ }
  act := fun b f => precompose f b
  act_zero_element := by
    intro m n f
    apply Bilinear.ext
    intro p q x y
    rfl
  act_zero_map := by
    intro m n b
    apply Bilinear.ext
    intro p q x y
    change Superoperator p m at x
    change b.app (Superoperator.comp (0 : Superoperator m n) x) y = 0
    rw [Superoperator.comp_zero_left]
    exact b.map_zero_left y
  act_id := by
    intro n b
    apply Bilinear.ext
    intro p q x y
    change Superoperator p n at x
    change b.app (Superoperator.comp (Superoperator.identity n) x) y =
      b.app x y
    rw [Superoperator.identity_comp]
  act_comp := by
    intro ℓ m n b f g
    apply Bilinear.ext
    intro p q x y
    change Superoperator p ℓ at x
    simp only [precompose]
    rw [Superoperator.comp_assoc]
  act_sum_element := by
    intro ι _ m n b s f h
    intro p q x y
    exact h p q (Superoperator.comp f x) y
  act_sum_map := by
    intro ι _ m n b f s h
    intro p q x y
    exact b.map_sum_left y (SigmaMon.ChoiSum.comp_right x h)
  act_sum_from_one := by
    intro ι _ m bx bs f hs
    have hadm :
        ∀ p q (r : Superoperator p m) (y : (A.obj q).Carrier),
          ∃ z, (N.obj (p * q)).HasSum
            (fun i =>
              (precompose (f i) (bx i)).app r y) z := by
      intro p q r y
      have h1 :
          (N.obj (1 * q)).HasSum
            (fun i =>
              (bx i).app (Superoperator.identity 1) y)
            (bs.app (Superoperator.identity 1) y) :=
        hs 1 q (Superoperator.identity 1) y
      obtain ⟨z0, hz0⟩ := N.act_sum_tensor_from_one (A := q) f h1
      have hnat (i : ι) :
          (bx i).app (Superoperator.comp (f i) r) y =
            N.act
              (N.act ((bx i).app (Superoperator.identity 1) y)
                (Superoperator.tensor (f i)
                  (Superoperator.identity q)))
              (Superoperator.tensor r (Superoperator.identity q)) := by
        have hf :
            (bx i).app (f i) y =
              N.act ((bx i).app (Superoperator.identity 1) y)
                (Superoperator.tensor (f i)
                  (Superoperator.identity q)) := by
          simpa [Superoperator.identity_comp, A.act_id] using
            (bx i).naturality (Superoperator.identity 1) y (f i)
              (Superoperator.identity q)
        have hfr :
            (bx i).app (Superoperator.comp (f i) r) y =
              N.act ((bx i).app (f i) y)
                (Superoperator.tensor r
                  (Superoperator.identity q)) := by
          simpa [A.act_id] using
            (bx i).naturality (f i) y r (Superoperator.identity q)
        rw [hfr, hf, N.act_comp]
      refine
        ⟨N.act z0 (Superoperator.tensor r (Superoperator.identity q)),
          ?_⟩
      have hz :=
        N.act_sum_element
          (Superoperator.tensor r (Superoperator.identity q)) hz0
      have hfam :
          (fun i => (precompose (f i) (bx i)).app r y) =
            fun i =>
              N.act
                (N.act ((bx i).app (Superoperator.identity 1) y)
                  (Superoperator.tensor (f i)
                    (Superoperator.identity q)))
                (Superoperator.tensor r (Superoperator.identity q)) := by
        funext i
        simpa [precompose] using hnat i
      rwa [hfam]
    exact
      ⟨Bilinear.sumOf (fun i => precompose (f i) (bx i)) hadm,
        Bilinear.sumOf_hasSum _ hadm⟩
  act_sum_tensor_from_one := by
    intro ι _ m B bx bs f hs
    have hadm :
        ∀ p q (r : Superoperator p (m * B)) (y : (A.obj q).Carrier),
          ∃ z, (N.obj (p * q)).HasSum
            (fun i =>
              (precompose
                  (Superoperator.tensor (f i)
                    (Superoperator.identity B))
                  (bx i)).app
                r y) z := by
      intro p q r y
      have h1 :
          (N.obj ((1 * B) * q)).HasSum
            (fun i =>
              (bx i).app (Superoperator.identity (1 * B)) y)
            (bs.app (Superoperator.identity (1 * B)) y) :=
        hs (1 * B) q (Superoperator.identity (1 * B)) y
      let α₁ : Superoperator (1 * (B * q)) ((1 * B) * q) :=
        Superoperator.tensorAssociatorInv 1 B q
      let α₂ : Superoperator ((m * B) * q) (m * (B * q)) :=
        Superoperator.tensorAssociator m B q
      let x' : ι → (N.obj (1 * (B * q))).Carrier :=
        fun i =>
          N.act ((bx i).app (Superoperator.identity (1 * B)) y) α₁
      let s' : (N.obj (1 * (B * q))).Carrier :=
        N.act (bs.app (Superoperator.identity (1 * B)) y) α₁
      have hs' : (N.obj (1 * (B * q))).HasSum x' s' :=
        N.act_sum_element α₁ h1
      obtain ⟨z0, hz0⟩ :=
        N.act_sum_tensor_from_one (A := B * q) f hs'
      have hten (g : Superoperator m 1) :
          Superoperator.tensor
              (Superoperator.tensor g (Superoperator.identity B))
              (Superoperator.identity q) =
            Superoperator.comp α₁
              (Superoperator.comp
                (Superoperator.tensor g
                  (Superoperator.identity (B * q)))
                α₂) := by
        have hnat :=
          Superoperator.tensorAssociator_naturality g
            (Superoperator.identity B) (Superoperator.identity q)
        have h :=
          congrArg (Superoperator.comp
            (Superoperator.tensorAssociatorInv 1 B q)) hnat
        simpa [Superoperator.comp_assoc,
          Superoperator.tensorAssociator_inv_hom,
          Superoperator.identity_comp, Superoperator.tensor_identity,
          α₁, α₂] using h
      have hnat (i : ι) :
          (bx i).app
              (Superoperator.comp
                (Superoperator.tensor (f i)
                  (Superoperator.identity B))
                r)
              y =
            N.act
              (N.act (x' i)
                (Superoperator.tensor (f i)
                  (Superoperator.identity (B * q))))
              (Superoperator.comp α₂
                (Superoperator.tensor r
                  (Superoperator.identity q))) := by
        have hf :
            (bx i).app
                (Superoperator.tensor (f i)
                  (Superoperator.identity B))
                y =
              N.act
                ((bx i).app (Superoperator.identity (1 * B)) y)
                (Superoperator.tensor
                  (Superoperator.tensor (f i)
                    (Superoperator.identity B))
                  (Superoperator.identity q)) := by
          simpa [Superoperator.identity_comp, A.act_id] using
            (bx i).naturality (Superoperator.identity (1 * B)) y
              (Superoperator.tensor (f i) (Superoperator.identity B))
              (Superoperator.identity q)
        have hfr :
            (bx i).app
                (Superoperator.comp
                  (Superoperator.tensor (f i)
                    (Superoperator.identity B))
                  r)
                y =
              N.act
                ((bx i).app
                  (Superoperator.tensor (f i)
                    (Superoperator.identity B))
                  y)
                (Superoperator.tensor r
                  (Superoperator.identity q)) := by
          simpa [A.act_id] using
            (bx i).naturality
              (Superoperator.tensor (f i) (Superoperator.identity B))
              y r (Superoperator.identity q)
        rw [hfr, hf, hten, ← N.act_comp, ← N.act_comp, ← N.act_comp]
      refine
        ⟨N.act z0
            (Superoperator.comp α₂
              (Superoperator.tensor r (Superoperator.identity q))),
          ?_⟩
      have hz :=
        N.act_sum_element
          (Superoperator.comp α₂
            (Superoperator.tensor r (Superoperator.identity q)))
          hz0
      have hfam :
          (fun i =>
            (precompose
                (Superoperator.tensor (f i)
                  (Superoperator.identity B))
                (bx i)).app
              r y) =
            fun i =>
              N.act
                (N.act (x' i)
                  (Superoperator.tensor (f i)
                    (Superoperator.identity (B * q))))
                (Superoperator.comp α₂
                  (Superoperator.tensor r
                    (Superoperator.identity q))) := by
        funext i
        simpa [precompose] using hnat i
      rwa [hfam]
    exact
      ⟨Bilinear.sumOf
          (fun i =>
            precompose
              (Superoperator.tensor (f i) (Superoperator.identity B))
              (bx i))
          hadm,
        Bilinear.sumOf_hasSum _ hadm⟩


noncomputable def curry {X A N : Module} (b : Bilinear X A N) :
    Hom X (module A N) where
  app := fun n x =>
    { app := fun r y => b.app (X.act x r) y
      map_zero_left := by
        intro p q y
        change b.app (X.act x (0 : Superoperator p n)) y = 0
        rw [X.act_zero_map]
        exact b.map_zero_left y
      map_zero_right := by
        intro p q r
        exact b.map_zero_right _
      map_sum_left := by
        intro ι _ p q r s y h
        exact b.map_sum_left y (X.act_sum_map x h)
      map_sum_right := by
        intro ι _ p q r y s h
        exact b.map_sum_right _ h
      naturality := by
        intro p' p q' q r y f g
        change Superoperator p n at r
        change
          b.app (X.act x (Superoperator.comp r f)) (A.act y g) =
            N.act (b.app (X.act x r) y) (Superoperator.tensor f g)
        rw [← X.act_comp]
        exact b.naturality (X.act x r) y f g }
  map_zero := by
    intro n
    apply Bilinear.ext
    intro p q r y
    change Superoperator p n at r
    change b.app (X.act (0 : (X.obj n).Carrier) r) y = 0
    rw [X.act_zero_element]
    exact b.map_zero_left y
  map_sum := by
    intro ι _ n x s h
    intro p q r y
    exact b.map_sum_left y (X.act_sum_element r h)
  naturality := by
    intro m n x f
    apply Bilinear.ext
    intro p q r y
    change Superoperator p m at r
    simp only [module, precompose]
    rw [X.act_comp]

/-- Uncurry a map into the pointwise internal hom. -/
noncomputable def uncurry {X A N : Module}
    (η : Hom X (module A N)) : Bilinear X A N where
  app := fun {m n} x y =>
    (η.app m x).app (Superoperator.identity m) y
  map_zero_left := by
    intro m n y
    rw [η.map_zero]
    rfl
  map_zero_right := by
    intro m n x
    exact (η.app m x).map_zero_right _
  map_sum_left := by
    intro ι _ m n x s y h
    exact η.map_sum h m n (Superoperator.identity m) y
  map_sum_right := by
    intro ι _ m n x y s h
    exact (η.app m x).map_sum_right _ h
  naturality := by
    intro m' m n' n x y f g
    have hη := η.naturality x f
    have happ := congrArg
      (fun b : Bilinear (representable m') A N =>
        b.app (Superoperator.identity m') (A.act y g)) hη
    simp only [module, precompose] at happ
    rw [Superoperator.comp_identity] at happ
    rw [happ]
    have hb := (η.app m x).naturality
      (Superoperator.identity m) y f g
    change
      (η.app m x).app
          (Superoperator.comp (Superoperator.identity m) f) (A.act y g) =
        N.act ((η.app m x).app (Superoperator.identity m) y)
          (Superoperator.tensor f g) at hb
    rw [Superoperator.identity_comp] at hb
    exact hb

noncomputable def curryEquiv (X A N : Module) :
    Bilinear X A N ≃ Hom X (module A N) where
  toFun := curry
  invFun := uncurry
  left_inv := by
    intro b
    apply Bilinear.ext
    intro m n x y
    change b.app (X.act x (Superoperator.identity m)) y = b.app x y
    rw [X.act_id]
  right_inv := by
    intro η
    apply Hom.ext
    intro n x
    apply Bilinear.ext
    intro p q r y
    change Superoperator p n at r
    change
      (η.app p (X.act x r)).app (Superoperator.identity p) y =
        (η.app n x).app r y
    have hη := η.naturality x r
    have happ := congrArg
      (fun b : Bilinear (representable p) A N =>
        b.app (Superoperator.identity p) y) hη
    change
      (η.app p (X.act x r)).app (Superoperator.identity p) y =
        (η.app n x).app
          (Superoperator.comp r (Superoperator.identity p)) y at happ
    rw [Superoperator.comp_identity] at happ
    exact happ

end DayInternalHom

/-- Genuine internal hom for arbitrary specialized modules. -/
noncomputable abbrev dayInternalHom (A N : Module) : Module :=
  DayInternalHom.module A N

/-- The concrete same-universe Day closed structure. -/
noncomputable def dayClosedPresentation : DayClosedPresentation where
  tensor := dayTensorPresentation
  internalHom := dayInternalHom
  closed := fun X A N =>
    (DayCoend.universalEquiv X A N).trans
      (DayInternalHom.curryEquiv X A N)

/-- Any two Day tensor presentations of the same pair are canonically
isomorphic. -/
noncomputable def dayPresentationIso {M N : Module}
    (P Q : DayTensorPresentation M N) : Iso P.object Q.object where
  hom := (P.universal Q.object).symm Q.intro
  inv := (Q.universal P.object).symm P.intro
  hom_inv := by
    apply (Q.universal Q.object).injective
    rw [Q.universal_apply, Q.universal_apply]
    apply Bilinear.ext
    intro m n x y
    have hi := (Q.universal P.object).apply_symm_apply P.intro
    rw [Q.universal_apply] at hi
    have hh := (P.universal Q.object).apply_symm_apply Q.intro
    rw [P.universal_apply] at hh
    have hiapp := congrArg (fun b => b.app x y) hi
    have hhapp := congrArg (fun b => b.app x y) hh
    exact congrArg
      (fun z => ((P.universal Q.object).symm Q.intro).app _ z)
      hiapp |>.trans hhapp
  inv_hom := by
    apply (P.universal P.object).injective
    rw [P.universal_apply, P.universal_apply]
    apply Bilinear.ext
    intro m n x y
    have hh := (P.universal Q.object).apply_symm_apply Q.intro
    rw [P.universal_apply] at hh
    have hi := (Q.universal P.object).apply_symm_apply P.intro
    rw [Q.universal_apply] at hi
    have hhapp := congrArg (fun b => b.app x y) hh
    have hiapp := congrArg (fun b => b.app x y) hi
    exact congrArg
      (fun z => ((Q.universal P.object).symm P.intro).app _ z)
      hhapp |>.trans hiapp

/-- The coend tensor agrees canonically with the existing representable
tensor. -/
noncomputable def dayTensorRepresentableIso (A B : ℕ) :
    Iso (dayTensor (representable A) (representable B))
      (dayTensorRepresentable A B) :=
  dayPresentationIso (dayTensorPresentation _ _)
    (dayTensorRepresentablePresentation A B)

/-- Fiberwise agreement of the general internal hom with the existing
representable formula `[y(A),N](n)=N(n*A)`. -/
noncomputable def dayInternalHomRepresentableFiberEquiv
    (A : ℕ) (N : Module) (n : ℕ) :
    ((dayInternalHom (representable A) N).obj n).Carrier ≃
      ((internalHomRepresentable A N).obj n).Carrier :=
  (dayTensorRepresentableEquiv n A N).symm.trans (yonedaEquiv N (n * A))

/-- Module-level agreement of the general internal hom with the existing
representable formula. -/
noncomputable def dayInternalHomRepresentableIso
    (A : ℕ) (N : Module) :
    Iso (dayInternalHom (representable A) N)
      (internalHomRepresentable A N) where
  hom :=
    { app := fun n b =>
        b.app (Superoperator.identity n) (Superoperator.identity A)
      map_zero := by
        intro n
        rfl
      map_sum := by
        intro ι _ n f s h
        exact h n A (Superoperator.identity n) (Superoperator.identity A)
      naturality := by
        intro m n b f
        change
          b.app (Superoperator.comp f (Superoperator.identity m))
              (Superoperator.identity A) =
            N.act
              (b.app (Superoperator.identity n) (Superoperator.identity A))
              (Superoperator.tensor f (Superoperator.identity A))
        rw [Superoperator.comp_identity]
        have hb := b.naturality (Superoperator.identity n)
          (Superoperator.identity A) f (Superoperator.identity A)
        change
          b.app
              (Superoperator.comp (Superoperator.identity n) f)
              (Superoperator.comp (Superoperator.identity A)
                (Superoperator.identity A)) =
            N.act
              (b.app (Superoperator.identity n) (Superoperator.identity A))
              (Superoperator.tensor f (Superoperator.identity A)) at hb
        simpa only [Superoperator.identity_comp] using hb }
  inv :=
    { app := fun n z =>
        { app := fun r s => N.act z (Superoperator.tensor r s)
          map_zero_left := by
            intro p q s
            change (N.obj (n * A)).Carrier at z
            change Superoperator q A at s
            change
              N.act z
                (Superoperator.tensor (0 : Superoperator p n) s) = 0
            rw [Superoperator.tensor_zero_left]
            exact N.act_zero_map z
          map_zero_right := by
            intro p q r
            change (N.obj (n * A)).Carrier at z
            change Superoperator p n at r
            change
              N.act z
                (Superoperator.tensor r (0 : Superoperator q A)) = 0
            rw [Superoperator.tensor_zero_right]
            exact N.act_zero_map z
          map_sum_left := by
            intro ι _ p q r t s h
            exact N.act_sum_map z
              (SigmaMon.ChoiSum.tensor_hasSum_left h s)
          map_sum_right := by
            intro ι _ p q r s t h
            exact N.act_sum_map z
              (SigmaMon.ChoiSum.tensor_hasSum_right r h)
          naturality := by
            intro p' p q' q r s f g
            change (N.obj (n * A)).Carrier at z
            change Superoperator p n at r
            change Superoperator q A at s
            change
              N.act z
                  (Superoperator.tensor (Superoperator.comp r f)
                    (Superoperator.comp s g)) =
                N.act (N.act z (Superoperator.tensor r s))
                  (Superoperator.tensor f g)
            rw [N.act_comp, Superoperator.tensor_comp] }
      map_zero := by
        intro n
        apply Bilinear.ext
        intro p q r s
        exact N.act_zero_element _
      map_sum := by
        intro ι _ n f z h
        intro p q r s
        exact N.act_sum_element (Superoperator.tensor r s) h
      naturality := by
        intro m n z f
        apply Bilinear.ext
        intro p q r s
        change (N.obj (n * A)).Carrier at z
        change Superoperator p m at r
        change Superoperator q A at s
        simp only [internalHomRepresentable, dayInternalHom,
          DayInternalHom.module, DayInternalHom.precompose]
        rw [N.act_comp, ← Superoperator.tensor_comp,
          Superoperator.identity_comp] }
  hom_inv := by
    apply Hom.ext
    intro n z
    change (N.obj (n * A)).Carrier at z
    change
      N.act z
        (Superoperator.tensor (Superoperator.identity n)
          (Superoperator.identity A)) = z
    rw [Superoperator.tensor_identity, N.act_id]
  inv_hom := by
    apply Hom.ext
    intro n b
    apply Bilinear.ext
    intro p q r s
    change Superoperator p n at r
    change Superoperator q A at s
    change
      N.act
          (b.app (Superoperator.identity n) (Superoperator.identity A))
          (Superoperator.tensor r s) =
        b.app r s
    symm
    have hb := b.naturality (Superoperator.identity n)
      (Superoperator.identity A) r s
    change
      b.app
          (Superoperator.comp (Superoperator.identity n) r)
          (Superoperator.comp (Superoperator.identity A) s) =
        N.act
          (b.app (Superoperator.identity n) (Superoperator.identity A))
          (Superoperator.tensor r s) at hb
    simpa only [Superoperator.identity_comp] using hb

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


end SuperoperatorModule

end QLambda.Domain.Presheaf
