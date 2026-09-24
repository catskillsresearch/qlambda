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
# Day coend sums and `dayTensor` presentation
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule
open Classical

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

end SuperoperatorModule
end QLambda.Domain.Presheaf
