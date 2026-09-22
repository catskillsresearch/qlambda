/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.SigmaMon

/-!
# Specialized modules over finite-dimensional superoperators

This is the elementary presentation of a `ΣMon`-enriched presheaf over the
finite-dimensional superoperator category.  It deliberately does not assert
Day closure or a cofree exponential; those require additional constructions.
-/

namespace QLambda.Domain.Presheaf

namespace SigmaMon.ChoiSum

variable {n m ℓ : ℕ}

/-- Postcomposition by a fixed superoperator preserves every defined Choi
sum. -/
theorem comp_left {ι : Type} [Countable ι]
    (Ψ : Superoperator m ℓ) {f : ι → Superoperator n m}
    {Φ : Superoperator n m} (h : HasSum f Φ) :
    HasSum (fun i => Superoperator.comp Ψ (f i))
      (Superoperator.comp Ψ Φ) := by
  change _root_.HasSum
      (fun k => (CPMap.comp Ψ.cp (f k).cp).choi)
      (CPMap.comp Ψ.cp Φ.cp).choi
  apply Pi.hasSum.mpr
  rintro ⟨a, i⟩
  apply Pi.hasSum.mpr
  rintro ⟨b, j⟩
  simp_rw [CPMap.choi_comp_apply]
  apply hasSum_sum
  intro x _
  apply hasSum_sum
  intro y _
  exact
    ((Pi.hasSum.mp (Pi.hasSum.mp h (x, i)) (y, j)).mul_left
      (Ψ.cp.choi (a, x) (b, y)))

/-- Precomposition by a fixed superoperator preserves every defined Choi
sum. -/
theorem comp_right {ι : Type} [Countable ι]
    {f : ι → Superoperator m ℓ} {Ψ : Superoperator m ℓ}
    (Φ : Superoperator n m) (h : HasSum f Ψ) :
    HasSum (fun i => Superoperator.comp (f i) Φ)
      (Superoperator.comp Ψ Φ) := by
  change _root_.HasSum
      (fun k => (CPMap.comp (f k).cp Φ.cp).choi)
      (CPMap.comp Ψ.cp Φ.cp).choi
  apply Pi.hasSum.mpr
  rintro ⟨a, i⟩
  apply Pi.hasSum.mpr
  rintro ⟨b, j⟩
  simp_rw [CPMap.choi_comp_apply]
  apply hasSum_sum
  intro x _
  apply hasSum_sum
  intro y _
  exact
    ((Pi.hasSum.mp (Pi.hasSum.mp h (a, x)) (b, y)).mul_right
      (Φ.cp.choi (x, i) (y, j)))

end SigmaMon.ChoiSum

namespace SigmaMon.CPMapSum

variable {n m ℓ : ℕ}

/-- Postcomposition by a fixed CP map preserves ambient CP sums. -/
theorem comp_left {ι : Type} [Countable ι]
    (Ψ : CPMap m ℓ) {f : ι → CPMap n m}
    {Φ : CPMap n m} (h : HasSum f Φ) :
    HasSum (fun i => CPMap.comp Ψ (f i)) (CPMap.comp Ψ Φ) := by
  change _root_.HasSum
    (fun k => (CPMap.comp Ψ (f k)).choi) (CPMap.comp Ψ Φ).choi
  apply Pi.hasSum.mpr
  rintro ⟨a, i⟩
  apply Pi.hasSum.mpr
  rintro ⟨b, j⟩
  simp_rw [CPMap.choi_comp_apply]
  apply hasSum_sum
  intro x _
  apply hasSum_sum
  intro y _
  exact
    ((Pi.hasSum.mp (Pi.hasSum.mp h (x, i)) (y, j)).mul_left
      (Ψ.choi (a, x) (b, y)))

/-- Precomposition by a fixed CP map preserves ambient CP sums. -/
theorem comp_right {ι : Type} [Countable ι]
    {f : ι → CPMap m ℓ} {Ψ : CPMap m ℓ}
    (Φ : CPMap n m) (h : HasSum f Ψ) :
    HasSum (fun i => CPMap.comp (f i) Φ) (CPMap.comp Ψ Φ) := by
  change _root_.HasSum
    (fun k => (CPMap.comp (f k) Φ).choi) (CPMap.comp Ψ Φ).choi
  apply Pi.hasSum.mpr
  rintro ⟨a, i⟩
  apply Pi.hasSum.mpr
  rintro ⟨b, j⟩
  simp_rw [CPMap.choi_comp_apply]
  apply hasSum_sum
  intro x _
  apply hasSum_sum
  intro y _
  exact
    ((Pi.hasSum.mp (Pi.hasSum.mp h (a, x)) (b, y)).mul_right
      (Φ.choi (x, i) (y, j)))

end SigmaMon.CPMapSum

namespace SuperoperatorModule

universe u v w x

/-- A carrier equipped with a relational partial countable sum. -/
structure Fiber where
  Carrier : Type u
  zero : Carrier
  summation : @SigmaMon.PartialCountableSum Carrier ⟨zero⟩

instance (X : Fiber) : Zero X.Carrier := ⟨X.zero⟩

/-- The relation saying that a family has the indicated partial sum in a
fiber. -/
abbrev Fiber.HasSum (X : Fiber) {ι : Type} [Countable ι]
    (f : ι → X.Carrier) (x : X.Carrier) : Prop :=
  X.summation.HasSum f x

/-- A specialized right module over finite-dimensional trace-nonincreasing
superoperators.  The two sum laws are exactly enriched functoriality in the
element and superoperator arguments. -/
structure Module where
  obj : ℕ → Fiber.{u}
  act : {m n : ℕ} → (obj n).Carrier → Superoperator m n → (obj m).Carrier
  act_zero_element :
    ∀ {m n} (f : Superoperator m n), act (0 : (obj n).Carrier) f = 0
  act_zero_map :
    ∀ {m n} (x : (obj n).Carrier), act x (0 : Superoperator m n) = 0
  act_id :
    ∀ {n} (x : (obj n).Carrier), act x (Superoperator.identity n) = x
  act_comp :
    ∀ {ℓ m n} (x : (obj n).Carrier)
      (f : Superoperator m n) (g : Superoperator ℓ m),
      act (act x f) g = act x (Superoperator.comp f g)
  act_sum_element :
    ∀ {ι : Type} [Countable ι] {m n} {x : ι → (obj n).Carrier}
      {s : (obj n).Carrier} (f : Superoperator m n),
      (obj n).HasSum x s →
        (obj m).HasSum (fun i => act (x i) f) (act s f)
  act_sum_map :
    ∀ {ι : Type} [Countable ι] {m n} (x : (obj n).Carrier)
      {f : ι → Superoperator m n} {s : Superoperator m n},
      SigmaMon.ChoiSum.HasSum f s →
        (obj m).HasSum (fun i => act x (f i)) (act x s)

/-- The ambient module `CPM(-, A)` of unrestricted completely positive maps.
It is distinct from the representable `Q(-, A)`, whose elements are TNI. -/
noncomputable def cpmModule (A : ℕ) : Module where
  obj n :=
    { Carrier := CPMap n A
      zero := 0
      summation := SigmaMon.cpMapPartialCountableSum }
  act := fun x f => CPMap.comp x f.cp
  act_zero_element := by
    intro m n f
    exact CPMap.comp_zero_left f.cp
  act_zero_map := by
    intro m n x
    exact CPMap.comp_zero_right x
  act_id := by
    intro n x
    change CPMap.comp x (Superoperator.identity n).cp = x
    rw [show (Superoperator.identity n).cp = CPMap.identity n from rfl]
    exact CPMap.comp_identity x
  act_comp := by
    intro ℓ m n x f g
    simpa using (CPMap.comp_assoc x f.cp g.cp).symm
  act_sum_element := by
    intro ι _ m n x s f h
    exact SigmaMon.CPMapSum.comp_right f.cp h
  act_sum_map := by
    intro ι _ m n x f s h
    exact SigmaMon.CPMapSum.comp_left x h

@[simp]
theorem cpmModule_obj (A n : ℕ) :
    ((cpmModule A).obj n).Carrier = CPMap n A :=
  rfl

@[simp]
theorem cpmModule_act {A m n : ℕ}
    (x : CPMap n A) (f : Superoperator m n) :
    (cpmModule A).act x f = CPMap.comp x f.cp :=
  rfl

/-- A sum-preserving natural transformation of specialized modules. -/
structure Hom (M : Module.{u}) (N : Module.{v}) where
  app : ∀ n, (M.obj n).Carrier → (N.obj n).Carrier
  map_zero : ∀ n, app n 0 = 0
  map_sum :
    ∀ {ι : Type} [Countable ι] {n} {f : ι → (M.obj n).Carrier}
      {x : (M.obj n).Carrier},
      (M.obj n).HasSum f x →
        (N.obj n).HasSum (fun i => app n (f i)) (app n x)
  naturality :
    ∀ {m n} (x : (M.obj n).Carrier) (f : Superoperator m n),
      app m (M.act x f) = N.act (app n x) f

namespace Hom

@[ext]
theorem ext {M : Module.{u}} {N : Module.{v}} {f g : Hom M N}
    (h : ∀ n x, f.app n x = g.app n x) : f = g := by
  cases f
  cases g
  congr
  funext n x
  exact h n x

def id (M : Module.{u}) : Hom M M where
  app := fun _ x => x
  map_zero := fun _ => rfl
  map_sum := fun h => h
  naturality := fun _ _ => rfl

def comp {L : Module.{u}} {M : Module.{v}} {N : Module.{w}}
    (g : Hom M N) (f : Hom L M) : Hom L N where
  app := fun n x => g.app n (f.app n x)
  map_zero := by
    intro n
    rw [f.map_zero, g.map_zero]
  map_sum := fun h => g.map_sum (f.map_sum h)
  naturality := by
    intro m n x h
    rw [f.naturality, g.naturality]

@[simp]
theorem id_app (M : Module.{u}) (n : ℕ) (x : (M.obj n).Carrier) :
    (id M).app n x = x :=
  rfl

@[simp]
theorem comp_app {L : Module.{u}} {M : Module.{v}} {N : Module.{w}}
    (g : Hom M N) (f : Hom L M)
    (n : ℕ) (x : (L.obj n).Carrier) :
    (comp g f).app n x = g.app n (f.app n x) :=
  rfl

@[simp]
theorem id_comp {M : Module.{u}} {N : Module.{v}} (f : Hom M N) :
    comp (id N) f = f := by
  ext
  rfl

@[simp]
theorem comp_id {M : Module.{u}} {N : Module.{v}} (f : Hom M N) :
    comp f (id M) = f := by
  ext
  rfl

theorem comp_assoc {K : Module.{u}} {L : Module.{v}}
    {M : Module.{w}} {N : Module.{x}}
    (h : Hom M N) (g : Hom L M) (f : Hom K L) :
    comp h (comp g f) = comp (comp h g) f := by
  ext
  rfl

/-- The zero natural transformation. -/
def zero (M : Module.{u}) (N : Module.{v}) : Hom M N where
  app := fun n _ => 0
  map_zero := fun _ => rfl
  map_sum := by
    intro ι _ n f x h
    have hz :
        (N.obj n).HasSum (fun _ : (∅ : Set ι) => 0) 0 := by
      convert ((N.obj n).summation.reindex (Equiv.Set.empty ι)
        (fun i : Empty => nomatch i) 0).mpr
          (N.obj n).summation.empty using 1
      funext i
      exact i.property.elim
    exact (N.obj n).summation.remove_zero
      (fun _ : ι => (0 : (N.obj n).Carrier)) ∅ 0
      (by simp) |>.mp hz
  naturality := by
    intro m n x f
    exact (N.act_zero_element f).symm

instance (M : Module.{u}) (N : Module.{v}) : Zero (Hom M N) :=
  ⟨zero M N⟩

@[simp]
theorem zero_app (M : Module.{u}) (N : Module.{v})
    (n : ℕ) (x : (M.obj n).Carrier) :
    (0 : Hom M N).app n x = 0 :=
  rfl

/-- Pointwise partial sums of natural transformations.  Naturality belongs to
the proposed result `s`, so no choice of a pointwise sum is hidden here. -/
def HasSum {M : Module.{u}} {N : Module.{v}} {ι : Type} [Countable ι]
    (f : ι → Hom M N) (s : Hom M N) : Prop :=
  ∀ n x, (N.obj n).HasSum (fun i => (f i).app n x) (s.app n x)

theorem hasSum_unique {M : Module.{u}} {N : Module.{v}}
    {ι : Type} [Countable ι] {f : ι → Hom M N} {s t : Hom M N}
    (hs : HasSum f s) (ht : HasSum f t) : s = t := by
  ext n x
  exact (N.obj n).summation.unique (hs n x) (ht n x)

theorem hasSum_empty (M : Module.{u}) (N : Module.{v}) :
    HasSum (fun i : Empty => nomatch i) (0 : Hom M N) := by
  intro n x
  convert (N.obj n).summation.empty using 1
  change (zero M N).app n x = 0
  rfl

theorem hasSum_singleton {M : Module.{u}} {N : Module.{v}} (f : Hom M N) :
    HasSum (fun _ : PUnit => f) f := by
  intro n x
  exact (N.obj n).summation.singleton _

theorem hasSum_remove_zero {M : Module.{u}} {N : Module.{v}}
    {ι : Type} [Countable ι] (f : ι → Hom M N) (s : Set ι)
    (g : Hom M N) (hzero : ∀ i, i ∉ s → f i = 0) :
    HasSum (fun i : s => f i) g ↔ HasSum f g := by
  constructor <;> intro h n x
  · apply ((N.obj n).summation.remove_zero
      (fun i => (f i).app n x) s (g.app n x) ?_).mp
    · exact h n x
    · intro i hi
      rw [hzero i hi]
      rfl
  · apply ((N.obj n).summation.remove_zero
      (fun i => (f i).app n x) s (g.app n x) ?_).mpr
    · exact h n x
    · intro i hi
      rw [hzero i hi]
      rfl

theorem hasSum_reindex {M : Module.{u}} {N : Module.{v}}
    {ι κ : Type} [Countable ι] [Countable κ]
    (e : κ ≃ ι) (f : ι → Hom M N) (s : Hom M N) :
    HasSum (f ∘ e) s ↔ HasSum f s := by
  constructor <;> intro h n x
  · exact ((N.obj n).summation.reindex e
      (fun i => (f i).app n x) (s.app n x)).mp (h n x)
  · exact ((N.obj n).summation.reindex e
      (fun i => (f i).app n x) (s.app n x)).mpr (h n x)

/-- Postcomposition preserves every defined pointwise sum of module maps. -/
theorem hasSum_comp_left {L : Module.{u}} {M : Module.{v}}
    {N : Module.{w}} {ι : Type} [Countable ι]
    (g : Hom M N) {f : ι → Hom L M} {s : Hom L M}
    (h : HasSum f s) :
    HasSum (fun i => comp g (f i)) (comp g s) := by
  intro n x
  exact g.map_sum (h n x)

/-- Precomposition preserves every defined pointwise sum of module maps. -/
theorem hasSum_comp_right {L : Module.{u}} {M : Module.{v}}
    {N : Module.{w}} {ι : Type} [Countable ι]
    {f : ι → Hom M N} {s : Hom M N} (g : Hom L M)
    (h : HasSum f s) :
    HasSum (fun i => comp (f i) g) (comp s g) := by
  intro n x
  exact h n (g.app n x)

end Hom

/-- A module isomorphism, used without importing a second categorical
interface. -/
structure Iso (M : Module.{u}) (N : Module.{v}) where
  hom : Hom M N
  inv : Hom N M
  hom_inv : Hom.comp hom inv = Hom.id N
  inv_hom : Hom.comp inv hom = Hom.id M

end SuperoperatorModule

end QLambda.Domain.Presheaf
