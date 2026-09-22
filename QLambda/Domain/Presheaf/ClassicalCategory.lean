import QLambda.Domain.Presheaf.Classical

/-!
# Biorthogonal category and additive products

The Day-negation classical category is the full category of objects whose
canonical double-negation unit has an exhibited inverse.  No idempotence of
the continuation monad is assumed.

This file also constructs the additive product of specialized modules.
Products are pointwise and therefore need no unjustified total addition in a
partial-sum fiber.  A coproduct/biproduct would require a separate
construction; it is not fabricated from the partial sum relation.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u

/-- A small ordinary-category interface used for the concrete full
biorthogonal subcategory. -/
structure CategoryPresentation where
  Obj : Type (u + 1)
  hom : Obj → Obj → Type u
  id : {A : Obj} → hom A A
  comp : {A B C : Obj} → hom B C → hom A B → hom A C
  id_comp : ∀ {A B : Obj} (f : hom A B), comp id f = f
  comp_id : ∀ {A B : Obj} (f : hom A B), comp f id = f
  assoc :
    ∀ {A B C D : Obj} (h : hom C D) (g : hom B C) (f : hom A B),
      comp (comp h g) f = comp h (comp g f)

/-- Exact, non-idempotence-assuming witness that the canonical continuation
map of one module is invertible. -/
structure CanonicalReflexivity (M : Module) where
  inv : Hom (DayNegation.neg (DayNegation.neg M)) M
  hom_inv :
    Hom.comp (DayNegation.unit M) inv =
      Hom.id (DayNegation.neg (DayNegation.neg M))
  inv_hom :
    Hom.comp inv (DayNegation.unit M) = Hom.id M

/-- Package a canonical-reflexivity witness as an isomorphism. -/
noncomputable def CanonicalReflexivity.iso {M : Module}
    (h : CanonicalReflexivity M) :
    Iso M (DayNegation.neg (DayNegation.neg M)) where
  hom := DayNegation.unit M
  inv := h.inv
  hom_inv := h.hom_inv
  inv_hom := h.inv_hom

/-- The exact finite-dimensional biorthogonality statement still required
to put a representable in the classical category. -/
abbrev RepresentableReflexivity (A : ℕ) :=
  CanonicalReflexivity (representable A)

/-- Concrete module-level description of the first Day negation of a
representable. -/
noncomputable def dayNegationRepresentableIso (A : ℕ) :
    Iso (DayNegation.neg (representable A))
      (internalHomRepresentable A dayTensorUnit) :=
  dayInternalHomRepresentableIso A dayTensorUnit

/-- Explicit fibers of representable Day negation:
`¬y(A)(n) ≃ Superoperator (n*A) 1`. -/
noncomputable def dayNegationRepresentableFiberEquiv (A n : ℕ) :
    ((DayNegation.neg (representable A)).obj n).Carrier ≃
      Superoperator (n * A) 1 :=
  (dayInternalHomRepresentableFiberEquiv A dayTensorUnit n).trans
    (Equiv.refl _)

/-- The tensor pairing is the distinguished element of `¬y(1)(1)`. -/
noncomputable def dayNegationOneProbe :
    ((DayNegation.neg (representable 1)).obj 1).Carrier :=
  dayTensorIntro 1 1

@[simp]
theorem dayNegationOneProbe_app {m n : ℕ}
    (x : Superoperator m 1) (y : Superoperator n 1) :
    dayNegationOneProbe.app x y = Superoperator.tensor x y :=
  rfl

/-- Evaluation at the tensor pairing gives a concrete inverse candidate
from `¬¬y(1)` to `y(1)`. -/
noncomputable def representableOneDoubleDualEvaluation :
    Hom (DayNegation.neg (DayNegation.neg (representable 1)))
      (representable 1) where
  app := fun n F =>
    Superoperator.comp
      (F.app (Superoperator.identity n) dayNegationOneProbe)
      (Superoperator.tensorRightUnitorInv n)
  map_zero := by
    intro n
    change Superoperator.comp 0
      (Superoperator.tensorRightUnitorInv n) = 0
    rw [Superoperator.comp_zero_left]
  map_sum := by
    intro ι _ n f s h
    exact SigmaMon.ChoiSum.comp_right
      (Superoperator.tensorRightUnitorInv n)
      (h n 1 (Superoperator.identity n) dayNegationOneProbe)
  naturality := by
    intro m n F f
    change
      Superoperator.comp
          (F.app
            (Superoperator.comp f (Superoperator.identity m))
            dayNegationOneProbe)
          (Superoperator.tensorRightUnitorInv m) =
        Superoperator.comp
          (Superoperator.comp
            (F.app (Superoperator.identity n) dayNegationOneProbe)
            (Superoperator.tensorRightUnitorInv n))
          f
    rw [Superoperator.comp_identity]
    have hF := F.naturality (Superoperator.identity n)
      dayNegationOneProbe f (Superoperator.identity 1)
    change
      F.app
          (Superoperator.comp (Superoperator.identity n) f)
          ((DayNegation.neg (representable 1)).act
            dayNegationOneProbe (Superoperator.identity 1)) =
        Superoperator.comp
          (F.app (Superoperator.identity n) dayNegationOneProbe)
          (Superoperator.tensor f (Superoperator.identity 1)) at hF
    rw [Superoperator.identity_comp,
      (DayNegation.neg (representable 1)).act_id] at hF
    rw [hF]
    calc
      Superoperator.comp
          (Superoperator.comp
            (F.app (Superoperator.identity n) dayNegationOneProbe)
            (Superoperator.tensor f (Superoperator.identity 1)))
          (Superoperator.tensorRightUnitorInv m) =
        Superoperator.comp
          (F.app (Superoperator.identity n) dayNegationOneProbe)
          (Superoperator.comp
            (Superoperator.tensor f (Superoperator.identity 1))
            (Superoperator.tensorRightUnitorInv m)) :=
              (Superoperator.comp_assoc _ _ _).symm
      _ = Superoperator.comp
          (F.app (Superoperator.identity n) dayNegationOneProbe)
          (Superoperator.comp
            (Superoperator.tensorRightUnitorInv n) f) := by
              rw [Superoperator.tensorRightUnitorInv_naturality]
      _ = Superoperator.comp
          (Superoperator.comp
            (F.app (Superoperator.identity n) dayNegationOneProbe)
            (Superoperator.tensorRightUnitorInv n))
          f :=
            Superoperator.comp_assoc _ _ _

@[simp]
theorem representableOneDoubleDualEvaluation_app
    (n : ℕ)
    (F : ((DayNegation.neg (DayNegation.neg (representable 1))).obj n).Carrier) :
    representableOneDoubleDualEvaluation.app n F =
      Superoperator.comp
        (F.app (Superoperator.identity n) dayNegationOneProbe)
        (Superoperator.tensorRightUnitorInv n) :=
  rfl

@[simp]
theorem representableOne_unit_app_app
    {n p q : ℕ} (x : Superoperator n 1)
    (r : Superoperator p n)
    (b : ((DayNegation.neg (representable 1)).obj q).Carrier) :
    ((DayNegation.unit (representable 1)).app n x).app r b =
      dayTensorUnit.act
        (b.app (Superoperator.identity q)
          ((representable 1).act x r))
        (Superoperator.tensorSwap p q) :=
  rfl

private theorem tensorSwap_one_one :
    Superoperator.tensorSwap 1 1 = Superoperator.identity 1 := by
  rw [show Superoperator.tensorSwap 1 1 =
    Superoperator.ofEquivalence (Superoperator.tensorSwapEquiv 1 1) from rfl]
  have h : Superoperator.tensorSwapEquiv 1 1 =
      Equiv.refl (Fin 1) := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    omega
  rw [h, Superoperator.ofEquivalence_refl]

private theorem tensorRightUnitorInv_one :
    Superoperator.tensorRightUnitorInv 1 =
      Superoperator.identity 1 := by
  rw [show Superoperator.tensorRightUnitorInv 1 =
    Superoperator.ofEquivalence
      (Superoperator.tensorRightUnitorEquiv 1).symm from rfl]
  have h : (Superoperator.tensorRightUnitorEquiv 1).symm =
      Equiv.refl (Fin 1) := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    omega
  rw [h, Superoperator.ofEquivalence_refl]

/-- Evaluation at the tensor probe is a retraction of the canonical unit for
`y(1)`.  The converse is precisely the remaining bipolar-surjectivity
direction. -/
theorem representableOneDoubleDualEvaluation_unit :
    Hom.comp representableOneDoubleDualEvaluation
      (DayNegation.unit (representable 1)) =
        Hom.id (representable 1) := by
  apply Hom.ext
  intro n x
  rw [Hom.comp_app, representableOneDoubleDualEvaluation_app, Hom.id_app]
  change Superoperator n 1 at x
  rw [representableOne_unit_app_app]
  unfold dayNegationOneProbe dayTensorIntro
  simp only [representable_act, Superoperator.comp_identity]
  change
    Superoperator.comp
        (Superoperator.comp
          (Superoperator.tensor (Superoperator.identity 1) x)
          (Superoperator.tensorSwap n 1))
        (Superoperator.tensorRightUnitorInv n) = x
  rw [← Superoperator.tensorSwap_naturality x
      (Superoperator.identity 1),
    tensorSwap_one_one, Superoperator.identity_comp,
    Superoperator.tensorRightUnitorInv_naturality,
    tensorRightUnitorInv_one, Superoperator.identity_comp]

/-- The canonical double-negation unit is fiberwise injective for `y(1)`. -/
theorem representableOne_unit_injective (n : ℕ) :
    Function.Injective
      ((DayNegation.unit (representable 1)).app n) := by
  intro x y hxy
  have hret (z : Superoperator n 1) :
      representableOneDoubleDualEvaluation.app n
          ((DayNegation.unit (representable 1)).app n z) = z := by
    have h := congrArg
      (fun f : Hom (representable 1) (representable 1) => f.app n z)
      representableOneDoubleDualEvaluation_unit
    exact h
  rw [← hret x, hxy, hret y]

/-- For `y(1)`, fiberwise bipolar surjectivity alone completes the concrete
reflexivity witness: the required sum-preserving inverse is the explicit
evaluation map above. -/
noncomputable def representableOneReflexivityOfSurjective
    (h : ∀ n, Function.Surjective
      ((DayNegation.unit (representable 1)).app n)) :
    RepresentableReflexivity 1 where
  inv := representableOneDoubleDualEvaluation
  hom_inv := by
    apply Hom.ext
    intro n F
    obtain ⟨x, rfl⟩ := h n F
    have hret := congrArg
      (fun f : Hom (representable 1) (representable 1) => f.app n x)
      representableOneDoubleDualEvaluation_unit
    exact congrArg ((DayNegation.unit (representable 1)).app n) hret
  inv_hom := representableOneDoubleDualEvaluation_unit

/-- A representable source constructor, once its concrete finite-dimensional
biorthogonality theorem is supplied. -/
noncomputable def representableBiorthogonalObject
    (A : ℕ) (hA : 0 < A) (h : RepresentableReflexivity A) :
    ClassicalObject (DayNegation.data) where
  module := representable A
  basis := representablePseudoBasis A hA
  reflexive := h.iso
  canonical := rfl

/-- The zero partial-sum fiber.  Every countable family has its unique value
because the carrier is a singleton. -/
noncomputable def zeroFiber : Fiber where
  Carrier := PUnit
  zero := PUnit.unit
  summation :=
    { HasSum := fun _ _ => True
      unique := fun _ _ => Subsingleton.elim _ _
      empty := trivial
      singleton := fun _ => trivial
      remove_zero := fun _ _ _ _ => iff_true_intro trivial
      reindex := fun _ _ _ => iff_true_intro trivial
      flatten := by
        intro ι _ κ _ f a
        constructor
        · intro _
          exact ⟨fun _ => PUnit.unit, fun _ => trivial, trivial⟩
        · intro _
          trivial }

theorem zeroFiber_subsingleton : Subsingleton zeroFiber.Carrier := by
  change Subsingleton PUnit
  infer_instance

/-- There is only one CP map into the zero-dimensional output. -/
theorem cpMap_to_zero_subsingleton (n : ℕ) :
    Subsingleton (CPMap n 0) where
  allEq _Φ _Ψ := by
    apply CPMap.ext
    ext i
    exact Fin.elim0 i.1

/-- Consequently every superoperator into dimension zero is the zero map. -/
theorem superoperator_to_zero_subsingleton (n : ℕ) :
    Subsingleton (Superoperator n 0) where
  allEq _Φ _Ψ :=
    Superoperator.ext ((cpMap_to_zero_subsingleton n).allEq _ _)

/-- Every fiber of the zero-dimensional representable is a singleton. -/
theorem representableZero_subsingleton (n : ℕ) :
    Subsingleton (((representable 0).obj n).Carrier) :=
  superoperator_to_zero_subsingleton n

/-- Zero specialized module. -/
noncomputable def zeroModule : Module where
  obj := fun _ => zeroFiber
  act := fun _ _ => (0 : zeroFiber.Carrier)
  act_zero_element := fun _ => rfl
  act_zero_map := fun _ => rfl
  act_id := fun _ => rfl
  act_comp := fun _ _ _ => rfl
  act_sum_element := by
    intros
    trivial
  act_sum_map := by
    intros
    trivial

/-- Negation of a fiberwise subsingleton module is fiberwise subsingleton. -/
theorem neg_subsingleton (M : Module)
    (hM : ∀ n, Subsingleton (M.obj n).Carrier) (n : ℕ) :
    Subsingleton ((DayNegation.neg M).obj n).Carrier where
  allEq b c := by
    change Bilinear (representable n) M dayTensorUnit at b c
    apply Bilinear.ext
    intro p q x y
    have hy : y = 0 := (hM q).allEq _ _
    subst y
    exact (b.map_zero_right x).trans (c.map_zero_right x).symm

/-- Canonical pseudo-basis of the zero module. -/
noncomputable def zeroPseudoBasis : PseudoBasis zeroModule where
  Index := PUnit
  countableIndex := inferInstance
  coeff := fun _ => PseudoRepresentable.representable 1 Nat.zero_lt_one
  ket := fun _ => 0
  bra := fun _ => 0
  resolves := by
    intro n x
    change True
    trivial

/-- The zero module is genuinely fixed by Day double negation. -/
noncomputable def zeroDoubleDualIso :
    Iso zeroModule
      (DayNegation.data.doubleDual zeroModule) where
  hom := DayNegation.unit zeroModule
  inv := 0
  hom_inv := by
    apply Hom.ext
    intro n x
    exact
      (neg_subsingleton (DayNegation.neg zeroModule)
        (neg_subsingleton zeroModule
          (fun _ => zeroFiber_subsingleton)) n).allEq _ _
  inv_hom := by
    apply Hom.ext
    intro n x
    exact zeroFiber_subsingleton.allEq _ _

/-- A concrete inhabitant of the biorthogonal category. -/
noncomputable def zeroBiorthogonalObject :
    ClassicalObject (DayNegation.data) where
  module := zeroModule
  basis := zeroPseudoBasis
  reflexive := zeroDoubleDualIso
  canonical := rfl

/-- The canonical pseudo-basis of the zero-dimensional representable.  Its
single coefficient factors through zero; this is the positive-dimensional
coefficient required by `PseudoBasis`, not a positivity assumption on the
represented dimension. -/
noncomputable def representableZeroPseudoBasis :
    PseudoBasis (representable 0) where
  Index := PUnit
  countableIndex := inferInstance
  coeff := fun _ => PseudoRepresentable.representable 1 Nat.zero_lt_one
  ket := fun _ => 0
  bra := fun _ => 0
  resolves := by
    intro n x
    have hx : x = 0 := (representableZero_subsingleton n).allEq _ _
    subst x
    change ((representable 0).obj n).HasSum (fun _ : PUnit => 0) 0
    simpa using ((representable 0).obj n).summation.singleton
      (0 : ((representable 0).obj n).Carrier)

/-- The zero-dimensional representable is canonically Day-reflexive. -/
noncomputable def representableZeroReflexivity :
    RepresentableReflexivity 0 where
  inv := 0
  hom_inv := by
    apply Hom.ext
    intro n x
    exact
      (neg_subsingleton (DayNegation.neg (representable 0))
        (neg_subsingleton (representable 0)
          representableZero_subsingleton) n).allEq _ _
  inv_hom := by
    apply Hom.ext
    intro n x
    exact (representableZero_subsingleton n).allEq _ _

/-- Concrete classical object for `y(0)`. -/
noncomputable def representableZeroBiorthogonalObject :
    ClassicalObject (DayNegation.data) where
  module := representable 0
  basis := representableZeroPseudoBasis
  reflexive := representableZeroReflexivity.iso
  canonical := rfl

/-- The mathematically valid full category of Day-biorthogonal objects.
Objects contain a pseudo-basis and an inverse to the canonical unit. -/
noncomputable def biorthogonalCategory : CategoryPresentation where
  Obj := ClassicalObject (DayNegation.data)
  hom := ClassicalObject.Hom
  id := ClassicalObject.id _
  comp := ClassicalObject.comp
  id_comp := ClassicalObject.id_comp
  comp_id := ClassicalObject.comp_id
  assoc := fun h g f => (ClassicalObject.comp_assoc h g f).symm

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
