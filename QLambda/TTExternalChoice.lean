/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Effects
import QLambda.OmegaQVA
import QLambda.TTInternalChoice
import QLambda.TTProbChoice

/-!
# Tagged TT computations

Exact external selection needs a carrier capable of retaining two arbitrary
computations.  A countable binary tree supplies that structure.  The root is
coordinate `0`; the left and right subtrees use the odd and positive-even
coordinates respectively.

Unlike a bare path-indexed complete lattice, this carrier is also closed under
the `ωQVA` requirements of `IsQuantumPowerModel`: it is a countable product.
The monad below is the reader transformer of the underlying TT continuation
monad, with unit, map, and bind evaluated at each tree coordinate.
-/

namespace QLambda

open Scott1972.ContinuousLattice

universe u

namespace TTContinuation

variable {n : ℕ}
variable {D E F : Type u}
variable [CompleteLattice D] [CompleteLattice E] [CompleteLattice F]

/-- A countably tagged family of computations. -/
abbrev BranchTagged (C : Type u) := ℕ → C

/-- The complete TT computation carrier with explicit external branches. -/
abbrev TTExternalContinuationPower (n : ℕ) (D : Type u)
    [CompleteLattice D] :=
  BranchTagged (TTContinuationPower n D)

private noncomputable def evalBranch {C : Type u} [CompleteLattice C]
    (i : ℕ) : ScottMap (BranchTagged C) C :=
  ⟨fun q => q i, continuous_of_preservesDirectedSup fun S _ _ => by
    rw [sSup_apply_eq_sSup_image]⟩

/-- Public coordinate evaluation for indexed logical relations. -/
noncomputable def atCoordinate {C : Type u} [CompleteLattice C]
    (i : ℕ) : ScottMap (BranchTagged C) C :=
  ⟨fun q => q i, continuous_of_preservesDirectedSup fun S _ _ => by
    rw [sSup_apply_eq_sSup_image]⟩

@[simp]
theorem atCoordinate_apply {C : Type u} [CompleteLattice C]
    (i : ℕ) (q : BranchTagged C) :
    atCoordinate i q = q i :=
  rfl

/-- Coordinatewise lifting of a Scott map. -/
noncomputable def liftTaggedMap {C C' : Type u}
    [CompleteLattice C] [CompleteLattice C']
    (f : ScottMap C C') : ScottMap (BranchTagged C) (BranchTagged C') :=
  ⟨fun q i => f (q i), continuous_of_preservesDirectedSup fun S hS hdir => by
    funext i
    have hi := f.preservesDirectedSup_coe
      ((fun q : BranchTagged C => q i) '' S) (hS.image _)
      (directedOn_image_monotone hdir fun _ _ h => h i)
    rw [sSup_apply_eq_sSup_image, sSup_apply_eq_sSup_image]
    simpa only [Set.image_image] using hi⟩

/-- Coordinatewise lifting of a binary Scott map. -/
noncomputable def liftTaggedBinary {C : Type u} [CompleteLattice C]
    (f : ScottMap (C × C) C) :
    ScottMap (BranchTagged C × BranchTagged C) (BranchTagged C) :=
  ⟨fun qr i => f (qr.1 i, qr.2 i),
    continuous_of_preservesDirectedSup fun S hS hdir => by
      funext i
      let T : Set (C × C) :=
        (fun qr : BranchTagged C × BranchTagged C =>
          (qr.1 i, qr.2 i)) '' S
      have hT : T.Nonempty := hS.image _
      have hTdir : DirectedOn (· ≤ ·) T := by
        rintro _ ⟨q, hqS, rfl⟩ _ ⟨r, hrS, rfl⟩
        obtain ⟨s, hsS, hqs, hrs⟩ := hdir q hqS r hrS
        exact ⟨(s.1 i, s.2 i), ⟨s, hsS, rfl⟩,
          ⟨hqs.1 i, hqs.2 i⟩, ⟨hrs.1 i, hrs.2 i⟩⟩
      have hf := f.preservesDirectedSup_coe T hT hTdir
      change f ((sSup S).1 i, (sSup S).2 i) =
        (sSup ((fun qr : BranchTagged C × BranchTagged C =>
          fun j => f (qr.1 j, qr.2 j)) '' S) : BranchTagged C) i
      rw [sSup_apply_eq_sSup_image, Prod.fst_sSup, Prod.snd_sSup,
        sSup_apply_eq_sSup_image, sSup_apply_eq_sSup_image]
      have hpair :
          (sSup T : C × C) =
            (sSup ((fun q : BranchTagged C => q i) '' (Prod.fst '' S)),
             sSup ((fun q : BranchTagged C => q i) '' (Prod.snd '' S))) := by
        apply Prod.ext
        · rw [Prod.fst_sSup]
          simp only [T, Set.image_image]
        · rw [Prod.snd_sSup]
          simp only [T, Set.image_image]
      rw [← hpair, hf]
      simp only [T, Set.image_image]⟩

@[simp] theorem liftTaggedMap_apply {C C' : Type u}
    [CompleteLattice C] [CompleteLattice C']
    (f : ScottMap C C') (q : BranchTagged C) (i : ℕ) :
    liftTaggedMap f q i = f (q i) := rfl

@[simp] theorem liftTaggedBinary_apply {C : Type u} [CompleteLattice C]
    (f : ScottMap (C × C) C) (q r : BranchTagged C) (i : ℕ) :
    liftTaggedBinary f (q, r) i = f (q i, r i) := rfl

private def externalChoiceAt {C : Type u} [CompleteLattice C]
    (qr : BranchTagged C × BranchTagged C) : BranchTagged C
  | 0 => ⊥
  | i + 1 => if i % 2 = 0 then qr.1 (i / 2) else qr.2 (i / 2)

/-- Pair two complete trees under a fresh unresolved root. -/
noncomputable def externalChoice {C : Type u} [CompleteLattice C] :
    ScottMap (BranchTagged C × BranchTagged C) (BranchTagged C) :=
  ⟨externalChoiceAt, continuous_of_preservesDirectedSup fun S hS _ => by
    funext i
    cases i with
    | zero =>
        rw [sSup_apply_eq_sSup_image]
        simp only [externalChoiceAt, Function.eval_apply, Set.image_image]
        have : (fun _ : BranchTagged C × BranchTagged C => (⊥ : C)) '' S = {⊥} := by
          ext x
          constructor
          · rintro ⟨_, _, rfl⟩
            simp
          · intro hx
            obtain ⟨q, hq⟩ := hS
            exact ⟨q, hq, Set.mem_singleton_iff.mp hx |>.symm⟩
        rw [this]
        simp
    | succ i =>
        rw [sSup_apply_eq_sSup_image]
        by_cases hi : i % 2 = 0
        · simp only [externalChoiceAt, Function.eval_apply, Set.image_image,
            hi, if_pos]
          rw [Prod.fst_sSup, sSup_apply_eq_sSup_image]
          simp only [Set.image_image]
        · simp only [externalChoiceAt, Function.eval_apply, Set.image_image,
            hi, if_neg]
          rw [Prod.snd_sSup, sSup_apply_eq_sSup_image]
          simp only [if_false, Set.image_image]⟩

/-- Select the left (odd coordinates) or right (positive-even coordinates)
subtree. -/
noncomputable def selectBranch {C : Type u} [CompleteLattice C]
    (tag : Bool) : ScottMap (BranchTagged C) (BranchTagged C) :=
  ⟨fun q i => if tag then q (2 * i + 2) else q (2 * i + 1),
    continuous_of_preservesDirectedSup fun S _ _ => by
      funext i
      rw [sSup_apply_eq_sSup_image, sSup_apply_eq_sSup_image]
      cases tag
      · change sSup ((fun q : BranchTagged C => q (2 * i + 1)) '' S) =
          (sSup ((fun q : BranchTagged C => fun j => q (2 * j + 1)) '' S) :
            BranchTagged C) i
        rw [sSup_apply_eq_sSup_image]
        simp only [Set.image_image]
      · change sSup ((fun q : BranchTagged C => q (2 * i + 2)) '' S) =
          (sSup ((fun q : BranchTagged C => fun j => q (2 * j + 2)) '' S) :
            BranchTagged C) i
        rw [sSup_apply_eq_sSup_image]
        simp only [Set.image_image]⟩

@[simp] theorem selectBranch_false_external {C : Type u} [CompleteLattice C]
    (q r : BranchTagged C) :
    selectBranch false (externalChoice (q, r)) = q := by
  funext i
  change (if (2 * i) % 2 = 0 then q ((2 * i) / 2) else r ((2 * i) / 2)) = q i
  simp

@[simp] theorem selectBranch_true_external {C : Type u} [CompleteLattice C]
    (q r : BranchTagged C) :
    selectBranch true (externalChoice (q, r)) = r := by
  funext i
  change (if (2 * i + 1) % 2 = 0 then q ((2 * i + 1) / 2)
    else r ((2 * i + 1) / 2)) = r i
  have hdiv : (2 * i + 1) / 2 = i := by omega
  simp [hdiv]

@[simp] theorem externalChoice_root_bot {C : Type u} [CompleteLattice C]
    (q r : BranchTagged C) :
    externalChoice (q, r) 0 = ⊥ :=
  rfl

/-- External pairing leaves the root unresolved.  Any binary operation
that is nontrivial at the root is therefore a different computation. -/
theorem externalChoice_ne_liftTaggedBinary {C : Type u} [CompleteLattice C]
    (f : ScottMap (C × C) C) (q r : BranchTagged C)
    (hne : f (q 0, r 0) ≠ ⊥) :
    externalChoice (q, r) ≠ liftTaggedBinary f (q, r) := by
  intro heq
  apply hne
  have h0 := congrArg (fun z => z 0) heq
  rw [externalChoice_root_bot, liftTaggedBinary_apply] at h0
  exact h0.symm

/-- External choice is not identified with TT internal choice. -/
theorem externalChoice_ne_internalChoice
    (q r : TTExternalContinuationPower n D)
    (hne : q 0 ⊔ r 0 ≠ ⊥) :
    externalChoice (q, r) ≠
      liftTaggedBinary (internalChoice (n := n) (D := D)) (q, r) :=
  externalChoice_ne_liftTaggedBinary
    (internalChoice (n := n) (D := D)) q r (by
      simpa [internalChoice_eq_sup] using hne)

/-! ## Reader-transformer quantum monad -/

noncomputable def taggedMap (f : ScottMap D E) :
    ScottMap (TTExternalContinuationPower n D)
      (TTExternalContinuationPower n E) :=
  liftTaggedMap (TTContinuation.map (n := n) f)

noncomputable def taggedUnit :
    ScottMap D (TTExternalContinuationPower n D) :=
  ⟨fun d _ => TTContinuation.unit (n := n) d,
    continuous_of_preservesDirectedSup fun S hS hdir => by
      funext i
      rw [sSup_apply_eq_sSup_image]
      simpa only [Set.image_image] using
        (TTContinuation.unit (n := n) :
          ScottMap D (TTContinuationPower n D)).preservesDirectedSup_coe S hS hdir⟩

private noncomputable def taggedBindAt
    (h : ScottMap D (TTExternalContinuationPower n E)) :
    ScottMap (TTExternalContinuationPower n D)
      (TTExternalContinuationPower n E) :=
  ⟨fun q i =>
      TTContinuation.bind
        ((evalBranch (C := TTContinuationPower n E) i).comp h) (q i),
    continuous_of_preservesDirectedSup fun S hS hdir => by
      funext i
      have hi := (TTContinuation.bind
        ((evalBranch (C := TTContinuationPower n E) i).comp h)).preservesDirectedSup_coe
          ((fun q : TTExternalContinuationPower n D => q i) '' S)
          (hS.image _) (directedOn_image_monotone hdir fun _ _ hq => hq i)
      rw [sSup_apply_eq_sSup_image, sSup_apply_eq_sSup_image]
      simpa only [Set.image_image] using hi⟩

noncomputable def taggedBindScott :
    ScottMap (ScottMap D (TTExternalContinuationPower n E))
      (ScottMap (TTExternalContinuationPower n D)
        (TTExternalContinuationPower n E)) :=
  ⟨taggedBindAt, continuous_of_preservesDirectedSup fun S hS hdir => by
    apply ScottMap.ext
    intro q
    funext i
    let K := fun h : ScottMap D (TTExternalContinuationPower n E) =>
      (evalBranch (C := TTContinuationPower n E) i).comp h
    have hK : K (sSup S) = sSup (K '' S) := by
      apply ScottMap.ext
      intro d
      change (sSup S : ScottMap D
        (TTExternalContinuationPower n E)) d i =
          (sSup (K '' S) : ScottMap D (TTContinuationPower n E)) d
      rw [ScottMap.sSup_apply, sSup_apply_eq_sSup_image, ScottMap.sSup_apply]
      simp only [Set.image_image]
      change sSup ((fun h : ScottMap D
          (TTExternalContinuationPower n E) => h d i) '' S) =
        sSup ((fun h : ScottMap D
          (TTExternalContinuationPower n E) => h d i) '' S)
      rfl
    have hKS : (K '' S).Nonempty := hS.image K
    have hKdir : DirectedOn (· ≤ ·) (K '' S) :=
      directedOn_image_monotone hdir fun _ _ hh d => hh d i
    have hb := (TTContinuation.bindScott (n := n)
      (D := D) (E := E)).preservesDirectedSup_coe
        (K '' S) hKS hKdir
    change TTContinuation.bind (K (sSup S)) (q i) =
      (sSup (taggedBindAt '' S) :
        ScottMap (TTExternalContinuationPower n D)
          (TTExternalContinuationPower n E)) q i
    rw [hK]
    have hbq := congrArg
      (fun m : ScottMap (TTContinuationPower n D)
        (TTContinuationPower n E) => m (q i)) hb
    calc
      TTContinuation.bind (sSup (K '' S)) (q i) =
          (sSup ((fun k => TTContinuation.bind k) '' (K '' S)) :
            ScottMap (TTContinuationPower n D)
              (TTContinuationPower n E)) (q i) := hbq
      _ = (sSup (taggedBindAt '' S) :
          ScottMap (TTExternalContinuationPower n D)
            (TTExternalContinuationPower n E)) q i := by
        rw [ScottMap.sSup_apply, ScottMap.sSup_apply,
          sSup_apply_eq_sSup_image]
        congr 1
        ext y
        constructor
        · rintro ⟨_, ⟨_, ⟨h, hh, rfl⟩, rfl⟩, rfl⟩
          exact ⟨taggedBindAt h q,
            ⟨taggedBindAt h, ⟨h, hh, rfl⟩, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨_, ⟨h, hh, rfl⟩, rfl⟩, rfl⟩
          exact ⟨TTContinuation.bind (K h),
            ⟨K h, ⟨h, hh, rfl⟩, rfl⟩, rfl⟩⟩

theorem taggedMap_id :
    taggedMap (n := n) (ScottMap.idMap : ScottMap D D) = ScottMap.idMap := by
  apply ScottMap.ext
  intro q
  funext i
  exact congrArg (fun f : ScottMap (TTContinuationPower n D)
    (TTContinuationPower n D) => f (q i)) (TTContinuation.map_id (n := n))

theorem taggedMap_comp (f : ScottMap E F) (g : ScottMap D E) :
    taggedMap (n := n) (f.comp g) =
      (taggedMap f).comp (taggedMap g) := by
  apply ScottMap.ext
  intro q
  funext i
  exact congrArg (fun h : ScottMap (TTContinuationPower n D)
    (TTContinuationPower n F) => h (q i))
      (TTContinuation.map_comp (n := n) f g)

theorem taggedMap_mono {f g : ScottMap D E} (hfg : f ≤ g) :
    taggedMap (n := n) f ≤ taggedMap g :=
  fun q i => TTContinuation.map_mono (n := n) hfg (q i)

theorem taggedMap_iSup (G : ℕ → ScottMap D E) (hG : Monotone G) :
    taggedMap (n := n) (⨆ i, G i) = ⨆ i, taggedMap (G i) := by
  apply ScottMap.ext
  intro q
  funext i
  have hbase := congrArg
    (fun m : ScottMap (TTContinuationPower n D) (TTContinuationPower n E) =>
      m (q i)) (TTContinuation.map_iSup (n := n) G hG)
  have houter := TTContinuation.iSup_apply
    (X := TTExternalContinuationPower n D)
    (Y := TTExternalContinuationPower n E)
    (fun j => taggedMap (n := n) (G j)) q
  have hcoord := congrArg
    (fun z : TTExternalContinuationPower n E => z i) houter
  have hinner := _root_.iSup_apply
    (f := fun j => taggedMap (n := n) (G j) q) (a := i)
  have hbaseEval := TTContinuation.iSup_apply
    (X := TTContinuationPower n D) (Y := TTContinuationPower n E)
    (fun j => TTContinuation.map (n := n) (G j)) (q i)
  exact hbase.trans (hbaseEval.trans (hinner.symm.trans hcoord.symm))

/-- External selection distributes through tagged bind only when it
reindexes both the source and the value continuation.  Omitting the latter
reindexing is false in this tagged reader model. -/
theorem selectBranch_taggedBind
    (selected : Bool)
    (h : ScottMap D (TTExternalContinuationPower n E))
    (q : TTExternalContinuationPower n D) :
    selectBranch selected (taggedBindScott (n := n) h q) =
      taggedBindScott (n := n) ((selectBranch selected).comp h)
        (selectBranch selected q) := by
  funext i
  cases selected <;> rfl

theorem taggedBind_atCoordinate
    (h : ScottMap D (TTExternalContinuationPower n E))
    (q : TTExternalContinuationPower n D)
    (i : ℕ) :
    atCoordinate i (taggedBindScott (n := n) h q) =
      TTContinuation.bind ((atCoordinate i).comp h) (q i) := by
  rfl

/-- A tagged computation that does not use the external-branch heap. -/
def CoordinateConstant {C : Type u} [CompleteLattice C]
    (q : BranchTagged C) : Prop :=
  ∀ i j : ℕ, q i = q j

theorem taggedUnit_coordinateConstant (d : D) :
    CoordinateConstant
      (taggedUnit (n := n) d : TTExternalContinuationPower n D) := by
  intro i j
  rfl

theorem selectBranch_coordinateConstant {C : Type u} [CompleteLattice C]
    (b : Bool) {q : BranchTagged C} (hq : CoordinateConstant q) :
    selectBranch b q = q := by
  funext i
  cases b
  · exact hq (2 * i + 1) i
  · exact hq (2 * i + 2) i

/-- If the Kleisli continuation is coordinate-constant, selection commutes
past bind without reindexing `h`. -/
theorem selectBranch_taggedBind_of_coordinateConstant
    (h : ScottMap D (TTExternalContinuationPower n E))
    (hh : ∀ d, CoordinateConstant (h d))
    (q : TTExternalContinuationPower n D)
    (b : Bool) :
    selectBranch b (taggedBindScott (n := n) h q) =
      taggedBindScott (n := n) h (selectBranch b q) := by
  have hcomp : (selectBranch b).comp h = h := by
    apply ScottMap.ext
    intro d
    exact selectBranch_coordinateConstant b (hh d)
  rw [selectBranch_taggedBind, hcomp]

theorem taggedBind_root_bot
    (h : ScottMap D (TTExternalContinuationPower n E))
    (q : TTExternalContinuationPower n D)
    (hq : q 0 = ⊥) :
    taggedBindScott (n := n) h q 0 = ⊥ := by
  change
      TTContinuation.bind
        ((evalBranch (C := TTContinuationPower n E) 0).comp h) (q 0) = ⊥
  rw [hq]
  apply ScottMap.ext
  intro k
  rw [bind_apply,
    ScottMap.bot_apply (D := ScottMap D (TTResult n)) (D' := TTResult n),
    ScottMap.bot_apply (D := ScottMap E (TTResult n)) (D' := TTResult n)]

theorem taggedBind_unit :
    taggedBindScott (n := n)
      (taggedUnit (n := n) : ScottMap D (TTExternalContinuationPower n D)) =
      ScottMap.idMap := by
  apply ScottMap.ext
  intro q
  funext i
  have hcont :
      (evalBranch (C := TTContinuationPower n D) i).comp
          (taggedUnit (n := n) :
            ScottMap D (TTExternalContinuationPower n D)) =
        (TTContinuation.unit (n := n) :
          ScottMap D (TTContinuationPower n D)) := by
    apply ScottMap.ext
    intro d
    rfl
  change TTContinuation.bind _ (q i) = q i
  rw [hcont]
  exact congrArg (fun f : ScottMap (TTContinuationPower n D)
    (TTContinuationPower n D) => f (q i))
      (TTContinuation.bind_unit (n := n))

theorem taggedUnit_bind
    (h : ScottMap D (TTExternalContinuationPower n E)) :
    (taggedBindScott (n := n) h).comp taggedUnit = h := by
  apply ScottMap.ext
  intro d
  funext i
  have hu := TTContinuation.unit_bind
    ((evalBranch (C := TTContinuationPower n E) i).comp h)
  exact congrArg (fun f : ScottMap D (TTContinuationPower n E) => f d) hu

/-- Selection commutes past bind of an external pairing of units when
the Kleisli map is coordinate-constant at those two values. -/
theorem selectBranch_taggedBind_extern_units
    (h : ScottMap D (TTExternalContinuationPower n E))
    (vL vR : D)
    (hL : CoordinateConstant (h vL))
    (hR : CoordinateConstant (h vR))
    (b : Bool) :
    selectBranch b
        (taggedBindScott (n := n) h
          (externalChoice (taggedUnit (n := n) vL,
            taggedUnit (n := n) vR))) =
      taggedBindScott (n := n) h
        (selectBranch b
          (externalChoice (taggedUnit (n := n) vL,
            taggedUnit (n := n) vR))) := by
  have hunit (v : D) :
      taggedBindScott (n := n) h (taggedUnit (n := n) v) = h v :=
    congrArg (fun g : ScottMap D (TTExternalContinuationPower n E) =>
      g v) (taggedUnit_bind (n := n) (E := E) h)
  cases b
  · rw [selectBranch_taggedBind, selectBranch_false_external]
    have hsel :
        taggedBindScott (n := n) ((selectBranch false).comp h)
            (taggedUnit (n := n) vL) =
          selectBranch false (h vL) :=
      congrArg (fun g : ScottMap D (TTExternalContinuationPower n E) =>
        g vL) (taggedUnit_bind (n := n) (E := E)
          ((selectBranch false).comp h))
    rw [hsel, selectBranch_coordinateConstant false hL, hunit]
  · rw [selectBranch_taggedBind, selectBranch_true_external]
    have hsel :
        taggedBindScott (n := n) ((selectBranch true).comp h)
            (taggedUnit (n := n) vR) =
          selectBranch true (h vR) :=
      congrArg (fun g : ScottMap D (TTExternalContinuationPower n E) =>
        g vR) (taggedUnit_bind (n := n) (E := E)
          ((selectBranch true).comp h))
    rw [hsel, selectBranch_coordinateConstant true hR, hunit]

theorem taggedBind_assoc
    (h : ScottMap D (TTExternalContinuationPower n E))
    (g : ScottMap E (TTExternalContinuationPower n F)) :
    (taggedBindScott (n := n) g).comp (taggedBindScott h) =
      taggedBindScott ((taggedBindScott g).comp h) := by
  apply ScottMap.ext
  intro q
  funext i
  let hi := (evalBranch (C := TTContinuationPower n E) i).comp h
  let gi := (evalBranch (C := TTContinuationPower n F) i).comp g
  have hassoc := TTContinuation.bind_assoc (n := n) hi gi
  have hinner :
      (evalBranch (C := TTContinuationPower n F) i).comp
          ((taggedBindScott (n := n) g).comp h) =
        (TTContinuation.bind gi).comp hi := by
    apply ScottMap.ext
    intro d
    rfl
  change TTContinuation.bind gi (TTContinuation.bind hi (q i)) =
    TTContinuation.bind _ (q i)
  rw [hinner]
  exact congrArg (fun f : ScottMap (TTContinuationPower n D)
    (TTContinuationPower n F) => f (q i)) hassoc

theorem taggedMap_eq_bind_unit (f : ScottMap D E) :
    taggedMap (n := n) f =
      taggedBindScott ((taggedUnit (n := n)).comp f) := by
  apply ScottMap.ext
  intro q
  funext i
  have hcont :
      (evalBranch (C := TTContinuationPower n E) i).comp
          ((taggedUnit (n := n)).comp f) =
        (TTContinuation.unit (n := n)).comp f := by
    apply ScottMap.ext
    intro d
    rfl
  change TTContinuation.map f (q i) =
    TTContinuation.bind _ (q i)
  rw [hcont]
  exact congrArg (fun m : ScottMap (TTContinuationPower n D)
    (TTContinuationPower n E) => m (q i))
      (TTContinuation.map_eq_bind_unit (n := n) f)

noncomputable instance instIsQuantumPowerModelTTExternal :
    IsQuantumPowerModel (TTExternalContinuationPower n) where
  str := fun _ _ => inferInstance
  map := fun f => taggedMap (n := n) f
  map_id := taggedMap_id (n := n)
  map_comp := taggedMap_comp (n := n)
  map_mono := taggedMap_mono (n := n)
  map_iSup := taggedMap_iSup (n := n)
  closed := by
    intro D _ hD
    letI : IsOmegaQVA D := hD
    letI : IsOmegaQVA (TTContinuationPower n D) :=
      IsQuantumPowerModel.closed (Q := TTContinuationPower n) hD
    exact omegaQVA_pi

noncomputable instance instIsQuantumMonadTTExternal :
    IsQuantumMonad (TTExternalContinuationPower n) where
  unit := taggedUnit (n := n)
  bind := taggedBindScott (n := n)
  bind_unit := taggedBind_unit (n := n)
  unit_bind := taggedUnit_bind (n := n)
  bind_assoc := taggedBind_assoc (n := n)
  map_eq_bind_unit := taggedMap_eq_bind_unit (n := n)

/-- The complete tagged TT model accepted by the interpreter. -/
noncomputable def externalModel (n : ℕ) : QuantumPowerModel where
  Power := TTExternalContinuationPower n

end TTContinuation

end QLambda
