/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.OmegaQVA
import Scott1972.ContinuousLattice.FunctionSpaces

/-!
# The quantum state powerdomain `Q(D)`

`IsQuantumPowerModel Q` is the conditional specification of a quantum
powerdomain: `Q` sends complete lattices to complete lattices, is a
Scott functor (including monotonicity and local continuity on monotone
`ℕ`-families), and preserves `ωQVA`.

The concrete computational layer starts from CP instruments in
`QLambda.QuantumInstrument`. A `QuantumPowerModel` is a bundled `Q`
with its instance. The capstone is parameterized by that bundle.
-/

namespace Scott1972.ContinuousLattice

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open DensityVec

/-- Conditional specification of a quantum powerdomain model. -/
class IsQuantumPowerModel (Q : (D : Type u) → [CompleteLattice D] → Type u) where
  str : ∀ (D : Type u) [CompleteLattice D], CompleteLattice (Q D)
  map : ∀ {D E : Type u} [CompleteLattice D] [CompleteLattice E],
    ScottMap D E →
      letI := str D
      letI := str E
      ScottMap (Q D) (Q E)
  map_id : ∀ {D : Type u} [CompleteLattice D],
    letI := str D
    map (ScottMap.idMap : ScottMap D D) = ScottMap.idMap
  map_comp : ∀ {D E F : Type u} [CompleteLattice D] [CompleteLattice E] [CompleteLattice F]
      (f : ScottMap E F) (g : ScottMap D E),
    letI := str D
    letI := str E
    letI := str F
    map (f.comp g) = (map f).comp (map g)
  /-- Order-enriched: `Q` is monotone on Scott maps. Needed so that a
  projection `A ◃ B` lifts to `Q(A) ◃ Q(B)` (`mapProjection`). -/
  map_mono : ∀ {D E : Type u} [CompleteLattice D] [CompleteLattice E]
      {f g : ScottMap D E},
    letI := str D
    letI := str E
    f ≤ g → map f ≤ map g
  /-- Local continuity on monotone `ℕ`-families: `Q(⨆ F n) = ⨆ Q(F n)`.
  This is the fragment of local continuity used to collapse
  `i_∞ ∘ j_∞ = id` on `[D_∞ → Q(D_∞)]`. -/
  map_iSup : ∀ {D E : Type u} [CompleteLattice D] [CompleteLattice E]
      (F : ℕ → ScottMap D E) (_hF : Monotone F),
    letI := str D
    letI := str E
    map (⨆ n, F n) = ⨆ n, map (F n)
  closed : ∀ {D : Type u} [CompleteLattice D] (_h : IsOmegaQVA D),
    letI := str D
    IsOmegaQVA (Q D)

attribute [instance] IsQuantumPowerModel.str

/-- `j ∘ i = id` as Scott maps. -/
theorem IsContinuousLatticeProjection.retr_incl_comp {A B : Type u}
    [CompleteLattice A] [CompleteLattice B]
    (P : IsContinuousLatticeProjection A B) :
    P.retr.comp P.incl = ScottMap.idMap :=
  ScottMap.ext fun x => P.retr_incl x

/-- `i ∘ j ⊑ id` as Scott maps. -/
theorem IsContinuousLatticeProjection.incl_retr_le_comp {A B : Type u}
    [CompleteLattice A] [CompleteLattice B]
    (P : IsContinuousLatticeProjection A B) :
    P.incl.comp P.retr ≤ ScottMap.idMap :=
  P.incl_retr_le

/-- A Scott functor sends a projection `A ◃ B` to a projection `Q(A) ◃ Q(B)`. -/
noncomputable def IsQuantumPowerModel.mapProjection
    {Q : (D : Type u) → [CompleteLattice D] → Type u} [inst : IsQuantumPowerModel Q]
    {A B : Type u} [CompleteLattice A] [CompleteLattice B]
    (P : IsContinuousLatticeProjection A B) :
    IsContinuousLatticeProjection (Q A) (Q B) :=
  letI := inst.str A
  letI := inst.str B
  { incl := inst.map P.incl
    retr := inst.map P.retr
    retr_incl := by
      intro d
      have hcomp := inst.map_comp (f := P.retr) (g := P.incl)
      have hid := inst.map_id (D := A)
      have hri := P.retr_incl_comp
      have : (inst.map P.retr).comp (inst.map P.incl) = ScottMap.idMap := by
        rw [← hcomp, hri, hid]
      exact congrArg (fun f : ScottMap (Q A) (Q A) => (f : Q A → Q A) d) this
    incl_retr_le := by
      intro d
      have hcomp := inst.map_comp (f := P.incl) (g := P.retr)
      have hid := inst.map_id (D := B)
      have hle := inst.map_mono (f := P.incl.comp P.retr) (g := ScottMap.idMap)
        P.incl_retr_le_comp
      have : (inst.map P.incl).comp (inst.map P.retr) ≤ ScottMap.idMap :=
        calc (inst.map P.incl).comp (inst.map P.retr)
            = inst.map (P.incl.comp P.retr) := hcomp.symm
          _ ≤ inst.map ScottMap.idMap := hle
          _ = ScottMap.idMap := hid
      exact this d }

/-- A bundled quantum powerdomain: a `Q` that satisfies the spec. -/
structure QuantumPowerModel where
  Power : (D : Type u) → [CompleteLattice D] → Type u
  [spec : IsQuantumPowerModel Power]

attribute [instance] QuantumPowerModel.spec

/-- Carrier of the model at `D`. -/
abbrev QuantumPower (M : QuantumPowerModel) (D : Type u) [CompleteLattice D] : Type u :=
  M.Power D

/-- `[D → Q(D)]` for the chosen model. -/
abbrev QuantumFunctor (M : QuantumPowerModel) (D : Type u) [CompleteLattice D] : Type u :=
  ScottMap D (M.Power D)

/-- `ωQVA` is closed under the model's powerdomain. -/
abbrev omegaQVA_closed_under_quantumPower (M : QuantumPowerModel) {D : Type u}
    [CompleteLattice D] (h : IsOmegaQVA D) : IsOmegaQVA (M.Power D) :=
  IsQuantumPowerModel.closed (Q := M.Power) h

/-! Helpers for Cartesian closure of `ωQVA`. -/
namespace FunctionSpaceOmega

variable {D E : Type u} [CompleteLattice D] [CompleteLattice E]

noncomputable def sampleStep (m : D) (b : ScottMap E E) :
    ScottMap (ScottMap D E) (ScottMap D E) :=
  ⟨fun f => stepMap m (b (f m)), continuous_of_preservesDirectedSup <| by
    intro S hS hSdir
    apply ScottMap.ext
    intro x
    by_cases hmx : m ≪ x
    · rw [stepMap_apply_of_wayBelow hmx]
      change b ((sSup S : ScottMap D E) m) =
        ((sSup ((fun f : ScottMap D E => stepMap m (b (f m))) '' S) :
          ScottMap D E) : D → E) x
      have hdir : DirectedOn (· ≤ ·)
          ((fun f : ScottMap D E => (f : D → E) m) '' S) := by
        rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
        obtain ⟨k, hk, hfk, hgk⟩ := hSdir f hf g hg
        exact ⟨k m, ⟨k, hk, rfl⟩, hfk m, hgk m⟩
      calc
        b ((sSup S : ScottMap D E) m) =
            b (sSup ((fun f : ScottMap D E => (f : D → E) m) '' S)) := by
              rw [ScottMap.sSup_apply]
        _ = sSup (b '' ((fun f : ScottMap D E => (f : D → E) m) '' S)) :=
          b.preservesDirectedSup_coe _
            (hS.image fun f : ScottMap D E => f m) hdir
        _ = ((sSup ((fun f : ScottMap D E => stepMap m (b (f m))) '' S) :
            ScottMap D E) : D → E) x := by
          rw [ScottMap.sSup_apply]
          congr 1
          ext z
          constructor
          · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
            exact ⟨stepMap m (b (f m)), ⟨f, hf, rfl⟩,
              stepMap_apply_of_wayBelow hmx⟩
          · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
            exact ⟨f m, ⟨f, hf, rfl⟩,
              (stepMap_apply_of_wayBelow hmx).symm⟩
    · change stepFun m (b ((sSup S : ScottMap D E) m)) x =
        ((sSup ((fun f : ScottMap D E => stepMap m (b (f m))) '' S) :
          ScottMap D E) : D → E) x
      rw [stepFun_of_not_wayBelow hmx, ScottMap.sSup_apply]
      apply le_antisymm bot_le
      refine sSup_le ?_
      rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      exact le_of_eq (stepFun_of_not_wayBelow hmx)⟩

noncomputable def sampleHull (M : Finset D) (b : ScottMap E E) :
    ScottMap (ScottMap D E) (ScottMap D E) :=
  M.sup fun m => sampleStep m b

theorem sampleHull_apply (M : Finset D) (b : ScottMap E E) (f : ScottMap D E) :
    sampleHull M b f = M.sup (fun m => stepMap m (b (f m))) := by
  classical
  unfold sampleHull
  induction M using Finset.induction_on with
  | empty => exact ScottMap.bot_apply f
  | @insert m M hm ih =>
    rw [Finset.sup_insert, Finset.sup_insert, ScottMap.sup_apply, ih]
    rfl

def repeatDims (dims : List ℕ) : List D → List ℕ
  | [] => []
  | _ :: ms => dims ++ repeatDims dims ms

def encSamples {b : ScottMap E E} (q : QFactorable b) : (ms : List D) →
    ScottMap D E → DensityVec (repeatDims q.dims ms)
  | [], _ => ⟨⟩
  | m :: ms, f => QFactorable.pairEnc (q.enc (f m)) (encSamples q ms f)

noncomputable def reconSamples {b : ScottMap E E} (q : QFactorable b) : (ms : List D) →
    DensityVec (repeatDims q.dims ms) → ScottMap D E
  | [], _ => ⊥
  | m :: ms, v =>
      let p := QFactorable.pairUnenc (ns := q.dims) v
      stepMap m (q.recon p.1) ⊔ reconSamples q ms p.2

theorem encSamples_mono {b : ScottMap E E} (q : QFactorable b) (ms : List D) :
    Monotone (encSamples q ms) := by
  induction ms with
  | nil => intro f g hfg; trivial
  | cons m ms ih =>
    intro f g hfg
    exact QFactorable.pairEnc_mono
      (show
        (q.enc (f m), encSamples q ms f) ≤
          (q.enc (g m), encSamples q ms g) from
        ⟨q.enc_mono (hfg m), ih hfg⟩)

theorem reconSamples_mono {b : ScottMap E E} (q : QFactorable b) (ms : List D) :
    Monotone (reconSamples q ms) := by
  induction ms with
  | nil => intro v w hvw; exact le_rfl
  | cons m ms ih =>
    intro v w hvw
    have hp := QFactorable.pairUnenc_mono (ns := q.dims) hvw
    exact sup_le_sup
      (show stepMap m (q.recon (QFactorable.pairUnenc (ns := q.dims) v).1) ≤
          stepMap m (q.recon (QFactorable.pairUnenc (ns := q.dims) w).1) by
        rw [ScottMap.le_def]
        intro x
        by_cases hmx : m ≪ x
        · simp only [stepMap_apply_of_wayBelow hmx]
          exact q.recon_mono hp.1
        · simp [stepMap, stepFun_of_not_wayBelow hmx])
      (ih hp.2)

theorem reconSamples_encSamples [DecidableEq D] {b : ScottMap E E} (q : QFactorable b)
    (ms : List D) (f : ScottMap D E) :
    reconSamples q ms (encSamples q ms f) =
      ms.toFinset.sup (fun m => stepMap m (b (f m))) := by
  classical
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [encSamples, reconSamples, QFactorable.pairEnc_unenc,
      List.toFinset_cons, Finset.sup_insert]
    rw [q.factor, ih]

noncomputable def sampleFactorable (M : Finset D) {b : ScottMap E E}
    (q : QFactorable b) : QFactorable (sampleHull M b) := by
  classical
  exact
    { dims := repeatDims q.dims M.toList
      enc := encSamples q M.toList
      recon := reconSamples q M.toList
      enc_mono := encSamples_mono q M.toList
      recon_mono := reconSamples_mono q M.toList
      factor := fun f => by
        rw [sampleHull_apply, reconSamples_encSamples]
        rw [Finset.toList_toFinset] }

def QFactorable.sup {X : Type*} [CompleteLattice X]
    {f g : ScottMap X X} (hf : QFactorable f) (hg : QFactorable g) :
    QFactorable (f ⊔ g) where
  dims := hf.dims ++ hg.dims
  enc := fun x => QFactorable.pairEnc (hf.enc x) (hg.enc x)
  recon := fun v =>
    let p := QFactorable.pairUnenc (ns := hf.dims) v
    hf.recon p.1 ⊔ hg.recon p.2
  enc_mono := fun x y h =>
    QFactorable.pairEnc_mono
      (show (hf.enc x, hg.enc x) ≤ (hf.enc y, hg.enc y) from
        ⟨hf.enc_mono h, hg.enc_mono h⟩)
  recon_mono := fun _ _ h => by
    have hp := QFactorable.pairUnenc_mono (ns := hf.dims) h
    exact sup_le_sup (hf.recon_mono hp.1) (hg.recon_mono hp.2)
  factor := fun x => by
    change (f ⊔ g) x =
      hf.recon (QFactorable.pairUnenc
        (QFactorable.pairEnc (hf.enc x) (hg.enc x))).1 ⊔
      hg.recon (QFactorable.pairUnenc
        (QFactorable.pairEnc (hf.enc x) (hg.enc x))).2
    rw [QFactorable.pairEnc_unenc, ← hf.factor, ← hg.factor]
    exact ScottMap.sup_apply f g x

def QFactorable.bot {X : Type*} [CompleteLattice X] : QFactorable (⊥ : ScottMap X X) where
  dims := []
  enc := fun _ => ⟨⟩
  recon := fun _ => ⊥
  enc_mono := fun _ _ _ => le_rfl
  recon_mono := fun _ _ _ => le_rfl
  factor := fun x => ScottMap.bot_apply x

theorem finitelySeparated_bot {X : Type*} [CompleteLattice X] :
    FinitelySeparated (⊥ : ScottMap X X) := by
  refine ⟨{(⊥ : X)}, fun x => ⟨(⊥ : X), Finset.mem_singleton_self _, ?_, bot_le⟩⟩
  simpa only [ScottMap.bot_apply] using (bot_le : (⊥ : X) ≤ ⊥)

theorem finitelySeparated_sup {X : Type*} [CompleteLattice X]
    {f g : ScottMap X X} (hf : FinitelySeparated f) (hg : FinitelySeparated g) :
    FinitelySeparated (f ⊔ g) := by
  classical
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨(M.product N).image fun p => p.1 ⊔ p.2, fun x => ?_⟩
  obtain ⟨m, hm, hfm, hmx⟩ := hM x
  obtain ⟨n, hn, hgn, hnx⟩ := hN x
  refine ⟨m ⊔ n, Finset.mem_image.mpr
    ⟨(m, n), Finset.mem_product.mpr ⟨hm, hn⟩, rfl⟩, ?_, sup_le hmx hnx⟩
  simpa [ScottMap.sup_apply] using sup_le_sup hfm hgn

theorem sampleHull_separated (M : Finset D)
    {b : ScottMap E E} (hb : FinitelySeparated b) :
    FinitelySeparated (sampleHull M b) := by
  classical
  obtain ⟨N, hN⟩ := hb
  let A : Finset (M → E) := Fintype.piFinset fun _ : M => N
  let mkMap : (M → E) → ScottMap D E :=
    fun v => M.attach.sup fun m => stepMap m.1 (v m)
  refine ⟨A.image mkMap, fun f => ?_⟩
  have hv : ∀ m : M, ∃ n ∈ N, b (f m.1) ≤ n ∧ n ≤ f m.1 :=
    fun m => hN (f m.1)
  choose v hv using hv
  have hvA : v ∈ A := by
    rw [Fintype.mem_piFinset]
    exact fun m => (hv m).1
  refine ⟨mkMap v, Finset.mem_image.mpr ⟨v, hvA, rfl⟩, ?_, ?_⟩
  · rw [sampleHull_apply]
    refine Finset.sup_le fun m hm => ?_
    calc
      stepMap m (b (f m)) ≤ stepMap m (v ⟨m, hm⟩) := by
        rw [ScottMap.le_def]
        intro x
        by_cases hmx : m ≪ x
        · simpa [stepMap_apply_of_wayBelow hmx] using (hv ⟨m, hm⟩).2.1
        · simp [stepMap, stepFun_of_not_wayBelow hmx]
      _ ≤ M.attach.sup (fun p : M => stepMap p.1 (v p)) :=
        by
          have hle := Finset.le_sup (f := fun p : M => stepMap p.1 (v p))
            (Finset.mem_attach M (⟨m, hm⟩ : M))
          exact hle
  · refine Finset.sup_le fun m hm => ?_
    rw [ScottMap.le_def]
    intro x
    by_cases hmx : (m.1 : D) ≪ x
    · rw [stepMap_apply_of_wayBelow hmx]
      exact (hv m).2.2.trans (f.monotone hmx.le)
    · simp [stepMap, stepFun_of_not_wayBelow hmx]

noncomputable def finiteHull (T : ℕ → ℕ → ScottMap (ScottMap D E) (ScottMap D E))
    (n : ℕ) : ScottMap (ScottMap D E) (ScottMap D E) :=
  (Finset.range (n + 1)).sup fun i =>
    (Finset.range (n + 1)).sup fun j => T i j

theorem finiteHull_ge (T : ℕ → ℕ → ScottMap (ScottMap D E) (ScottMap D E))
    {i j n : ℕ} (hi : i ≤ n) (hj : j ≤ n) : T i j ≤ finiteHull T n :=
  calc
    T i j ≤ (Finset.range (n + 1)).sup (fun j => T i j) :=
      Finset.le_sup (f := fun j => T i j)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    _ ≤ finiteHull T n :=
      Finset.le_sup (f := fun i =>
        (Finset.range (n + 1)).sup fun j => T i j)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

theorem finiteHull_mono (T : ℕ → ℕ → ScottMap (ScottMap D E) (ScottMap D E)) :
    Monotone (finiteHull T) := by
  intro n k hnk
  refine Finset.sup_le fun i hi => Finset.sup_le fun j hj => finiteHull_ge T
    ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hnk)
    ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hnk)

noncomputable def qFactorableFinsetSup {X I : Type*} [CompleteLattice X]
    (s : Finset I) (f : I → ScottMap X X) (hf : ∀ i ∈ s, QFactorable (f i)) :
    QFactorable (s.sup f) :=
  Classical.choice <| by
    classical
    induction s using Finset.induction_on with
    | empty => exact ⟨QFactorable.bot⟩
    | @insert i s hi ih =>
      rw [Finset.sup_insert]
      exact ⟨QFactorable.sup (hf i (Finset.mem_insert_self i s))
        (Classical.choice (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)))⟩

theorem finitelySeparated_finsetSup {X I : Type*} [CompleteLattice X]
    (s : Finset I) (f : I → ScottMap X X)
    (hf : ∀ i ∈ s, FinitelySeparated (f i)) :
    FinitelySeparated (s.sup f) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact finitelySeparated_bot
  | @insert i s hi ih =>
    rw [Finset.sup_insert]
    exact finitelySeparated_sup (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

noncomputable def finiteHull_factorable
    (T : ℕ → ℕ → ScottMap (ScottMap D E) (ScottMap D E))
    (hT : ∀ i j, QFactorable (T i j)) (n : ℕ) :
    QFactorable (finiteHull T n) := by
  classical
  unfold finiteHull
  exact qFactorableFinsetSup _ _ fun i hi =>
    qFactorableFinsetSup _ _ fun j hj => hT i j

theorem finiteHull_separated
    (T : ℕ → ℕ → ScottMap (ScottMap D E) (ScottMap D E))
    (hT : ∀ i j, FinitelySeparated (T i j)) (n : ℕ) :
    FinitelySeparated (finiteHull T n) := by
  classical
  unfold finiteHull
  exact finitelySeparated_finsetSup _ _ fun i hi =>
    finitelySeparated_finsetSup _ _ fun j hj => hT i j

theorem map_approx_iSup {X Y : Type*} [CompleteLattice X] [CompleteLattice Y]
    (hX : IsOmegaQVA X) (f : ScottMap X Y) (x : X) :
    f x = ⨆ n, f (hX.approx n x) := by
  have hx : x = ⨆ n, (hX.approx n : X → X) x := by
    simpa [scottMap_iSup_apply, ScottMap.idMap_apply] using
      (congrArg (fun g : ScottMap X X => (g : X → X) x) hX.iSup_approx).symm
  have hdir : DirectedOn (· ≤ ·)
      (Set.range fun n => (hX.approx n : X → X) x) :=
    directedOn_range.2 fun i j =>
      ⟨max i j, hX.monotone_approx (le_max_left i j) x,
        hX.monotone_approx (le_max_right i j) x⟩
  calc
    f x = f (sSup (Set.range fun n => (hX.approx n : X → X) x)) := by
      exact congrArg (f : X → Y) (by rw [sSup_range]; exact hx)
    _ = sSup (f '' Set.range (fun n => (hX.approx n : X → X) x)) :=
      f.preservesDirectedSup_coe _ (Set.range_nonempty _) hdir
    _ = ⨆ n, f (hX.approx n x) := by
      rw [← Set.range_comp, sSup_range]
      rfl

end FunctionSpaceOmega

/-- `ωQVA` is Cartesian closed (not a field of the quantum-power spec). -/
noncomputable def omegaQVA_closed_under_functionSpace {D E : Type u}
    [CompleteLattice D] [CompleteLattice E]
    (hD : IsOmegaQVA D) (hE : IsOmegaQVA E) : IsOmegaQVA (ScottMap D E) := by
  let M : ℕ → Finset D := fun i => Classical.choose (hD.separated i)
  have hM : ∀ i x, ∃ m ∈ M i, (hD.approx i : D → D) x ≤ m ∧ m ≤ x :=
    fun i => Classical.choose_spec (hD.separated i)
  let T : ℕ → ℕ → ScottMap (ScottMap D E) (ScottMap D E) :=
    fun i j => FunctionSpaceOmega.sampleHull (M i) (hE.approx j)
  exact
    { isContinuousLattice :=
        theorem_3_3_isContinuousLattice hD.isContinuousLattice hE.isContinuousLattice
      approx := FunctionSpaceOmega.finiteHull T
      qfactorable := fun n => FunctionSpaceOmega.finiteHull_factorable T
        (fun i j => FunctionSpaceOmega.sampleFactorable (M i) (hE.qfactorable j)) n
      separated := fun n => FunctionSpaceOmega.finiteHull_separated T
        (fun i j => FunctionSpaceOmega.sampleHull_separated (M i) (hE.separated j)) n
      monotone_approx := FunctionSpaceOmega.finiteHull_mono T
      iSup_approx := by
        apply ScottMap.ext
        intro f
        apply ScottMap.ext
        intro x
        rw [scottMap_iSup_apply, ScottMap.idMap_apply]
        change ((⨆ n, FunctionSpaceOmega.finiteHull T n f) : ScottMap D E) x = f x
        rw [show (⨆ n, FunctionSpaceOmega.finiteHull T n f) =
            sSup (Set.range fun n => FunctionSpaceOmega.finiteHull T n f) from
          sSup_range.symm,
          ScottMap.sSup_apply, ← Set.range_comp, sSup_range]
        apply le_antisymm
        · refine iSup_le fun n => ?_
          have hn := finitelySeparated_le_id
            (FunctionSpaceOmega.finiteHull_separated T
              (fun i j => FunctionSpaceOmega.sampleHull_separated
                (M i) (hE.separated j)) n) f
          exact hn x
        · have hfx : f x =
              sSup ((f : D → E) '' {y : D | y ≪ x}) := by
            rw [← f.preservesDirectedSup_coe {y : D | y ≪ x}
              ⟨⊥, bot_wayBelow x⟩ (directedOn_wayBelow x),
              hD.isContinuousLattice.sSup_wayBelow x]
          rw [hfx]
          refine sSup_le ?_
          rintro _ ⟨y, hyx, rfl⟩
          rw [FunctionSpaceOmega.map_approx_iSup hD f y]
          refine iSup_le fun i => ?_
          rw [show f (hD.approx i y) =
              ⨆ j, hE.approx j (f (hD.approx i y)) by
            simpa [ScottMap.idMap_apply] using
              FunctionSpaceOmega.map_approx_iSup hE
                (ScottMap.idMap : ScottMap E E) (f (hD.approx i y))]
          refine iSup_le fun j => ?_
          obtain ⟨m, hmM, haim, hmy⟩ := hM i y
          have hmx : m ≪ x := WayBelow.le_trans hmy hyx
          let n := max i j
          calc
            hE.approx j (f (hD.approx i y)) ≤ hE.approx j (f m) :=
              (hE.approx j).monotone (f.monotone haim)
            _ = (stepMap m (hE.approx j (f m)) : D → E) x :=
              (stepMap_apply_of_wayBelow hmx).symm
            _ ≤ ((FunctionSpaceOmega.sampleHull (M i) (hE.approx j) f :
                ScottMap D E) : D → E) x := by
              rw [FunctionSpaceOmega.sampleHull_apply]
              exact Finset.le_sup (f := fun m =>
                stepMap m (hE.approx j (f m))) hmM x
            _ ≤ (FunctionSpaceOmega.finiteHull T n f : D → E) x :=
              FunctionSpaceOmega.finiteHull_ge T
                (le_max_left i j) (le_max_right i j) f x
            _ ≤ ⨆ n, (FunctionSpaceOmega.finiteHull T n f : D → E) x :=
              le_iSup (fun n =>
                (FunctionSpaceOmega.finiteHull T n f : D → E) x) n }

end Scott1972.ContinuousLattice
