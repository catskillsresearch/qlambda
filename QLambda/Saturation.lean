/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Scott1972.ContinuousLattice.FunctionSpaces
import Scott1972.ContinuousLattice.WayBelow

/-!
# Finite separation and 2-level saturation flattening

Mechanization of Chen–Kou–Lyu (arXiv:2608.03073) Lemmas 6.8 and 6.9
in the `Scott1972` continuous-lattice setting. The mathematics is
Chen–Kou–Lyu arXiv:2608.03073 (v1 Lemmas 6.5–6.7); see
`sources/Finite-valuation-approximable-structures-a-solution-to-the-Jung--Tix-problem-of-probabilistic-powerdomains.md`.
-/

namespace Scott1972.ContinuousLattice

variable {D : Type*} [CompleteLattice D]

/-- Jung / CKL finite separator: `f` is finitely separated from `id` if a
finite set `M` interpolates `f(x) ≤ m ≤ x` at every `x`. -/
def FinitelySeparated (f : ScottMap D D) : Prop :=
  ∃ M : Finset D, ∀ x, ∃ m ∈ M, (f : D → D) x ≤ m ∧ m ≤ x

theorem finitelySeparated_le_id {f : ScottMap D D} (hf : FinitelySeparated f) (x : D) :
    (f : D → D) x ≤ x := by
  obtain ⟨_, hM⟩ := hf
  obtain ⟨m, _, hfxm, hmx⟩ := hM x
  exact hfxm.trans hmx

theorem finitelySeparated_comp_self {f : ScottMap D D} (hf : FinitelySeparated f) :
    FinitelySeparated (f.comp f) := by
  obtain ⟨M, hM⟩ := hf
  refine ⟨M, fun x => ?_⟩
  obtain ⟨m, hmM, hfx, hmx⟩ := hM x
  obtain ⟨m', _, hfm, hm'm⟩ := hM m
  exact ⟨m, hmM, ((f.monotone hfx).trans hfm).trans hm'm, hmx⟩

theorem scottMap_iSup_apply {ι : Type*} (f : ι → ScottMap D D) (x : D) :
    ((⨆ i, f i) : ScottMap D D) x = ⨆ i, (f i : D → D) x := by
  rw [show (⨆ i, f i) = sSup (Set.range f) from sSup_range.symm,
    ScottMap.sSup_apply, ← Set.range_comp]
  rfl

theorem iSup_apply_eq_sSup_range {ι : Type*} (f : ι → D) :
    (⨆ i, f i) = sSup (Set.range f) :=
  sSup_range.symm

theorem finsetSup_wayBelow (M : Finset D) (x : D) (h : ∀ m ∈ M, m ≪ x) :
    M.sup id ≪ x := by
  classical
  induction M using Finset.induction_on with
  | empty =>
    simpa using bot_wayBelow x
  | insert a S ha ih =>
    rw [Finset.sup_insert]
    exact (h a (Finset.mem_insert_self a S)).sup
      (ih fun m hm => h m (Finset.mem_insert_of_mem hm))

/-- **Chen–Kou–Lyu Lemma 6.8.** A finitely separated Scott map satisfies `f x ≪ x`. -/
theorem finitelySeparated_wayBelow (hD : IsContinuousLattice D) {f : ScottMap D D}
    (hf : FinitelySeparated f) (x : D) : (f : D → D) x ≪ x := by
  classical
  obtain ⟨M, hM⟩ := hf
  have hx : x = sSup {y | y ≪ x} := (hD.sSup_wayBelow x).symm
  have hne : {y | y ≪ x}.Nonempty := ⟨⊥, bot_wayBelow x⟩
  have hfsup : (f : D → D) x = sSup ((f : D → D) '' {y | y ≪ x}) := by
    conv_lhs => rw [hx]
    exact f.preservesDirectedSup_coe _ hne (directedOn_wayBelow x)
  set N : Finset D := M.filter (fun m => m ≪ x)
  have hle : (f : D → D) x ≤ N.sup id := by
    rw [hfsup]
    refine sSup_le ?_
    rintro _ ⟨y, hyx, rfl⟩
    obtain ⟨m, hmM, hfym, hmy⟩ := hM y
    exact hfym.trans (Finset.le_sup (f := id)
      (Finset.mem_filter.mpr ⟨hmM, WayBelow.le_trans hmy hyx⟩))
  exact WayBelow.le_trans hle
    (finsetSup_wayBelow N x fun m hm => (Finset.mem_filter.mp hm).2)

/-- Jointly monotone hull of a double sequence. -/
noncomputable def monotoneHull (h : ℕ → ℕ → ScottMap D D) (i j : ℕ) : ScottMap D D :=
  ⨆ (i' : Fin (i + 1)), ⨆ (j' : Fin (j + 1)), h i'.val j'.val

theorem monotoneHull_ge (h : ℕ → ℕ → ScottMap D D) {i j i' j' : ℕ}
    (hi : i' ≤ i) (hj : j' ≤ j) : h i' j' ≤ monotoneHull h i j := by
  have hi' : i' < i + 1 := Nat.lt_succ_of_le hi
  have hj' : j' < j + 1 := Nat.lt_succ_of_le hj
  calc
    h i' j' ≤ ⨆ b : Fin (j + 1), h i' b.val :=
      le_iSup (fun b : Fin (j + 1) => h i' b.val) ⟨j', hj'⟩
    _ ≤ monotoneHull h i j :=
      le_iSup (fun a : Fin (i + 1) => ⨆ b : Fin (j + 1), h a.val b.val) ⟨i', hi'⟩

theorem monotoneHull_le_of_le (h : ℕ → ℕ → ScottMap D D) {i i' j j' : ℕ}
    (hi : i ≤ i') (hj : j ≤ j') : monotoneHull h i j ≤ monotoneHull h i' j' := by
  rw [ScottMap.le_def]
  intro x
  rw [monotoneHull, scottMap_iSup_apply]
  refine iSup_le fun a => ?_
  rw [scottMap_iSup_apply]
  refine iSup_le fun b => ?_
  exact monotoneHull_ge h
    ((Nat.lt_succ_iff.mp a.isLt).trans hi)
    ((Nat.lt_succ_iff.mp b.isLt).trans hj) x

theorem monotoneHull_le_id (h : ℕ → ℕ → ScottMap D D)
    (hh_sep : ∀ i j, FinitelySeparated (h i j)) (i j : ℕ) :
    monotoneHull h i j ≤ ScottMap.idMap := by
  rw [ScottMap.le_def]
  intro x
  rw [monotoneHull, scottMap_iSup_apply]
  refine iSup_le fun i' => ?_
  rw [scottMap_iSup_apply]
  refine iSup_le fun j' => ?_
  simpa [ScottMap.idMap_apply] using finitelySeparated_le_id (hh_sep i'.val j'.val) x

/-- **Chen–Kou–Lyu Lemma 6.9, diagonal form.**

Given `⊔ a_n = id` and inner approximate identities `⊔_j h i j = a i`
(increasing and finitely separated in `j`), the jointly monotone hull
produces `c n = (h̄ n n)²` with `⊔ c n = id`. -/
theorem saturation_flattening (hD : IsContinuousLattice D)
    (a : ℕ → ScottMap D D) (ha_mono : Monotone a)
    (ha_id : (⨆ n, a n) = ScottMap.idMap)
    (h : ℕ → ℕ → ScottMap D D)
    (hh_mono : ∀ i, Monotone (h i))
    (hh_sup : ∀ i, (⨆ j, h i j) = a i)
    (hh_sep : ∀ i j, FinitelySeparated (h i j)) :
    ∃ idx : ℕ → ℕ,
      let c := fun n =>
        (monotoneHull h (idx n) (idx n)).comp (monotoneHull h (idx n) (idx n))
      Monotone c ∧ (⨆ n, c n) = ScottMap.idMap := by
  refine ⟨id, ?_⟩
  set H : ℕ → ScottMap D D := fun n => monotoneHull h n n
  set c : ℕ → ScottMap D D := fun n => (H n).comp (H n)
  have hH_mono : Monotone H := fun _ _ hnm => monotoneHull_le_of_le h hnm hnm
  have hc_mono : Monotone c := by
    intro n m hnm
    rw [ScottMap.le_def]
    intro x
    exact (hH_mono hnm ((H n : D → D) x)).trans
      ((H m).monotone (hH_mono hnm x))
  refine ⟨hc_mono, ?_⟩
  apply ScottMap.ext
  intro x
  rw [scottMap_iSup_apply, ScottMap.idMap_apply]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun n =>
      (monotoneHull_le_id h hh_sep n n ((H n : D → D) x)).trans
        (by simpa [ScottMap.idMap_apply] using monotoneHull_le_id h hh_sep n n x)
  · have hgoal : sSup {y | y ≪ x} ≤ ⨆ n, (c n : D → D) x := by
      refine sSup_le fun y hyx => ?_
      obtain ⟨r, hyr, hrx⟩ := wayBelow_interpolate hD hyx
      obtain ⟨s, hrs, hsx⟩ := wayBelow_interpolate hD hrx
      obtain ⟨t, hst, htx⟩ := wayBelow_interpolate hD hsx
      have hxA : x = ⨆ n, (a n : D → D) x := by
        simpa [scottMap_iSup_apply, ScottMap.idMap_apply] using
          (congrArg (fun f : ScottMap D D => (f : D → D) x) ha_id).symm
      have hsA : s = ⨆ n, (a n : D → D) s := by
        simpa [scottMap_iSup_apply, ScottMap.idMap_apply] using
          (congrArg (fun f : ScottMap D D => (f : D → D) s) ha_id).symm
      have hdirx : DirectedOn (· ≤ ·) (Set.range fun n => (a n : D → D) x) :=
        directedOn_range.2 fun p q =>
          ⟨max p q, ha_mono (le_max_left p q) x, ha_mono (le_max_right p q) x⟩
      have hdirs : DirectedOn (· ≤ ·) (Set.range fun n => (a n : D → D) s) :=
        directedOn_range.2 fun p q =>
          ⟨max p q, ha_mono (le_max_left p q) s, ha_mono (le_max_right p q) s⟩
      obtain ⟨i, hi⟩ : ∃ i, t ≤ (a i : D → D) x := by
        have hsup : sSup (Set.range fun n => (a n : D → D) x) = x := by
          rw [sSup_range, ← hxA]
        obtain ⟨_, ⟨i, rfl⟩, hit⟩ :=
          (wayBelow_sSup_iff (Set.range_nonempty _) hdirx).1 (by rwa [hsup])
        exact ⟨i, hit.le⟩
      obtain ⟨i', hi'⟩ : ∃ i', r ≤ (a i' : D → D) s := by
        have hsup : sSup (Set.range fun n => (a n : D → D) s) = s := by
          rw [sSup_range, ← hsA]
        obtain ⟨_, ⟨i', rfl⟩, hir⟩ :=
          (wayBelow_sSup_iff (Set.range_nonempty _) hdirs).1 (by rwa [hsup])
        exact ⟨i', hir.le⟩
      let k := max i i'
      have hk₁ : t ≤ (a k : D → D) x := hi.trans (ha_mono (le_max_left i i') x)
      have hk₂ : r ≤ (a k : D → D) s := hi'.trans (ha_mono (le_max_right i i') s)
      have hakx : (a k : D → D) x = ⨆ j, (h k j : D → D) x := by
        simpa [scottMap_iSup_apply] using
          (congrArg (fun f : ScottMap D D => (f : D → D) x) (hh_sup k)).symm
      have haks : (a k : D → D) s = ⨆ j, (h k j : D → D) s := by
        simpa [scottMap_iSup_apply] using
          (congrArg (fun f : ScottMap D D => (f : D → D) s) (hh_sup k)).symm
      have hdirh : ∀ z, DirectedOn (· ≤ ·) (Set.range fun j => (h k j : D → D) z) :=
        fun z => directedOn_range.2 fun p q =>
          ⟨max p q, hh_mono k (le_max_left p q) z, hh_mono k (le_max_right p q) z⟩
      obtain ⟨j, hj⟩ : ∃ j, s ≤ (h k j : D → D) x := by
        have hsup : sSup (Set.range fun j => (h k j : D → D) x) = (a k : D → D) x := by
          rw [sSup_range, ← hakx]
        have hs : s ≪ (a k : D → D) x := hst.trans_le hk₁
        obtain ⟨_, ⟨j, rfl⟩, hsj⟩ :=
          (wayBelow_sSup_iff (Set.range_nonempty _) (hdirh x)).1 (by rwa [hsup])
        exact ⟨j, hsj.le⟩
      obtain ⟨j', hj'⟩ : ∃ j', y ≤ (h k j' : D → D) s := by
        have hsup : sSup (Set.range fun j => (h k j : D → D) s) = (a k : D → D) s := by
          rw [sSup_range, ← haks]
        have hy : y ≪ (a k : D → D) s := hyr.trans_le hk₂
        obtain ⟨_, ⟨j', rfl⟩, hyj⟩ :=
          (wayBelow_sSup_iff (Set.range_nonempty _) (hdirh s)).1 (by rwa [hsup])
        exact ⟨j', hyj.le⟩
      let K := max k (max j j')
      have hkj : k ≤ K := le_max_left _ _
      have hjK : j ≤ K := (le_max_left j j').trans (le_max_right _ _)
      have hj'K : j' ≤ K := (le_max_right j j').trans (le_max_right _ _)
      have hsH : s ≤ (H K : D → D) x :=
        hj.trans (monotoneHull_ge h hkj hjK x)
      have hyH : y ≤ (H K : D → D) s :=
        hj'.trans (monotoneHull_ge h hkj hj'K s)
      have hyc : y ≤ (c K : D → D) x :=
        hyH.trans ((H K).monotone hsH)
      exact hyc.trans (le_iSup (fun n => (c n : D → D) x) K)
    rwa [hD.sSup_wayBelow] at hgoal

end Scott1972.ContinuousLattice
