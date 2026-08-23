/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Monad
import QLambda.TTRoundedTheory

open Set

namespace QLambda

open Scott1972.ContinuousLattice

universe u v

namespace TTContinuation

def resultCode : OutputCode ℕ PUnit.{1} :=
  ⟨fun _ => ⟨Set.univ, scottOpen_univ⟩⟩

abbrev TTResult (n : ℕ) : Type :=
  @TTTokenTheory n PUnit.{1} inferInstance resultCode

abbrev TTContinuationPower (n : ℕ) (D : Type u) [CompleteLattice D] :=
  ScottMap (ScottMap D (TTResult n)) (TTResult n)

variable {n : ℕ}
variable {D E F : Type u}
variable [CompleteLattice D] [CompleteLattice E] [CompleteLattice F]

theorem iSup_apply {X : Type u} {Y : Type v}
    [CompleteLattice X] [CompleteLattice Y]
    (H : ℕ → ScottMap X Y) (x : X) :
    ((⨆ i, H i : ScottMap X Y) : X → Y) x = ⨆ i, H i x := by
  rw [show (⨆ i, H i : ScottMap X Y) = sSup (Set.range H) from sSup_range.symm,
    ScottMap.sSup_apply, ← Set.range_comp, sSup_range]
  rfl

noncomputable def evaluationAt (d : D) :
    ScottMap (ScottMap D (TTResult n)) (TTResult n) :=
  ⟨fun k => k d, continuous_of_preservesDirectedSup fun S _ _ => by
    rw [ScottMap.sSup_apply]⟩

@[simp]
theorem evaluationAt_apply (d : D) (k : ScottMap D (TTResult n)) :
    evaluationAt (n := n) d k = k d :=
  rfl

noncomputable def precompose (f : ScottMap D E) :
    ScottMap (ScottMap E (TTResult n)) (ScottMap D (TTResult n)) :=
  ⟨fun k => k.comp f, continuous_of_preservesDirectedSup fun S _ _ => by
    apply ScottMap.ext
    intro d
    rw [ScottMap.comp_apply, ScottMap.sSup_apply, ScottMap.sSup_apply,
      Set.image_image]
    congr 1⟩

@[simp]
theorem precompose_apply (f : ScottMap D E) (k : ScottMap E (TTResult n))
    (d : D) :
    precompose (n := n) f k d = k (f d) :=
  rfl

noncomputable def continuation (h : ScottMap D (TTContinuationPower n E)) :
    ScottMap (ScottMap E (TTResult n)) (ScottMap D (TTResult n)) :=
  ⟨fun k => (evaluationAt (n := n) k).comp h,
    continuous_of_preservesDirectedSup fun S hS hdir => by
      apply ScottMap.ext
      intro d
      change h d (sSup S) =
        ((sSup ((fun k : ScottMap E (TTResult n) =>
          (evaluationAt (n := n) k).comp h) '' S) :
            ScottMap D (TTResult n)) : D → TTResult n) d
      rw [ScottMap.sSup_apply, Set.image_image]
      exact (h d).preservesDirectedSup_coe S hS hdir⟩

@[simp]
theorem continuation_apply (h : ScottMap D (TTContinuationPower n E))
    (k : ScottMap E (TTResult n)) (d : D) :
    continuation h k d = h d k :=
  rfl

noncomputable def unit : ScottMap D (TTContinuationPower n D) :=
  ⟨fun d => evaluationAt (n := n) d,
    continuous_of_preservesDirectedSup fun S hS hdir => by
      apply ScottMap.ext
      intro k
      change k (sSup S) =
        ((sSup (evaluationAt (n := n) '' S) :
          TTContinuationPower n D) : ScottMap D (TTResult n) → TTResult n) k
      rw [ScottMap.sSup_apply, Set.image_image]
      exact k.preservesDirectedSup_coe S hS hdir⟩

@[simp]
theorem unit_apply (d : D) (k : ScottMap D (TTResult n)) :
    unit (n := n) d k = k d :=
  rfl

noncomputable def map (f : ScottMap D E) :
    ScottMap (TTContinuationPower n D) (TTContinuationPower n E) :=
  precompose (n := n) (precompose (n := n) f)

@[simp]
theorem map_apply (f : ScottMap D E) (q : TTContinuationPower n D)
    (k : ScottMap E (TTResult n)) :
    map f q k = q (k.comp f) :=
  rfl

noncomputable def transpose (h : ScottMap D (TTContinuationPower n E)) :
    ScottMap (TTContinuationPower n D) (TTContinuationPower n E) :=
  precompose (n := n) (continuation h)

@[simp]
theorem transpose_apply (h : ScottMap D (TTContinuationPower n E))
    (q : TTContinuationPower n D) (k : ScottMap E (TTResult n)) :
    transpose h q k = q (continuation h k) :=
  rfl

noncomputable def bind (h : ScottMap D (TTContinuationPower n E)) :
    ScottMap (TTContinuationPower n D) (TTContinuationPower n E) :=
  transpose h

@[simp]
theorem bind_apply (h : ScottMap D (TTContinuationPower n E))
    (q : TTContinuationPower n D) (k : ScottMap E (TTResult n)) :
    bind h q k = q (continuation h k) :=
  rfl

theorem map_id :
    map (n := n) (ScottMap.idMap : ScottMap D D) = ScottMap.idMap := by
  apply ScottMap.ext
  intro q
  apply ScottMap.ext
  intro k
  rfl

theorem map_comp (f : ScottMap E F) (g : ScottMap D E) :
    map (n := n) (f.comp g) = (map f).comp (map g) := by
  apply ScottMap.ext
  intro q
  apply ScottMap.ext
  intro k
  rfl

theorem map_mono {f g : ScottMap D E} (hfg : f ≤ g) :
    map (n := n) f ≤ map g := by
  intro q k
  exact q.monotone (fun d => k.monotone (hfg d))

theorem map_iSup (G : ℕ → ScottMap D E) (hG : Monotone G) :
    map (n := n) (⨆ i, G i) = ⨆ i, map (G i) := by
  have hinner (k : ScottMap E (TTResult n)) :
      k.comp (⨆ i, G i) = ⨆ i, k.comp (G i) := by
    apply ScottMap.ext
    intro d
    rw [ScottMap.comp_apply, iSup_apply G d,
      iSup_apply (X := D) (Y := TTResult n) (fun i => k.comp (G i)) d]
    have hdir : DirectedOn (· ≤ ·) (Set.range fun i => G i d) :=
      directedOn_range.2 fun i j =>
        ⟨max i j, hG (le_max_left i j) d, hG (le_max_right i j) d⟩
    have hpres := k.preservesDirectedSup_coe
      (Set.range fun i => G i d) (Set.range_nonempty _) hdir
    rw [sSup_range, ← Set.range_comp, sSup_range] at hpres
    simpa [Function.comp_def, ScottMap.comp_apply] using hpres
  apply ScottMap.ext
  intro q
  apply ScottMap.ext
  intro k
  rw [map_apply, hinner]
  have hdir : DirectedOn (· ≤ ·)
      (Set.range fun i => k.comp (G i)) :=
    directedOn_range.2 fun i j =>
      ⟨max i j,
        fun d => k.monotone (hG (le_max_left i j) d),
        fun d => k.monotone (hG (le_max_right i j) d)⟩
  have hpres := q.preservesDirectedSup_coe
    (Set.range fun i => k.comp (G i))
    (Set.range_nonempty _) hdir
  rw [sSup_range, ← Set.range_comp, sSup_range] at hpres
  rw [hpres,
    iSup_apply (X := TTContinuationPower n D) (Y := TTContinuationPower n E)
      (fun i => map (n := n) (G i)) q,
    iSup_apply (X := ScottMap E (TTResult n)) (Y := TTResult n)
      (fun i => map (n := n) (G i) q) k]
  rfl

theorem bind_unit :
    bind (n := n) (unit (n := n) : ScottMap D (TTContinuationPower n D)) =
      ScottMap.idMap := by
  apply ScottMap.ext
  intro q
  apply ScottMap.ext
  intro k
  rfl

theorem unit_bind (h : ScottMap D (TTContinuationPower n E)) :
    (bind h).comp (unit (n := n)) = h := by
  apply ScottMap.ext
  intro d
  apply ScottMap.ext
  intro k
  rfl

theorem bind_assoc (h : ScottMap D (TTContinuationPower n E))
    (g : ScottMap E (TTContinuationPower n F)) :
    (bind g).comp (bind h) = bind ((bind g).comp h) := by
  apply ScottMap.ext
  intro q
  apply ScottMap.ext
  intro k
  rfl

theorem map_eq_bind_unit (f : ScottMap D E) :
    map (n := n) f = bind ((unit (n := n)).comp f) := by
  apply ScottMap.ext
  intro q
  apply ScottMap.ext
  intro k
  rfl

noncomputable instance instIsQuantumPowerModel :
    IsQuantumPowerModel (TTContinuationPower n) where
  str := fun _ _ => inferInstance
  map := fun f => map (n := n) f
  map_id := map_id (n := n)
  map_comp := map_comp (n := n)
  map_mono := map_mono (n := n)
  map_iSup := map_iSup (n := n)
  closed := by
    intro D _ hD
    exact omegaQVA_closed_under_functionSpace
      (omegaQVA_closed_under_functionSpace hD (inferInstance : IsOmegaQVA (TTResult n)))
      (inferInstance : IsOmegaQVA (TTResult n))

noncomputable instance instIsQuantumMonad :
    IsQuantumMonad (TTContinuationPower n) where
  unit := unit (n := n)
  bind := bind (n := n)
  bind_unit := bind_unit (n := n)
  unit_bind := unit_bind (n := n)
  bind_assoc := bind_assoc (n := n)
  map_eq_bind_unit := map_eq_bind_unit (n := n)

/-- The concrete fixed-register Scott-continuation quantum power model. -/
noncomputable def model (n : ℕ) : QuantumPowerModel where
  Power := TTContinuationPower n

end TTContinuation

end QLambda
