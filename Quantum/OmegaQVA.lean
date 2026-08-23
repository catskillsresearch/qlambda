/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Data.Fintype.Pi
import Quantum.Saturation
import QuantumStateSpace
import Scott1972.ContinuousLattice.Constructions
import Scott1972.ContinuousLattice.FunctionSpaces

/-!
# Quantum-valuation approximable domains (`ωQVA`)

A continuous lattice is in `ωQVA` when `id` is the directed supremum of
an increasing sequence of maps that factor through a finite direct sum
of spectrahedra `S_≤1(M_{d_k})` (the state space of `⊕_k M_{d_k}(ℂ)`
with per-block trace bound; a single `SubNormalizedDensity dim` when
`dims = [dim]`).
-/

namespace Scott1972.ContinuousLattice

open SubNormalizedDensity

variable {D E : Type*} [CompleteLattice D] [CompleteLattice E]

/-- Finite product of Loewner spectrahedra, one block per matrix size. -/
def DensityVec : List ℕ → Type
  | [] => PUnit
  | n :: ns => SubNormalizedDensity n × DensityVec ns

namespace DensityVec

instance instPartialOrder : (ns : List ℕ) → PartialOrder (DensityVec ns)
  | [] => inferInstanceAs (PartialOrder PUnit)
  | _ :: ns =>
    haveI := instPartialOrder ns
    inferInstanceAs (PartialOrder (_ × _))

instance instOrderBot : (ns : List ℕ) → OrderBot (DensityVec ns)
  | [] => { bot := ⟨⟩, bot_le := fun _ => trivial }
  | _ :: ns =>
    haveI := instOrderBot ns
    inferInstanceAs (OrderBot (_ × _))

end DensityVec

/-- `a` factors through `DensityVec dims` via monotone encoding and
reconstruction. For `dims = [dim]` this is factorization through
`SubNormalizedDensity dim`. -/
structure QFactorable (a : ScottMap D E) where
  dims : List ℕ
  enc : D → DensityVec dims
  recon : DensityVec dims → E
  enc_mono : Monotone enc
  recon_mono : Monotone recon
  factor : ∀ x, (a : D → E) x = recon (enc x)

theorem directedOn_image_monotone {α β : Type*} [Preorder α] [Preorder β]
    {S : Set α} {f : α → β} (hdir : DirectedOn (· ≤ ·) S) (hf : Monotone f) :
    DirectedOn (· ≤ ·) (f '' S) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
  exact ⟨f c, ⟨c, hc, rfl⟩, hf hac, hf hbc⟩

/-- Product of Scott self-maps, acting coordinatewise. -/
def prodMap (f : ScottMap D D) (g : ScottMap E E) : ScottMap (D × E) (D × E) :=
  ⟨fun p => (f p.1, g p.2), continuous_of_preservesDirectedSup <| by
    intro S hS hSdir
    refine Prod.ext ?_ ?_
    · have hf := f.preservesDirectedSup_coe (Prod.fst '' S) (hS.image Prod.fst)
        (directedOn_image_monotone hSdir fun _ _ h => h.1)
      change f (sSup S).1 = sSup (Prod.fst '' ((fun p => (f p.1, g p.2)) '' S))
      rw [Prod.fst_sSup, hf]
      congr 1
      ext y
      constructor
      · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨(f p.1, g p.2), ⟨p, hp, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨p.1, ⟨p, hp, rfl⟩, rfl⟩
    · have hg := g.preservesDirectedSup_coe (Prod.snd '' S) (hS.image Prod.snd)
        (directedOn_image_monotone hSdir fun _ _ h => h.2)
      change g (sSup S).2 = sSup (Prod.snd '' ((fun p => (f p.1, g p.2)) '' S))
      rw [Prod.snd_sSup, hg]
      congr 1
      ext y
      constructor
      · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨(f p.1, g p.2), ⟨p, hp, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨p.2, ⟨p, hp, rfl⟩, rfl⟩⟩

@[simp] theorem prodMap_apply (f : ScottMap D D) (g : ScottMap E E) (p : D × E) :
    (prodMap f g : (D × E) → D × E) p = (f p.1, g p.2) :=
  rfl

namespace QFactorable

def square {a : ScottMap D D} (h : QFactorable a) : QFactorable (a.comp a) where
  dims := h.dims
  enc := h.enc
  recon := (a : D → D) ∘ h.recon
  enc_mono := h.enc_mono
  recon_mono := (ScottMap.monotone a).comp h.recon_mono
  factor := fun x => by simp [ScottMap.comp_apply, h.factor]

def conjRetr (R : IsContinuousLatticeRetraction E D) {a : ScottMap D D}
    (h : QFactorable a) : QFactorable (R.retr.comp (a.comp R.incl)) where
  dims := h.dims
  enc := h.enc ∘ (R.incl : E → D)
  recon := (R.retr : D → E) ∘ h.recon
  enc_mono := h.enc_mono.comp R.incl.monotone
  recon_mono := R.retr.monotone.comp h.recon_mono
  factor := fun x => by simp [ScottMap.comp_apply, h.factor]

/-- Pair of density vectors. -/
def pairEnc {ns ms : List ℕ} (p : DensityVec ns) (q : DensityVec ms) :
    DensityVec (ns ++ ms) :=
  match ns, p with
  | [], _ => q
  | _ :: _, (ρ, p') => (ρ, pairEnc p' q)

def pairUnenc {ns ms : List ℕ} (v : DensityVec (ns ++ ms)) :
    DensityVec ns × DensityVec ms :=
  match ns, v with
  | [], v => (⟨⟩, v)
  | _ :: ns', (ρ, v') =>
    let iq := pairUnenc (ns := ns') v'
    ((ρ, iq.1), iq.2)

theorem pairEnc_unenc {ns ms : List ℕ} (p : DensityVec ns) (q : DensityVec ms) :
    pairUnenc (pairEnc p q) = (p, q) :=
  match ns, p with
  | [], ⟨⟩ => rfl
  | _ :: _, (ρ, p') => by
    simp [pairEnc, pairUnenc, pairEnc_unenc p' q]

theorem pairEnc_mono_aux {ns ms : List ℕ}
    (p p' : DensityVec ns) (q q' : DensityVec ms) (hp : p ≤ p') (hq : q ≤ q') :
    pairEnc p q ≤ pairEnc p' q' :=
  match ns, p, p' with
  | [], ⟨⟩, ⟨⟩ => hq
  | _ :: _, (_, t), (_, t') =>
    ⟨hp.1, pairEnc_mono_aux t t' q q' hp.2 hq⟩

theorem pairEnc_mono {ns ms : List ℕ} :
    Monotone (fun pq : DensityVec ns × DensityVec ms => pairEnc pq.1 pq.2) :=
  fun pq pq' hpq => pairEnc_mono_aux pq.1 pq'.1 pq.2 pq'.2 hpq.1 hpq.2

theorem pairUnenc_mono_aux {ns ms : List ℕ} (v v' : DensityVec (ns ++ ms))
    (hv : v ≤ v') : pairUnenc (ns := ns) (ms := ms) v ≤ pairUnenc (ns := ns) v' :=
  match ns, v, v' with
  | [], _, _ => ⟨le_rfl, hv⟩
  | _ :: _, (_, w), (_, w') =>
    have ih := pairUnenc_mono_aux (ns := _) w w' hv.2
    ⟨⟨hv.1, ih.1⟩, ih.2⟩

theorem pairUnenc_mono {ns ms : List ℕ} :
    Monotone (pairUnenc (ns := ns) (ms := ms)) :=
  fun v v' hv => pairUnenc_mono_aux v v' hv

def prod {f : ScottMap D D} {g : ScottMap E E}
    (hf : QFactorable f) (hg : QFactorable g) :
    QFactorable (prodMap f g) where
  dims := hf.dims ++ hg.dims
  enc := fun p => pairEnc (hf.enc p.1) (hg.enc p.2)
  recon := fun v =>
    let iq := pairUnenc (ns := hf.dims) v
    (hf.recon iq.1, hg.recon iq.2)
  enc_mono := by
    intro p p' hp
    exact pairEnc_mono
      (show (hf.enc p.1, hg.enc p.2) ≤ (hf.enc p'.1, hg.enc p'.2) from
        ⟨hf.enc_mono hp.1, hg.enc_mono hp.2⟩)
  recon_mono := by
    intro v v' hv
    have h := pairUnenc_mono (ns := hf.dims) (ms := hg.dims) hv
    exact ⟨hf.recon_mono h.1, hg.recon_mono h.2⟩
  factor := fun p => by
    simp [prodMap, pairEnc_unenc, hf.factor, hg.factor]

end QFactorable

/-- A continuous lattice whose identity is a directed supremum of
Q-factorable, finitely separated approximants. -/
class IsOmegaQVA (D : Type*) [CompleteLattice D] where
  isContinuousLattice : IsContinuousLattice D
  approx : ℕ → ScottMap D D
  qfactorable : ∀ n, QFactorable (approx n)
  separated : ∀ n, FinitelySeparated (approx n)
  monotone_approx : Monotone approx
  iSup_approx : (⨆ n, approx n) = ScottMap.idMap

/-- Binary products of continuous lattices are continuous (Prop. 2.9, two factors). -/
theorem continuousLattice_prod (hD : IsContinuousLattice D) (hE : IsContinuousLattice E) :
    IsContinuousLattice (D × E) := by
  intro y
  refine ⟨fun x hx => hx.le, fun b hb => ?_⟩
  constructor
  · rw [← hD.sSup_wayBelow y.1]
    apply sSup_le
    intro a ha
    set e : D × E := (a, ⊥)
    have he : e ≪ y := by
      obtain ⟨U, hU, hyU, hsub⟩ := ha
      refine ⟨{p : D × E | p.1 ∈ U}, ⟨?_, ?_⟩, hyU, ?_⟩
      · intro p q hpq hp
        exact hU.1 hpq.1 hp
      · intro S hS hSdir hmem
        have hmem' : sSup (Prod.fst '' S) ∈ U := by
          rwa [← Prod.fst_sSup]
        have hdir' : DirectedOn (· ≤ ·) (Prod.fst '' S) :=
          directedOn_image_monotone hSdir fun _ _ h => h.1
        obtain ⟨t, htimg, htU⟩ := hU.2 (hS.image Prod.fst) hdir' hmem'
        obtain ⟨p, hpS, rfl⟩ := htimg
        exact ⟨p, hpS, htU⟩
      · intro p hp
        exact ⟨Set.mem_Ici.1 (hsub hp), bot_le⟩
    exact (hb he).1
  · rw [← hE.sSup_wayBelow y.2]
    apply sSup_le
    intro a ha
    set e : D × E := (⊥, a)
    have he : e ≪ y := by
      obtain ⟨U, hU, hyU, hsub⟩ := ha
      refine ⟨{p : D × E | p.2 ∈ U}, ⟨?_, ?_⟩, hyU, ?_⟩
      · intro p q hpq hp
        exact hU.1 hpq.2 hp
      · intro S hS hSdir hmem
        have hmem' : sSup (Prod.snd '' S) ∈ U := by
          rwa [← Prod.snd_sSup]
        have hdir' : DirectedOn (· ≤ ·) (Prod.snd '' S) :=
          directedOn_image_monotone hSdir fun _ _ h => h.2
        obtain ⟨t, htimg, htU⟩ := hU.2 (hS.image Prod.snd) hdir' hmem'
        obtain ⟨p, hpS, rfl⟩ := htimg
        exact ⟨p, hpS, htU⟩
      · intro p hp
        exact ⟨bot_le, Set.mem_Ici.1 (hsub hp)⟩
    exact (hb he).2

/-- `ωQVA` is closed under Scott-continuous retracts. -/
@[reducible] def omegaQVA_of_retract [IsOmegaQVA D]
    (R : IsContinuousLatticeRetraction E D) : IsOmegaQVA E where
  isContinuousLattice := proposition_2_10_a R IsOmegaQVA.isContinuousLattice
  approx := fun n => R.retr.comp ((IsOmegaQVA.approx n).comp R.incl)
  qfactorable := fun n => QFactorable.conjRetr R (IsOmegaQVA.qfactorable n)
  separated := fun n => by
    classical
    obtain ⟨M, hM⟩ := IsOmegaQVA.separated (D := D) n
    refine ⟨M.image (R.retr : D → E), fun x => ?_⟩
    obtain ⟨m, hmM, hax, hmx⟩ := hM (R.incl x)
    refine ⟨R.retr m, Finset.mem_image.mpr ⟨m, hmM, rfl⟩, R.retr.monotone hax, ?_⟩
    have := R.retr.monotone hmx
    rwa [R.retr_incl] at this
  monotone_approx := fun i j hij => by
    rw [ScottMap.le_def]
    intro x
    exact R.retr.monotone (IsOmegaQVA.monotone_approx hij (R.incl x))
  iSup_approx := by
    apply ScottMap.ext
    intro x
    have hsup : R.incl x =
        ⨆ n, (IsOmegaQVA.approx (D := D) n : D → D) (R.incl x) := by
      simpa [scottMap_iSup_apply, ScottMap.idMap_apply] using
        (congrArg (fun f : ScottMap D D => (f : D → D) (R.incl x))
          IsOmegaQVA.iSup_approx).symm
    have hdir : DirectedOn (· ≤ ·)
        (Set.range fun n => (IsOmegaQVA.approx (D := D) n : D → D) (R.incl x)) :=
      directedOn_range.2 fun p q =>
        ⟨max p q,
          IsOmegaQVA.monotone_approx (le_max_left p q) (R.incl x),
          IsOmegaQVA.monotone_approx (le_max_right p q) (R.incl x)⟩
    have hne : (Set.range fun n =>
        (IsOmegaQVA.approx (D := D) n : D → D) (R.incl x)).Nonempty :=
      Set.range_nonempty _
    rw [scottMap_iSup_apply, ScottMap.idMap_apply]
    have hswap :
        (⨆ n, R.retr ((IsOmegaQVA.approx (D := D) n : D → D) (R.incl x))) =
          R.retr (⨆ n, (IsOmegaQVA.approx (D := D) n : D → D) (R.incl x)) := by
      have hr : (⨆ n, (IsOmegaQVA.approx (D := D) n : D → D) (R.incl x)) =
          sSup (Set.range fun n => (IsOmegaQVA.approx (D := D) n : D → D) (R.incl x)) :=
        sSup_range.symm
      rw [hr, R.retr.preservesDirectedSup_coe _ hne hdir, ← Set.range_comp, sSup_range]
      rfl
    change ⨆ n, R.retr ((IsOmegaQVA.approx (D := D) n : D → D) (R.incl x)) = x
    rw [hswap, ← hsup, R.retr_incl]

/-- `ωQVA` is closed under binary products. -/
@[reducible] def omegaQVA_prod [IsOmegaQVA D] [IsOmegaQVA E] : IsOmegaQVA (D × E) where
  isContinuousLattice :=
    continuousLattice_prod IsOmegaQVA.isContinuousLattice
      IsOmegaQVA.isContinuousLattice
  approx := fun n =>
    prodMap (IsOmegaQVA.approx (D := D) n) (IsOmegaQVA.approx (D := E) n)
  qfactorable := fun n =>
    QFactorable.prod (IsOmegaQVA.qfactorable n) (IsOmegaQVA.qfactorable n)
  separated := fun n => by
    obtain ⟨M, hM⟩ := IsOmegaQVA.separated (D := D) n
    obtain ⟨N, hN⟩ := IsOmegaQVA.separated (D := E) n
    refine ⟨M.product N, fun p => ?_⟩
    obtain ⟨m, hmM, hfx, hmx⟩ := hM p.1
    obtain ⟨n, hnN, hgy, hny⟩ := hN p.2
    exact ⟨(m, n), Finset.mem_product.mpr ⟨hmM, hnN⟩, ⟨hfx, hgy⟩, ⟨hmx, hny⟩⟩
  monotone_approx := fun i j hij => by
    rw [ScottMap.le_def]
    intro p
    exact ⟨IsOmegaQVA.monotone_approx hij p.1, IsOmegaQVA.monotone_approx hij p.2⟩
  iSup_approx := by
    apply ScottMap.ext
    intro p
    rw [scottMap_iSup_apply, ScottMap.idMap_apply]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_iSup]
      have h := congrArg (fun f : ScottMap D D => (f : D → D) p.1)
        (IsOmegaQVA.iSup_approx (D := D))
      simpa [scottMap_iSup_apply, ScottMap.idMap_apply, prodMap_apply] using h
    · rw [Prod.snd_iSup]
      have h := congrArg (fun f : ScottMap E E => (f : E → E) p.2)
        (IsOmegaQVA.iSup_approx (D := E))
      simpa [scottMap_iSup_apply, ScottMap.idMap_apply, prodMap_apply] using h

/-! ### Countable products

Finite-support stagewise approximants put `Πₙ Eₙ` in `ωQVA` when each factor is.
The inverse limit is then a retract, hence also in `ωQVA`. -/

section PiOmega

variable {E : ℕ → Type*} [∀ n, CompleteLattice (E n)] [∀ n, IsOmegaQVA (E n)]

/-- Prefix approximant: apply the `N`-th factor approximant on coordinates `≤ N`,
and send the tail to `⊥`. -/
def prefixFun (N : ℕ) (x : ∀ n, E n) : ∀ n, E n :=
  fun n => if n ≤ N then (IsOmegaQVA.approx (D := E n) N : E n → E n) (x n) else ⊥

theorem prefixFun_mono (N : ℕ) : Monotone (prefixFun (E := E) N) := by
  intro x y hxy n
  by_cases hn : n ≤ N
  · simpa [prefixFun, hn] using
      (IsOmegaQVA.approx (D := E n) N).monotone (hxy n)
  · simp [prefixFun, hn]

def prefixMap (N : ℕ) : ScottMap (∀ n, E n) (∀ n, E n) :=
  ⟨prefixFun N, continuous_of_preservesDirectedSup <| by
    intro S hS hSdir
    funext n
    rw [sSup_apply_eq_sSup_image]
    by_cases hn : n ≤ N
    · have hdir' : DirectedOn (· ≤ ·) (Function.eval n '' S) :=
        directedOn_image_monotone hSdir fun _ _ h => h n
      have hsup :=
        (IsOmegaQVA.approx (D := E n) N).preservesDirectedSup_coe
          (Function.eval n '' S) (hS.image _) hdir'
      change prefixFun (E := E) N (sSup S) n =
        sSup (Function.eval n '' (prefixFun (E := E) N '' S))
      simp only [prefixFun, hn, ↓reduceIte]
      rw [sSup_apply_eq_sSup_image, hsup]
      congr 1
      ext y
      constructor
      · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
        refine ⟨prefixFun (E := E) N x, ⟨x, hx, rfl⟩, ?_⟩
        simp [prefixFun, hn]
      · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
        refine ⟨x n, ⟨x, hx, rfl⟩, ?_⟩
        simp [prefixFun, hn]
    · change prefixFun (E := E) N (sSup S) n =
        sSup (Function.eval n '' (prefixFun (E := E) N '' S))
      simp only [prefixFun, hn, ↓reduceIte]
      apply le_antisymm
      · exact bot_le
      · refine sSup_le ?_
        rintro _ ⟨w, ⟨x, hx, rfl⟩, rfl⟩
        simp [prefixFun, hn]⟩

@[simp] theorem prefixMap_apply (N : ℕ) (x : ∀ n, E n) (n : ℕ) :
    (prefixMap (E := E) N : _ → _) x n = prefixFun (E := E) N x n :=
  rfl

def prefixDims (j : ℕ) : ℕ → List ℕ
  | 0 => (IsOmegaQVA.qfactorable (D := E 0) j).dims
  | k + 1 => prefixDims j k ++ (IsOmegaQVA.qfactorable (D := E (k + 1)) j).dims

def encPrefix (j : ℕ) : (k : ℕ) → (∀ n, E n) → DensityVec (prefixDims (E := E) j k)
  | 0, x => (IsOmegaQVA.qfactorable (D := E 0) j).enc (x 0)
  | k + 1, x =>
      QFactorable.pairEnc (encPrefix j k x)
        ((IsOmegaQVA.qfactorable (D := E (k + 1)) j).enc (x (k + 1)))

def recPrefix (j : ℕ) : (k : ℕ) → DensityVec (prefixDims (E := E) j k) → (∀ n, E n)
  | 0, v => fun n =>
      if h : n = 0 then
        h ▸ (IsOmegaQVA.qfactorable (D := E 0) j).recon v
      else ⊥
  | k + 1, v => fun n =>
      if h : n = k + 1 then
        h ▸ (IsOmegaQVA.qfactorable (D := E (k + 1)) j).recon
          (QFactorable.pairUnenc (ns := prefixDims (E := E) j k) v).2
      else
        recPrefix j k (QFactorable.pairUnenc (ns := prefixDims (E := E) j k) v).1 n

theorem encPrefix_mono (j k : ℕ) : Monotone (encPrefix (E := E) j k) := by
  induction k with
  | zero =>
    intro x y hxy
    exact (IsOmegaQVA.qfactorable (D := E 0) j).enc_mono (hxy 0)
  | succ k ih =>
    intro x y hxy
    exact QFactorable.pairEnc_mono
      (show
          (encPrefix (E := E) j k x,
              (IsOmegaQVA.qfactorable (D := E (k + 1)) j).enc (x (k + 1))) ≤
            (encPrefix (E := E) j k y,
              (IsOmegaQVA.qfactorable (D := E (k + 1)) j).enc (y (k + 1))) from
        ⟨ih hxy, (IsOmegaQVA.qfactorable (D := E (k + 1)) j).enc_mono (hxy (k + 1))⟩)

theorem recPrefix_mono (j k : ℕ) : Monotone (recPrefix (E := E) j k) := by
  induction k with
  | zero =>
    intro v w hvw n
    by_cases hn : n = 0
    · subst hn
      simpa [recPrefix] using (IsOmegaQVA.qfactorable (D := E 0) j).recon_mono hvw
    · simp [recPrefix, hn]
  | succ k ih =>
    intro v w hvw n
    have h := QFactorable.pairUnenc_mono (ns := prefixDims (E := E) j k) hvw
    by_cases hn : n = k + 1
    · subst hn
      simpa [recPrefix] using
        (IsOmegaQVA.qfactorable (D := E (k + 1)) j).recon_mono h.2
    · simp [recPrefix, hn]
      exact ih h.1 n

theorem recPrefix_encPrefix (j k : ℕ) (x : ∀ n, E n) (n : ℕ) :
    recPrefix (E := E) j k (encPrefix (E := E) j k x) n =
      if n ≤ k then (IsOmegaQVA.approx (D := E n) j : E n → E n) (x n) else ⊥ := by
  induction k generalizing n with
  | zero =>
    by_cases hn : n = 0
    · subst hn
      simp [recPrefix, encPrefix, (IsOmegaQVA.qfactorable (D := E 0) j).factor]
    · have : ¬ n ≤ 0 := fun h => hn (Nat.eq_zero_of_le_zero h)
      simp [recPrefix, encPrefix, hn, this]
  | succ k ih =>
    have hpair := QFactorable.pairEnc_unenc (encPrefix (E := E) j k x)
      ((IsOmegaQVA.qfactorable (D := E (k + 1)) j).enc (x (k + 1)))
    by_cases hn : n = k + 1
    · subst hn
      simp [recPrefix, encPrefix, hpair,
        (IsOmegaQVA.qfactorable (D := E (k + 1)) j).factor]
    · have hle : (n ≤ k + 1) ↔ n ≤ k :=
        ⟨fun h => Nat.le_of_lt_succ (lt_of_le_of_ne h hn), fun h => h.trans (Nat.le_succ k)⟩
      simp [recPrefix, encPrefix, hpair, hn, hle, ih]

def prefixFactorable (N : ℕ) : QFactorable (prefixMap (E := E) N) where
  dims := prefixDims (E := E) N N
  enc := encPrefix (E := E) N N
  recon := recPrefix (E := E) N N
  enc_mono := encPrefix_mono N N
  recon_mono := recPrefix_mono N N
  factor := fun x => by
    funext n
    simpa [prefixMap, prefixFun] using (recPrefix_encPrefix (E := E) N N x n).symm

theorem prefixMap_separated (N : ℕ) : FinitelySeparated (prefixMap (E := E) N) := by
  classical
  let Ms : (i : Fin (N + 1)) → Finset (E i.val) := fun i =>
    Classical.choose (IsOmegaQVA.separated (D := E i.val) N)
  have hMs : ∀ i : Fin (N + 1), ∀ x : E i.val,
      ∃ m ∈ Ms i, (IsOmegaQVA.approx (D := E i.val) N : _ → _) x ≤ m ∧ m ≤ x :=
    fun i => Classical.choose_spec (IsOmegaQVA.separated (D := E i.val) N)
  let Mπ : Finset (∀ i : Fin (N + 1), E i.val) := Fintype.piFinset Ms
  refine ⟨Mπ.image fun m => fun n => if h : n < N + 1 then m ⟨n, h⟩ else ⊥, fun x => ?_⟩
  have hx : ∀ i : Fin (N + 1),
      ∃ m ∈ Ms i, (IsOmegaQVA.approx (D := E i.val) N : _ → _) (x i.val) ≤ m ∧
        m ≤ x i.val :=
    fun i => hMs i (x i.val)
  choose m hm using hx
  have hmπ : m ∈ Mπ := by
    rw [Fintype.mem_piFinset]
    exact fun i => (hm i).1
  refine ⟨fun n => if h : n < N + 1 then m ⟨n, h⟩ else ⊥,
    Finset.mem_image.mpr ⟨m, hmπ, rfl⟩, ?_, ?_⟩
  · intro n
    by_cases hn : n < N + 1
    · have hle : n ≤ N := Nat.lt_succ_iff.mp hn
      simpa [prefixFun, prefixMap, hle, hn] using (hm ⟨n, hn⟩).2.1
    · have hle : ¬ n ≤ N := fun h => hn (Nat.lt_succ_of_le h)
      simp [prefixFun, prefixMap, hle, hn]
  · intro n
    by_cases hn : n < N + 1
    · simpa [hn] using (hm ⟨n, hn⟩).2.2
    · simp [hn]

theorem prefixMap_mono : Monotone (prefixMap (E := E)) := by
  intro i j hij
  rw [ScottMap.le_def]
  intro x n
  by_cases hn : n ≤ i
  · have hj : n ≤ j := hn.trans hij
    simpa [prefixMap, prefixFun, hn, hj] using
      IsOmegaQVA.monotone_approx (D := E n) hij (x n)
  · by_cases hj : n ≤ j
    · simp [prefixMap, prefixFun, hn, hj]
    · simp [prefixMap, prefixFun, hn, hj]

/-- `ωQVA` is closed under countable products. -/
@[reducible] def omegaQVA_pi : IsOmegaQVA (∀ n, E n) where
  isContinuousLattice :=
    proposition_2_9_a E fun n => IsOmegaQVA.isContinuousLattice (D := E n)
  approx := prefixMap
  qfactorable := prefixFactorable
  separated := prefixMap_separated
  monotone_approx := prefixMap_mono
  iSup_approx := by
    apply ScottMap.ext
    intro x
    funext k
    have hid := congrArg (fun f : ScottMap (E k) (E k) => (f : E k → E k) (x k))
      (IsOmegaQVA.iSup_approx (D := E k))
    have hcoord : (⨆ n, (IsOmegaQVA.approx (D := E k) n : E k → E k) (x k)) = x k := by
      simpa [scottMap_iSup_apply, ScottMap.idMap_apply] using hid
    rw [scottMap_iSup_apply, ScottMap.idMap_apply, iSup_apply]
    change (⨆ n, prefixFun (E := E) n x k) = x k
    refine le_antisymm ?_ ?_
    · refine iSup_le fun n => ?_
      by_cases hk : k ≤ n
      · simpa [prefixFun, hk] using finitelySeparated_le_id
          (IsOmegaQVA.separated (D := E k) n) (x k)
      · simp [prefixFun, hk]
    · rw [← hcoord]
      refine iSup_le fun n => ?_
      have hn : k ≤ max n k := le_max_right _ _
      calc
        (IsOmegaQVA.approx (D := E k) n : E k → E k) (x k)
            ≤ (IsOmegaQVA.approx (D := E k) (max n k) : E k → E k) (x k) :=
          IsOmegaQVA.monotone_approx (le_max_left n k) (x k)
        _ = prefixFun (E := E) (max n k) x k := by simp [prefixFun, hn]
        _ ≤ ⨆ m, prefixFun (E := E) m x k :=
          le_iSup (fun m => prefixFun (E := E) m x k) (max n k)

end PiOmega

end Scott1972.ContinuousLattice
