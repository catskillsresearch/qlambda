/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.InstrumentPower
import QLambda.RationalComplex

/-!
# Rational Choi/output observations

A finite quantum observation asks whether a strict rational lower bound
holds for a quadratic form of the Choi matrix accumulated over a
Scott-open set of returned values.  Rational vectors and thresholds are
countable.  Output observations are universal for arbitrary complete
lattices and separately admit countable coded subfamilies.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QLambda

open Scott1972.ContinuousLattice

universe u v

/-- A nonnegative rational threshold. -/
abbrev NonnegRat := {q : ℚ // 0 ≤ q}

/-- A countable quadratic Choi test: a Gaussian-rational vector and a
strict nonnegative rational threshold. -/
abbrev ChoiTest (n : ℕ) :=
  RatChoiVec n × NonnegRat

instance (n : ℕ) : Countable (ChoiTest n) :=
  inferInstance

namespace ChoiTest

def vector {n : ℕ} (t : ChoiTest n) : Fin n × Fin n → ℂ :=
  t.1.toComplex

def threshold {n : ℕ} (t : ChoiTest n) : ℝ :=
  t.2.1

/-- Real part of the quadratic form `vᴴ J v`. -/
noncomputable def eval {n : ℕ} (t : ChoiTest n)
    (J : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) : ℝ :=
  RCLike.re (star t.vector ⬝ᵥ (J *ᵥ t.vector))

theorem eval_nonneg {n : ℕ} (t : ChoiTest n)
    {J : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ}
    (hJ : J.PosSemidef) : 0 ≤ t.eval J :=
  hJ.re_dotProduct_nonneg t.vector

theorem eval_sub {n : ℕ} (t : ChoiTest n)
    (J K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    t.eval (K - J) = t.eval K - t.eval J := by
  simp [eval, Matrix.sub_mulVec, dotProduct_sub]

theorem eval_mono {n : ℕ} (t : ChoiTest n)
    {J K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ}
    (hJK : J ≤ K) : t.eval J ≤ t.eval K := by
  have hdiff : (K - J).PosSemidef := hJK
  have hnonneg := t.eval_nonneg hdiff
  rw [eval_sub] at hnonneg
  linarith

/-- Continuity of a finite-dimensional Choi quadratic form in its
vector argument. -/
theorem continuous_quadratic {n : ℕ}
    (J : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    Continuous (fun x : Fin n × Fin n → ℂ =>
      (star x ⬝ᵥ (J *ᵥ x)).re) := by
  apply Complex.continuous_re.comp
  apply continuous_finsetSum Finset.univ
  intro i hi
  apply (continuous_apply i).star.mul
  apply continuous_finsetSum Finset.univ
  intro j hj
  exact continuous_const.mul (continuous_apply j)

/-- Inequalities on Gaussian-rational vectors extend to all complex
vectors by density and continuity. -/
theorem all_quadratic_le_of_rational {n : ℕ}
    (J K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (h : ∀ v : RatChoiVec n,
      eval (v, ⟨0, le_rfl⟩) J ≤ eval (v, ⟨0, le_rfl⟩) K) :
    ∀ x : Fin n × Fin n → ℂ,
      (star x ⬝ᵥ (J *ᵥ x)).re ≤
        (star x ⬝ᵥ (K *ᵥ x)).re := by
  let f : (Fin n × Fin n → RatComplex) →
      (Fin n × Fin n → ℂ) :=
    Pi.map fun _ => RatComplex.toComplex
  have hf : DenseRange f :=
    DenseRange.piMap fun _ => RatComplex.denseRange_toComplex
  intro x
  refine DenseRange.induction_on (p := fun y =>
      (star y ⬝ᵥ (J *ᵥ y)).re ≤ (star y ⬝ᵥ (K *ᵥ y)).re)
    hf x (isClosed_le (continuous_quadratic J) (continuous_quadratic K)) ?_
  intro q
  let v : RatChoiVec n := fun k => q (finProdFinEquiv.symm k)
  have hv : v.toComplex = f q := by
    funext i
    change (q (finProdFinEquiv.symm (finProdFinEquiv i))).toComplex =
      (q i).toComplex
    rw [Equiv.symm_apply_apply]
  simpa [eval, vector, hv] using h v

theorem hermitian_quadratic_star {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (hA : A.IsHermitian) (x : m → ℂ) :
    star (star x ⬝ᵥ (A *ᵥ x)) = star x ⬝ᵥ (A *ᵥ x) := by
  change (starRingEnd ℂ) (∑ i, star (x i) * ∑ j, A i j * x j) =
    ∑ i, star (x i) * ∑ j, A i j * x j
  rw [map_sum]
  calc
    (∑ i, (starRingEnd ℂ) (star (x i) * ∑ j, A i j * x j)) =
        ∑ i, ∑ j, x i * star (A i j) * star (x j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_mul]
      have hss : (starRingEnd ℂ) (star (x i)) = x i := star_star (x i)
      rw [hss, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_mul]
      change x i * (star (A i j) * star (x j)) = _
      ring
    _ = ∑ i, ∑ j, star (x i) * A i j * x j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hA.apply]
      ring
    _ = ∑ i, star (x i) * ∑ j, A i j * x j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem posSemidef_of_re_quadratic_nonneg {m : Type*}
    [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (hA : A.IsHermitian)
    (h : ∀ x : m → ℂ, 0 ≤ (star x ⬝ᵥ (A *ᵥ x)).re) :
    A.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA
  intro x
  rw [Complex.nonneg_iff]
  constructor
  · exact h x
  · have hs := hermitian_quadratic_star A hA x
    have him := congrArg Complex.im hs
    rw [RCLike.star_def, Complex.conj_im] at him
    linarith

/-- Gaussian-rational quadratic inequalities characterize Loewner order
on Hermitian matrices. -/
theorem le_of_rational_quadratic_le {n : ℕ}
    {J K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ}
    (hJ : J.IsHermitian) (hK : K.IsHermitian)
    (h : ∀ v : RatChoiVec n,
      eval (v, ⟨0, le_rfl⟩) J ≤ eval (v, ⟨0, le_rfl⟩) K) :
    J ≤ K := by
  rw [Matrix.le_iff]
  apply posSemidef_of_re_quadratic_nonneg (K - J) (hK.sub hJ)
  intro x
  have hx := all_quadratic_le_of_rational J K h x
  simpa [Matrix.sub_mulVec, dotProduct_sub] using sub_nonneg.mpr hx

end ChoiTest

/-- A Scott-open observation of returned values.  It is intentionally
not required to be countable: the quantum power construction is defined
on every complete lattice, while countability is a closure theorem for
`ωQVA` inputs. -/
structure OutputObservation (D : Type u) [CompleteLattice D] where
  carrier : Set D
  isScottOpen : ScottOpen carrier

namespace OutputObservation

instance {D : Type u} [CompleteLattice D] : SetLike (OutputObservation D) D where
  coe U := U.carrier
  coe_injective U V h := by
    cases U
    cases V
    simp only [mk.injEq]
    exact h

@[simp] theorem mem_carrier {D : Type u} [CompleteLattice D]
    (U : OutputObservation D) (d : D) :
    d ∈ U.carrier ↔ d ∈ U :=
  Iff.rfl

def univ (D : Type u) [CompleteLattice D] : OutputObservation D :=
  ⟨Set.univ, scottOpen_univ⟩

def empty (D : Type u) [CompleteLattice D] : OutputObservation D :=
  ⟨∅, by
    constructor
    · intro a b hab ha
      exact False.elim ha
    · intro S hS hdir hmem
      exact False.elim hmem⟩

@[simp]
theorem not_mem_empty {D : Type u} [CompleteLattice D] (d : D) :
    d ∉ empty D :=
  id

def inter {D : Type u} [CompleteLattice D]
    (U V : OutputObservation D) : OutputObservation D :=
  ⟨U ∩ V, scottOpen_inter U.isScottOpen V.isScottOpen⟩

def union {D : Type u} [CompleteLattice D]
    (U V : OutputObservation D) : OutputObservation D :=
  ⟨U ∪ V, by
    constructor
    · intro a b hab ha
      rcases ha with ha | ha
      · exact Or.inl (U.isScottOpen.1 hab ha)
      · exact Or.inr (V.isScottOpen.1 hab ha)
    · intro S hS hdir hmem
      rcases hmem with hmem | hmem
      · obtain ⟨s, hs, hsU⟩ := U.isScottOpen.2 hS hdir hmem
        exact ⟨s, hs, Or.inl hsU⟩
      · obtain ⟨s, hs, hsV⟩ := V.isScottOpen.2 hS hdir hmem
        exact ⟨s, hs, Or.inr hsV⟩⟩

@[simp]
theorem mem_union {D : Type u} [CompleteLattice D]
    {d : D} {U V : OutputObservation D} :
    d ∈ union U V ↔ d ∈ U ∨ d ∈ V :=
  Iff.rfl

/-- A finite union of Scott-open output observations. -/
def listUnion {D : Type u} [CompleteLattice D] :
    List (OutputObservation D) → OutputObservation D
  | [] => empty D
  | U :: Us => union U (listUnion Us)

@[simp]
theorem mem_listUnion {D : Type u} [CompleteLattice D]
    {d : D} {Us : List (OutputObservation D)} :
    d ∈ listUnion Us ↔ ∃ U ∈ Us, d ∈ U := by
  induction Us with
  | nil => simp [listUnion]
  | cons U Us ih =>
      simp [listUnion, ih]

/-- Pull an output observation back along a Scott map. -/
def preimage {D E : Type u} [CompleteLattice D] [CompleteLattice E]
    (f : ScottMap D E) (V : OutputObservation E) : OutputObservation D :=
  ⟨f ⁻¹' V, scottOpen_preimage
    (fun S hS hdir => f.preservesDirectedSup_coe S hS hdir)
    V.isScottOpen⟩

end OutputObservation

/-- A countable family of Scott-open output observations.  The index is
kept separate from `D`, so no encodability assumption is imposed on the
semantic domain itself. -/
structure OutputCode (ι : Type v) (D : Type u) [CompleteLattice D] where
  observe : ι → OutputObservation D

namespace OutputCode

/-- Close an output code under finite unions.  Lists preserve
countability whenever the original code is countable. -/
def finiteUnion {ι : Type v} {D : Type u} [CompleteLattice D]
    (C : OutputCode ι D) : OutputCode (List ι) D :=
  ⟨fun is => OutputObservation.listUnion (is.map C.observe)⟩

@[simp]
theorem mem_finiteUnion {ι : Type v} {D : Type u} [CompleteLattice D]
    (C : OutputCode ι D) {is : List ι} {d : D} :
    d ∈ (finiteUnion C).observe is ↔ ∃ i ∈ is, d ∈ C.observe i := by
  simp [finiteUnion, OutputObservation.mem_listUnion]

theorem finiteUnion_subset {ι : Type v} {D : Type u} [CompleteLattice D]
    (C : OutputCode ι D) {is : List ι} {U : Set D}
    (h : ∀ i ∈ is, (C.observe i : Set D) ⊆ U) :
    ((finiteUnion C).observe is : Set D) ⊆ U := by
  intro d hd
  change d ∈ (finiteUnion C).observe is at hd
  rw [mem_finiteUnion] at hd
  obtain ⟨i, hi, hdi⟩ := hd
  exact h i hi hdi

end OutputCode

/-- A countable topological basis of output observations.  This is the
interface required from an `ωQVA` witness; it is deliberately separate
from the universal definition above. -/
structure CountableOutputBasis (D : Type u) [CompleteLattice D] where
  code : OutputCode ℕ D
  cofinal : ∀ (U : OutputObservation D) ⦃d : D⦄, d ∈ U →
    ∃ i, d ∈ code.observe i ∧ (code.observe i : Set D) ⊆ U

namespace CountableOutputBasis

variable {D : Type u} [CompleteLattice D]

/-- Decode a natural number as a finite list of natural-number codes. -/
noncomputable def decodedList (k : ℕ) : List ℕ :=
  match Encodable.decode (α := List ℕ) k with
  | some is => is
  | none => []

@[simp]
theorem decodedList_encode (is : List ℕ) :
    decodedList (Encodable.encode is) = is := by
  rw [decodedList, Encodable.encodek]

/-- Close a countable output basis under finite unions while retaining a
natural-number code type. -/
noncomputable def finiteUnionClosure (B : CountableOutputBasis D) :
    CountableOutputBasis D where
  code := ⟨fun k => (OutputCode.finiteUnion B.code).observe (decodedList k)⟩
  cofinal := by
    intro U d hd
    obtain ⟨i, hdi, hiU⟩ := B.cofinal U hd
    refine ⟨Encodable.encode [i], ?_, ?_⟩
    · change d ∈ (OutputCode.finiteUnion B.code).observe
        (decodedList (Encodable.encode [i]))
      rw [decodedList_encode, OutputCode.mem_finiteUnion]
      exact ⟨i, by simp, hdi⟩
    · change ((OutputCode.finiteUnion B.code).observe
        (decodedList (Encodable.encode [i])) : Set D) ⊆ U
      rw [decodedList_encode]
      apply OutputCode.finiteUnion_subset
      intro j hj
      simp only [List.mem_singleton] at hj
      subst j
      exact hiU

private theorem exists_covering_codes (B : CountableOutputBasis D)
    (U : OutputObservation D) (xs : List D)
    (hxs : ∀ d ∈ xs, d ∈ U) :
    ∃ is : List ℕ,
      (∀ d ∈ xs, ∃ i ∈ is, d ∈ B.code.observe i) ∧
      (∀ i ∈ is, (B.code.observe i : Set D) ⊆ U) := by
  induction xs with
  | nil =>
      exact ⟨[], by simp, by simp⟩
  | cons d ds ih =>
      obtain ⟨i, hdi, hiU⟩ := B.cofinal U (hxs d (by simp))
      obtain ⟨is, hcover, hisU⟩ :=
        ih (fun x hx => hxs x (by simp [hx]))
      refine ⟨i :: is, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨i, by simp, hdi⟩
        · obtain ⟨j, hj, hxj⟩ := hcover x hx
          exact ⟨j, by simp [hj], hxj⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hiU
        · exact hisU j hj

/-- A finite family of points in one Scott open is contained in one
coded finite-union neighbourhood lying inside that open. -/
theorem finiteUnionClosure_finite_cover (B : CountableOutputBasis D)
    (U : OutputObservation D) (xs : List D)
    (hxs : ∀ d ∈ xs, d ∈ U) :
    ∃ k, (∀ d ∈ xs, d ∈ (finiteUnionClosure B).code.observe k) ∧
      ((finiteUnionClosure B).code.observe k : Set D) ⊆ U := by
  obtain ⟨is, hcover, hisU⟩ := exists_covering_codes B U xs hxs
  refine ⟨Encodable.encode is, ?_, ?_⟩
  · intro d hd
    change d ∈ (OutputCode.finiteUnion B.code).observe
      (decodedList (Encodable.encode is))
    rw [decodedList_encode, OutputCode.mem_finiteUnion]
    exact hcover d hd
  · change ((OutputCode.finiteUnion B.code).observe
      (decodedList (Encodable.encode is)) : Set D) ⊆ U
    rw [decodedList_encode]
    exact OutputCode.finiteUnion_subset B.code hisU

variable [IsOmegaQVA D]

/-- A chosen finite separator for the `n`th approximant. -/
noncomputable def omegaSeparator (n : ℕ) : Finset D :=
  Classical.choose (IsOmegaQVA.separated (D := D) n)

theorem omegaSeparator_spec (n : ℕ) (x : D) :
    ∃ m ∈ omegaSeparator (D := D) n,
      (IsOmegaQVA.approx n : D → D) x ≤ m ∧ m ≤ x :=
  Classical.choose_spec (IsOmegaQVA.separated (D := D) n) x

/-- Indices for the CKL countable element basis.  An index records an
approximant and an element of one of the chosen finite separators. -/
abbrev OmegaBasisIndex :=
  Σ n : ℕ, ℕ × (omegaSeparator (D := D) n : Type u)

noncomputable instance : Encodable (OmegaBasisIndex (D := D)) := by
  unfold OmegaBasisIndex
  letI (n : ℕ) : Encodable (omegaSeparator (D := D) n : Type u) :=
    Fintype.toEncodable _
  infer_instance

/-- The basis element coded by `(n,j,m)` is `approx j m`. -/
def OmegaBasisIndex.point (i : OmegaBasisIndex (D := D)) : D :=
  (IsOmegaQVA.approx i.2.1 : D → D) i.2.2.1

/-- Every way-below pair is interpolated by a coded CKL basis element. -/
theorem exists_omegaBasisIndex {a x : D} (hax : a ≪ x) :
    ∃ i : OmegaBasisIndex (D := D), a ≤ i.point ∧ i.point ≪ x := by
  have hx : x =
      sSup (Set.range fun n => (IsOmegaQVA.approx n : D → D) x) := by
    rw [sSup_range]
    simpa [scottMap_iSup_apply, ScottMap.idMap_apply] using
      (congrArg (fun f : ScottMap D D => (f : D → D) x)
        (IsOmegaQVA.iSup_approx (D := D))).symm
  have hdirx : DirectedOn (· ≤ ·)
      (Set.range fun n => (IsOmegaQVA.approx n : D → D) x) :=
    directedOn_range.2 fun i j =>
      ⟨max i j,
        IsOmegaQVA.monotone_approx (D := D) (le_max_left i j) x,
        IsOmegaQVA.monotone_approx (D := D) (le_max_right i j) x⟩
  rw [hx] at hax
  obtain ⟨_, ⟨n, rfl⟩, han⟩ :=
    (wayBelow_sSup_iff (Set.range_nonempty _) hdirx).1 hax
  obtain ⟨m, hm, hnxm, hmx⟩ := omegaSeparator_spec (D := D) n x
  have ham : a ≪ m := han.trans_le hnxm
  have hmSup : m =
      sSup (Set.range fun j => (IsOmegaQVA.approx j : D → D) m) := by
    rw [sSup_range]
    simpa [scottMap_iSup_apply, ScottMap.idMap_apply] using
      (congrArg (fun f : ScottMap D D => (f : D → D) m)
        (IsOmegaQVA.iSup_approx (D := D))).symm
  have hdirm : DirectedOn (· ≤ ·)
      (Set.range fun j => (IsOmegaQVA.approx j : D → D) m) :=
    directedOn_range.2 fun i j =>
      ⟨max i j,
        IsOmegaQVA.monotone_approx (D := D) (le_max_left i j) m,
        IsOmegaQVA.monotone_approx (D := D) (le_max_right i j) m⟩
  rw [hmSup] at ham
  obtain ⟨_, ⟨j, rfl⟩, haj⟩ :=
    (wayBelow_sSup_iff (Set.range_nonempty _) hdirm).1 ham
  let i : OmegaBasisIndex (D := D) := ⟨n, j, ⟨m, hm⟩⟩
  refine ⟨i, haj.le, ?_⟩
  exact (finitelySeparated_wayBelow IsOmegaQVA.isContinuousLattice
    (IsOmegaQVA.separated (D := D) j) m).trans_le hmx

/-- The standard Scott-open way-above neighbourhood of an element. -/
def wayAbove (a : D) : OutputObservation D :=
  ⟨{x | a ≪ x}, scottOpen_wayBelow a⟩

/-- Decode a natural number as a CKL basis element, using bottom for
unused codes. -/
noncomputable def decodedPoint (k : ℕ) : D :=
  match Encodable.decode (α := OmegaBasisIndex (D := D)) k with
  | some i => i.point
  | none => ⊥

@[simp]
theorem decodedPoint_encode (i : OmegaBasisIndex (D := D)) :
    decodedPoint (D := D) (Encodable.encode i) = i.point := by
  rw [decodedPoint, Encodable.encodek]

/-- The countable family of way-above opens generated by the CKL basis. -/
noncomputable def omegaCode : OutputCode ℕ D :=
  ⟨fun k => wayAbove (decodedPoint (D := D) k)⟩

/-- Every `ωQVA` carries a countable basis for its Scott-open output
observations. -/
noncomputable def ofOmegaQVA : CountableOutputBasis D where
  code := omegaCode (D := D)
  cofinal := by
    intro U d hd
    obtain ⟨a, had, haU⟩ :=
      exists_wayBelow_Ici_subset IsOmegaQVA.isContinuousLattice
        U.isScottOpen hd
    obtain ⟨i, hai, hid⟩ := exists_omegaBasisIndex (D := D) had
    refine ⟨Encodable.encode i, ?_, ?_⟩
    · change decodedPoint (D := D) (Encodable.encode i) ≪ d
      rw [decodedPoint_encode]
      exact hid
    · intro x hx
      change decodedPoint (D := D) (Encodable.encode i) ≪ x at hx
      rw [decodedPoint_encode] at hx
      apply haU
      exact Set.mem_Ici.2 (hai.trans hx.le)

/-- The canonical `ωQVA` output basis closed under finite unions. -/
noncomputable def ofOmegaQVAFiniteUnion : CountableOutputBasis D :=
  finiteUnionClosure (ofOmegaQVA (D := D))

/-- Finitely many points of an `ωQVA` Scott open admit one coded
finite-union neighbourhood contained in that open. -/
theorem ofOmegaQVAFiniteUnion_finite_cover
    (U : OutputObservation D) (xs : List D)
    (hxs : ∀ d ∈ xs, d ∈ U) :
    ∃ k, (∀ d ∈ xs, d ∈ (ofOmegaQVAFiniteUnion (D := D)).code.observe k) ∧
      ((ofOmegaQVAFiniteUnion (D := D)).code.observe k : Set D) ⊆ U :=
  finiteUnionClosure_finite_cover (ofOmegaQVA (D := D)) U xs hxs

end CountableOutputBasis

/-- A universal atomic observation. -/
structure ObservationAtom (n : ℕ) (D : Type u) [CompleteLattice D] where
  output : OutputObservation D
  choi : ChoiTest n

/-- A coded atom from a countable output-observation family. -/
abbrev CodedAtom (n : ℕ) (ι : Type v) :=
  ChoiTest n × ι

/-- Finite conjunctions of universal observations. -/
abbrev ObservationToken (n : ℕ) (D : Type u) [CompleteLattice D] :=
  List (ObservationAtom n D)

/-- Finite conjunctions from a coded output family are countable. -/
abbrev CodedToken (n : ℕ) (ι : Type v) :=
  List (CodedAtom n ι)

instance (n : ℕ) {ι : Type v} [Encodable ι] : Encodable (CodedAtom n ι) :=
  inferInstance

instance (n : ℕ) {ι : Type v} [Encodable ι] : Countable (CodedAtom n ι) :=
  inferInstance

instance (n : ℕ) {ι : Type v} [Encodable ι] : Encodable (CodedToken n ι) :=
  inferInstance

instance (n : ℕ) {ι : Type v} [Encodable ι] : Countable (CodedToken n ι) :=
  inferInstance

namespace FiniteInstrumentComp

variable {n : ℕ} {D : Type u} [CompleteLattice D]

/-- Choi denotation distributes over a finite list of Kraus families. -/
theorem choi_flatMap {α : Type*} (xs : List α) (f : α → KrausFamily n n) :
    KrausFamily.choi (xs.flatMap f) = (xs.map fun x => KrausFamily.choi (f x)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.flatMap_cons, KrausFamily.choi_append, List.map_cons, List.sum_cons, ih]

/-- Intrinsic Choi matrix accumulated over branches whose return value
lies in `U`. -/
noncomputable def observationChoi (μ : FiniteInstrumentComp n D) (U : Set D) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  KrausFamily.choi (μ.selectedKraus U)

omit [CompleteLattice D] in
theorem observationChoi_posSemidef (μ : FiniteInstrumentComp n D) (U : Set D) :
    (μ.observationChoi U).PosSemidef :=
  KrausFamily.choi_posSemidef (μ.selectedKraus U)

omit [CompleteLattice D] in
theorem observationChoi_eq_testChoi (μ : FiniteInstrumentComp n D) (U : Set D) :
    μ.observationChoi U = μ.testChoi U := by
  classical
  rw [observationChoi, selectedKraus, choi_flatMap]
  simp [testChoi, Finset.sum_filter]

/-- For a finite instrument, every Scott-open observation can be
replaced by one coded finite-union observation that selects exactly the
same branches and lies inside the original open. -/
theorem exists_coded_observationChoi_eq [IsOmegaQVA D]
    (μ : FiniteInstrumentComp n D) (U : OutputObservation D) :
    ∃ k,
      ((CountableOutputBasis.ofOmegaQVAFiniteUnion
        (D := D)).code.observe k : Set D) ⊆ U ∧
      μ.observationChoi
          ((CountableOutputBasis.ofOmegaQVAFiniteUnion
            (D := D)).code.observe k : Set D) =
        μ.observationChoi U := by
  classical
  let xs : List D :=
    ((Finset.univ.filter fun o : μ.Outcome => μ.value o ∈ U).toList).map μ.value
  have hxs : ∀ d ∈ xs, d ∈ U := by
    intro d hd
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hd
    simpa using ho
  obtain ⟨k, hkcover, hkU⟩ :=
    CountableOutputBasis.ofOmegaQVAFiniteUnion_finite_cover U xs hxs
  refine ⟨k, hkU, ?_⟩
  have hmem (o : μ.Outcome) :
      μ.value o ∈
          ((CountableOutputBasis.ofOmegaQVAFiniteUnion
            (D := D)).code.observe k : Set D) ↔
        μ.value o ∈ (U : Set D) := by
    constructor
    · intro hV
      apply hkU
      exact hV
    · intro hoU
      change μ.value o ∈ U at hoU
      apply hkcover (μ.value o)
      apply List.mem_map.mpr
      exact ⟨o, by simp [hoU], rfl⟩
  rw [observationChoi_eq_testChoi, observationChoi_eq_testChoi]
  unfold testChoi
  apply Finset.sum_congr rfl
  intro o ho
  exact if_congr (hmem o) rfl rfl

/-- One coded sub-observation can simultaneously select the same
branches as an arbitrary Scott open for two finite instruments. -/
theorem exists_pair_coded_observationChoi_eq [IsOmegaQVA D]
    (μ ν : FiniteInstrumentComp n D) (U : OutputObservation D) :
    ∃ k,
      ((CountableOutputBasis.ofOmegaQVAFiniteUnion
        (D := D)).code.observe k : Set D) ⊆ U ∧
      μ.observationChoi
          ((CountableOutputBasis.ofOmegaQVAFiniteUnion
            (D := D)).code.observe k : Set D) =
        μ.observationChoi U ∧
      ν.observationChoi
          ((CountableOutputBasis.ofOmegaQVAFiniteUnion
            (D := D)).code.observe k : Set D) =
        ν.observationChoi U := by
  classical
  let xsμ : List D :=
    ((Finset.univ.filter fun o : μ.Outcome => μ.value o ∈ U).toList).map μ.value
  let xsν : List D :=
    ((Finset.univ.filter fun o : ν.Outcome => ν.value o ∈ U).toList).map ν.value
  have hxs : ∀ d ∈ xsμ ++ xsν, d ∈ U := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hd
      simpa using ho
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hd
      simpa using ho
  obtain ⟨k, hkcover, hkU⟩ :=
    CountableOutputBasis.ofOmegaQVAFiniteUnion_finite_cover U (xsμ ++ xsν) hxs
  refine ⟨k, hkU, ?_, ?_⟩
  · rw [observationChoi_eq_testChoi, observationChoi_eq_testChoi]
    unfold testChoi
    apply Finset.sum_congr rfl
    intro o ho
    apply if_congr
    · constructor
      · intro hV
        exact hkU hV
      · intro hoU
        change μ.value o ∈ U at hoU
        apply hkcover (μ.value o)
        apply List.mem_append_left xsν
        apply List.mem_map.mpr
        exact ⟨o, by simp [hoU], rfl⟩
    · rfl
    · rfl
  · rw [observationChoi_eq_testChoi, observationChoi_eq_testChoi]
    unfold testChoi
    apply Finset.sum_congr rfl
    intro o ho
    apply if_congr
    · constructor
      · intro hV
        exact hkU hV
      · intro hoU
        change ν.value o ∈ U at hoU
        apply hkcover (ν.value o)
        apply List.mem_append_right xsμ
        apply List.mem_map.mpr
        exact ⟨o, by simp [hoU], rfl⟩
    · rfl
    · rfl

end FiniteInstrumentComp

namespace ObservationAtom

variable {n : ℕ} {D : Type u} [CompleteLattice D]

/-- A physical finite instrument satisfies an atom when the selected
Choi quadratic form lies strictly above its rational threshold. -/
def Holds (a : ObservationAtom n D) (μ : FiniteInstrumentComp n D) : Prop :=
  a.choi.threshold < a.choi.eval (μ.observationChoi a.output)

theorem eval_nonneg (a : ObservationAtom n D) (μ : FiniteInstrumentComp n D) :
    0 ≤ a.choi.eval (μ.observationChoi a.output) :=
  a.choi.eval_nonneg (μ.observationChoi_posSemidef a.output)

theorem holds_of_threshold_lt {a b : ObservationAtom n D}
    (hout : a.output = b.output) (hvec : a.choi.1 = b.choi.1)
    (hthreshold : a.choi.threshold ≤ b.choi.threshold)
    {μ : FiniteInstrumentComp n D} (hμ : b.Holds μ) :
    a.Holds μ := by
  have heval :
      b.choi.eval (μ.observationChoi b.output) =
        a.choi.eval (μ.observationChoi a.output) := by
    simp only [ChoiTest.eval, ChoiTest.vector]
    rw [hout, hvec]
  exact hthreshold.trans_lt (hμ.trans_eq heval)

end ObservationAtom

namespace ObservationToken

variable {n : ℕ} {D : Type u} [CompleteLattice D]

def Holds (t : ObservationToken n D) (μ : FiniteInstrumentComp n D) : Prop :=
  ∀ a ∈ t, a.Holds μ

/-- Semantic weakening order on finite observations.  `t ≤ s` means
that the stronger conjunction `s` entails `t`. -/
def Entails (t s : ObservationToken n D) : Prop :=
  ∀ μ, Holds s μ → Holds t μ

instance : Preorder (ObservationToken n D) where
  le := Entails
  le_refl _ _ h := h
  le_trans _ _ _ h₁ h₂ μ h := h₁ μ (h₂ μ h)

theorem nil_le (t : ObservationToken n D) : [] ≤ t := by
  intro μ h a ha
  simp at ha

theorem le_append_left (t s : ObservationToken n D) : t ≤ t ++ s := by
  intro μ h a ha
  exact h a (List.mem_append_left s ha)

theorem le_append_right (t s : ObservationToken n D) : s ≤ t ++ s := by
  intro μ h a ha
  exact h a (List.mem_append_right t ha)

end ObservationToken

namespace FiniteInstrumentComp

variable {n : ℕ} {D : Type u} [CompleteLattice D]

/-- Pointwise Choi refinement on every Scott-open output observation. -/
def ObservationRefines (μ ν : FiniteInstrumentComp n D) : Prop :=
  ∀ U : OutputObservation D, μ.observationChoi U ≤ ν.observationChoi U

theorem observationRefines_refl (μ : FiniteInstrumentComp n D) :
    ObservationRefines μ μ :=
  fun _ => le_rfl

theorem observationRefines_trans {μ ν ξ : FiniteInstrumentComp n D}
    (hμν : ObservationRefines μ ν) (hνξ : ObservationRefines ν ξ) :
    ObservationRefines μ ξ :=
  fun U => (hμν U).trans (hνξ U)

theorem ObservationRefines.atom_holds {μ ν : FiniteInstrumentComp n D}
    (hμν : ObservationRefines μ ν) {a : ObservationAtom n D}
    (ha : a.Holds μ) : a.Holds ν :=
  ha.trans_le (a.choi.eval_mono (hμν a.output))

theorem ObservationRefines.token_holds {μ ν : FiniteInstrumentComp n D}
    (hμν : ObservationRefines μ ν) {t : ObservationToken n D}
    (ht : t.Holds μ) : t.Holds ν := by
  intro a ha
  exact hμν.atom_holds (ht a ha)

end FiniteInstrumentComp

namespace RatChoiVec

/-- The rational vector `e_p + e_q`, used to recover real parts by
polarization. -/
def realPair {n : ℕ} (p q : Fin n × Fin n) : RatChoiVec n :=
  single (finProdFinEquiv p) + single (finProdFinEquiv q)

/-- The rational vector `e_p + i e_q`, used to recover imaginary parts
by polarization. -/
def imagPair {n : ℕ} (p q : Fin n × Fin n) : RatChoiVec n :=
  fun k => single (finProdFinEquiv p) k +
    RatComplex.I * single (finProdFinEquiv q) k

@[simp]
theorem toComplex_realPair {n : ℕ} (p q : Fin n × Fin n) :
    (realPair p q).toComplex =
      Pi.single p (1 : ℂ) + Pi.single q (1 : ℂ) := by
  simp [realPair]

@[simp]
theorem toComplex_imagPair {n : ℕ} (p q : Fin n × Fin n) :
    (imagPair p q).toComplex =
      Pi.single p (1 : ℂ) + Complex.I • Pi.single q (1 : ℂ) := by
  funext i
  by_cases hip : i = p
  · subst i
    by_cases hpq : p = q
    · subst q
      simp [imagPair, RatChoiVec.toComplex, RatChoiVec.single]
    · simp [imagPair, RatChoiVec.toComplex, RatChoiVec.single, hpq]
  · by_cases hiq : i = q
    · subst i
      have hqp : q ≠ p := fun h => hip h
      simp [imagPair, RatChoiVec.toComplex, RatChoiVec.single, hqp]
    · simp [imagPair, RatChoiVec.toComplex, RatChoiVec.single, hip, hiq]

end RatChoiVec

namespace ChoiTest

theorem eval_single {n : ℕ}
    (J : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (p : Fin n × Fin n) :
    eval (RatChoiVec.single (finProdFinEquiv p), ⟨0, le_rfl⟩) J =
      (J p p).re := by
  simp [eval, vector, single_dotProduct]

theorem eval_realPair {n : ℕ}
    (J : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (p q : Fin n × Fin n) :
    eval (RatChoiVec.realPair p q, ⟨0, le_rfl⟩) J =
      (J p p + J p q + J q p + J q q).re := by
  simp only [eval, vector, RatChoiVec.toComplex_realPair]
  simp [add_dotProduct, dotProduct_add, Matrix.mulVec_add, single_dotProduct]
  ring

theorem eval_imagPair {n : ℕ}
    (J : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (p q : Fin n × Fin n) :
    eval (RatChoiVec.imagPair p q, ⟨0, le_rfl⟩) J =
      (J p p + Complex.I * J p q - Complex.I * J q p + J q q).re := by
  simp only [eval, vector, RatChoiVec.toComplex_imagPair]
  simp [add_dotProduct, dotProduct_add, Matrix.mulVec_add, Matrix.mulVec_smul,
    star_smul, single_dotProduct]
  ring

end ChoiTest

/-- Exact analytic checkpoint for the countable quantum tests.  It says
that Gaussian-rational quadratic forms separate Hermitian matrices.
The finite-coordinate algebra needed to discharge this proposition is
kept explicit rather than hidden in the definition of the token order. -/
def RationalQuadraticSeparation (n : ℕ) : Prop :=
  ∀ J K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ,
    J.IsHermitian → K.IsHermitian →
    (∀ v : RatChoiVec n,
      ChoiTest.eval (v, ⟨0, le_rfl⟩) J =
        ChoiTest.eval (v, ⟨0, le_rfl⟩) K) →
    J = K

/-- Gaussian-rational quadratic forms separate finite-dimensional
Hermitian matrices.  Coordinate vectors recover the diagonal, while
`e_p + e_q` and `e_p + i e_q` recover the real and imaginary parts of
each off-diagonal entry by polarization. -/
theorem rationalQuadraticSeparation (n : ℕ) :
    RationalQuadraticSeparation n := by
  intro J K hJ hK h
  ext p q
  apply Complex.ext
  · have hdp := h (RatChoiVec.single (finProdFinEquiv p))
    have hdq := h (RatChoiVec.single (finProdFinEquiv q))
    have hr := h (RatChoiVec.realPair p q)
    rw [ChoiTest.eval_single, ChoiTest.eval_single] at hdp hdq
    rw [ChoiTest.eval_realPair, ChoiTest.eval_realPair] at hr
    have hJqp : J q p = star (J p q) := (hJ.apply q p).symm
    have hKqp : K q p = star (K p q) := (hK.apply q p).symm
    rw [hJqp, hKqp] at hr
    have hJstar : (star (J p q)).re = (J p q).re := by
      rw [RCLike.star_def, Complex.conj_re]
    have hKstar : (star (K p q)).re = (K p q).re := by
      rw [RCLike.star_def, Complex.conj_re]
    simp only [Complex.add_re, hJstar, hKstar] at hr
    linarith
  · have hdp := h (RatChoiVec.single (finProdFinEquiv p))
    have hdq := h (RatChoiVec.single (finProdFinEquiv q))
    have hi := h (RatChoiVec.imagPair p q)
    rw [ChoiTest.eval_single, ChoiTest.eval_single] at hdp hdq
    rw [ChoiTest.eval_imagPair, ChoiTest.eval_imagPair] at hi
    have hJqp : J q p = star (J p q) := (hJ.apply q p).symm
    have hKqp : K q p = star (K p q) := (hK.apply q p).symm
    rw [hJqp, hKqp] at hi
    have hJstar : (star (J p q)).im = -(J p q).im := by
      rw [RCLike.star_def, Complex.conj_im]
    have hKstar : (star (K p q)).im = -(K p q).im := by
      rw [RCLike.star_def, Complex.conj_im]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
      hJstar, hKstar, neg_neg] at hi
    linarith

theorem choi_eq_of_rational_tests {n : ℕ}
    (K L : KrausFamily n n)
    (h : ∀ v : RatChoiVec n,
      ChoiTest.eval (v, ⟨0, le_rfl⟩) (KrausFamily.choi K) =
        ChoiTest.eval (v, ⟨0, le_rfl⟩) (KrausFamily.choi L)) :
    KrausFamily.choi K = KrausFamily.choi L :=
  rationalQuadraticSeparation n _ _ (KrausFamily.choi_posSemidef K).1
    (KrausFamily.choi_posSemidef L).1 h

theorem exists_strict_rational_test_of_nonzero {n : ℕ}
    {J : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ}
    (hJ : J.PosSemidef) (hne : J ≠ 0) :
    ∃ v : RatChoiVec n,
      ChoiTest.threshold (v, ⟨0, le_rfl⟩) <
        ChoiTest.eval (v, ⟨0, le_rfl⟩) J := by
  have hex : ∃ v : RatChoiVec n,
      ChoiTest.eval (v, ⟨0, le_rfl⟩) J ≠ 0 := by
    by_contra h
    have hall : ∀ v : RatChoiVec n,
        ChoiTest.eval (v, ⟨0, le_rfl⟩) J = 0 := by
      intro v
      by_contra hv
      exact h ⟨v, hv⟩
    apply hne
    apply rationalQuadraticSeparation n J 0 hJ.1 Matrix.isHermitian_zero
    intro v
    simpa [ChoiTest.eval] using hall v
  obtain ⟨v, hv⟩ := hex
  refine ⟨v, ?_⟩
  have hnonneg := ChoiTest.eval_nonneg (v, ⟨0, le_rfl⟩) hJ
  simpa [ChoiTest.threshold] using (lt_of_le_of_ne hnonneg hv.symm)

/-- The computational-basis measurement is accepted by the physical
observation semantics: every Scott-open selected Choi sum is positive
semidefinite and hence yields nonnegative rational quadratic tests. -/
theorem measureZComp_observation_nonnegative
    (U : OutputObservation Bool) (t : ChoiTest 2) :
    0 ≤ t.eval (Qubit.measureZComp.observationChoi U) :=
  t.eval_nonneg (Qubit.measureZComp.observationChoi_posSemidef U)

namespace CodedAtom

variable {n : ℕ} {D : Type u} [CompleteLattice D]
variable {ι : Type v}

def toObservation (C : OutputCode ι D) (a : CodedAtom n ι) :
    ObservationAtom n D :=
  ⟨C.observe a.2, a.1⟩

def Holds (C : OutputCode ι D) (a : CodedAtom n ι)
    (μ : FiniteInstrumentComp n D) : Prop :=
  (toObservation C a).Holds μ

end CodedAtom

namespace CodedToken

variable {n : ℕ} {D : Type u} [CompleteLattice D]
variable {ι : Type v}

def toObservation (C : OutputCode ι D) (t : CodedToken n ι) :
    ObservationToken n D :=
  t.map (CodedAtom.toObservation C)

def Holds (C : OutputCode ι D) (t : CodedToken n ι)
    (μ : FiniteInstrumentComp n D) : Prop :=
  (toObservation C t).Holds μ

theorem holds_iff (C : OutputCode ι D) (t : CodedToken n ι)
    (μ : FiniteInstrumentComp n D) :
    Holds C t μ ↔ ∀ a ∈ t, CodedAtom.Holds C a μ := by
  constructor
  · intro ht a ha
    exact ht _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
  · intro ht x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact ht a ha

end CodedToken

end QLambda
