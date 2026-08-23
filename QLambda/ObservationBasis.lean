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

def inter {D : Type u} [CompleteLattice D]
    (U V : OutputObservation D) : OutputObservation D :=
  ⟨U ∩ V, scottOpen_inter U.isScottOpen V.isScottOpen⟩

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

/-- A countable topological basis of output observations.  This is the
interface required from an `ωQVA` witness; it is deliberately separate
from the universal definition above. -/
structure CountableOutputBasis (D : Type u) [CompleteLattice D] where
  code : OutputCode ℕ D
  cofinal : ∀ (U : OutputObservation D) ⦃d : D⦄, d ∈ U →
    ∃ i, d ∈ code.observe i ∧ (code.observe i : Set D) ⊆ U

namespace CountableOutputBasis

variable {D : Type u} [CompleteLattice D] [IsOmegaQVA D]

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

end CodedToken

end QLambda
