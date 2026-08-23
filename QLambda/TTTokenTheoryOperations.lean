/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.RoundedTheoryMorphisms
import QLambda.TTRoundedTheory

open Set

namespace QLambda

open Scott1972.ContinuousLattice

universe u

/-- Exact closure of chosen output codes under pullback along a Scott map. -/
structure OutputCodeHom {D E : Type u} [CompleteLattice D] [CompleteLattice E]
    (C : OutputCode ℕ D) (C' : OutputCode ℕ E) (f : ScottMap D E) where
  pull : ℕ → ℕ
  observe_pull : ∀ i, C.observe (pull i) = OutputObservation.preimage f (C'.observe i)

/-- Exact closure of finite rational postconditions under a finite
instrument continuation. -/
structure BindCodeHom {n : ℕ} {D E : Type u}
    [CompleteLattice D] [CompleteLattice E]
    (C : OutputCode ℕ D) (C' : OutputCode ℕ E)
    (k : D → FiniteInstrumentComp n E) where
  pullPost : RatStepPostCode n → RatStepPostCode n
  wp_semEq : ∀ c d,
    KrausFamily.SemEq ((k d).wpKraus (c.decode C'))
      ((pullPost c).decode C d)

namespace OutputCodeHom

variable {D E F : Type u}
variable [CompleteLattice D] [CompleteLattice E] [CompleteLattice F]
variable {C : OutputCode ℕ D} {C' : OutputCode ℕ E} {C'' : OutputCode ℕ F}
variable {f : ScottMap D E} {g : ScottMap E F}

/-- Pull a rational finite-step postcondition through a code-compatible map. -/
def pullPost (h : OutputCodeHom C C' f) {n : ℕ}
    (c : RatStepPostCode n) : RatStepPostCode n where
  arity := c.arity
  opens := h.pull ∘ c.opens
  table := c.table
  table_mono := c.table_mono

theorem signature_pullPost (h : OutputCodeHom C C' f) {n : ℕ}
    (c : RatStepPostCode n) (d : D) :
    (h.pullPost c).signature C d = c.signature C' (f d) := by
  classical
  funext i
  change (if d ∈ C.observe (h.pull (c.opens i)) then true else false) =
    if f d ∈ C'.observe (c.opens i) then true else false
  rw [h.observe_pull]
  rfl

theorem decode_pullPost (h : OutputCodeHom C C' f) {n : ℕ}
    (c : RatStepPostCode n) (d : D) :
    (h.pullPost c).decode C d = c.decode C' (f d) := by
  change ((h.pullPost c).decodedMatrix C d).realize =
    (c.decodedMatrix C' (f d)).realize
  unfold RatStepPostCode.decodedMatrix
  rw [signature_pullPost]
  rfl

def pullAtom (h : OutputCodeHom C C' f) {n : ℕ}
    (a : TTObservationAtom n) : TTObservationAtom n :=
  ⟨h.pullPost a.post, a.choi⟩

def pullToken (h : OutputCodeHom C C' f) {n : ℕ}
    (t : TTObservationToken n) : TTObservationToken n :=
  t.map h.pullAtom

theorem holds_map_iff (h : OutputCodeHom C C' f) {n : ℕ}
    (a : TTObservationAtom n) (μ : FiniteInstrumentComp n D) :
    TTObservationAtom.Holds C' a (μ.map f) ↔
      TTObservationAtom.Holds C (h.pullAtom a) μ := by
  have hdecode :
      a.post.decode C' ∘ (f : D → E) = (h.pullPost a.post).decode C := by
    funext d
    exact (decode_pullPost h a.post d).symm
  unfold TTObservationAtom.Holds pullAtom
  rw [FiniteInstrumentComp.wpKraus_map, hdecode]

theorem token_holds_map_iff (h : OutputCodeHom C C' f) {n : ℕ}
    (t : TTObservationToken n) (μ : FiniteInstrumentComp n D) :
    TTObservationToken.Holds C' t (μ.map f) ↔
      TTObservationToken.Holds C (h.pullToken t) μ := by
  constructor
  · intro ht a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact (holds_map_iff h b μ).mp (ht b hb)
  · intro ht a ha
    exact (holds_map_iff h a μ).mpr
      (ht (h.pullAtom a) (List.mem_map.mpr ⟨a, ha, rfl⟩))

end OutputCodeHom

namespace BindCodeHom

variable {n : ℕ} {D E : Type u}
variable [CompleteLattice D] [CompleteLattice E]
variable {C : OutputCode ℕ D} {C' : OutputCode ℕ E}
variable {k : D → FiniteInstrumentComp n E}

def pullAtom (h : BindCodeHom C C' k)
    (a : TTObservationAtom n) : TTObservationAtom n :=
  ⟨h.pullPost a.post, a.choi⟩

def pullToken (h : BindCodeHom C C' k)
    (t : TTObservationToken n) : TTObservationToken n :=
  t.map h.pullAtom

theorem holds_bind_iff (h : BindCodeHom C C' k)
    (a : TTObservationAtom n) (μ : FiniteInstrumentComp n D) :
    TTObservationAtom.Holds C' a (μ.bind k) ↔
      TTObservationAtom.Holds C (h.pullAtom a) μ := by
  have hsem :
      KrausFamily.SemEq ((μ.bind k).wpKraus (a.post.decode C'))
        (μ.wpKraus ((h.pullPost a.post).decode C)) :=
    KrausFamily.applySemEq_trans
      (FiniteInstrumentComp.wpKraus_bind_semEq μ k (a.post.decode C'))
      (FiniteInstrumentComp.wpKraus_semEq_pred μ fun d =>
        h.wp_semEq a.post d)
  have hchoi := KrausFamily.choi_eq_of_semEq hsem
  unfold TTObservationAtom.Holds pullAtom
  rw [hchoi]

theorem token_holds_bind_iff (h : BindCodeHom C C' k)
    (t : TTObservationToken n) (μ : FiniteInstrumentComp n D) :
    TTObservationToken.Holds C' t (μ.bind k) ↔
      TTObservationToken.Holds C (h.pullToken t) μ := by
  constructor
  · intro ht a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact (holds_bind_iff h b μ).mp (ht b hb)
  · intro ht a ha
    exact (holds_bind_iff h a μ).mpr
      (ht (h.pullAtom a) (List.mem_map.mpr ⟨a, ha, rfl⟩))

end BindCodeHom

namespace FiniteInstrumentComp

variable {n : ℕ} {D E : Type u}
variable [CompleteLattice D] [CompleteLattice E]
variable {C : OutputCode ℕ D} {C' : OutputCode ℕ E}
variable {f : ScottMap D E}

theorem finitaryTTRefines_map (h : OutputCodeHom C C' f)
    {μ ν : FiniteInstrumentComp n D}
    (hμν : FinitaryTTRefines C μ ν) :
    FinitaryTTRefines C' (μ.map f) (ν.map f) := by
  intro c
  have hpull := hμν (h.pullPost c)
  have hdecode :
      c.decode C' ∘ (f : D → E) = (h.pullPost c).decode C := by
    funext d
    exact (OutputCodeHom.decode_pullPost h c d).symm
  rw [wpKraus_map, wpKraus_map, hdecode]
  exact hpull

theorem finitaryTTRefines_bind_left
    {k : D → FiniteInstrumentComp n E}
    (h : BindCodeHom C C' k)
    {μ ν : FiniteInstrumentComp n D}
    (hμν : FinitaryTTRefines C μ ν) :
    FinitaryTTRefines C' (μ.bind k) (ν.bind k) := by
  intro c
  exact KrausFamily.residualRefines_trans
    (KrausFamily.residualRefines_of_semEq <|
      KrausFamily.applySemEq_trans
        (wpKraus_bind_semEq μ k (c.decode C'))
        (wpKraus_semEq_pred μ fun d => h.wp_semEq c d))
    (KrausFamily.residualRefines_trans
      (hμν (h.pullPost c))
      (KrausFamily.residualRefines_of_semEq <|
        KrausFamily.applySemEq_symm <|
          KrausFamily.applySemEq_trans
            (wpKraus_bind_semEq ν k (c.decode C'))
            (wpKraus_semEq_pred ν fun d => h.wp_semEq c d)))

end FiniteInstrumentComp

namespace TTObservationAtom

variable {n : ℕ} {D : Type u} [CompleteLattice D]

theorem exists_unit_holds_of_directed (C : OutputCode ℕ D)
    (a : TTObservationAtom n) {S : Set D}
    (hS : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S)
    (ha : Holds C a (FiniteInstrumentComp.unit (n := n) (sSup S))) :
    ∃ d ∈ S, Holds C a (FiniteInstrumentComp.unit (n := n) d) := by
  obtain ⟨d, hdS, hsig⟩ :=
    RatStepPostCode.exists_signature_eq_of_directed C a.post hS hdir
  refine ⟨d, hdS, ?_⟩
  have hpost :
      a.post.decode C d = a.post.decode C (sSup S) := by
    change (a.post.decodedMatrix C d).realize =
      (a.post.decodedMatrix C (sSup S)).realize
    unfold RatStepPostCode.decodedMatrix
    rw [hsig]
  have hchoi :
      KrausFamily.choi
          ((FiniteInstrumentComp.unit (n := n) d).wpKraus
            (a.post.decode C)) =
        KrausFamily.choi
          ((FiniteInstrumentComp.unit (n := n) (sSup S)).wpKraus
            (a.post.decode C)) := by
    calc
      KrausFamily.choi
          ((FiniteInstrumentComp.unit (n := n) d).wpKraus
            (a.post.decode C)) =
          KrausFamily.choi (a.post.decode C d) :=
        KrausFamily.choi_eq_of_semEq
          (FiniteInstrumentComp.wpKraus_unit_semEq d (a.post.decode C))
      _ = KrausFamily.choi (a.post.decode C (sSup S)) :=
        congrArg KrausFamily.choi hpost
      _ = KrausFamily.choi
          ((FiniteInstrumentComp.unit (n := n) (sSup S)).wpKraus
            (a.post.decode C)) :=
        (KrausFamily.choi_eq_of_semEq
          (FiniteInstrumentComp.wpKraus_unit_semEq
            (sSup S) (a.post.decode C))).symm
  unfold Holds at ha ⊢
  rw [hchoi]
  exact ha

end TTObservationAtom

namespace TTObservationToken

variable {n : ℕ} {D : Type u} [CompleteLattice D]

theorem exists_unit_holds_of_directed (C : OutputCode ℕ D)
    (t : TTObservationToken n) {S : Set D}
    (hS : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S)
    (ht : Holds C t (FiniteInstrumentComp.unit (n := n) (sSup S))) :
    ∃ d ∈ S, Holds C t (FiniteInstrumentComp.unit (n := n) d) := by
  induction t with
  | nil =>
      obtain ⟨d, hdS⟩ := hS
      exact ⟨d, hdS, nil_holds C _⟩
  | cons a t ih =>
      have ha : TTObservationAtom.Holds C a
          (FiniteInstrumentComp.unit (n := n) (sSup S)) :=
        ht a (by simp)
      have ht' : Holds C t
          (FiniteInstrumentComp.unit (n := n) (sSup S)) := by
        intro b hb
        exact ht b (by simp [hb])
      obtain ⟨d, hdS, had⟩ :=
        TTObservationAtom.exists_unit_holds_of_directed C a hS hdir ha
      obtain ⟨e, heS, hte⟩ := ih ht'
      obtain ⟨z, hzS, hdz, hez⟩ := hdir d hdS e heS
      refine ⟨z, hzS, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact TTObservationAtom.holds_mono C
          (FiniteInstrumentComp.unit_mono hdz) had
      · exact holds_mono C (FiniteInstrumentComp.unit_mono hez) hte b hb

end TTObservationToken

namespace TTTokenTheory

variable {n : ℕ} {D : Type u} [CompleteLattice D]

/-- Deterministic return as a TT theory of finitary observations. -/
noncomputable def unit (C : OutputCode ℕ D) (d : D) : TTTokenTheory n C :=
  (FiniteInstrumentComp.unit (n := n) d).satisfiedTTTheory C

theorem mem_unit (C : OutputCode ℕ D) (d : D) (t : TTObservationToken n) :
    t ∈ unit (n := n) C d ↔
      TTObservationToken.Holds C t (FiniteInstrumentComp.unit (n := n) d) :=
  Iff.rfl

theorem unit_mono (C : OutputCode ℕ D) :
    Monotone (unit (n := n) C) := by
  intro d e hde t ht
  exact TTObservationToken.holds_mono C
    (FiniteInstrumentComp.unit_mono hde) ht

theorem unit_sSup_directed (C : OutputCode ℕ D)
    {S : Set D} (hS : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S) :
    unit (n := n) C (sSup S) = sSup (unit (n := n) C '' S) := by
  apply RoundedTheory.ext
  ext t
  change t ∈ unit (n := n) C (sSup S) ↔
    t ∈ (sSup (unit (n := n) C '' S) : TTTokenTheory n C)
  rw [RoundedTheory.mem_sSup]
  constructor
  · intro ht
    obtain ⟨d, hdS, htd⟩ :=
      TTObservationToken.exists_unit_holds_of_directed C t hS hdir ht
    exact ⟨unit (n := n) C d, ⟨d, hdS, rfl⟩, htd⟩
  · rintro ⟨_, ⟨d, hdS, rfl⟩, htd⟩
    exact TTObservationToken.holds_mono C
      (FiniteInstrumentComp.unit_mono (le_sSup hdS)) htd

/-- Deterministic return is Scott-continuous for every chosen output code. -/
noncomputable def unitScott (C : OutputCode ℕ D) :
    ScottMap D (TTTokenTheory n C) :=
  ⟨unit (n := n) C, continuous_of_preservesDirectedSup fun _ hS hdir =>
    unit_sSup_directed C hS hdir⟩

@[simp]
theorem unitScott_apply (C : OutputCode ℕ D) (d : D) :
    unitScott (n := n) C d = unit (n := n) C d :=
  rfl

/-- A token-derivation relation induces a Scott-continuous TT-theory map. -/
noncomputable def mapOfDerivation
    {E : Type u} [CompleteLattice E]
    (C : OutputCode ℕ D) (C' : OutputCode ℕ E)
    (R : TTObservationToken n → TTObservationToken n → Prop) :
    ScottMap (TTTokenTheory n C) (TTTokenTheory n C') :=
  RoundedTheory.extendRelation
    (TTObservationToken.roundedBasis (n := n) C)
    (TTObservationToken.roundedBasis (n := n) C') R

/-- Token derivation for pushforward along a code-compatible Scott map. -/
def MapDerives
    {E : Type u} [CompleteLattice E]
    {C : OutputCode ℕ D} {C' : OutputCode ℕ E}
    {f : ScottMap D E} (h : OutputCodeHom C C' f)
    (s t : TTObservationToken n) : Prop :=
  s = h.pullToken t

/-- Pushforward generated by exact pullback of finite TT observations. -/
noncomputable def map
    {E : Type u} [CompleteLattice E]
    (C : OutputCode ℕ D) (C' : OutputCode ℕ E)
    (f : ScottMap D E) (h : OutputCodeHom C C' f) :
    ScottMap (TTTokenTheory n C) (TTTokenTheory n C') :=
  mapOfDerivation C C' (MapDerives h)

/-- The derivation-generated map agrees exactly with finite pushforward. -/
theorem map_satisfiedTTTheory
    {E : Type u} [CompleteLattice E]
    (C : OutputCode ℕ D) (C' : OutputCode ℕ E)
    (f : ScottMap D E) (h : OutputCodeHom C C' f)
    (μ : FiniteInstrumentComp n D) :
    map C C' f h (μ.satisfiedTTTheory C) =
      (μ.map f).satisfiedTTTheory C' := by
  apply RoundedTheory.ext
  ext t
  constructor
  · intro ht
    obtain ⟨s, hs, c, hsc, htc⟩ :=
      (RoundedTheory.mem_extendRelation
        (B := TTObservationToken.roundedBasis (n := n) C)
        (C := TTObservationToken.roundedBasis (n := n) C')).mp ht
    subst s
    have hc :
        TTObservationToken.Holds C' c (μ.map f) :=
      (OutputCodeHom.token_holds_map_iff h c μ).mpr hs
    exact TTObservationToken.roundedBelow_entails C' htc (μ.map f) hc
  · intro ht
    obtain ⟨c, htc, hc⟩ :=
      TTObservationToken.exists_stronglyBelow_holds C' (μ.map f) ht
    apply (RoundedTheory.mem_extendRelation
      (B := TTObservationToken.roundedBasis (n := n) C)
      (C := TTObservationToken.roundedBasis (n := n) C')).2
    refine ⟨h.pullToken c,
      (OutputCodeHom.token_holds_map_iff h c μ).mp hc, c, rfl, ?_⟩
    exact ⟨t, TTObservationToken.entails_refl C' t, htc⟩

/-- Token derivation induced by an exactly representable finite continuation. -/
def BindDerives
    {E : Type u} [CompleteLattice E]
    {C : OutputCode ℕ D} {C' : OutputCode ℕ E}
    {k : D → FiniteInstrumentComp n E} (h : BindCodeHom C C' k)
    (s t : TTObservationToken n) : Prop :=
  s = h.pullToken t

/-- Finitary bind generated by pulling TT tokens through a finite continuation. -/
noncomputable def bindFinite
    {E : Type u} [CompleteLattice E]
    (C : OutputCode ℕ D) (C' : OutputCode ℕ E)
    (k : D → FiniteInstrumentComp n E) (h : BindCodeHom C C' k) :
    ScottMap (TTTokenTheory n C) (TTTokenTheory n C') :=
  mapOfDerivation C C' (BindDerives h)

/-- The derivation-generated finitary bind agrees with finite instrument bind. -/
theorem bindFinite_satisfiedTTTheory
    {E : Type u} [CompleteLattice E]
    (C : OutputCode ℕ D) (C' : OutputCode ℕ E)
    (k : D → FiniteInstrumentComp n E) (h : BindCodeHom C C' k)
    (μ : FiniteInstrumentComp n D) :
    bindFinite C C' k h (μ.satisfiedTTTheory C) =
      (μ.bind k).satisfiedTTTheory C' := by
  apply RoundedTheory.ext
  ext t
  constructor
  · intro ht
    obtain ⟨s, hs, c, hsc, htc⟩ :=
      (RoundedTheory.mem_extendRelation
        (B := TTObservationToken.roundedBasis (n := n) C)
        (C := TTObservationToken.roundedBasis (n := n) C')).mp ht
    subst s
    have hc :
        TTObservationToken.Holds C' c (μ.bind k) :=
      (BindCodeHom.token_holds_bind_iff h c μ).mpr hs
    exact TTObservationToken.roundedBelow_entails C' htc (μ.bind k) hc
  · intro ht
    obtain ⟨c, htc, hc⟩ :=
      TTObservationToken.exists_stronglyBelow_holds C' (μ.bind k) ht
    apply (RoundedTheory.mem_extendRelation
      (B := TTObservationToken.roundedBasis (n := n) C)
      (C := TTObservationToken.roundedBasis (n := n) C')).2
    refine ⟨h.pullToken c,
      (BindCodeHom.token_holds_bind_iff h c μ).mp hc, c, rfl, ?_⟩
    exact ⟨t, TTObservationToken.entails_refl C' t, htc⟩

end TTTokenTheory

end QLambda
