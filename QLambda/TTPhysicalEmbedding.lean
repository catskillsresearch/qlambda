/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.TTExternalChoice
import QLambda.TTResultOperations

namespace QLambda

open Scott1972.ContinuousLattice

universe u

namespace TTPhysicalEmbedding

variable {n : ℕ} {D E : Type u}
variable [CompleteLattice D] [CompleteLattice E]

/-- Embed a finite physical instrument into the continuation model by
aggregating finite branch-local result observations. -/
noncomputable def embed (μ : FiniteInstrumentComp n D) :
    TTContinuation.TTContinuationPower n D :=
  TTTokenTheory.bindResultScott μ

@[simp]
theorem embed_apply (μ : FiniteInstrumentComp n D)
    (k : Scott1972.ContinuousLattice.ScottMap D
      (TTContinuation.TTResult n)) :
    embed μ k = TTTokenTheory.aggregateResult μ k :=
  rfl

/-- On a continuation represented by finite result instruments at every
returned value of `μ`, the embedding computes physical finite bind exactly. -/
theorem embed_satisfied
    (μ : FiniteInstrumentComp n D)
    (ν : D → FiniteInstrumentComp n PUnit.{1})
    (k : Scott1972.ContinuousLattice.ScottMap D
      (TTContinuation.TTResult n))
    (hk : ∀ o : μ.Outcome,
      k (μ.value o) =
        (ν (μ.value o)).satisfiedTTTheory TTContinuation.resultCode) :
    embed μ k =
      (μ.bind ν).satisfiedTTTheory TTContinuation.resultCode :=
  TTTokenTheory.bindResultScott_satisfied μ ν k hk

/-- A source-code test represented inside the result continuation model.

The Scott postcondition is finitely presented pointwise, and `probe` recovers
the original source weakest precondition after finite bind.  Keeping this
representation hypothesis explicit isolates the density statement that would
be needed for an unconditional order equivalence. -/
structure CodedTestRepresentation
    (C : OutputCode ℕ D) (c : RatStepPostCode n) where
  post : ScottMap D (TTContinuation.TTResult n)
  result : D → FiniteInstrumentComp n PUnit.{1}
  post_eq : ∀ d,
    post d = (result d).satisfiedTTTheory TTContinuation.resultCode
  probe : RatStepPostCode n
  wp_semEq : ∀ ρ : FiniteInstrumentComp n D,
    KrausFamily.SemEq
      ((ρ.bind result).wpKraus
        (probe.decode TTContinuation.resultCode))
      (ρ.wpKraus (c.decode C))

/-- Order between physical embeddings preserves every source-code test that
has an explicit Scott representation in the result model. -/
theorem finitaryTTRefines_test_of_embed_le
    (C : OutputCode ℕ D) {μ ν : FiniteInstrumentComp n D}
    (hμν : embed μ ≤ embed ν) (c : RatStepPostCode n)
    (R : CodedTestRepresentation C c) :
    KrausFamily.Refines
      (μ.wpKraus (c.decode C)) (ν.wpKraus (c.decode C)) := by
  have htheory :
      (μ.bind R.result).satisfiedTTTheory TTContinuation.resultCode ≤
        (ν.bind R.result).satisfiedTTTheory TTContinuation.resultCode := by
    calc
      (μ.bind R.result).satisfiedTTTheory TTContinuation.resultCode =
          embed μ R.post := by
        symm
        exact embed_satisfied μ R.result R.post fun o =>
          R.post_eq (μ.value o)
      _ ≤ embed ν R.post := hμν R.post
      _ = (ν.bind R.result).satisfiedTTTheory
          TTContinuation.resultCode := by
        exact embed_satisfied ν R.result R.post fun o =>
          R.post_eq (ν.value o)
  have hprobe :
      KrausFamily.Refines
        ((μ.bind R.result).wpKraus
          (R.probe.decode TTContinuation.resultCode))
        ((ν.bind R.result).wpKraus
          (R.probe.decode TTContinuation.resultCode)) :=
    ((FiniteInstrumentComp.satisfiedTTTheory_le_iff_finitaryTTRefines
      TTContinuation.resultCode).1 htheory) R.probe
  exact KrausFamily.residualRefines_trans
    (KrausFamily.residualRefines_of_semEq
      (KrausFamily.applySemEq_symm (R.wp_semEq μ)))
    (KrausFamily.residualRefines_trans hprobe
      (KrausFamily.residualRefines_of_semEq (R.wp_semEq ν)))

/-- Consequently, embedding order implies finitary TT refinement whenever
the chosen source code has Scott representations for all of its tests. -/
theorem finitaryTTRefines_of_embed_le
    (C : OutputCode ℕ D) {μ ν : FiniteInstrumentComp n D}
    (represented : ∀ c : RatStepPostCode n, CodedTestRepresentation C c)
    (hμν : embed μ ≤ embed ν) :
    FiniteInstrumentComp.FinitaryTTRefines C μ ν :=
  fun c => finitaryTTRefines_test_of_embed_le C hμν c (represented c)

private theorem satisfiedTTTheory_eq_of_wpKraus_semEq
    {μ ν : FiniteInstrumentComp n PUnit.{1}}
    (h : ∀ P : PUnit.{1} → KrausFamily n n,
      KrausFamily.SemEq (μ.wpKraus P) (ν.wpKraus P)) :
    μ.satisfiedTTTheory TTContinuation.resultCode =
      ν.satisfiedTTTheory TTContinuation.resultCode := by
  apply (FiniteInstrumentComp.satisfiedTTTheory_eq_iff_mutual_finitaryTTRefines
    TTContinuation.resultCode).2
  constructor
  · intro c
    exact KrausFamily.residualRefines_of_semEq
      (h (c.decode TTContinuation.resultCode))
  · intro c
    exact KrausFamily.residualRefines_of_semEq
      (KrausFamily.applySemEq_symm
        (h (c.decode TTContinuation.resultCode)))

/-- The physical embedding preserves deterministic return exactly. -/
theorem embed_unit (d : D) :
    embed (FiniteInstrumentComp.unit (n := n) d) =
      TTContinuation.unit (n := n) d := by
  apply ScottMap.ext
  intro k
  apply RoundedTheory.ext
  ext t
  let B := TTObservationToken.roundedBasis
    (n := n) TTContinuation.resultCode
  constructor
  · intro ht
    obtain ⟨sources, hsources, target, hderives, httarget⟩ :=
      (TTTokenTheory.mem_aggregateResult
        (FiniteInstrumentComp.unit (n := n) d) k t).mp ht
    let s := sources Unit.unit
    have hs : s ∈ k d := hsources Unit.unit
    have hsround : s ∈ RoundedTheory.round B (k d).carrier := by
      rw [(k d).rounded]
      exact hs
    obtain ⟨s', hs'k, hss'⟩ := hsround
    have htarget_s :
        TTObservationToken.Entails TTContinuation.resultCode target s := by
      intro ξ hsξ
      let ν : D → FiniteInstrumentComp n PUnit.{1} := fun _ => ξ
      have hbind : TTObservationToken.Holds TTContinuation.resultCode target
          ((FiniteInstrumentComp.unit (n := n) d).bind ν) := by
        apply hderives ν
        intro o
        rcases o with ⟨⟩
        exact hsξ
      have heq :
          ((FiniteInstrumentComp.unit (n := n) d).bind ν).satisfiedTTTheory
              TTContinuation.resultCode =
            ξ.satisfiedTTTheory TTContinuation.resultCode := by
        apply satisfiedTTTheory_eq_of_wpKraus_semEq
        intro P
        exact KrausFamily.applySemEq_trans
          (FiniteInstrumentComp.wpKraus_bind_semEq
            (FiniteInstrumentComp.unit (n := n) d) ν P)
          (FiniteInstrumentComp.wpKraus_unit_semEq d
            fun x => (ν x).wpKraus P)
      apply (FiniteInstrumentComp.mem_satisfiedTTTheory
        TTContinuation.resultCode ξ target).mp
      rw [← heq]
      exact (FiniteInstrumentComp.mem_satisfiedTTTheory
        TTContinuation.resultCode
        ((FiniteInstrumentComp.unit (n := n) d).bind ν) target).2 hbind
    have hts' :
        TTObservationToken.RoundedBelow
          TTContinuation.resultCode t s' := by
      obtain ⟨v, hsv, hvs'⟩ := hss'
      exact ⟨v,
        TTObservationToken.entails_trans TTContinuation.resultCode
          (TTObservationToken.roundedBelow_entails
            TTContinuation.resultCode httarget)
          (TTObservationToken.entails_trans TTContinuation.resultCode
            htarget_s hsv),
        hvs'⟩
    have htround : t ∈ RoundedTheory.round B (k d).carrier :=
      ⟨s', hs'k, hts'⟩
    rw [(k d).rounded] at htround
    exact htround
  · intro ht
    have htround : t ∈ RoundedTheory.round B (k d).carrier := by
      rw [(k d).rounded]
      exact ht
    obtain ⟨target, htargetk, httarget⟩ := htround
    let sources :
        (FiniteInstrumentComp.unit (n := n) d).Outcome →
          TTObservationToken n :=
      fun _ => target
    apply (TTTokenTheory.mem_aggregateResult
      (FiniteInstrumentComp.unit (n := n) d) k t).2
    refine ⟨sources, ?_, target, ?_, httarget⟩
    · intro o
      rcases o with ⟨⟩
      exact htargetk
    · intro ν hsources
      have hν : TTObservationToken.Holds TTContinuation.resultCode target
          (ν d) := hsources Unit.unit
      have heq :
          ((FiniteInstrumentComp.unit (n := n) d).bind ν).satisfiedTTTheory
              TTContinuation.resultCode =
            (ν d).satisfiedTTTheory TTContinuation.resultCode := by
        apply satisfiedTTTheory_eq_of_wpKraus_semEq
        intro P
        exact KrausFamily.applySemEq_trans
          (FiniteInstrumentComp.wpKraus_bind_semEq
            (FiniteInstrumentComp.unit (n := n) d) ν P)
          (FiniteInstrumentComp.wpKraus_unit_semEq d
            fun x => (ν x).wpKraus P)
      apply (FiniteInstrumentComp.mem_satisfiedTTTheory
        TTContinuation.resultCode
        ((FiniteInstrumentComp.unit (n := n) d).bind ν) target).mp
      rw [heq]
      exact (FiniteInstrumentComp.mem_satisfiedTTTheory
        TTContinuation.resultCode (ν d) target).2 hν

/-- Right unit in the continuation model, specialized to an embedded
finite instrument. -/
theorem embed_bind_unit (μ : FiniteInstrumentComp n D) :
    TTContinuation.bind
        (TTContinuation.unit (n := n) :
          ScottMap D (TTContinuation.TTContinuationPower n D))
        (embed μ) =
      embed μ := by
  have h := TTContinuation.bind_unit (n := n) (D := D)
  exact congrArg (fun F => F (embed μ)) h

/-- Left unit in the continuation model, using exact preservation of
finite deterministic return. -/
theorem embed_unit_bind
    (d : D)
    (h : ScottMap D (TTContinuation.TTContinuationPower n E)) :
    TTContinuation.bind h
        (embed (FiniteInstrumentComp.unit (n := n) d)) =
      h d := by
  rw [embed_unit]
  exact congrArg (fun q : ScottMap D
    (TTContinuation.TTContinuationPower n E) => q d)
    (TTContinuation.unit_bind h)

/-- The physical embedding agrees with continuation return whenever the
result continuation at the returned value has a finite presentation. -/
theorem embed_unit_satisfied
    (d : D) (ξ : FiniteInstrumentComp n PUnit.{1})
    (k : ScottMap D (TTContinuation.TTResult n))
    (hk : k d = ξ.satisfiedTTTheory TTContinuation.resultCode) :
    embed (FiniteInstrumentComp.unit (n := n) d) k =
      TTContinuation.unit (n := n) d k := by
  let ν : D → FiniteInstrumentComp n PUnit.{1} := fun _ => ξ
  calc
    embed (FiniteInstrumentComp.unit (n := n) d) k =
        ((FiniteInstrumentComp.unit (n := n) d).bind ν).satisfiedTTTheory
          TTContinuation.resultCode := by
      apply embed_satisfied
      intro o
      rcases o with ⟨⟩
      exact hk
    _ = ξ.satisfiedTTTheory TTContinuation.resultCode := by
      apply satisfiedTTTheory_eq_of_wpKraus_semEq
      intro P
      exact KrausFamily.applySemEq_trans
        (FiniteInstrumentComp.wpKraus_bind_semEq
          (FiniteInstrumentComp.unit (n := n) d) ν P)
        (FiniteInstrumentComp.wpKraus_unit_semEq d
          fun x => (ν x).wpKraus P)
    _ = k d := hk.symm
    _ = TTContinuation.unit (n := n) d k := rfl

/-- Finite functor compatibility on finitely presented result
continuations. -/
theorem embed_map_satisfied
    (g : ScottMap D E) (μ : FiniteInstrumentComp n D)
    (ξ : E → FiniteInstrumentComp n PUnit.{1})
    (k : ScottMap E (TTContinuation.TTResult n))
    (hk : ∀ o : (μ.map g).Outcome,
      k ((μ.map g).value o) =
        (ξ ((μ.map g).value o)).satisfiedTTTheory
          TTContinuation.resultCode) :
    TTContinuation.map g (embed μ) k =
      embed (μ.map g) k := by
  have hsource (o : μ.Outcome) :
      (k.comp g) (μ.value o) =
        (ξ (g (μ.value o))).satisfiedTTTheory
          TTContinuation.resultCode := by
    exact hk o
  calc
    TTContinuation.map g (embed μ) k = embed μ (k.comp g) := rfl
    _ = (μ.bind fun d => ξ (g d)).satisfiedTTTheory
          TTContinuation.resultCode := by
      exact embed_satisfied μ (fun d => ξ (g d)) (k.comp g) hsource
    _ = ((μ.map g).bind ξ).satisfiedTTTheory
          TTContinuation.resultCode := by
      apply satisfiedTTTheory_eq_of_wpKraus_semEq
      intro P
      have hright :=
        FiniteInstrumentComp.wpKraus_bind_semEq (μ.map g) ξ P
      rw [FiniteInstrumentComp.wpKraus_map] at hright
      exact KrausFamily.applySemEq_trans
        (FiniteInstrumentComp.wpKraus_bind_semEq μ (fun d => ξ (g d)) P)
        (KrausFamily.applySemEq_symm hright)
    _ = embed (μ.map g) k := by
      exact (embed_satisfied (μ.map g) ξ k hk).symm

/-- Finite Kleisli compatibility on finitely presented result
continuations. The Scott map `h` need only agree with the embedded finite
continuation at the values returned by `μ`. -/
theorem embed_bind_satisfied
    (μ : FiniteInstrumentComp n D)
    (f : D → FiniteInstrumentComp n E)
    (h : ScottMap D (TTContinuation.TTContinuationPower n E))
    (hh : ∀ o : μ.Outcome, h (μ.value o) = embed (f (μ.value o)))
    (ξ : E → FiniteInstrumentComp n PUnit.{1})
    (k : ScottMap E (TTContinuation.TTResult n))
    (hk : ∀ p : (μ.bind f).Outcome,
      k ((μ.bind f).value p) =
        (ξ ((μ.bind f).value p)).satisfiedTTTheory
          TTContinuation.resultCode) :
    TTContinuation.bind h (embed μ) k =
      embed (μ.bind f) k := by
  have hinner (o : μ.Outcome) :
      TTContinuation.continuation h k (μ.value o) =
        ((f (μ.value o)).bind ξ).satisfiedTTTheory
          TTContinuation.resultCode := by
    rw [TTContinuation.continuation_apply, hh o]
    apply embed_satisfied
    intro q
    exact hk ⟨o, q⟩
  calc
    TTContinuation.bind h (embed μ) k =
        embed μ (TTContinuation.continuation h k) := rfl
    _ = (μ.bind fun d => (f d).bind ξ).satisfiedTTTheory
          TTContinuation.resultCode := by
      exact embed_satisfied μ (fun d => (f d).bind ξ)
        (TTContinuation.continuation h k) hinner
    _ = ((μ.bind f).bind ξ).satisfiedTTTheory
          TTContinuation.resultCode := by
      apply satisfiedTTTheory_eq_of_wpKraus_semEq
      intro P
      apply KrausFamily.applySemEq_symm
      exact KrausFamily.applySemEq_trans
        (FiniteInstrumentComp.wpKraus_bind_semEq (μ.bind f) ξ P)
        (KrausFamily.applySemEq_trans
          (FiniteInstrumentComp.wpKraus_bind_semEq μ f
            fun e => (ξ e).wpKraus P)
          (KrausFamily.applySemEq_trans
            (FiniteInstrumentComp.wpKraus_semEq_pred μ fun d =>
              KrausFamily.applySemEq_symm
                (FiniteInstrumentComp.wpKraus_bind_semEq (f d) ξ P))
            (KrausFamily.applySemEq_symm
              (FiniteInstrumentComp.wpKraus_bind_semEq μ
                (fun d => (f d).bind ξ) P))))
    _ = embed (μ.bind f) k := by
      exact (embed_satisfied (μ.bind f) ξ k hk).symm

/-! ## Compatibility with the complete tagged model -/

/-- A finite physical computation represented at every branch-tree
coordinate.  Physical primitives introduce no unresolved external branch. -/
noncomputable def taggedEmbed (μ : FiniteInstrumentComp n D) :
    TTContinuation.TTExternalContinuationPower n D :=
  fun _ => embed μ

@[simp]
theorem taggedEmbed_apply (μ : FiniteInstrumentComp n D) (i : ℕ)
    (k : ScottMap D (TTContinuation.TTResult n)) :
    taggedEmbed μ i k = embed μ k :=
  rfl

/-- Tagged physical return agrees exactly with the reader-transformer unit. -/
theorem taggedEmbed_unit (d : D) :
    taggedEmbed (FiniteInstrumentComp.unit (n := n) d) =
      TTContinuation.taggedUnit (n := n) d := by
  funext i
  exact embed_unit d

/-- Represented-continuation compatibility for tagged Kleisli extension.
The finite presentation condition is the exact boundary inherited from
`embed_bind_satisfied`; no density or finite-image retraction is assumed. -/
theorem taggedEmbed_bind_satisfied
    (μ : FiniteInstrumentComp n D)
    (f : D → FiniteInstrumentComp n E)
    (h : ScottMap D (TTContinuation.TTExternalContinuationPower n E))
    (hh : ∀ o : μ.Outcome, h (μ.value o) = taggedEmbed (f (μ.value o)))
    (ξ : E → FiniteInstrumentComp n PUnit.{1})
    (k : ScottMap E (TTContinuation.TTResult n))
    (hk : ∀ p : (μ.bind f).Outcome,
      k ((μ.bind f).value p) =
        (ξ ((μ.bind f).value p)).satisfiedTTTheory
          TTContinuation.resultCode)
    (i : ℕ) :
    TTContinuation.taggedBindScott h (taggedEmbed μ) i k =
      taggedEmbed (μ.bind f) i k := by
  let hi : ScottMap D (TTContinuation.TTContinuationPower n E) :=
    ⟨fun d => h d i, continuous_of_preservesDirectedSup fun S hS hdir => by
      have hs := h.preservesDirectedSup_coe S hS hdir
      have hsi := congrArg (fun q => q i) hs
      rw [sSup_apply_eq_sSup_image] at hsi
      simpa only [Set.image_image] using hsi⟩
  change TTContinuation.bind hi (embed μ) k = embed (μ.bind f) k
  apply embed_bind_satisfied μ f hi
  · intro o
    exact congrArg (fun q => q i) (hh o)
  · exact hk

/-- A Scott-continuous projection of the ambient continuation domain onto
exactly the finite physical image.  Such a projection is intentionally not
asserted to exist. -/
structure FiniteImageScottRetraction (n : ℕ) (D : Type u)
    [CompleteLattice D] where
  project : ScottMap (TTContinuation.TTContinuationPower n D)
    (TTContinuation.TTContinuationPower n D)
  fixes : ∀ μ : FiniteInstrumentComp n D, project (embed μ) = embed μ
  lands : ∀ q, ∃ μ : FiniteInstrumentComp n D, project q = embed μ

/-- Any Scott retraction onto the finite image would force that image to be
closed under all nonempty directed suprema. -/
theorem finiteImage_directedSupClosed_of_retraction
    (R : FiniteImageScottRetraction n D)
    {S : Set (TTContinuation.TTContinuationPower n D)}
    (hS : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S)
    (hfinite : S ⊆ Set.range (embed (n := n) (D := D))) :
    sSup S ∈ Set.range (embed (n := n) (D := D)) := by
  have himage : R.project '' S = S := by
    ext q
    constructor
    · rintro ⟨p, hpS, rfl⟩
      obtain ⟨μ, hμ⟩ := hfinite hpS
      have hpfix : R.project p = p := by
        calc
          R.project p = R.project (embed μ) :=
            congrArg (fun q => R.project q) hμ.symm
          _ = embed μ := R.fixes μ
          _ = p := hμ
      simpa only [hpfix] using hpS
    · intro hqS
      refine ⟨q, hqS, ?_⟩
      obtain ⟨μ, hμ⟩ := hfinite hqS
      calc
        R.project q = R.project (embed μ) :=
          congrArg (fun p => R.project p) hμ.symm
        _ = embed μ := R.fixes μ
        _ = q := hμ
  have hpres := R.project.preservesDirectedSup_coe S hS hdir
  rw [himage] at hpres
  obtain ⟨μ, hμ⟩ := R.lands (sSup S)
  exact ⟨μ, hμ.symm.trans hpres⟩

/-- Thus any directed family of finite embeddings whose supremum is not
finite rules out a Scott retraction onto the finite image.  This is the valid
formal boundary: a concrete non-closure witness is required, rather than an
unsupported finite-retract claim. -/
theorem no_finiteImageScottRetraction_of_directedSup_not_finite
    {S : Set (TTContinuation.TTContinuationPower n D)}
    (hS : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S)
    (hfinite : S ⊆ Set.range (embed (n := n) (D := D)))
    (hnot : sSup S ∉ Set.range (embed (n := n) (D := D))) :
    FiniteImageScottRetraction n D → False := by
  intro R
  exact hnot
    (finiteImage_directedSupClosed_of_retraction R hS hdir hfinite)

end TTPhysicalEmbedding

end QLambda
