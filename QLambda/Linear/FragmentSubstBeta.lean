/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentIdentityBeta

/-!
# F4b: closed substitution β on `FragCert.denote` past identity bodies

`fragment_betaL_closed_post` / `fragment_betaU_closed_post` widen the closed
identity β spines to bodies that post-process the bound variable by an
arbitrary map, so the body no longer has to be the projection `var 0`.

Since the classical-bit counit `classicalBitWeakening` is such a map, the
unrestricted form also covers *constant* bodies.  That yields the first
substitution equations on `FragCert.denote` whose body is a genuinely
non-identity first-order term:

    app (λ!x. bitLit c) (bitLit b)  ↦  bitLit c
    app (λ!x. unit)     (bitLit b)  ↦  unit
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf

/-! ## Discarding a prepared classical bit -/

open Matrix in
private theorem basisBra_sandwich_basisKet (k i : Fin 2)
    (ρ : Matrix (Fin 1) (Fin 1) ℂ) :
    SigmaMon.ChoiSum.basisBra k *
        (SigmaMon.ChoiSum.basisKet i * ρ * (SigmaMon.ChoiSum.basisKet i)ᴴ) *
        (SigmaMon.ChoiSum.basisBra k)ᴴ =
      if k = i then ρ else 0 := by
  have hfuse :
      SigmaMon.ChoiSum.basisBra k *
          (SigmaMon.ChoiSum.basisKet i * ρ * (SigmaMon.ChoiSum.basisKet i)ᴴ) *
          (SigmaMon.ChoiSum.basisBra k)ᴴ =
        (SigmaMon.ChoiSum.basisBra k * SigmaMon.ChoiSum.basisKet i) * ρ *
          ((SigmaMon.ChoiSum.basisBra k * SigmaMon.ChoiSum.basisKet i)ᴴ) := by
    simp [Matrix.mul_assoc, ← Matrix.conjTranspose_mul]
  rw [hfuse]
  by_cases h : k = i
  · subst h
    rw [if_pos rfl, SigmaMon.ChoiSum.basisBra_mul_basisKet k]
    simp
  · rw [if_neg h, SigmaMon.ChoiSum.basisBra_mul_basisKet_of_ne h]
    simp

/-- Discarding a computational-basis preparation is the identity channel. -/
theorem discardTwo_comp_isometricBasisPrep (i : Fin 2) :
    Superoperator.comp SigmaMon.ChoiSum.discardTwo
        (SigmaMon.ChoiSum.isometricBasisPrep i) =
      Superoperator.identity 1 := by
  apply Superoperator.ext
  apply CPMap.ext_apply
  intro ρ
  simp only [Superoperator.cp_comp, SigmaMon.ChoiSum.discardTwo,
    SigmaMon.ChoiSum.isometricBasisPrep, Superoperator.identity,
    CPMap.applyMat_comp, CPMap.applyMat_ofKraus, CPMap.applyMat_identity,
    KrausFamily.applyMat_cons, KrausFamily.applyMat_nil, add_zero]
  rw [basisBra_sandwich_basisKet 0 i, basisBra_sandwich_basisKet 1 i]
  fin_cases i <;> simp

/-- Discarding a bit literal collapses to the Day unit identity. -/
theorem bitDiscard_comp_bitLitHom (b : Bool) :
    Hom.comp bitDiscard (bitLitHom b) = Hom.id dayTensorUnit := by
  have hb :
      Superoperator.comp SigmaMon.ChoiSum.discardTwo (bitPrepare b) =
        Superoperator.identity 1 := by
    cases b <;> simp only [bitPrepare]
    · exact discardTwo_comp_isometricBasisPrep 0
    · exact discardTwo_comp_isometricBasisPrep 1
  change Hom.comp (yonedaMap SigmaMon.ChoiSum.discardTwo)
      (yonedaMap (bitPrepare b)) = Hom.id dayTensorUnit
  rw [← yonedaMap_comp, hb, yonedaMap_id]

/-- The classical-bit counit is physical discard after inclusion. -/
theorem classicalBitWeakening_eq_bitDiscard :
    classicalBitWeakening = Hom.comp bitDiscard classicalBitInclusion := by
  ext n x
  rfl

/-- Classicalising then discarding a bit literal is the Day unit identity. -/
theorem classicalBitWeakening_comp_bitClassicalize_bitLit (b : Bool) :
    Hom.comp classicalBitWeakening (Hom.comp bitClassicalize (bitLitHom b)) =
      Hom.id dayTensorUnit := by
  rw [classicalBitWeakening_eq_bitDiscard,
    ← Hom.comp_assoc bitDiscard classicalBitInclusion
      (Hom.comp bitClassicalize (bitLitHom b)),
    classicalBitInclusion_comp_bitClassicalize_bitLit b]
  exact bitDiscard_comp_bitLitHom b

/-! ## The singleton bit context discards through the classical counit -/

/-- On `Γ = [bit]`, `Δ = []` the combined discard is the counit after the two
unitors that strip the empty context slots. -/
theorem combinedAllDiscard_bit_nil (hΓ : CtxUAllBit [Ty.bit])
    (hΔ : AllNone ([] : List (Option Ty))) :
    FragmentContext.combinedAllDiscard hΓ hΔ =
      Hom.comp classicalBitWeakening
        (Hom.comp (DayTensor.rightUnitor classicalBitModule)
          (DayTensor.rightUnitor
            (dayTensor classicalBitModule dayTensorUnit))) := by
  have hconv :
      FragmentContext.combinedAllDiscard hΓ hΔ =
        Hom.comp (DayTensor.leftUnitor dayTensorUnit)
          (DayTensor.map
            (Hom.comp (DayTensor.leftUnitor dayTensorUnit)
              (DayTensor.map classicalBitWeakening (Hom.id dayTensorUnit)))
            (Hom.id dayTensorUnit)) := rfl
  rw [hconv, leftUnitor_unit_eq_rightUnitor_unit, rightUnitor_natural,
    rightUnitor_natural, Hom.comp_assoc]

/-! ## Closed β for post-processing bodies -/

/-- Pull a post-processing map out of a three-fold composite. -/
private theorem post_regroup {A₀ A₁ A₂ A₃ A₄ : Module}
    (k : Hom A₃ A₄) (r : Hom A₂ A₃) (m : Hom A₁ A₂) (p : Hom A₀ A₁) :
    Hom.comp (Hom.comp (Hom.comp k r) m) p =
      Hom.comp k (Hom.comp (Hom.comp r m) p) := by
  simp only [Hom.comp_assoc]

/-- Closed linear β for a body of the form `k ∘ (projection of the bound
variable)`; `k = id` is the identity body already proved in
`FragmentIdentityBeta`. -/
theorem fragment_betaL_closed_post {A : Ty} {N : Module}
    (hA : Ty.FirstOrder A) (k : Hom (fragmentModule A) N)
    (body : Hom
      (dayTensor dayTensorUnit (dayTensor (fragmentModule A) dayTensorUnit)) N)
    (f : Hom dayTensorUnit (fragmentModule A))
    (hbody :
      body =
        Hom.comp k
          (Hom.comp (DayTensor.leftUnitor (fragmentModule A))
            (DayTensor.map (Hom.id dayTensorUnit)
              (DayTensor.rightUnitor (fragmentModule A))))) :
    Hom.comp (FragmentContext.evalFragmentFirstOrder hA N)
      (Hom.comp
        (DayTensor.map (FragmentContext.abstractLinear hA body)
          (FragmentContext.closedPoint f))
        (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) =
      FragmentContext.closedPoint (Hom.comp k f) := by
  let Φ : Hom (FragmentContext.combined [] [])
      (internalHomRepresentable A.hilbertDim N) :=
    FragmentContext.abstractLinear hA body
  have hfactor :
      DayTensor.map Φ (FragmentContext.closedPoint f) =
        Hom.comp (DayTensor.map Φ (Hom.id (fragmentModule A)))
          (DayTensor.map (Hom.id (FragmentContext.combined [] []))
            (FragmentContext.closedPoint f)) := by
    simpa only [Hom.comp_id, Hom.id_comp] using
      DayTensor.map_comp Φ (Hom.id (FragmentContext.combined [] []))
        (Hom.id (fragmentModule A)) (FragmentContext.closedPoint f)
  change Hom.comp (FragmentContext.evalFragmentFirstOrder hA N)
      (Hom.comp (DayTensor.map Φ (FragmentContext.closedPoint f))
        (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) =
    FragmentContext.closedPoint (Hom.comp k f)
  rw [hfactor]
  have hreassoc :
      Hom.comp (FragmentContext.evalFragmentFirstOrder hA N)
          (Hom.comp
            (Hom.comp (DayTensor.map Φ (Hom.id (fragmentModule A)))
              (DayTensor.map (Hom.id (FragmentContext.combined [] []))
                (FragmentContext.closedPoint f)))
            (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) =
        Hom.comp
          (Hom.comp (FragmentContext.evalFragmentFirstOrder hA N)
            (DayTensor.map Φ (Hom.id (fragmentModule A))))
          (Hom.comp
            (DayTensor.map (Hom.id (FragmentContext.combined [] []))
              (FragmentContext.closedPoint f))
            (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) := by
    rw [Hom.comp_assoc, Hom.comp_assoc, ← Hom.comp_assoc]
  rw [hreassoc]
  have hβ :
      Hom.comp (FragmentContext.evalFragmentFirstOrder hA N)
          (DayTensor.map Φ (Hom.id (fragmentModule A))) =
        Hom.comp body
          (FragmentContext.moveArgumentIntoLinear dayTensorUnit dayTensorUnit
            (fragmentModule A)) := by
    dsimp only [Φ]
    exact FragmentContext.evalFragmentFirstOrder_abstractLinear hA body
  rw [hβ, hbody]
  refine Eq.trans (post_regroup _ _ _ _) ?_
  refine Eq.trans
    (congrArg (Hom.comp k) (closed_identity_move_cancel_frag f)) ?_
  simp only [FragmentContext.closedPoint]
  exact Hom.comp_assoc k f FragmentContext.combinedClosedCollapse

/-- Regroup the unrestricted composite so the body unitors meet the move and
the classicalisation meets the closed argument. -/
private theorem unres_post_regroup {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : Module}
    (i : Hom A₅ A₆) (r : Hom A₄ A₅) (m : Hom A₃ A₄) (c : Hom A₂ A₃)
    (p : Hom A₁ A₂) (s : Hom A₀ A₁) :
    Hom.comp (Hom.comp (Hom.comp i r) (Hom.comp m c)) (Hom.comp p s) =
      Hom.comp i (Hom.comp (Hom.comp r m) (Hom.comp (Hom.comp c p) s)) := by
  simp only [Hom.comp_assoc]

/-- Cancellation of the unrestricted move, split and classicalisation against
a closed argument, for a body that post-processes the classical variable. -/
private theorem closed_unres_post_cancel {N : Module}
    (k : Hom classicalBitModule N)
    (f : Hom dayTensorUnit (fragmentModule .bit)) :
    Hom.comp
        (Hom.comp
          (Hom.comp k
            (Hom.comp (DayTensor.rightUnitor classicalBitModule)
              (DayTensor.rightUnitor
                (dayTensor classicalBitModule dayTensorUnit))))
          (Hom.comp
            (FragmentContext.moveArgumentIntoUnrestricted
              dayTensorUnit dayTensorUnit classicalBitModule)
            (DayTensor.map (Hom.id (dayTensor dayTensorUnit dayTensorUnit))
              bitClassicalize)))
        (Hom.comp
          (DayTensor.map (Hom.id (FragmentContext.combined [] []))
            (FragmentContext.closedPoint f))
          (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) =
      FragmentContext.closedPoint (Hom.comp k (Hom.comp bitClassicalize f)) := by
  have hmove := FragmentContext.identity_body_unres_move_eq classicalBitModule
  have hO :
      FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil =
        DayTensor.map FragmentContext.closedLeftUnitorInv
          FragmentContext.closedLeftUnitorInv := by
    rw [FragmentContext.combinedOSplit_nil]; rfl
  have hfuse :
      Hom.comp bitClassicalize (FragmentContext.closedPoint f) =
        FragmentContext.closedPoint (Hom.comp bitClassicalize f) := by
    simp only [FragmentContext.closedPoint]
    exact Hom.comp_assoc bitClassicalize f
      FragmentContext.combinedClosedCollapse
  have hmap :
      Hom.comp
          (DayTensor.map (Hom.id (dayTensor dayTensorUnit dayTensorUnit))
            bitClassicalize)
          (DayTensor.map (Hom.id (FragmentContext.combined [] []))
            (FragmentContext.closedPoint f)) =
        DayTensor.map (Hom.id (FragmentContext.combined [] []))
          (FragmentContext.closedPoint (Hom.comp bitClassicalize f)) := by
    rw [← hfuse]
    change Hom.comp
        (DayTensor.map (Hom.id (FragmentContext.combined [] [])) bitClassicalize)
        (DayTensor.map (Hom.id (FragmentContext.combined [] []))
          (FragmentContext.closedPoint f)) =
      DayTensor.map (Hom.id (FragmentContext.combined [] []))
        (Hom.comp bitClassicalize (FragmentContext.closedPoint f))
    simpa only [Hom.id_comp] using
      (DayTensor.map_comp
        (Hom.id (FragmentContext.combined [] []))
        (Hom.id (FragmentContext.combined [] []))
        bitClassicalize (FragmentContext.closedPoint f)).symm
  have hcancel :
      Hom.comp
          (Hom.comp (DayTensor.leftUnitor classicalBitModule)
            (DayTensor.map (DayTensor.rightUnitor dayTensorUnit)
              (Hom.id classicalBitModule)))
          (Hom.comp
            (DayTensor.map (Hom.id (FragmentContext.combined [] []))
              (FragmentContext.closedPoint (Hom.comp bitClassicalize f)))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv)) =
        FragmentContext.closedPoint (Hom.comp bitClassicalize f) := by
    rw [FragmentContext.closedPoint]
    exact closed_identity_move_cancel (Hom.comp bitClassicalize f)
  refine Eq.trans (unres_post_regroup _ _ _ _ _ _) ?_
  rw [hmove, hmap, hO]
  refine Eq.trans (congrArg (Hom.comp k) hcancel) ?_
  simp only [FragmentContext.closedPoint]
  exact Hom.comp_assoc k (Hom.comp bitClassicalize f)
    FragmentContext.combinedClosedCollapse

/-- Closed unrestricted β for a body of the form `k ∘ (projection of the
classical bound variable)`.  Taking `k = classicalBitInclusion` recovers the
identity body; taking `k = g ∘ classicalBitWeakening` gives a constant body. -/
theorem fragment_betaU_closed_post {N : Module}
    (k : Hom classicalBitModule N)
    (body : Hom
      (dayTensor (dayTensor classicalBitModule dayTensorUnit) dayTensorUnit) N)
    (f : Hom dayTensorUnit (fragmentModule .bit))
    (hbody :
      body =
        Hom.comp k
          (Hom.comp (DayTensor.rightUnitor classicalBitModule)
            (DayTensor.rightUnitor
              (dayTensor classicalBitModule dayTensorUnit)))) :
    Hom.comp (FragmentContext.evalUnrestrictedBit N)
      (Hom.comp
        (DayTensor.map (FragmentContext.abstractUnrestricted body)
          (FragmentContext.closedPoint f))
        (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) =
      FragmentContext.closedPoint
        (Hom.comp k (Hom.comp bitClassicalize f)) := by
  let Φ : Hom (FragmentContext.combined [] [])
      (dayInternalHom classicalBitModule N) :=
    FragmentContext.abstractUnrestricted body
  have hfactor :
      DayTensor.map Φ (FragmentContext.closedPoint f) =
        Hom.comp (DayTensor.map Φ (Hom.id (fragmentModule .bit)))
          (DayTensor.map (Hom.id (FragmentContext.combined [] []))
            (FragmentContext.closedPoint f)) := by
    simpa only [Hom.comp_id, Hom.id_comp] using
      DayTensor.map_comp Φ (Hom.id (FragmentContext.combined [] []))
        (Hom.id (fragmentModule .bit)) (FragmentContext.closedPoint f)
  change Hom.comp (FragmentContext.evalUnrestrictedBit N)
      (Hom.comp (DayTensor.map Φ (FragmentContext.closedPoint f))
        (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) =
    FragmentContext.closedPoint (Hom.comp k (Hom.comp bitClassicalize f))
  rw [hfactor]
  have hreassoc :
      Hom.comp (FragmentContext.evalUnrestrictedBit N)
          (Hom.comp
            (Hom.comp (DayTensor.map Φ (Hom.id (fragmentModule .bit)))
              (DayTensor.map (Hom.id (FragmentContext.combined [] []))
                (FragmentContext.closedPoint f)))
            (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) =
        Hom.comp
          (Hom.comp (FragmentContext.evalUnrestrictedBit N)
            (DayTensor.map Φ (Hom.id (fragmentModule .bit))))
          (Hom.comp
            (DayTensor.map (Hom.id (FragmentContext.combined [] []))
              (FragmentContext.closedPoint f))
            (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) := by
    rw [Hom.comp_assoc, Hom.comp_assoc, ← Hom.comp_assoc]
  rw [hreassoc]
  have hβ :
      Hom.comp (FragmentContext.evalUnrestrictedBit N)
          (DayTensor.map Φ (Hom.id (fragmentModule .bit))) =
        Hom.comp body
          (Hom.comp
            (FragmentContext.moveArgumentIntoUnrestricted
              dayTensorUnit dayTensorUnit classicalBitModule)
            (DayTensor.map (Hom.id (dayTensor dayTensorUnit dayTensorUnit))
              bitClassicalize)) := by
    dsimp only [Φ]
    exact FragmentContext.evalUnrestrictedBit_abstractUnrestricted body
  rw [hβ, hbody]
  exact closed_unres_post_cancel k f

/-! ## Constant unrestricted bodies -/

/-- Closed unrestricted β for a constant body: the argument is discarded
through the classical-bit counit, leaving the body's point. -/
theorem fragment_betaU_const_closed {N : Module}
    (g : Hom dayTensorUnit N)
    (body : Hom
      (dayTensor (dayTensor classicalBitModule dayTensorUnit) dayTensorUnit) N)
    (f : Hom dayTensorUnit (fragmentModule .bit))
    (hbody :
      body =
        FragmentContext.combinedPoint fragment_ctxU_bit_nil
          (show AllNone ([] : List (Option Ty)) from trivial) g)
    (hf :
      Hom.comp classicalBitWeakening (Hom.comp bitClassicalize f) =
        Hom.id dayTensorUnit) :
    Hom.comp (FragmentContext.evalUnrestrictedBit N)
      (Hom.comp
        (DayTensor.map (FragmentContext.abstractUnrestricted body)
          (FragmentContext.closedPoint f))
        (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) =
      FragmentContext.closedPoint g := by
  have hpost :
      body =
        Hom.comp (Hom.comp g classicalBitWeakening)
          (Hom.comp (DayTensor.rightUnitor classicalBitModule)
            (DayTensor.rightUnitor
              (dayTensor classicalBitModule dayTensorUnit))) := by
    rw [hbody, FragmentContext.combinedPoint, combinedAllDiscard_bit_nil]
    exact Hom.comp_assoc g classicalBitWeakening
      (Hom.comp (DayTensor.rightUnitor classicalBitModule)
        (DayTensor.rightUnitor (dayTensor classicalBitModule dayTensorUnit)))
  rw [fragment_betaU_closed_post (Hom.comp g classicalBitWeakening) body f
    hpost, ← Hom.comp_assoc, hf, Hom.comp_id]

/-! ## General substitution lemmas on `FragCert.denote` -/

/-- **F4b (linear)**: substituting a closed first-order value into a body
whose denotation post-processes the bound variable by `k`.  `k = id` is the
identity body of `FragmentIdentityBeta`; every other `k` is a non-identity
body. -/
theorem fragment_substLin_closed_denote {A B : Ty} {M X : Term}
    (hAd : Ty.Admissible A) (hFO : Ty.FirstOrder A)
    (hB : Ty.SemanticFragment B)
    (cBody : FragCert [] [some A] M B) (cX : FragCert [] [] X A)
    (k : Hom (fragmentModule A) (fragmentModule B))
    (f : Hom dayTensorUnit (fragmentModule A))
    (hbody :
      FragCert.denote cBody =
        Hom.comp k
          (Hom.comp (DayTensor.leftUnitor (fragmentModule A))
            (DayTensor.map (Hom.id dayTensorUnit)
              (DayTensor.rightUnitor (fragmentModule A)))))
    (harg : FragCert.denote cX = FragmentContext.closedPoint f) :
    FragCert.denote
        (.appL CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil hFO hB
          (.lamL CtxUAllBit.nil CtxLAllSomeFragment.nil hAd hFO hB cBody)
          cX) =
      FragmentContext.closedPoint (Hom.comp k f) := by
  rw [fragment_subst_lin_spine CtxUAllBit.nil CtxLAllSomeFragment.nil
    OSplit.nil hAd hFO hB CtxLAllSomeFragment.nil cBody cX, harg, hbody]
  exact fragment_betaL_closed_post hFO k _ f rfl

/-- **F4b (unrestricted)**: substituting a closed bit value into a body whose
denotation post-processes the classical bound variable by `k`. -/
theorem fragment_substUnres_closed_denote {B : Ty} {M X : Term}
    (hB : Ty.SemanticFragment B)
    (hArr : Ty.SemanticFragment (.arrow .unres .bit B))
    (cBody : FragCert [.bit] [] M B) (cX : FragCert [] [] X .bit)
    (k : Hom classicalBitModule (fragmentModule B))
    (f : Hom dayTensorUnit (fragmentModule .bit))
    (hbody :
      FragCert.denote cBody =
        Hom.comp k
          (Hom.comp (DayTensor.rightUnitor classicalBitModule)
            (DayTensor.rightUnitor
              (dayTensor classicalBitModule dayTensorUnit))))
    (harg : FragCert.denote cX = FragmentContext.closedPoint f) :
    FragCert.denote
        (.appU CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil trivial hB
          (.lamU CtxUAllBit.nil CtxLAllSomeFragment.nil
            fragment_bit_admissible fragment_bit_duplicable trivial hArr
            cBody)
          cX) =
      FragmentContext.closedPoint
        (Hom.comp k (Hom.comp bitClassicalize f)) := by
  rw [fragment_subst_unres_bit_spine CtxUAllBit.nil CtxLAllSomeFragment.nil
    OSplit.nil fragment_bit_admissible fragment_bit_duplicable trivial hArr hB
    CtxLAllSomeFragment.nil trivial cBody cX, harg, hbody]
  exact fragment_betaU_closed_post k _ f rfl

/-- **F4b (constant body)**: substituting a closed bit value into a body that
does not mention the bound variable returns the body's point. -/
theorem fragment_substUnres_const_denote {B : Ty} {M X : Term}
    (hB : Ty.SemanticFragment B)
    (hArr : Ty.SemanticFragment (.arrow .unres .bit B))
    (cBody : FragCert [.bit] [] M B) (cX : FragCert [] [] X .bit)
    (g : Hom dayTensorUnit (fragmentModule B))
    (f : Hom dayTensorUnit (fragmentModule .bit))
    (hbody :
      FragCert.denote cBody =
        FragmentContext.combinedPoint fragment_ctxU_bit_nil
          (show AllNone ([] : List (Option Ty)) from trivial) g)
    (harg : FragCert.denote cX = FragmentContext.closedPoint f)
    (hf :
      Hom.comp classicalBitWeakening (Hom.comp bitClassicalize f) =
        Hom.id dayTensorUnit) :
    FragCert.denote
        (.appU CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil trivial hB
          (.lamU CtxUAllBit.nil CtxLAllSomeFragment.nil
            fragment_bit_admissible fragment_bit_duplicable trivial hArr
            cBody)
          cX) =
      FragmentContext.closedPoint g := by
  rw [fragment_subst_unres_bit_spine CtxUAllBit.nil CtxLAllSomeFragment.nil
    OSplit.nil fragment_bit_admissible fragment_bit_duplicable trivial hArr hB
    CtxLAllSomeFragment.nil trivial cBody cX, harg, hbody]
  exact fragment_betaU_const_closed g _ f rfl hf

/-! ## Certificates for constant unrestricted combinators -/

/-- Constant bit body `bitLit c` under an unrestricted bit binder. -/
noncomputable def fragCert_bitLit_ctxU_bit (c : Bool) :
    FragCert [.bit] [] (.bitLit c) .bit :=
  .bitLit fragment_ctxU_bit_nil CtxLAllSomeFragment.nil c trivial

/-- Closed constant combinator `λ!x. bitLit c`. -/
noncomputable def fragCert_lamU_const_bit (c : Bool) :
    FragCert [] [] (.lam .unres .bit (.bitLit c))
      (.arrow .unres .bit .bit) :=
  .lamU CtxUAllBit.nil CtxLAllSomeFragment.nil fragment_bit_admissible
    fragment_bit_duplicable trivial
    (.arrowUnresBit Ty.SemanticFragment.bit) (fragCert_bitLit_ctxU_bit c)

/-- Closed β-redex `app (λ!x. bitLit c) (bitLit b)`. -/
noncomputable def fragCert_appU_const_bit (c b : Bool) :
    FragCert [] []
      (.app (.lam .unres .bit (.bitLit c)) (.bitLit b)) .bit :=
  .appU CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil trivial
    Ty.SemanticFragment.bit (fragCert_lamU_const_bit c)
    (FragCert.closed_bitLit_cert b)

/-- Constant unit body under an unrestricted bit binder. -/
noncomputable def fragCert_unit_ctxU_bit :
    FragCert [.bit] [] .unit .unit :=
  .unit fragment_ctxU_bit_nil CtxLAllSomeFragment.nil trivial

/-- Closed constant combinator `λ!x. unit`. -/
noncomputable def fragCert_lamU_const_unit :
    FragCert [] [] (.lam .unres .bit .unit) (.arrow .unres .bit .unit) :=
  .lamU CtxUAllBit.nil CtxLAllSomeFragment.nil fragment_bit_admissible
    fragment_bit_duplicable trivial
    (.arrowUnresBit Ty.SemanticFragment.unit) fragCert_unit_ctxU_bit

/-- Closed β-redex `app (λ!x. unit) (bitLit b)`. -/
noncomputable def fragCert_appU_const_unit (b : Bool) :
    FragCert [] [] (.app (.lam .unres .bit .unit) (.bitLit b)) .unit :=
  .appU CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil trivial
    Ty.SemanticFragment.unit fragCert_lamU_const_unit
    (FragCert.closed_bitLit_cert b)

theorem fragCert_bitLit_ctxU_bit_denote (c : Bool) :
    FragCert.denote (fragCert_bitLit_ctxU_bit c) =
      FragmentContext.combinedPoint fragment_ctxU_bit_nil
        (show AllNone ([] : List (Option Ty)) from trivial) (bitLitHom c) :=
  rfl

theorem fragCert_unit_ctxU_bit_denote :
    FragCert.denote fragCert_unit_ctxU_bit =
      FragmentContext.combinedPoint fragment_ctxU_bit_nil
        (show AllNone ([] : List (Option Ty)) from trivial)
        routeAFragmentModel.unitIntro :=
  rfl

/-! ## F4b substitution equations with a non-identity body -/

/-- Term-level substitution into a constant body. -/
theorem substUnres_const_bitLit (c : Bool) (V : Term) :
    Term.substUnres 0 V (.bitLit c) = .bitLit c := by
  simp [Term.substUnres]

/-- Term-level substitution into the constant unit body. -/
theorem substUnres_const_unit (V : Term) :
    Term.substUnres 0 V .unit = .unit := by
  simp [Term.substUnres]

/-- **F4b (bit)**: substituting the closed value `bitLit b` into the
non-identity constant body `bitLit c` agrees with the contractum on
`FragCert.denote`. -/
theorem fragment_substUnres_const_denote_bit (c b : Bool) :
    FragCert.denote (fragCert_appU_const_bit c b) =
      FragCert.denote (FragCert.closed_bitLit_cert c) := by
  rw [FragCert.closed_bitLit_denote_eq c]
  exact fragment_substUnres_const_denote Ty.SemanticFragment.bit
    (.arrowUnresBit Ty.SemanticFragment.bit) (fragCert_bitLit_ctxU_bit c)
    (FragCert.closed_bitLit_cert b) (bitLitHom c) (bitLitHom b)
    (fragCert_bitLit_ctxU_bit_denote c)
    (FragCert.closed_bitLit_denote_eq b)
    (classicalBitWeakening_comp_bitClassicalize_bitLit b)

/-- **F4b (unit)**: substituting the closed value `bitLit b` into the
non-identity constant body `unit` agrees with the contractum. -/
theorem fragment_substUnres_const_denote_unit (b : Bool) :
    FragCert.denote (fragCert_appU_const_unit b) =
      FragCert.denote FragCert.closed_unit_cert := by
  rw [fragment_step_denote_sound_unit FragCert.closed_unit_cert]
  exact fragment_substUnres_const_denote Ty.SemanticFragment.unit
    (.arrowUnresBit Ty.SemanticFragment.unit) fragCert_unit_ctxU_bit
    (FragCert.closed_bitLit_cert b) routeAFragmentModel.unitIntro
    (bitLitHom b) fragCert_unit_ctxU_bit_denote
    (FragCert.closed_bitLit_denote_eq b)
    (classicalBitWeakening_comp_bitClassicalize_bitLit b)

end QLambda.Linear
