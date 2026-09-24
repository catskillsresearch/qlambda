/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.ScottFunction
import QLambda.Domain.instCoeScottFunction
import QLambda.Domain.instLEScottFunction
import QLambda.Domain.instPartialOrderScottFunction
import QLambda.Domain.instOmegaComplete

/-!
# Instances from `ScottFunction`
-/

namespace QLambda.Domain
namespace ScottFunction


/-- Composition is monotone in its left argument. -/
theorem comp_mono_left {P Q R : QuantumCPO}
    (F : ScottFunction P Q) :
    Monotone (fun G : ScottFunction Q R => comp G F) := by
  intro G H hGH
  change H.rel.comp F.rel ≤
    R.poset.order.comp (G.rel.comp F.rel)
  calc
    H.rel.comp F.rel ≤
        (R.poset.order.comp G.rel).comp F.rel :=
      QuantumRel.comp_mono_left F.rel hGH
    _ = R.poset.order.comp (G.rel.comp F.rel) :=
      QuantumRel.assoc _ _ _

/-- Composition is monotone in its right argument. -/
theorem comp_mono_right {P Q R : QuantumCPO}
    (G : ScottFunction Q R) :
    Monotone (fun F : ScottFunction P Q => comp G F) := by
  intro F H hFH
  change G.rel.comp H.rel ≤
    R.poset.order.comp (G.rel.comp F.rel)
  calc
    G.rel.comp H.rel ≤
        G.rel.comp (Q.poset.order.comp F.rel) :=
      QuantumRel.comp_mono_right hFH
    _ = (G.rel.comp Q.poset.order).comp F.rel :=
      (QuantumRel.assoc _ _ _).symm
    _ ≤ (R.poset.order.comp G.rel).comp F.rel :=
      QuantumRel.comp_mono_left F.rel G.monotone
    _ = R.poset.order.comp (G.rel.comp F.rel) :=
      QuantumRel.assoc _ _ _

theorem restrict_tends {P : QuantumPoset} {Q : QuantumCPO}
    (K : ℕ → QuantumFunction P Q.poset) (Kinf : QuantumFunction P Q.poset)
    (hlim :
      Q.poset.order.comp Kinf.rel =
        ⨅ n, Q.poset.order.comp (K n).rel)
    (x : P.carrier.Atom) :
    ProbeTends Q.poset
      (fun n => QuantumFunction.restrictAtom (K n) x)
      (QuantumFunction.restrictAtom Kinf x) := by
  change
    Q.poset.order.comp (QuantumRel.restrictAtom Kinf.rel x) =
      ⨅ n, Q.poset.order.comp
        (QuantumRel.restrictAtom (K n).rel x)
  rw [← QuantumRel.restrictAtom_comp, hlim,
    QuantumRel.restrictAtom_iInf]
  simp only [QuantumRel.restrictAtom_comp]

/-- Lemma 3.3.3: postcomposition of an internal limit by a fixed
function preserves the limit. -/
theorem comp_tends_right {P Q : QuantumPoset} {R : QuantumCPO}
    (K : ℕ → QuantumFunction Q R.poset)
    (Kinf : QuantumFunction Q R.poset)
    (hlim :
      R.poset.order.comp Kinf.rel =
        ⨅ n, R.poset.order.comp (K n).rel)
    (F : QuantumFunction P Q) :
    R.poset.order.comp (Kinf.rel.comp F.rel) =
      ⨅ n, R.poset.order.comp ((K n).rel.comp F.rel) := by
  calc
    R.poset.order.comp (Kinf.rel.comp F.rel) =
        (R.poset.order.comp Kinf.rel).comp F.rel :=
      (QuantumRel.assoc _ _ _).symm
    _ = (⨅ n, R.poset.order.comp (K n).rel).comp F.rel :=
      congrArg (fun S => S.comp F.rel) hlim
    _ = ⨅ n, (R.poset.order.comp (K n).rel).comp F.rel :=
      QuantumRel.iInf_comp_of_function
        (fun n => R.poset.order.comp (K n).rel)
        F.rel F.isFunction
    _ = ⨅ n, R.poset.order.comp ((K n).rel.comp F.rel) := by
      simp only [QuantumRel.assoc]

/-- Lemma 3.3.4: precomposition of an arbitrary-domain internal limit
by a Scott function preserves the limit. -/
theorem comp_tends_left {P : QuantumPoset} {Q R : QuantumCPO}
    (G : ScottFunction Q R)
    (K : ℕ → QuantumFunction P Q.poset) (hK : Monotone K)
    (Kinf : QuantumFunction P Q.poset)
    (hlim :
      Q.poset.order.comp Kinf.rel =
        ⨅ n, Q.poset.order.comp (K n).rel) :
    R.poset.order.comp (G.rel.comp Kinf.rel) =
      ⨅ n, R.poset.order.comp (G.rel.comp (K n).rel) := by
  apply QuantumRel.ext
  intro x z
  have hKr :
      Monotone (fun n => QuantumFunction.restrictAtom (K n) x) := by
    intro n m hnm
    exact QuantumFunction.restrictAtom_mono (hK hnm) x
  have hx := G.continuous (P.carrier.dim x)
    (fun n => QuantumFunction.restrictAtom (K n) x)
    (QuantumFunction.restrictAtom Kinf x)
    hKr (restrict_tends K Kinf hlim x)
  have hre :
      QuantumRel.restrictAtom
          (R.poset.order.comp (G.rel.comp Kinf.rel)) x =
        QuantumRel.restrictAtom
          (⨅ n, R.poset.order.comp (G.rel.comp (K n).rel)) x := by
    rw [QuantumRel.restrictAtom_iInf]
    simp only [QuantumRel.restrictAtom_comp]
    exact hx
  exact congrArg
    (fun S => S.component
      (default : (QuantumSet.atomic (P.carrier.dim x)).Atom) z) hre

/-- Every function whose domain has the discrete order is Scott continuous:
probe chains into the domain are constant. -/
def ofDiscreteDomain {X : QuantumSet} [DecidableEq X.Atom]
    {Q : QuantumCPO}
    (F : QuantumFunction (QuantumPoset.discrete X) Q.poset) :
    ScottFunction (QuantumCPO.discrete X) Q where
  toQuantumFunction := F
  continuous := by
    intro d K Kinf hK hlim
    have hconst : ∀ n, K n = K 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          have hle : (K (n + 1)).rel ≤ (K n).rel := by
            have h := hK (Nat.le_succ n)
            change (K (n + 1)).rel ≤
              (QuantumPoset.discrete X).order.comp (K n).rel at h
            change (K (n + 1)).rel ≤
              (QuantumRel.id
                (QuantumCPO.discrete X).poset.carrier).comp (K n).rel at h
            rw [QuantumRel.id_comp] at h
            exact h
          exact
            (QuantumFunction.ext
              (QuantumRel.function_eq_of_le
                (K (n + 1)).isFunction (K n).isFunction hle)).trans ih
    have hKinf : Kinf = K 0 := by
      apply QuantumFunction.ext
      have hlim' := hlim
      change
        (QuantumRel.id
            (QuantumCPO.discrete X).poset.carrier).comp Kinf.rel =
          ⨅ n, (QuantumRel.id
            (QuantumCPO.discrete X).poset.carrier).comp (K n).rel at hlim'
      rw [QuantumRel.id_comp] at hlim'
      simp only [hconst, iInf_const] at hlim'
      rw [QuantumRel.id_comp] at hlim'
      exact hlim'
    subst Kinf
    simp only [ProbeTends, hconst, iInf_const]

/-- The chosen hom supremum is characterized by internal convergence. -/
theorem ωSup_tends {P Q : QuantumCPO}
    (K : ℕ → ScottFunction P Q) (hK : Monotone K) :
    Q.poset.order.comp (OmegaComplete.ωSup K hK).rel =
      ⨅ n, Q.poset.order.comp (K n).rel :=
  scottLimit_tends K hK

theorem tends_isLUB_scott {P Q : QuantumCPO}
    (K : ℕ → ScottFunction P Q) (Kinf : ScottFunction P Q)
    (hlim :
      Q.poset.order.comp Kinf.rel =
        ⨅ n, Q.poset.order.comp (K n).rel) :
    IsLUB (Set.range K) Kinf := by
  have hq := tends_isLUB
    (fun n => (K n).toQuantumFunction)
    Kinf.toQuantumFunction hlim
  constructor
  · rintro F ⟨n, rfl⟩
    exact hq.1 ⟨n, rfl⟩
  · intro F hF
    apply hq.2
    rintro _ ⟨n, rfl⟩
    exact hF ⟨n, rfl⟩

/-- Composition preserves hom suprema in its left argument. -/
theorem comp_ωSup_left {P Q R : QuantumCPO}
    (K : ℕ → ScottFunction Q R) (hK : Monotone K)
    (F : ScottFunction P Q) :
    comp (OmegaComplete.ωSup K hK) F =
      OmegaComplete.ωSup (fun n => comp (K n) F)
        ((comp_mono_left F).comp hK) := by
  let c : ℕ → ScottFunction P R := fun n => comp (K n) F
  have hc : Monotone c := (comp_mono_left F).comp hK
  have hlim :
      R.poset.order.comp
          ((comp (OmegaComplete.ωSup K hK) F).rel) =
        ⨅ n, R.poset.order.comp (c n).rel :=
    comp_tends_right
      (fun n => (K n).toQuantumFunction)
      (OmegaComplete.ωSup K hK).toQuantumFunction
      (ωSup_tends K hK) F.toQuantumFunction
  have hlub :
      IsLUB (Set.range c) (comp (OmegaComplete.ωSup K hK) F) :=
    tends_isLUB_scott c (comp (OmegaComplete.ωSup K hK) F) hlim
  exact (OmegaComplete.ωSup_unique c hc
    (fun n => hlub.1 ⟨n, rfl⟩)
    (fun G hG => hlub.2 (by
      rintro _ ⟨n, rfl⟩
      exact hG n))).symm

/-- Composition preserves hom suprema in its right argument. -/
theorem comp_ωSup_right {P Q R : QuantumCPO}
    (G : ScottFunction Q R)
    (K : ℕ → ScottFunction P Q) (hK : Monotone K) :
    comp G (OmegaComplete.ωSup K hK) =
      OmegaComplete.ωSup (fun n => comp G (K n))
        ((comp_mono_right G).comp hK) := by
  let c : ℕ → ScottFunction P R := fun n => comp G (K n)
  have hc : Monotone c := (comp_mono_right G).comp hK
  have hlim :
      R.poset.order.comp
          ((comp G (OmegaComplete.ωSup K hK)).rel) =
        ⨅ n, R.poset.order.comp (c n).rel :=
    comp_tends_left G
      (fun n => (K n).toQuantumFunction) hK
      (OmegaComplete.ωSup K hK).toQuantumFunction
      (ωSup_tends K hK)
  have hlub :
      IsLUB (Set.range c) (comp G (OmegaComplete.ωSup K hK)) :=
    tends_isLUB_scott c (comp G (OmegaComplete.ωSup K hK)) hlim
  exact (OmegaComplete.ωSup_unique c hc
    (fun n => hlub.1 ⟨n, rfl⟩)
    (fun F hF => hlub.2 (by
      rintro _ ⟨n, rfl⟩
      exact hF n))).symm


end ScottFunction

end QLambda.Domain
