/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumCPO
import QLambda.Domain.Enriched

/-!
# Scott-continuous quantum functions
-/

namespace QLambda.Domain

/-- A probe function from the atomic quantum set `H_d`. -/
abbrev ProbeFunction (P : QuantumPoset) (d : ℕ) :=
  QuantumFunction (QuantumPoset.discrete (.atomic d)) P

/-- Internal convergence of an increasing probe chain. -/
def ProbeTends (P : QuantumPoset) {d : ℕ}
    (K : ℕ → ProbeFunction P d) (Kinf : ProbeFunction P d) : Prop :=
  P.order.comp Kinf.rel = ⨅ n, P.order.comp (K n).rel

/-- Scott-continuous quantum function, Definition 3.2.4 of
*Categories of quantum cpos*. -/
structure ScottFunction (P Q : QuantumCPO) extends
    QuantumFunction P.poset Q.poset where
  continuous :
    ∀ (d : ℕ) (K : ℕ → ProbeFunction P.poset d)
      (Kinf : ProbeFunction P.poset d),
      Monotone K →
      ProbeTends P.poset K Kinf →
      ProbeTends Q.poset
        (fun n => QuantumFunction.comp toQuantumFunction (K n))
        (QuantumFunction.comp toQuantumFunction Kinf)

namespace ScottFunction

@[ext]
theorem ext {P Q : QuantumCPO} {F G : ScottFunction P Q}
    (h : F.toQuantumFunction = G.toQuantumFunction) : F = G := by
  cases F
  cases G
  congr

/-- Identity is Scott continuous. -/
def id (P : QuantumCPO) : ScottFunction P P where
  toQuantumFunction := QuantumFunction.idFun P.poset
  continuous := by
    intro d K Kinf hK hlim
    change
      P.poset.order.comp
          ((QuantumRel.id P.poset.carrier).comp Kinf.rel) =
        ⨅ n, P.poset.order.comp
          ((QuantumRel.id P.poset.carrier).comp (K n).rel)
    change
      P.poset.order.comp Kinf.rel =
        ⨅ n, P.poset.order.comp (K n).rel at hlim
    simpa only [QuantumRel.id_comp] using hlim

/-- Scott-continuous quantum functions compose. -/
def comp {P Q R : QuantumCPO}
    (G : ScottFunction Q R) (F : ScottFunction P Q) :
    ScottFunction P R where
  toQuantumFunction :=
    QuantumFunction.comp G.toQuantumFunction F.toQuantumFunction
  continuous := by
    intro d K Kinf hK hlim
    have hFK : Monotone
        (fun n => QuantumFunction.comp F.toQuantumFunction (K n)) := by
      intro n m hnm
      change
        (QuantumFunction.comp F.toQuantumFunction (K n)) ≤
          QuantumFunction.comp F.toQuantumFunction (K m)
      have hrel :
          (K m).rel ≤ P.poset.order.comp (K n).rel :=
        hK hnm
      calc
        (QuantumFunction.comp F.toQuantumFunction (K m)).rel
            = F.rel.comp (K m).rel := rfl
        _ ≤ F.rel.comp (P.poset.order.comp (K n).rel) :=
          QuantumRel.comp_mono_right hrel
        _ = (F.rel.comp P.poset.order).comp (K n).rel :=
          (QuantumRel.assoc _ _ _).symm
        _ ≤ (Q.poset.order.comp F.rel).comp (K n).rel :=
          QuantumRel.comp_mono_left _ F.monotone
        _ = Q.poset.order.comp
            (QuantumFunction.comp F.toQuantumFunction (K n)).rel :=
          QuantumRel.assoc _ _ _
    simpa only [QuantumFunction.comp, QuantumRel.assoc] using
      (G.continuous d
        (fun n => QuantumFunction.comp F.toQuantumFunction (K n))
        (QuantumFunction.comp F.toQuantumFunction Kinf)
        hFK (F.continuous d K Kinf hK hlim))

@[simp] theorem id_comp {P Q : QuantumCPO} (F : ScottFunction P Q) :
    comp (id Q) F = F := by
  apply ext
  apply QuantumFunction.ext
  exact QuantumRel.id_comp F.rel

@[simp] theorem comp_id {P Q : QuantumCPO} (F : ScottFunction P Q) :
    comp F (id P) = F := by
  apply ext
  apply QuantumFunction.ext
  exact QuantumRel.comp_id F.rel

theorem assoc {P Q R S : QuantumCPO}
    (H : ScottFunction R S) (G : ScottFunction Q R)
    (F : ScottFunction P Q) :
    comp (comp H G) F = comp H (comp G F) := by
  apply ext
  apply QuantumFunction.ext
  exact QuantumRel.assoc H.rel G.rel F.rel

section Limits

variable {P : QuantumPoset} {Q : QuantumCPO}

/-- Proposition 3.2.3 on one atomic summand of an arbitrary domain. -/
theorem restrictedChain_hasLimit
    (K : ℕ → QuantumFunction P Q.poset) (hK : Monotone K)
    (x : P.carrier.Atom) :
    ∃ Kinf : ProbeFunction Q.poset (P.carrier.dim x),
      ProbeTends Q.poset
        (fun n => QuantumFunction.restrictAtom (K n) x) Kinf := by
  have hinc :
      ∀ n,
        (QuantumFunction.restrictAtom (K (n + 1)) x).rel ≤
          Q.poset.order.comp
            (QuantumFunction.restrictAtom (K n) x).rel := by
    intro n
    have h :=
      QuantumFunction.restrictAtom_mono
        (hK (Nat.le_succ n)) x
    exact h
  obtain ⟨R, hRfun, hRlim⟩ :=
    Q.complete (P.carrier.dim x)
      (fun n => (QuantumFunction.restrictAtom (K n) x).rel)
      (fun n => (QuantumFunction.restrictAtom (K n) x).isFunction)
      hinc
  let Kinf : ProbeFunction Q.poset (P.carrier.dim x) :=
    { rel := R
      isFunction := hRfun
      monotone := by
        change R.comp
            (QuantumRel.id (.atomic (P.carrier.dim x))) ≤
          Q.poset.order.comp R
        rw [QuantumRel.comp_id]
        calc
          R = (QuantumRel.id Q.poset.carrier).comp R :=
            (QuantumRel.id_comp _).symm
          _ ≤ Q.poset.order.comp R :=
            QuantumRel.comp_mono_left _ Q.poset.reflexive }
  exact ⟨Kinf, hRlim⟩

/-- The atomic limit selected from qCPO completeness. -/
noncomputable def atomLimit
    (K : ℕ → QuantumFunction P Q.poset) (hK : Monotone K)
    (x : P.carrier.Atom) :
    ProbeFunction Q.poset (P.carrier.dim x) :=
  Classical.choose (restrictedChain_hasLimit K hK x)

theorem atomLimit_tends
    (K : ℕ → QuantumFunction P Q.poset) (hK : Monotone K)
    (x : P.carrier.Atom) :
    ProbeTends Q.poset
      (fun n => QuantumFunction.restrictAtom (K n) x)
      (atomLimit K hK x) :=
  Classical.choose_spec (restrictedChain_hasLimit K hK x)

/-- Reassembly of the atomic limits from Proposition 3.2.3. -/
noncomputable def limitRel
    (K : ℕ → QuantumFunction P Q.poset) (hK : Monotone K) :
    QuantumRel P.carrier Q.poset.carrier :=
  QuantumRel.assembleAtoms (fun x => (atomLimit K hK x).rel)

theorem limitRel_isFunction
    (K : ℕ → QuantumFunction P Q.poset) (hK : Monotone K) :
    (limitRel K hK).IsFunction :=
  QuantumRel.assembleAtoms_isFunction
    (fun x => (atomLimit K hK x).rel)
    (fun x => (atomLimit K hK x).isFunction)

/-- The reassembled relation is the internal pointwise limit on the
whole, possibly non-atomic, quantum-set domain. -/
theorem limitRel_tends
    (K : ℕ → QuantumFunction P Q.poset) (hK : Monotone K) :
    Q.poset.order.comp (limitRel K hK) =
      ⨅ n, Q.poset.order.comp (K n).rel := by
  apply QuantumRel.ext
  intro x y
  have hx := atomLimit_tends K hK x
  have hre :
      QuantumRel.restrictAtom
          (Q.poset.order.comp (limitRel K hK)) x =
        QuantumRel.restrictAtom
          (⨅ n, Q.poset.order.comp (K n).rel) x := by
    rw [QuantumRel.restrictAtom_comp]
    change
      Q.poset.order.comp (atomLimit K hK x).rel =
        QuantumRel.restrictAtom
          (⨅ n, Q.poset.order.comp (K n).rel) x
    rw [QuantumRel.restrictAtom_iInf]
    simp only [QuantumRel.restrictAtom_comp]
    exact hx
  exact congrArg
    (fun R => R.component
      (default : (QuantumSet.atomic (P.carrier.dim x)).Atom) y) hre

/-- Proposition 3.3.1: an internal limit of monotone maps remains monotone. -/
theorem limitRel_monotone
    (K : ℕ → QuantumFunction P Q.poset) (hK : Monotone K) :
    (limitRel K hK).comp P.order ≤
      Q.poset.order.comp (limitRel K hK) := by
  have hlim := limitRel_tends K hK
  calc
    (limitRel K hK).comp P.order ≤
        Q.poset.order.comp ((limitRel K hK).comp P.order) := by
      calc
        (limitRel K hK).comp P.order =
            (QuantumRel.id Q.poset.carrier).comp
              ((limitRel K hK).comp P.order) :=
          (QuantumRel.id_comp _).symm
        _ ≤ Q.poset.order.comp ((limitRel K hK).comp P.order) :=
          QuantumRel.comp_mono_left _ Q.poset.reflexive
    _ = (Q.poset.order.comp (limitRel K hK)).comp P.order :=
      (QuantumRel.assoc _ _ _).symm
    _ = (⨅ n, Q.poset.order.comp (K n).rel).comp P.order :=
      congrArg (fun R => R.comp P.order) hlim
    _ ≤ ⨅ n, (Q.poset.order.comp (K n).rel).comp P.order := by
      apply le_iInf
      intro n
      exact QuantumRel.comp_mono_left P.order
        (iInf_le (fun n => Q.poset.order.comp (K n).rel) n)
    _ ≤ ⨅ n, Q.poset.order.comp (K n).rel := by
      apply le_iInf
      intro n
      refine (iInf_le
        (fun n => (Q.poset.order.comp (K n).rel).comp P.order) n).trans ?_
      calc
        (Q.poset.order.comp (K n).rel).comp P.order =
            Q.poset.order.comp ((K n).rel.comp P.order) :=
          QuantumRel.assoc _ _ _
        _ ≤ Q.poset.order.comp
              (Q.poset.order.comp (K n).rel) :=
          QuantumRel.comp_mono_right (K n).monotone
        _ = (Q.poset.order.comp Q.poset.order).comp (K n).rel :=
          (QuantumRel.assoc _ _ _).symm
        _ = Q.poset.order.comp (K n).rel := by
          rw [QuantumPoset.order_comp_self]
    _ = Q.poset.order.comp (limitRel K hK) := hlim.symm

/-- The arbitrary-domain limit as a monotone quantum function. -/
noncomputable def functionLimit
    (K : ℕ → QuantumFunction P Q.poset) (hK : Monotone K) :
    QuantumFunction P Q.poset where
  rel := limitRel K hK
  isFunction := limitRel_isFunction K hK
  monotone := limitRel_monotone K hK

theorem functionLimit_tends
    (K : ℕ → QuantumFunction P Q.poset) (hK : Monotone K) :
    Q.poset.order.comp (functionLimit K hK).rel =
      ⨅ n, Q.poset.order.comp (K n).rel :=
  limitRel_tends K hK

/-- Lemma 3.1.2: an internal limit is exactly the external hom supremum. -/
theorem tends_isLUB
    (K : ℕ → QuantumFunction P Q.poset)
    (Kinf : QuantumFunction P Q.poset)
    (hlim :
      Q.poset.order.comp Kinf.rel =
        ⨅ n, Q.poset.order.comp (K n).rel) :
    IsLUB (Set.range K) Kinf := by
  constructor
  · rintro F ⟨n, rfl⟩
    change Kinf.rel ≤ Q.poset.order.comp (K n).rel
    calc
      Kinf.rel =
          (QuantumRel.id Q.poset.carrier).comp Kinf.rel :=
        (QuantumRel.id_comp _).symm
      _ ≤ Q.poset.order.comp Kinf.rel :=
        QuantumRel.comp_mono_left _ Q.poset.reflexive
      _ = ⨅ m, Q.poset.order.comp (K m).rel := hlim
      _ ≤ Q.poset.order.comp (K n).rel :=
        iInf_le _ n
  · intro G hG
    change G.rel ≤ Q.poset.order.comp Kinf.rel
    rw [hlim]
    apply le_iInf
    intro n
    exact hG ⟨n, rfl⟩

theorem functionLimit_isLUB
    (K : ℕ → QuantumFunction P Q.poset) (hK : Monotone K) :
    IsLUB (Set.range K) (functionLimit K hK) :=
  tends_isLUB K (functionLimit K hK) (functionLimit_tends K hK)

end Limits

end ScottFunction

end QLambda.Domain
