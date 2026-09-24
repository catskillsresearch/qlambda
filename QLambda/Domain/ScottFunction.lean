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

instance instCoeScottFunction {P Q : QuantumCPO} : Coe (ScottFunction P Q)
    (QuantumFunction P.poset Q.poset) :=
  ⟨ScottFunction.toQuantumFunction⟩

instance instLEScottFunction {P Q : QuantumCPO} : LE (ScottFunction P Q) where
  le F G := F.toQuantumFunction ≤ G.toQuantumFunction

@[ext]
theorem ext {P Q : QuantumCPO} {F G : ScottFunction P Q}
    (h : F.toQuantumFunction = G.toQuantumFunction) : F = G := by
  cases F
  cases G
  congr

instance instPartialOrderScottFunction {P Q : QuantumCPO} : PartialOrder (ScottFunction P Q) where
  le_refl F := by
    change F.toQuantumFunction ≤ F.toQuantumFunction
    exact le_rfl
  le_trans F G H hFG hGH := by
    change F.toQuantumFunction ≤ H.toQuantumFunction
    change F.toQuantumFunction ≤ G.toQuantumFunction at hFG
    change G.toQuantumFunction ≤ H.toQuantumFunction at hGH
    exact hFG.trans hGH
  le_antisymm F G hFG hGF :=
    ext (le_antisymm hFG hGF)

/-- Identity is Scott continuous. -/
def id (P : QuantumCPO) : ScottFunction P P where
  toQuantumFunction := idFun P.poset
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

section ScottLimits

variable {P Q R : QuantumCPO}

/-- Proposition 3.3.1: the limit of a chain of Scott-continuous functions
is Scott continuous. -/
noncomputable def scottLimit
    (K : ℕ → ScottFunction P Q) (hK : Monotone K) :
    ScottFunction P Q where
  toQuantumFunction :=
    functionLimit (fun n => (K n).toQuantumFunction) (by
      intro n m hnm
      exact hK hnm)
  continuous := by
    intro d L Linf hL hLinf
    let c : ℕ → QuantumFunction P.poset Q.poset :=
      fun n => (K n).toQuantumFunction
    have hc : Monotone c := by
      intro n m hnm
      exact hK hnm
    have hhom :
        Q.poset.order.comp (functionLimit c hc).rel =
          ⨅ n, Q.poset.order.comp (c n).rel :=
      functionLimit_tends c hc
    have hcont :
        ∀ n,
          (Q.poset.order.comp (c n).rel).comp Linf.rel =
            ⨅ m, (Q.poset.order.comp (c n).rel).comp (L m).rel := by
      intro n
      have hn := (K n).continuous d L Linf hL hLinf
      change
        Q.poset.order.comp ((c n).rel.comp Linf.rel) =
          ⨅ m, Q.poset.order.comp ((c n).rel.comp (L m).rel) at hn
      simpa only [QuantumRel.assoc] using hn
    change
      Q.poset.order.comp ((functionLimit c hc).rel.comp Linf.rel) =
        ⨅ m, Q.poset.order.comp
          ((functionLimit c hc).rel.comp (L m).rel)
    calc
      Q.poset.order.comp ((functionLimit c hc).rel.comp Linf.rel) =
          (Q.poset.order.comp (functionLimit c hc).rel).comp Linf.rel :=
        (QuantumRel.assoc _ _ _).symm
      _ = (⨅ n, Q.poset.order.comp (c n).rel).comp Linf.rel :=
        congrArg (fun S => S.comp Linf.rel) hhom
      _ = ⨅ n, (Q.poset.order.comp (c n).rel).comp Linf.rel :=
        QuantumRel.iInf_comp_of_function
          (fun n => Q.poset.order.comp (c n).rel)
          Linf.rel Linf.isFunction
      _ = ⨅ n, ⨅ m,
          (Q.poset.order.comp (c n).rel).comp (L m).rel := by
        congr 1
        funext n
        exact hcont n
      _ = ⨅ m, ⨅ n,
          (Q.poset.order.comp (c n).rel).comp (L m).rel :=
        iInf_comm
      _ = ⨅ m, (⨅ n, Q.poset.order.comp (c n).rel).comp (L m).rel := by
        congr 1
        funext m
        exact (QuantumRel.iInf_comp_of_function
          (fun n => Q.poset.order.comp (c n).rel)
          (L m).rel (L m).isFunction).symm
      _ = ⨅ m,
          (Q.poset.order.comp (functionLimit c hc).rel).comp (L m).rel := by
        rw [hhom]
      _ = ⨅ m, Q.poset.order.comp
          ((functionLimit c hc).rel.comp (L m).rel) := by
        simp only [QuantumRel.assoc]

theorem scottLimit_tends
    (K : ℕ → ScottFunction P Q) (hK : Monotone K) :
    Q.poset.order.comp (scottLimit K hK).rel =
      ⨅ n, Q.poset.order.comp (K n).rel :=
  functionLimit_tends (fun n => (K n).toQuantumFunction) hK

theorem scottLimit_isLUB
    (K : ℕ → ScottFunction P Q) (hK : Monotone K) :
    IsLUB (Set.range K) (scottLimit K hK) := by
  have hq := functionLimit_isLUB
    (fun n => (K n).toQuantumFunction) hK
  constructor
  · rintro F ⟨n, rfl⟩
    exact hq.1 ⟨n, rfl⟩
  · intro F hF
    apply hq.2
    rintro _ ⟨n, rfl⟩
    exact hF ⟨n, rfl⟩

/-- Corollary 3.3.2: Scott-function homs are ω-complete. -/
noncomputable instance instOmegaComplete
    (P Q : QuantumCPO) : OmegaComplete (ScottFunction P Q) where
  ωSup := scottLimit
  le_ωSup K hK n := (scottLimit_isLUB K hK).1 ⟨n, rfl⟩
  ωSup_le K hK F hF := (scottLimit_isLUB K hK).2 (by
    rintro _ ⟨n, rfl⟩
    exact hF n)

end ScottLimits

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
