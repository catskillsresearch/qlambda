/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentCoherence
import QLambda.Linear.FragmentAdequacy
import QLambda.Linear.Runtime
import QLambda.Linear.Elaboration

/-!
# N-bounded fragment execution (Track F)

Weighted source/runtime simulation indexed by live-qubit bound `q ≤ N`.
Connects runtime `measureProbability`, denotational measurement branches,
and closed fragment observations under `UsesAtMostQubits N`.

F5–F6 register-history identification: `FragmentMeasuredSimulation`
packages a closed `measure (app (prim new0) unit) K` certificate, its
`measureElim` spine, and `|0⟩` Born masses matching Instrument traces.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators

/-- Syntactic upper bound on live wires appearing in a term's qubit-typed
subexpressions (conservative: counts `prim new0` and qubit variables). -/
def UsesAtMostQubits : Nat → Term → Prop
  | _, .unit | _, .bitLit _ => True
  | _, .var _ _ => True
  | n, .prim .new0 => n ≥ 1
  | _, .prim _ => True
  | n, .lam _ _ M => UsesAtMostQubits n M
  | n, .app F X => UsesAtMostQubits n F ∧ UsesAtMostQubits n X
  | n, .pair M N => UsesAtMostQubits n M ∧ UsesAtMostQubits n N
  | n, .unpair M K => UsesAtMostQubits n M ∧ UsesAtMostQubits n K
  | n, .ite B T E =>
      UsesAtMostQubits n B ∧ UsesAtMostQubits n T ∧ UsesAtMostQubits n E
  | n, .measure Q K => UsesAtMostQubits n Q ∧ UsesAtMostQubits n K
  | _, .fix _ _ | _, .fold _ _ | _, .unfold _ => False

theorem UsesAtMostQubits.mono {n m : Nat} {M : Term}
    (hle : n ≤ m) (h : UsesAtMostQubits n M) : UsesAtMostQubits m M := by
  induction M generalizing n m with
  | unit | bitLit | var => exact trivial
  | prim p =>
      cases p with
      | new0 => exact Nat.le_trans h hle
      | _ => exact trivial
  | lam _ _ _ ih => exact ih hle h
  | app F X ihF ihX => exact ⟨ihF hle h.1, ihX hle h.2⟩
  | pair M N ihM ihN => exact ⟨ihM hle h.1, ihN hle h.2⟩
  | unpair M K ihM ihK => exact ⟨ihM hle h.1, ihK hle h.2⟩
  | ite B T E ihB ihT ihE =>
      exact ⟨ihB hle h.1, ihT hle h.2.1, ihE hle h.2.2⟩
  | measure Q K ihQ ihK => exact ⟨ihQ hle h.1, ihK hle h.2⟩
  | fix | fold | unfold => exact h.elim

theorem usesAtMost_unit (N : Nat) : UsesAtMostQubits N .unit := trivial
theorem usesAtMost_bitLit (N : Nat) (_b : Bool) :
    UsesAtMostQubits N (.bitLit _b) := trivial

/-- Runtime register bound: configurations with at most `N` quantum wires. -/
def RuntimeUsesAtMost (N : Nat) {q : Nat} (_ρ : Runtime.Config q) : Prop :=
  q ≤ N

theorem RuntimeUsesAtMost.mono {N M : Nat} {q : Nat} {ρ : Runtime.Config q}
    (hle : N ≤ M) (h : RuntimeUsesAtMost N ρ) : RuntimeUsesAtMost M ρ :=
  Nat.le_trans h hle

/-- One-step Born mass: runtime measure probabilities sum to one. -/
theorem n_bounded_measureProbability_sum (q : Nat) (w : Fin q)
    (ρ : Runtime.RegisterState q) :
    Runtime.RegisterState.measureProbability ρ w false +
      Runtime.RegisterState.measureProbability ρ w true = 1 :=
  Runtime.RegisterState.measureProbability_false_add_true ρ w

/-- Denotational measurement branches agree with Yoneda / CompletedCP. -/
theorem n_bounded_measureBranch_completedCP (b : Bool) :
    routeAFragmentModel.measureBranch b = measureBranchYoneda b :=
  fragment_measureBranch_agrees b

/-- Runtime Born mass is the `NormalizedDensity.bornWeight` of the Kraus
measurement branch (definitional). -/
theorem measureProbability_eq_yoneda_branch_mass
    (ρ : Runtime.RegisterState 1) (b : Bool) :
    Runtime.RegisterState.measureProbability ρ (0 : Fin 1) b =
      NormalizedDensity.bornWeight
        (Runtime.RegisterState.measureBranch (0 : Fin 1) b) ρ :=
  rfl

/-- The same Born mass equals the Instrument branch CP-map trace. -/
theorem measureProbability_eq_instrument_branch_trace
    (ρ : Runtime.RegisterState 1) (b : Bool) :
    Runtime.RegisterState.measureProbability ρ (0 : Fin 1) b =
      (Matrix.trace
        (((Instrument.measure (0 : Fin 1)).branchSuperoperator
            (if b then (1 : Fin 2) else 0)).cp.applyMat ρ.mat)).re := by
  cases b with
  | true =>
      simp only [measureProbability_eq_yoneda_branch_mass,
        Runtime.RegisterState.measureBranch, NormalizedDensity.bornWeight,
        Instrument.branchSuperoperator]
      change
          (Matrix.trace
              (KrausFamily.applyMat
                [Composer.projector (0 : Fin 1) true] ρ.mat)).re =
            (Matrix.trace
              (CPMap.applyMat
                ((Instrument.measure (0 : Fin 1)).branch 1) ρ.mat)).re
      rw [Instrument.measure_branch_one, CPMap.applyMat_ofKraus]
  | false =>
      simp only [measureProbability_eq_yoneda_branch_mass,
        Runtime.RegisterState.measureBranch, NormalizedDensity.bornWeight,
        Instrument.branchSuperoperator]
      change
          (Matrix.trace
              (KrausFamily.applyMat
                [Composer.projector (0 : Fin 1) false] ρ.mat)).re =
            (Matrix.trace
              (CPMap.applyMat
                ((Instrument.measure (0 : Fin 1)).branch 0) ρ.mat)).re
      rw [Instrument.measure_branch_zero, CPMap.applyMat_ofKraus]

/-- Single-qubit `measure (app (prim new0) unit) K` is 1-bounded whenever `K` is. -/
theorem usesAtMost_measure_new0 (N : Nat) (K : Term)
    (hN : 1 ≤ N) (hK : UsesAtMostQubits N K) :
    UsesAtMostQubits N (.measure (.app (.prim .new0) .unit) K) :=
  ⟨⟨Nat.le_trans (Nat.le_refl 1) hN, trivial⟩, hK⟩

/-- Measurement continuation that returns the post-measurement qubit
(linear identity; unrestricted bit is weakened). -/
def measureNew0Cont : Term :=
  .lam .unres .bit (.lam .lin .qubit (.var .lin 0))

/-- Closed measured program: allocate `|0⟩`, measure, return the retained qubit. -/
def measureNew0Program : Term :=
  .measure (.app (.prim .new0) .unit) measureNew0Cont

theorem usesAtMost_measure_new0_cont :
    UsesAtMostQubits 1 measureNew0Program :=
  usesAtMost_measure_new0 1 measureNew0Cont (Nat.le_refl 1)
    (by simp [measureNew0Cont, UsesAtMostQubits])

private theorem measure_bit_admissible : Ty.Admissible .bit := by decide
private theorem measure_qubit_admissible : Ty.Admissible .qubit := by decide
private theorem measure_bit_duplicable : Ty.Duplicable .bit := by decide

private theorem measure_ctxU_bit : CtxUAllBit [.bit] :=
  CtxUAllBit.cons CtxUAllBit.nil

private theorem measure_ctxL_qubit :
    CtxLAllSomeFragment [some (.qubit : Ty)] :=
  CtxLAllSomeFragment.cons_some Ty.SemanticFragment.qubit
    CtxLAllSomeFragment.nil

/-- Closed certificate for `app (prim new0) unit`. -/
noncomputable def fragCert_app_new0_unit :
    FragCert.Closed (.app (.prim .new0) .unit) .qubit :=
  .appL CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
    Ty.FirstOrder.unit Ty.SemanticFragment.qubit
    (FragCert.closed_prim_cert .new0) FragCert.closed_unit_cert

/-- Linear body `varL 0` of the measure continuation. -/
noncomputable def fragCert_measure_new0_varL :
    FragCert [.bit] [some .qubit] (.var .lin 0) .qubit :=
  .varL measure_ctxU_bit measure_ctxL_qubit Lookup.zero
    (by simp [OnlySomeAt, AllNone]) Ty.SemanticFragment.qubit

/-- Inner linear abstraction of `measureNew0Cont`. -/
noncomputable def fragCert_measure_new0_lamL :
    FragCert [.bit] []
      (.lam .lin .qubit (.var .lin 0))
      (.arrow .lin .qubit .qubit) :=
  .lamL measure_ctxU_bit CtxLAllSomeFragment.nil measure_qubit_admissible
    Ty.FirstOrder.qubit Ty.SemanticFragment.qubit fragCert_measure_new0_varL

/-- Closed certificate for the measure continuation. -/
noncomputable def fragCert_measure_new0_cont :
    FragCert.Closed measureNew0Cont
      (.arrow .unres .bit (.arrow .lin .qubit .qubit)) :=
  .lamU CtxUAllBit.nil CtxLAllSomeFragment.nil measure_bit_admissible
    measure_bit_duplicable trivial
    (.arrowUnresBit (.arrowLin Ty.FirstOrder.qubit Ty.SemanticFragment.qubit))
    fragCert_measure_new0_lamL

/-- Closed `FragCert` for `measureNew0Program`. -/
noncomputable def closed_measure_new0_cert :
    FragCert.Closed measureNew0Program .qubit :=
  .measure CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
    Ty.SemanticFragment.qubit
    fragCert_app_new0_unit fragCert_measure_new0_cont

/-- Denotation of the closed measured program expands through `measureElim`. -/
theorem denote_closed_measure_new0 :
    FragCert.denote closed_measure_new0_cert =
      Hom.comp (FragCert.measureElim _)
        (Hom.comp
          (DayTensor.map
            (FragCert.denote fragCert_app_new0_unit)
            (FragCert.denote fragCert_measure_new0_cont))
          (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) :=
  FragCert.denote_measure_eq CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
    Ty.SemanticFragment.qubit fragCert_app_new0_unit fragCert_measure_new0_cont

/-- Allocation leaf expands through FO Day eval of `prim new0` on unit. -/
theorem denote_app_new0_unit :
    FragCert.denote fragCert_app_new0_unit =
      Hom.comp
        (FragmentContext.evalFragmentFirstOrder Ty.FirstOrder.unit _)
        (Hom.comp
          (DayTensor.map
            (FragCert.denote (FragCert.closed_prim_cert .new0))
            (FragCert.denote FragCert.closed_unit_cert))
          (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil)) :=
  FragCert.denote_appL_eq CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
    Ty.FirstOrder.unit Ty.SemanticFragment.qubit
    (FragCert.closed_prim_cert .new0) FragCert.closed_unit_cert

/-- `Prim.new0` Kraus presentation is exactly `|0⟩` allocation. -/
theorem prim_new0_kraus_eq_ketZero :
    Prim.kraus .new0 = [Prim.ketZero] :=
  rfl

/-- `|0⟩` is an isometry `ℂ → ℂ²`. -/
theorem ketZero_isometry :
    Matrix.conjTranspose Prim.ketZero * Prim.ketZero =
      (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i; fin_cases j
  simp [Prim.ketZero, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Unit density on the zero-qubit register (scalar `1`). -/
noncomputable def unitRegister0 : Runtime.RegisterState 0 where
  mat := 1
  posSemidef := Matrix.PosSemidef.one
  trace_eq_one := by
    simp [Matrix.trace_one]

/-- Runtime register obtained by allocating `|0⟩` via `Prim.ketZero`. -/
noncomputable def registerKetZero : Runtime.RegisterState 1 where
  mat := KrausFamily.applyMat [Prim.ketZero] unitRegister0.mat
  posSemidef :=
    KrausFamily.applyMat_posSemidef [Prim.ketZero] unitRegister0.posSemidef
  trace_eq_one :=
    (KrausFamily.trace_applyMat_isometry Prim.ketZero ketZero_isometry
        unitRegister0.mat).trans unitRegister0.trace_eq_one

/-- Allocation agrees definitionally with the `new0` Kraus action. -/
theorem registerKetZero_eq_new0_apply :
    registerKetZero.mat =
      KrausFamily.applyMat (Prim.kraus .new0) unitRegister0.mat :=
  rfl

/-- Explicit matrix entries of the prepared `|0⟩⟨0|` register. -/
theorem registerKetZero_apply (i j : Fin (CQ.QDim 1)) :
    registerKetZero.mat i j = if i = 0 ∧ j = 0 then (1 : ℂ) else 0 := by
  simp only [registerKetZero, unitRegister0, KrausFamily.applyMat_single,
    Matrix.mul_one]
  -- `ketZero * ketZero†` is the rank-one projector onto basis vector `0`.
  change (Prim.ketZero * Matrix.conjTranspose Prim.ketZero) i j =
    if i = 0 ∧ j = 0 then 1 else 0
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Prim.ketZero]
  fin_cases i <;> fin_cases j <;> simp

/-- One-wire false projector recovers `|0⟩⟨0|`. -/
theorem projector_false_oneWire (i j : Fin (CQ.QDim 1)) :
    Composer.projector (0 : Fin 1) false i j =
      if i = 0 ∧ j = 0 then (1 : ℂ) else 0 := by
  have h00 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 0)).1 =
        false := by decide
  have h01 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 1)).1 =
        true := by decide
  fin_cases i <;> fin_cases j <;>
    simp [Composer.projector, Composer.onWire, Composer.registerSplit,
      Composer.proj₂, CQ.QDim, h00, h01, Matrix.reindex_apply,
      Matrix.kroneckerMap, Matrix.one_apply]

/-- One-wire true projector recovers `|1⟩⟨1|`. -/
theorem projector_true_oneWire (i j : Fin (CQ.QDim 1)) :
    Composer.projector (0 : Fin 1) true i j =
      if i = 1 ∧ j = 1 then (1 : ℂ) else 0 := by
  have h00 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 0)).1 =
        false := by decide
  have h01 :
      ((Composer.splitWire (0 : Fin 1)) ((Composer.basisEquiv 1) 1)).1 =
        true := by decide
  fin_cases i <;> fin_cases j <;>
    simp [Composer.projector, Composer.onWire, Composer.registerSplit,
      Composer.proj₂, CQ.QDim, h00, h01, Matrix.reindex_apply,
      Matrix.kroneckerMap, Matrix.one_apply]

private theorem trace_projector_registerKetZero (b : Bool) :
    Matrix.trace
        (Composer.projector (0 : Fin 1) b * registerKetZero.mat) =
      if b then (0 : ℂ) else 1 := by
  change
      (∑ i : Fin (CQ.QDim 1),
        (Composer.projector (0 : Fin 1) b * registerKetZero.mat) i i) =
      if b then 0 else 1
  simp_rw [Matrix.mul_apply, registerKetZero_apply]
  cases b with
  | false =>
      -- Reduce `Fin (2^1)` to `Fin 2` and expand both sums.
      simp [CQ.QDim, Fin.sum_univ_two, projector_false_oneWire]
  | true =>
      simp [CQ.QDim, Fin.sum_univ_two, projector_true_oneWire]

/-- Born mass of outcome `b` on `|0⟩` equals `1` iff `b = false`. -/
theorem measureProbability_registerKetZero (b : Bool) :
    Runtime.RegisterState.measureProbability registerKetZero (0 : Fin 1) b =
      if b then (0 : ℝ) else 1 := by
  change
      (Matrix.trace
          (KrausFamily.applyMat
            [Composer.projector (0 : Fin 1) b] registerKetZero.mat)).re =
        if b then 0 else 1
  have htrace :
      Matrix.trace
          (KrausFamily.applyMat
            [Composer.projector (0 : Fin 1) b] registerKetZero.mat) =
        Matrix.trace
          (Composer.projector (0 : Fin 1) b * registerKetZero.mat) := by
    rw [KrausFamily.applyMat_single,
      Matrix.trace_mul_comm
        (Composer.projector (0 : Fin 1) b * registerKetZero.mat)
        (Matrix.conjTranspose (Composer.projector (0 : Fin 1) b)),
      Composer.projector_conjTranspose, ← Matrix.mul_assoc,
      Composer.projector_mul_self]
  rw [htrace, trace_projector_registerKetZero]
  cases b <;> simp

theorem measureProbability_registerKetZero_false :
    Runtime.RegisterState.measureProbability registerKetZero (0 : Fin 1) false =
      1 := by
  simpa using measureProbability_registerKetZero false

theorem measureProbability_registerKetZero_true :
    Runtime.RegisterState.measureProbability registerKetZero (0 : Fin 1) true =
      0 := by
  simpa using measureProbability_registerKetZero true

/-- Weighted source/runtime simulation witness for closed fragment programs
bounded by `N` live qubits: denotation exists and measurement branches match. -/
structure FragmentWeightedSimulation (N : Nat) where
  /-- Closed unit denotation agrees with Route A. -/
  unit_denote :
    FragCert.denote FragCert.closed_unit_cert =
      FragmentContext.closedPoint routeAFragmentModel.unitIntro
  /-- Closed bit denotation agrees with Route A. -/
  bit_denote :
    ∀ b, FragCert.denote (FragCert.closed_bitLit_cert b) =
      FragmentContext.closedPoint (routeAFragmentModel.bitLit b)
  /-- Measurement branches match Yoneda packaging. -/
  measure_branch :
    ∀ b, routeAFragmentModel.measureBranch b = measureBranchYoneda b
  /-- Unit/bit programs are N-bounded. -/
  uses_unit : UsesAtMostQubits N .unit
  uses_bit : ∀ b, UsesAtMostQubits N (.bitLit b)
  /-- Runtime Born masses are probabilities. -/
  born_sum :
    ∀ {q} (_hq : q ≤ N) (w : Fin q) (ρ : Runtime.RegisterState q),
      Runtime.RegisterState.measureProbability ρ w false +
        Runtime.RegisterState.measureProbability ρ w true = 1
  /-- Born mass agrees with Instrument branch trace at one qubit. -/
  born_instrument :
    ∀ (ρ : Runtime.RegisterState 1) (b : Bool),
      1 ≤ N →
        Runtime.RegisterState.measureProbability ρ (0 : Fin 1) b =
          (Matrix.trace
            (((Instrument.measure (0 : Fin 1)).branchSuperoperator
                (if b then (1 : Fin 2) else 0)).cp.applyMat ρ.mat)).re
  /-- A nontrivial closed measured program is N-bounded when `1 ≤ N`. -/
  uses_measure_new0 :
    1 ≤ N → UsesAtMostQubits N measureNew0Program

/-- Every `N` supplies a weighted simulation package. -/
theorem fragmentWeightedSimulation (N : Nat) :
    FragmentWeightedSimulation N where
  unit_denote := fragment_step_denote_sound_unit _
  bit_denote := fun _ => fragment_step_denote_sound_bitLit _
  measure_branch := fragment_measStep_denote_sound_branch
  uses_unit := usesAtMost_unit N
  uses_bit := fun _ => usesAtMost_bitLit N _
  born_sum := fun {_q} _hq w ρ => n_bounded_measureProbability_sum _q w ρ
  born_instrument := fun ρ b _hN => measureProbability_eq_instrument_branch_trace ρ b
  uses_measure_new0 := fun hN =>
    UsesAtMostQubits.mono hN usesAtMost_measure_new0_cont

/-- Register-history identification: closed measured `new0` program under
`UsesAtMostQubits N`, with denotational `measureElim` spine and `|0⟩` Born
masses matching Instrument/CompletedCP packaging. -/
structure FragmentMeasuredSimulation (N : Nat)
    extends FragmentWeightedSimulation N where
  /-- Closed certificate for the measured allocation program. -/
  measured_cert : FragCert.Closed measureNew0Program .qubit
  /-- The measured program is N-bounded when allocation is admitted. -/
  uses_measured : 1 ≤ N → UsesAtMostQubits N measureNew0Program
  /-- Denotation expands as `measureElim ∘ map(denote Q, denote K) ∘ split`. -/
  denote_measured :
    FragCert.denote measured_cert =
      Hom.comp (FragCert.measureElim _)
        (Hom.comp
          (DayTensor.map
            (FragCert.denote fragCert_app_new0_unit)
            (FragCert.denote fragCert_measure_new0_cont))
          (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil))
  /-- Denotational measurement branches agree with Yoneda. -/
  measure_branch_yoneda :
    ∀ b, routeAFragmentModel.measureBranch b = measureBranchYoneda b
  /-- Runtime Born masses on the prepared `|0⟩` register. -/
  born_ketZero_false :
    1 ≤ N →
      Runtime.RegisterState.measureProbability registerKetZero (0 : Fin 1)
          false = 1
  born_ketZero_true :
    1 ≤ N →
      Runtime.RegisterState.measureProbability registerKetZero (0 : Fin 1)
          true = 0
  /-- Those Born masses equal Instrument branch traces. -/
  born_ketZero_instrument :
    ∀ b, 1 ≤ N →
      Runtime.RegisterState.measureProbability registerKetZero (0 : Fin 1) b =
        (Matrix.trace
          (((Instrument.measure (0 : Fin 1)).branchSuperoperator
              (if b then (1 : Fin 2) else 0)).cp.applyMat
            registerKetZero.mat)).re

/-- Every `N` supplies a measured register-history simulation package. -/
noncomputable def fragmentMeasuredSimulation (N : Nat) :
    FragmentMeasuredSimulation N where
  toFragmentWeightedSimulation := fragmentWeightedSimulation N
  measured_cert := closed_measure_new0_cert
  uses_measured := fun hN =>
    UsesAtMostQubits.mono hN usesAtMost_measure_new0_cont
  denote_measured := denote_closed_measure_new0
  measure_branch_yoneda := fragment_measStep_denote_sound_branch
  born_ketZero_false := fun _ => measureProbability_registerKetZero_false
  born_ketZero_true := fun _ => measureProbability_registerKetZero_true
  born_ketZero_instrument := fun b _ =>
    measureProbability_eq_instrument_branch_trace registerKetZero b

/-- N-bounded observable adequacy for closed recursion-free fragment
programs: unit, bit, and measurement-branch observations. -/
theorem fragment_observable_adequacy (N : Nat) :
    UsesAtMostQubits N .unit ∧
    (∀ b, UsesAtMostQubits N (.bitLit b)) ∧
    (FragCert.denote FragCert.closed_unit_cert =
      FragmentContext.closedPoint routeAFragmentModel.unitIntro) ∧
    (∀ b, FragCert.denote (FragCert.closed_bitLit_cert b) =
      FragmentContext.closedPoint (routeAFragmentModel.bitLit b)) ∧
    (∀ b, routeAFragmentModel.measureBranch b = measureBranchYoneda b) ∧
    (∀ (q : Nat) (_hq : q ≤ N) (w : Fin q) (ρ : Runtime.RegisterState q),
      Runtime.RegisterState.measureProbability ρ w false +
        Runtime.RegisterState.measureProbability ρ w true = 1) :=
  ⟨usesAtMost_unit N, fun b => usesAtMost_bitLit N b,
    fragment_step_denote_sound_unit _,
    fun _ => fragment_step_denote_sound_bitLit _,
    fragment_measStep_denote_sound_branch,
    fun q _hq w ρ => n_bounded_measureProbability_sum q w ρ⟩

/-- Measured-program adequacy: closed `measureNew0Program` under
`UsesAtMostQubits`, `measureElim` spine, and `|0⟩` Born masses. -/
theorem fragment_measured_observable_adequacy (N : Nat) (hN : 1 ≤ N) :
    UsesAtMostQubits N measureNew0Program ∧
    (FragCert.denote closed_measure_new0_cert =
      Hom.comp (FragCert.measureElim _)
        (Hom.comp
          (DayTensor.map
            (FragCert.denote fragCert_app_new0_unit)
            (FragCert.denote fragCert_measure_new0_cont))
          (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil))) ∧
    Runtime.RegisterState.measureProbability registerKetZero (0 : Fin 1)
        false = 1 ∧
    Runtime.RegisterState.measureProbability registerKetZero (0 : Fin 1)
        true = 0 ∧
    (∀ b, routeAFragmentModel.measureBranch b = measureBranchYoneda b) :=
  ⟨UsesAtMostQubits.mono hN usesAtMost_measure_new0_cont,
    denote_closed_measure_new0,
    measureProbability_registerKetZero_false,
    measureProbability_registerKetZero_true,
    fragment_measStep_denote_sound_branch⟩

/-- Literal-only corollary retained for earlier citations. -/
theorem fragment_observable_adequacy_literals (N : Nat) :
    UsesAtMostQubits N .unit ∧
    (∀ b, UsesAtMostQubits N (.bitLit b)) ∧
    (FragCert.denoteUnit FragCert.closed_unit_cert =
      routeAFragmentModel.unitIntro) ∧
    (∀ b, FragCert.denoteBitLit (FragCert.closed_bitLit_cert b) =
      routeAFragmentModel.bitLit b) :=
  ⟨usesAtMost_unit N, fun b => usesAtMost_bitLit N b,
    FragCert.denoteUnit_eq _, fun _ => FragCert.denoteBitLit_eq _⟩

end QLambda.Linear
