/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda

@[expose] public section

/-! # Sorry-free solutions to the typed-linear Palomar challenge. -/

namespace QLambda.Palomar

open QLambda.Linear
open QLambda.Linear.Command.GeneralQuotation

theorem source_type_safety {M : Term} {A : Ty} (h : HasType [] [] M A) :
    MakesProgress M ∧
      (∀ N, Step M N → HasType [] [] N A) ∧
      (∀ b N, MeasStep M b N → HasType [] [] N A) ∧
      (∀ N₁ N₂, Step M N₁ → Step M N₂ → N₁ = N₂) :=
  ⟨progress h,
    fun _ hs => step_preservation hs h,
    fun _ _ hm => measStep_preservation hm h,
    fun _ _ h₁ h₂ => step_deterministic h₁ h₂⟩

theorem quotation_capstone
    (C : Command quantumSize classicalSize) (hC : Quotable C) :
    HasType [] [] (Quotation.reflect C hC).term quotationTy ∧
    (Quotation.reflect C hC).compile = C :=
  ⟨(Quotation.reflect C hC).typing, Quotation.compile_reflect C hC⟩

noncomputable def RuntimeRegister (q : Nat) : Type :=
  QLambda.Linear.Runtime.RegisterState q

noncomputable def runtimeMeasureProbability {q : Nat}
    (ρ : RuntimeRegister q) (w : Fin q) (b : Bool) : Real :=
  QLambda.Linear.Runtime.RegisterState.measureProbability ρ w b

noncomputable def RuntimeConfig (q : Nat) : Type :=
  QLambda.Linear.Runtime.Config q

def runtimeWellTyped {q : Nat} (s : RuntimeConfig q) (A : Ty) : Prop :=
  QLambda.Linear.Runtime.Config.WellTyped s A

def runtimeInternalStep {q : Nat} (s s' : RuntimeConfig q) : Prop :=
  QLambda.Linear.Runtime.InternalStep s s'

def runtimeMeasurementStep {q : Nat} (s : RuntimeConfig q) (weight : Real)
    (outcome : Bool) (s' : RuntimeConfig q) : Prop :=
  QLambda.Linear.Runtime.MeasurementStep s weight outcome s'

def runtimeNormal {q : Nat} (s : RuntimeConfig q) : Prop :=
  QLambda.Linear.Runtime.Config.Normal s

def runtimeOutOfWires {q : Nat} (s : RuntimeConfig q) : Prop :=
  QLambda.Linear.Runtime.Config.OutOfWires s

theorem runtime_born_normalizes {q : Nat} (ρ : RuntimeRegister q) (w : Fin q) :
    runtimeMeasureProbability ρ w false + runtimeMeasureProbability ρ w true = 1 := by
  unfold RuntimeRegister at ρ
  simpa [runtimeMeasureProbability] using
    QLambda.Linear.Runtime.RegisterState.measureProbability_false_add_true ρ w

theorem runtime_internal_preservation {q : Nat} {s s' : RuntimeConfig q} {A : Ty}
    (ht : runtimeWellTyped s A) (hs : runtimeInternalStep s s') :
    runtimeWellTyped s' A := by
  unfold RuntimeConfig runtimeWellTyped runtimeInternalStep at *
  exact QLambda.Linear.Runtime.internal_preservation ht hs

theorem runtime_measurement_preservation {q : Nat} {s s' : RuntimeConfig q}
    {weight : Real} {outcome : Bool} {A : Ty}
    (ht : runtimeWellTyped s A)
    (hs : runtimeMeasurementStep s weight outcome s') :
    runtimeWellTyped s' A := by
  unfold RuntimeConfig runtimeWellTyped runtimeMeasurementStep at *
  exact QLambda.Linear.Runtime.measurement_preservation ht hs

theorem runtime_progress {q : Nat} {s : RuntimeConfig q} {A : Ty}
    (ht : runtimeWellTyped s A) :
    runtimeNormal s ∨ runtimeOutOfWires s ∨
      (∃ s', runtimeInternalStep s s') ∨
      (∃ weight outcome s', runtimeMeasurementStep s weight outcome s') := by
  unfold RuntimeConfig runtimeWellTyped runtimeNormal runtimeOutOfWires
    runtimeInternalStep runtimeMeasurementStep at *
  simpa using QLambda.Linear.Runtime.progress ht

noncomputable def QuantumSet : Type 1 :=
  QLambda.Domain.QuantumSet

noncomputable def QuantumRel (X Y : QuantumSet) : Type :=
  QLambda.Domain.QuantumRel X Y

noncomputable def relComp {X Y Z : QuantumSet}
    (S : QuantumRel Y Z) (R : QuantumRel X Y) : QuantumRel X Z :=
  QLambda.Domain.QuantumRel.comp S R

noncomputable def relDagger {X Y : QuantumSet}
    (R : QuantumRel X Y) : QuantumRel Y X :=
  QLambda.Domain.QuantumRel.dagger R

noncomputable def relISup {X Y : QuantumSet}
    (S : Nat → QuantumRel X Y) : QuantumRel X Y :=
  @iSup
    (QLambda.Domain.QuantumRel (X : QLambda.Domain.QuantumSet) (Y : QLambda.Domain.QuantumSet))
    Nat
    (@QLambda.Domain.QuantumRel.instSupSetQuantumRel
      (X : QLambda.Domain.QuantumSet) (Y : QLambda.Domain.QuantumSet))
    S

def quantumDecEq (X : QuantumSet) : Type :=
  DecidableEq (X : QLambda.Domain.QuantumSet).Atom

noncomputable def relId (X : QuantumSet) (_h : quantumDecEq X) : QuantumRel X X :=
  let _ : DecidableEq (X : QLambda.Domain.QuantumSet).Atom := _h
  QLambda.Domain.QuantumRel.id (X : QLambda.Domain.QuantumSet)

noncomputable def QuantumPoset : Type 1 :=
  QLambda.Domain.QuantumPoset

noncomputable def qubitPoset : QuantumPoset :=
  QLambda.Domain.QuantumPoset.qubit

def isQuantumCPO (P : QuantumPoset) : Prop :=
  QLambda.Domain.IsQuantumCPO P

noncomputable def modelLinearObjects : Type 1 :=
  QLambda.Domain.quantumLNL.linear.Obj

noncomputable def qRelObjects : Type 1 :=
  QLambda.Domain.qRelCategory.Obj

noncomputable def qCPOCategoryObjects : Type 1 :=
  QLambda.Domain.qCPOCategory.Obj

noncomputable def quantumCPOCarrier : Type 1 :=
  QLambda.Domain.QuantumCPO

theorem quantumRel_assoc {X Y Z W : QuantumSet}
    (T : QuantumRel Z W) (S : QuantumRel Y Z) (R : QuantumRel X Y) :
    relComp (relComp T S) R = relComp T (relComp S R) :=
  QLambda.Domain.QuantumRel.assoc T S R

theorem quantumRel_dagger_comp {X Y Z : QuantumSet}
    (S : QuantumRel Y Z) (R : QuantumRel X Y) :
    relDagger (relComp S R) = relComp (relDagger R) (relDagger S) :=
  QLambda.Domain.QuantumRel.dagger_comp S R

theorem quantumRel_comp_iSup_left {X Y Z : QuantumSet}
    (S : Nat → QuantumRel Y Z) (R : QuantumRel X Y) :
    relComp (relISup S) R = relISup (fun n => relComp (S n) R) := by
  simpa [relComp, relISup, QuantumRel, QuantumSet] using
    QLambda.Domain.QuantumRel.comp_iSup_left S R

theorem quantumRel_comp_iSup_right {X Y Z : QuantumSet}
    (S : QuantumRel Y Z) (R : Nat → QuantumRel X Y) :
    relComp S (relISup R) = relISup (fun n => relComp S (R n)) := by
  simpa [relComp, relISup, QuantumRel, QuantumSet] using
    QLambda.Domain.QuantumRel.comp_iSup_right S R

theorem quantumRel_id_comp {X Y : QuantumSet} (hY : quantumDecEq Y)
    (R : QuantumRel X Y) :
    relComp (relId Y hY) R = R := by
  let _ : DecidableEq (Y : QLambda.Domain.QuantumSet).Atom := hY
  simpa [relComp, relId, QuantumRel, QuantumSet, quantumDecEq] using
    QLambda.Domain.QuantumRel.id_comp R

theorem quantumRel_comp_id {X Y : QuantumSet} (hX : quantumDecEq X)
    (R : QuantumRel X Y) :
    relComp R (relId X hX) = R := by
  let _ : DecidableEq (X : QLambda.Domain.QuantumSet).Atom := hX
  simpa [relComp, relId, QuantumRel, QuantumSet, quantumDecEq] using
    QLambda.Domain.QuantumRel.comp_id R

theorem qubit_isQuantumCPO : isQuantumCPO qubitPoset :=
  QLambda.Domain.qubit_isQuantumCPO

theorem set_qRel_linear_objects : modelLinearObjects = qRelObjects := rfl

theorem qCPO_category_objects : qCPOCategoryObjects = quantumCPOCarrier := rfl

noncomputable def ProjChain : Type 1 :=
  QLambda.Domain.ProjectionChain

noncomputable def ChainPoint (C : ProjChain) : Type :=
  C.Bilimit

noncomputable def TailPoint (C : ProjChain) : Type :=
  C.tail.Bilimit

noncomputable def shiftForward {C : ProjChain} (x : ChainPoint C) : TailPoint C :=
  C.shiftForward x

noncomputable def shiftBackward {C : ProjChain} (x : TailPoint C) : ChainPoint C :=
  C.shiftBackward x

def PrimCP (p : Prim) : Type :=
  QLambda.Domain.CompletedCP (QLambda.CQ.QDim p.inputQ) (QLambda.CQ.QDim p.outputQ)

noncomputable def primSuperoperator (p : Prim) : PrimCP p :=
  (QLambda.Linear.Prim.superoperator p).cp.toCompleted

noncomputable def primCompletedCP (p : Prim) : PrimCP p :=
  QLambda.Linear.Prim.completedCP p

theorem prim_cp_agreement (p : Prim) :
    primSuperoperator p = primCompletedCP p :=
  QLambda.Linear.Prim.superoperator_completedCP p

theorem cx_cp_agreement : primSuperoperator .cx = primCompletedCP .cx :=
  prim_cp_agreement .cx

def FragmentHom : Type :=
  QLambda.Domain.Presheaf.SuperoperatorModule.Hom
    (QLambda.Linear.FragmentContext.combined [] [])
    (QLambda.Linear.fragmentModule .qubit)

noncomputable def denoteClosedMeasureNew0 : FragmentHom :=
  QLambda.Linear.FragCert.denote QLambda.Linear.closed_measure_new0_cert

noncomputable def measureElimClosedNew0 : FragmentHom :=
  QLambda.Domain.Presheaf.SuperoperatorModule.Hom.comp
    (QLambda.Linear.FragCert.measureElim _)
    (QLambda.Domain.Presheaf.SuperoperatorModule.Hom.comp
      (QLambda.Domain.Presheaf.SuperoperatorModule.DayTensor.map
        (QLambda.Linear.FragCert.denote QLambda.Linear.fragCert_app_new0_unit)
        (QLambda.Linear.FragCert.denote QLambda.Linear.fragCert_measure_new0_cont))
      (QLambda.Linear.FragmentContext.combinedOSplit
        QLambda.Linear.CtxUAllBit.nil QLambda.Linear.OSplit.nil))

theorem shift_forward_backward {C : ProjChain} (x : TailPoint C) :
    shiftForward (shiftBackward x) = x :=
  QLambda.Domain.ProjectionChain.shiftForward_shiftBackward C x

theorem shift_backward_forward {C : ProjChain} (x : ChainPoint C) :
    shiftBackward (shiftForward x) = x :=
  QLambda.Domain.ProjectionChain.shiftBackward_shiftForward C x

theorem measure_elim_denotation :
    denoteClosedMeasureNew0 = measureElimClosedNew0 :=
  (QLambda.Linear.fragment_measured_observable_adequacy 1 (by decide)).2.1

def StagingResult (q c : Nat) (M : Term) : Type :=
  QLambda.Linear.Compilation q c M

def StagingSucceeds (fuel : Nat) {q c : Nat} {M : Term}
    (P : StagingResult q c M) : Prop :=
  QLambda.Linear.Elaborates fuel M P

def stagingWellFormed {q c : Nat} {M : Term}
    (P : StagingResult q c M) : Prop :=
  P.command.WellFormed

def CircuitModel (q c : Nat) : Type :=
  QLambda.Composer.Model q c

def CircuitSem (q c : Nat) : Type 1 :=
  QLambda.CQ.Sem q c

noncomputable def stagedDenotation {q c : Nat} {M : Term}
    (P : StagingResult q c M) (model : CircuitModel q c) : CircuitSem q c :=
  QLambda.Composer.denoteBlock model P.command.compile

noncomputable def compiledDenotation {q c : Nat} {M : Term}
    (P : StagingResult q c M) (model : CircuitModel q c) : CircuitSem q c :=
  P.command.denote model

def circuitAgrees {q c : Nat} (a b : CircuitSem q c) : Prop :=
  QLambda.CQ.Eq a b

theorem staging_deterministic {q c fuel : Nat} {M : Term}
    {P Q : StagingResult q c M}
    (hP : StagingSucceeds fuel P) (hQ : StagingSucceeds fuel Q) : P = Q :=
  QLambda.Linear.elaborates_deterministic hP hQ

theorem staging_well_formed {q c fuel : Nat} {M : Term}
    {P : StagingResult q c M} (h : StagingSucceeds fuel P) :
    stagingWellFormed P :=
  QLambda.Linear.elaborates_command_wellFormed h

theorem staging_compile_agreement {q c fuel : Nat} {M : Term}
    {P : StagingResult q c M} (h : StagingSucceeds fuel P)
    (model : CircuitModel q c) :
    circuitAgrees (stagedDenotation P model) (compiledDenotation P model) :=
  QLambda.Linear.elaborates_compile_agreement h model

def OpenQASMProgram (q c : Nat) : Type :=
  QLambda.Composer.Program QLambda.Composer.Version.openQASM3_0_ibmComposer_2026_09 q c

noncomputable def parseOpenQASM (q c : Nat) (text : String) : Option (OpenQASMProgram q c) :=
  QLambda.Composer.parseStructuredProgram q c text

noncomputable def renderOpenQASM {q c : Nat} (P : OpenQASMProgram q c) : String :=
  P.renderOpenQASM

def openQASMWellFormed {q c : Nat} (P : OpenQASMProgram q c) : Prop :=
  P.WellFormed

noncomputable def exportOpenQASM {q c : Nat} (P : OpenQASMProgram q c)
    (h : openQASMWellFormed P) : String :=
  P.toOpenQASM h

theorem openqasm_render_roundTrip {q c : Nat} {text : String}
    {P : OpenQASMProgram q c} (h : parseOpenQASM q c text = some P) :
    renderOpenQASM P = text :=
  QLambda.Composer.parseStructuredProgram_render_roundTrip h

theorem openqasm_export_roundTrip {q c : Nat} {text : String}
    {P : OpenQASMProgram q c} (hP : openQASMWellFormed P)
    (h : parseOpenQASM q c text = some P) :
    exportOpenQASM P hP = text :=
  QLambda.Composer.parseStructuredProgram_toOpenQASM_roundTrip hP h

noncomputable def ketZeroRegister : RuntimeRegister 1 :=
  QLambda.Linear.registerKetZero

def measuredNew0Within (N : Nat) : Prop :=
  QLambda.Linear.UsesAtMostQubits N QLambda.Linear.measureNew0Program

def MeasureBranchHom : Type :=
  QLambda.Domain.Presheaf.SuperoperatorModule.Hom
    (QLambda.Domain.Presheaf.SuperoperatorModule.representable 2)
    (QLambda.Domain.Presheaf.SuperoperatorModule.representable 2)

noncomputable def fragmentMeasureBranch (b : Bool) : MeasureBranchHom :=
  QLambda.Linear.routeAFragmentModel.measureBranch b

noncomputable def yonedaMeasureBranch (b : Bool) : MeasureBranchHom :=
  QLambda.Linear.measureBranchYoneda b

theorem measured_new0_born_false :
    runtimeMeasureProbability ketZeroRegister (0 : Fin 1) false = 1 :=
  QLambda.Linear.measureProbability_registerKetZero_false

theorem measured_new0_born_true :
    runtimeMeasureProbability ketZeroRegister (0 : Fin 1) true = 0 :=
  QLambda.Linear.measureProbability_registerKetZero_true

theorem measured_new0_within_bound (N : Nat) (hN : 1 ≤ N) :
    measuredNew0Within N :=
  (QLambda.Linear.fragment_measured_observable_adequacy N hN).1

theorem measure_branch_agrees (b : Bool) :
    fragmentMeasureBranch b = yonedaMeasureBranch b :=
  (QLambda.Linear.fragment_measured_observable_adequacy 1 (by omega)).2.2.2.2 b

end QLambda.Palomar
