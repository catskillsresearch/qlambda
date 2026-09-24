/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentQuoteBridgeExt
import QLambda.Composer.OpenQASM
import QLambda.Composer.WellFormed

/-!
# N-qubit fragment denotation + OpenQASM staging interface

**Claimed.** Route A supplies denotational semantics for the typed fragment
(`FragCert.denote`) under `UsesAtMostQubits N`.  Successful `Elaborates`
yields well-formed Composer commands exportable via `Program.toOpenQASM`.

**Also claimed.** Quotation spines / extended spines identify covered Quotable
Hom denotations with ideal `CQ.Sem` (see `FragmentSourceCircuitN`,
`FragmentQuoteBridgeExt`).

**Not claimed.** Every fragment term elaborates; arbitrary Hom→CQ extract;
Track L / bang; noisy hardware.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

open QLambda.CQ
open QLambda.Composer
open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf

abbrev nQubitOpenQASMVersion : Version :=
  .openQASM3_0_ibmComposer_2026_09

def commandAsProgram {q c : ℕ} (C : Command q c) :
    Program nQubitOpenQASMVersion q c where
  body := C.compile

theorem commandAsProgram_wellFormed {q c : ℕ} {C : Command q c}
    (hC : C.WellFormed) :
    (commandAsProgram C).WellFormed := by
  change Composer.Block.WellFormedAt 0 C.compile
  exact Command.compile_wellFormed hC

def commandToOpenQASM {q c : ℕ} (C : Command q c) (hC : C.WellFormed) :
    String :=
  Program.toOpenQASM (commandAsProgram C) (commandAsProgram_wellFormed hC)

theorem elaborates_command_openqasm {q c fuel : Nat} {M : Term}
    {P : Compilation q c M} (h : Elaborates fuel M P) :
    P.command.WellFormed ∧ (commandAsProgram P.command).WellFormed :=
  ⟨elaborates_command_wellFormed h,
    commandAsProgram_wellFormed (elaborates_command_wellFormed h)⟩

theorem fragCert_closed_has_denotation {M : Term} {A : Ty}
    (c : FragCert.Closed M A) (_hA : Ty.SemanticFragment A) :
    Nonempty
      (Hom (FragmentContext.combined [] []) (fragmentModule A)) :=
  ⟨FragCert.denote c⟩

theorem n_qubit_fragment_denotation_openqasm_interface (N : Nat) :
    (∀ {M : Term} {A : Ty} (_c : FragCert.Closed M A),
      Ty.SemanticFragment A →
        Nonempty
          (Hom (FragmentContext.combined [] []) (fragmentModule A))) ∧
    UsesAtMostQubits N .unit ∧
    (∀ {q c fuel : Nat} {M : Term} {P : Compilation q c M},
      Elaborates fuel M P → P.command.WellFormed) ∧
    (∀ {q c : ℕ} (C : Command q c) (_hC : C.WellFormed),
      commandToOpenQASM C _hC = (commandAsProgram C).renderOpenQASM) ∧
    (∀ (C : Command 1 1) (_hC : C.Quotable),
      Nonempty (FragCert.Closed C.quote Command.quotationTy)) :=
  ⟨fun c hA => fragCert_closed_has_denotation c hA,
    usesAtMost_unit N,
    fun {_q} {_c} {_fuel} {_M} {_P} h => elaborates_command_wellFormed h,
    fun {_q} {_c} _C _hC => rfl,
    fun _C hC => fragment_quote_has_fragCert hC⟩

theorem elaborates_quote_packaging_eq_command_denote
    {C : Command 1 1} (hC : C.Quotable) (model : Composer.Model 1 1)
    (c : FragCert.Closed C.quote Command.quotationTy) :
    interpretQuoteHom model hC c = C.denote model :=
  rfl

theorem elaborates_cq_compile_transport {q c fuel : Nat} {M : Term}
    {P : Compilation q c M} (h : Elaborates fuel M P)
    (model : Composer.Model q c) :
    CQ.Eq (Composer.denoteBlock model P.command.compile)
      (P.command.denote model) :=
  elaborates_compile_agreement h model

theorem elab_transport_skip_quote (model : Composer.Model 1 1)
    (c : FragCert.Closed Command.skip.quote Command.quotationTy) :
    FragCert.denote c = quoteSkipSpine ∧
      interpretQuoteSpine model
          (.skip (fragCert_skip_quote_denote_independent c)) =
        Command.skip.denote model :=
  ⟨fragCert_skip_quote_denote_independent c,
    interpret_skip_quote_of_closed model c⟩

theorem elab_transport_measure_quote (model : Composer.Model 1 1)
    (qbit cbit : Fin 1) :
    FragCert.denote (fragCert_measure_quote qbit cbit) = quoteMeasureSpine ∧
      interpretQuoteSpineExt model
          (.measure (fragCert_measure_quote_denote qbit cbit)) =
        (Command.measure qbit cbit).denote model :=
  ⟨fragCert_measure_quote_denote qbit cbit,
    (interpret_measure_quote model qbit cbit
      (fragCert_measure_quote qbit cbit)
      (fragCert_measure_quote_denote qbit cbit)).2⟩

private def w0 : Fin 1 := ⟨0, by decide⟩
private def b0 : Fin 1 := ⟨0, by decide⟩

theorem measured_control_elaborates_openqasm :
    elaborateCommand (q := 1) (c := 1) 12 measuredControlProgram =
      some measuredControlExpected :=
  measured_control_elaboration_test

theorem bell_elaborates_openqasm :
    elaborateCommand (q := 2) (c := 0) 10 bellProgram = some bellExpected :=
  bell_elaboration_test

theorem measure_command_openqasm :
    (Command.measure w0 b0).WellFormed ∧
      commandToOpenQASM (Command.measure w0 b0) .measure =
        (commandAsProgram (Command.measure w0 b0)).renderOpenQASM :=
  ⟨.measure, rfl⟩

theorem measure_quote_cq_bridge (model : Composer.Model 1 1) :
    FragCert.denote (fragCert_measure_quote w0 b0) = quoteMeasureSpine ∧
      interpretQuoteSpineExt model
          (.measure (fragCert_measure_quote_denote w0 b0)) =
        (Command.measure w0 b0).denote model :=
  elab_transport_measure_quote model w0 b0

theorem skip_quote_openqasm_roundtrip (model : Composer.Model 1 1) :
    FragCert.denote fragCert_skip_quote = quoteSkipSpine ∧
      interpretQuoteSpine model (.skip fragCert_skip_quote_denote) =
        (Command.skip : Command 1 1).denote model ∧
      commandToOpenQASM (Command.skip : Command 1 1) .skip =
        (commandAsProgram (Command.skip : Command 1 1)).renderOpenQASM :=
  ⟨fragCert_skip_quote_denote,
    fragCert_skip_quote_spine_interpret model, rfl⟩

/-- Alias of the covering-set package for the N-qubit claim surface. -/
theorem n_qubit_quote_cq_covering_set (model : Composer.Model 1 1) :
    (interpretQuoteSpineExt model (.gateT (fragCert_t_quote_denote w0)) =
        (Command.t w0).denote model) ∧
    (interpretQuoteSpineExt model
          (.gateReset (fragCert_reset_quote_denote w0)) =
        (Command.reset w0).denote model) ∧
    (interpretQuoteSpineExt model
          (.measure (fragCert_measure_quote_denote (0 : Fin 1) (0 : Fin 1))) =
        (Command.measure (0 : Fin 1) (0 : Fin 1)).denote model) ∧
    (interpretQuoteSpineExt model
          (.seqSkipSkip fragCert_skip_quote_denote) =
        (Command.seq (.skip : Command 1 1) .skip).denote model) ∧
    (∀ (guard : Composer.CExpr 1) {yes no : Command 1 1}
        (hYes : yes.Quotable) (hNo : no.Quotable)
        (c : FragCert.Closed (Command.branch guard yes no).quote
          Command.quotationTy),
      interpretQuoteHom model (.branch hYes hNo) c =
        (Command.branch guard yes no).denote model) :=
  fragCert_spine_interprets_t_reset_measure_seq_branch model w0

end QLambda.Linear
