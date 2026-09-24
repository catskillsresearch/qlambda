/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentSourceCircuitN

/-!
# Extended quotation Hom ⇒ CQ.Sem bridge (measure / t / reset / seq / branch)

Extends the skip/x/h spine bridge with additional Quotable forms used by the
N-qubit OpenQASM translation claim.  Gate `t` / `reset` reuse `quoteGateSpine`.
Measure uses a choice certificate (any closed quote cert) as the Hom spine.
`seq skip skip` collapses to the skip spine.  Branch uses packaging
`interpretQuoteHom` (Command.denote) with a closed quote certificate.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

open QLambda.CQ
open Domain.Presheaf
open Domain.Presheaf.SuperoperatorModule

/-! ## Gate `t` and `reset` (same spine shape as `x` / `h`) -/

/-- Hand-built closed `FragCert` for `(Command.t w).quote`. -/
noncomputable def fragCert_t_quote (w : Fin 1) :
    FragCert.Closed (Command.t w).quote Command.quotationTy :=
  .lamU CtxUAllBit.nil CtxLAllSomeFragment.nil fragment_bit_admissible
    fragment_bit_duplicable (by simp [AllNone]) quotationTy_semanticFragment
    (fragCert_gate_lamL .t rfl)

/-- Hand-built closed `FragCert` for `(Command.reset qbit).quote`. -/
noncomputable def fragCert_reset_quote (qbit : Fin 1) :
    FragCert.Closed (Command.reset qbit).quote Command.quotationTy :=
  .lamU CtxUAllBit.nil CtxLAllSomeFragment.nil fragment_bit_admissible
    fragment_bit_duplicable (by simp [AllNone]) quotationTy_semanticFragment
    (fragCert_gate_lamL .reset rfl)

theorem fragCert_t_quote_denote (w : Fin 1) :
    FragCert.denote (fragCert_t_quote w) = quoteGateSpine .t rfl :=
  rfl

theorem fragCert_reset_quote_denote (qbit : Fin 1) :
    FragCert.denote (fragCert_reset_quote qbit) = quoteGateSpine .reset rfl :=
  rfl

theorem command_t_denote_eq_gateBlock (model : Composer.Model 1 1)
    (w : Fin 1) :
    (Command.t w).denote model =
      Composer.denoteBlock model [.gate (.t w)] :=
  rfl

theorem command_reset_denote_eq_resetBlock (model : Composer.Model 1 1)
    (qbit : Fin 1) :
    (Command.reset qbit).denote model =
      Composer.denoteBlock model [.reset qbit] :=
  rfl

/-! ## Measure quotation spine -/

/-- Closed certificate for a measure quotation (choice from nonempty package). -/
noncomputable def fragCert_measure_quote (qbit cbit : Fin 1) :
    FragCert.Closed (Command.measure qbit cbit).quote Command.quotationTy :=
  Classical.choice (fragment_quote_has_fragCert .measure)

/-- Hom spine of the canonical measure quotation at wire/bit 0. -/
noncomputable def quoteMeasureSpine :
    Hom (FragmentContext.combined [] [])
      (fragmentModule Command.quotationTy) :=
  FragCert.denote (fragCert_measure_quote (0 : Fin 1) (0 : Fin 1))

theorem fragCert_measure_quote_denote (qbit cbit : Fin 1) :
    FragCert.denote (fragCert_measure_quote qbit cbit) = quoteMeasureSpine := by
  have hq : qbit = (0 : Fin 1) := Fin.eq_zero qbit
  have hc : cbit = (0 : Fin 1) := Fin.eq_zero cbit
  subst hq; subst hc
  rfl

theorem command_measure_denote_eq_measureBlock (model : Composer.Model 1 1)
    (qbit cbit : Fin 1) :
    (Command.measure qbit cbit).denote model =
      Composer.denoteBlock model [.measure qbit cbit] :=
  rfl

/-! ## `seq skip skip` collapses to skip -/

theorem quote_seq_skip_skip :
    (Command.seq .skip .skip).quote = Command.skip.quote :=
  rfl

theorem quote_seq_skip_skip_denote
    (c : FragCert.Closed (Command.seq .skip .skip).quote Command.quotationTy) :
    FragCert.denote c = quoteSkipSpine := by
  simpa [quote_seq_skip_skip] using fragCert_skip_quote_denote_independent
    (quote_seq_skip_skip ▸ c)

/-! ## Extended spine witness -/

/-- Extended witness covering skip/x/h plus t/reset/measure and seq-skip. -/
inductive QuoteSpineWitnessExt (η : Hom (FragmentContext.combined [] [])
    (fragmentModule Command.quotationTy)) : Type where
  | core : QuoteSpineWitness η → QuoteSpineWitnessExt η
  | gateT (h : η = quoteGateSpine .t rfl)
  | gateReset (h : η = quoteGateSpine .reset rfl)
  | measure (h : η = quoteMeasureSpine)
  | seqSkipSkip (h : η = quoteSkipSpine)

/-- Spine-driven CQ interpret for the extended witness set. -/
noncomputable def interpretQuoteSpineExt (model : Composer.Model 1 1)
    {η : Hom (FragmentContext.combined [] [])
      (fragmentModule Command.quotationTy)} :
    QuoteSpineWitnessExt η → CQ.Sem 1 1
  | .core w => interpretQuoteSpine model w
  | .gateT _ => Composer.denoteBlock model [.gate (.t (0 : Fin 1))]
  | .gateReset _ => Composer.denoteBlock model [.reset (0 : Fin 1)]
  | .measure _ => Composer.denoteBlock model [.measure (0 : Fin 1) (0 : Fin 1)]
  | .seqSkipSkip _ => CQ.skip

theorem interpret_t_quote {t : Term} (model : Composer.Model 1 1) (w : Fin 1)
    (c : FragCert.Closed t Command.quotationTy)
    (hc : FragCert.denote c = quoteGateSpine .t rfl) :
    interpretQuoteSpineExt model (.gateT hc) =
        Composer.denoteBlock model [.gate (.t w)] ∧
    interpretQuoteSpineExt model (.gateT hc) = (Command.t w).denote model := by
  have hw := Fin.eq_zero w
  subst hw
  exact ⟨rfl, (command_t_denote_eq_gateBlock model (0 : Fin 1)).symm⟩

theorem interpret_reset_quote {t : Term} (model : Composer.Model 1 1)
    (qbit : Fin 1) (c : FragCert.Closed t Command.quotationTy)
    (hc : FragCert.denote c = quoteGateSpine .reset rfl) :
    interpretQuoteSpineExt model (.gateReset hc) =
        Composer.denoteBlock model [.reset qbit] ∧
    interpretQuoteSpineExt model (.gateReset hc) =
      (Command.reset qbit).denote model := by
  have hq := Fin.eq_zero qbit
  subst hq
  exact ⟨rfl, (command_reset_denote_eq_resetBlock model (0 : Fin 1)).symm⟩

theorem interpret_measure_quote {t : Term} (model : Composer.Model 1 1)
    (qbit cbit : Fin 1) (c : FragCert.Closed t Command.quotationTy)
    (hc : FragCert.denote c = quoteMeasureSpine) :
    interpretQuoteSpineExt model (.measure hc) =
        Composer.denoteBlock model [.measure qbit cbit] ∧
    interpretQuoteSpineExt model (.measure hc) =
      (Command.measure qbit cbit).denote model := by
  have hq := Fin.eq_zero qbit
  have hcbit := Fin.eq_zero cbit
  subst hq; subst hcbit
  exact ⟨rfl, (command_measure_denote_eq_measureBlock model (0 : Fin 1)
    (0 : Fin 1)).symm⟩

theorem interpret_seq_skip_skip_quote {t : Term} (model : Composer.Model 1 1)
    (c : FragCert.Closed t Command.quotationTy)
    (hc : FragCert.denote c = quoteSkipSpine) :
    interpretQuoteSpineExt model (.seqSkipSkip hc) = CQ.skip ∧
    interpretQuoteSpineExt model (.seqSkipSkip hc) =
      (Command.seq .skip .skip).denote model := by
  refine ⟨rfl, ?_⟩
  -- `seq skip skip` compiles to `[] ++ []` and denotes as `CQ.skip`.
  change CQ.skip = (Command.seq .skip .skip).denote model
  rfl

/-- Packaging branch bridge: Hom-side certificate interprets as Command.denote. -/
theorem interpret_branch_quote_packaging (model : Composer.Model 1 1)
    (guard : Composer.CExpr 1) {yes no : Command 1 1}
    (hYes : yes.Quotable) (hNo : no.Quotable)
    (c : FragCert.Closed (Command.branch guard yes no).quote
      Command.quotationTy) :
    interpretQuoteHom model (.branch hYes hNo) c =
      (Command.branch guard yes no).denote model :=
  rfl

/-- Covering-set package: t, reset, measure, seq-skip, and branch packaging. -/
theorem fragCert_spine_interprets_t_reset_measure_seq_branch
    (model : Composer.Model 1 1) (w : Fin 1) :
    (interpretQuoteSpineExt model (.gateT (fragCert_t_quote_denote w)) =
        (Command.t w).denote model) ∧
    (interpretQuoteSpineExt model
          (.gateReset (fragCert_reset_quote_denote w)) =
        (Command.reset w).denote model) ∧
    (interpretQuoteSpineExt model
          (.measure (fragCert_measure_quote_denote (0 : Fin 1) (0 : Fin 1))) =
        (Command.measure (0 : Fin 1) (0 : Fin 1)).denote model) ∧
    (interpretQuoteSpineExt model
          (.seqSkipSkip fragCert_skip_quote_denote) =
        (Command.seq .skip .skip).denote model) ∧
    (∀ (guard : Composer.CExpr 1) {yes no : Command 1 1}
        (hYes : yes.Quotable) (hNo : no.Quotable)
        (c : FragCert.Closed (Command.branch guard yes no).quote
          Command.quotationTy),
      interpretQuoteHom model (.branch hYes hNo) c =
        (Command.branch guard yes no).denote model) :=
  ⟨(interpret_t_quote model w (fragCert_t_quote w)
      (fragCert_t_quote_denote w)).2,
    (interpret_reset_quote model w (fragCert_reset_quote w)
      (fragCert_reset_quote_denote w)).2,
    (interpret_measure_quote model (0 : Fin 1) (0 : Fin 1)
      (fragCert_measure_quote (0 : Fin 1) (0 : Fin 1))
      (fragCert_measure_quote_denote (0 : Fin 1) (0 : Fin 1))).2,
    (interpret_seq_skip_skip_quote model fragCert_skip_quote
      fragCert_skip_quote_denote).2,
    fun guard {_yes} {_no} hYes hNo c =>
      interpret_branch_quote_packaging model guard hYes hNo c⟩

end QLambda.Linear
