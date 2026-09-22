/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.Quotation
import QLambda.Linear.Metatheory

/-!
# Canonical quotation for a two-wire finite register

This module extends canonical quotation to the fixed finite register
`Command 2 1`.  It is the first genuinely multi-wire fragment: both
orientations of a distinct-wire `cx` are represented, together with all
single-wire gates, rational `ry`, measurement, reset, store, sequencing, and
classical branching.

The generated source type is

```
Bit →ω Qubit →¹ Qubit →¹ ((Qubit ⊗ Qubit) ⊗ Bit).
```

Measurement does not put an unrestricted lambda around a free linear wire.
Instead, its closed unrestricted continuation returns a curried linear
function which subsequently consumes the untouched wire.  This is the
essential extra construction beyond the one-wire quotation.

As in `QLambda.Linear.Quotation`, `coin` angles are outside the exact source
fragment because source `Prim.ry` carries only a rational.  The boundary is
recorded by `AngleQuotable` and `coin_not_quotable`.
-/

namespace QLambda.Linear

open QLambda.CQ

namespace Command

namespace GeneralQuotation

/-- The declared finite register sizes of this quotation. -/
abbrev quantumSize : Nat := 2
abbrev classicalSize : Nat := 1

def qubitRegisterTy : Ty :=
  .tensor .qubit .qubit

def resultTy : Ty :=
  .tensor qubitRegisterTy .bit

/-- Curried source type for the fixed `2 × 1` register. -/
def quotationTy : Ty :=
  .arrow .unres .bit <|
    .arrow .lin .qubit <|
      .arrow .lin .qubit resultTy

private def unused (n : Nat) : List (Option Ty) :=
  List.replicate n none

private def liveRegister (n : Nat) : List (Option Ty) :=
  some qubitRegisterTy :: unused n

private theorem allNone_unused (n : Nat) : AllNone (unused n) := by
  simpa [unused] using allNone_replicate_none n

private theorem split_unused (n : Nat) :
    OSplit (unused n) (unused n) (unused n) :=
  OSplit.self_of_allNone (allNone_unused n)

private theorem split_live_left (n : Nat) :
    OSplit (liveRegister n) (liveRegister n) (unused (n + 1)) := by
  simpa [liveRegister, unused, List.replicate_succ] using
    (OSplit.left (split_unused n))

private theorem split_live_right (n : Nat) :
    OSplit (liveRegister n) (unused (n + 1)) (liveRegister n) :=
  (split_live_left n).symm

private theorem bit_admissible : Ty.Admissible .bit :=
  Ty.admissible_eq_true_iff.mp rfl

private theorem bit_duplicable : Ty.Duplicable .bit :=
  Ty.duplicable_eq_true_iff.mp rfl

private theorem qubit_admissible : Ty.Admissible .qubit :=
  Ty.admissible_eq_true_iff.mp rfl

private theorem register_admissible : Ty.Admissible qubitRegisterTy :=
  Ty.admissible_eq_true_iff.mp rfl

private theorem typed_register_var (Γ : List Ty) (n : Nat) :
    HasType Γ (liveRegister n) (.var .lin 0) qubitRegisterTy :=
  .varL .zero (allNone_unused n)

private theorem typed_bit_var (Γ : List Ty) (n : Nat) :
    HasType (.bit :: Γ) (unused n) (.var .unres 0) .bit :=
  .varU .zero bit_duplicable (allNone_unused n)

/-- Exactly the target angles represented by source `Prim.ry`. -/
inductive AngleQuotable : Composer.AngleExpr → Prop where
  | rational (r : ℚ) : AngleQuotable (.rational r)

/-- Probability-derived Composer angles have no exact source primitive. -/
theorem coin_not_quotable (p : Composer.Probability) :
    ¬ AngleQuotable (.coin p) := by
  intro h
  cases h

/-- Exact `Command 2 1` fragment represented by this module. -/
inductive Quotable : Command quantumSize classicalSize → Prop where
  | skip : Quotable .skip
  | x {w} : Quotable (.x w)
  | h {w} : Quotable (.h w)
  | t {w} : Quotable (.t w)
  | ry {θ w} : AngleQuotable θ → Quotable (.ry θ w)
  | cx {control target} :
      control ≠ target → Quotable (.cx control target)
  | measure {qbit cbit} : Quotable (.measure qbit cbit)
  | reset {qbit} : Quotable (.reset qbit)
  | store {cbit e} : Quotable (.store cbit e)
  | seq {A B} : Quotable A → Quotable B → Quotable (.seq A B)
  | branch {guard yes no} :
      Quotable yes → Quotable no → Quotable (.branch guard yes no)

theorem Quotable.wellFormed
    {C : Command quantumSize classicalSize} (hC : Quotable C) :
    C.WellFormed := by
  induction hC with
  | skip => exact .skip
  | x => exact .x
  | h => exact .h
  | t => exact .t
  | ry => exact .ry
  | cx hne => exact .cx hne
  | measure => exact .measure
  | reset => exact .reset
  | store => exact .store
  | seq _ _ ihA ihB => exact .seq ihA ihB
  | branch _ _ ihYes ihNo => exact .branch ihYes ihNo

/-- Interpret the sole classical register cell as a pure source bit term. -/
def quoteCExpr (current : Term) : Composer.CExpr classicalSize → Term
  | .lit b => .bitLit b
  | .bit _ => current
  | .not e => .ite (quoteCExpr current e) (.bitLit false) (.bitLit true)
  | .and e₁ e₂ =>
      .ite (quoteCExpr current e₁) (quoteCExpr current e₂) (.bitLit false)
  | .or e₁ e₂ =>
      .ite (quoteCExpr current e₁) (.bitLit true) (quoteCExpr current e₂)
  | .xor e₁ e₂ =>
      .ite (quoteCExpr current e₁)
        (.ite (quoteCExpr current e₂) (.bitLit false) (.bitLit true))
        (quoteCExpr current e₂)

private theorem quoteCExpr_typed
    {Γ : List Ty} {current : Term}
    (hcurrent : ∀ n, HasType (.bit :: Γ) (unused n) current .bit) :
    ∀ (e : Composer.CExpr classicalSize) (n : Nat),
      HasType (.bit :: Γ) (unused n) (quoteCExpr current e) .bit := by
  intro e
  induction e with
  | lit b =>
      intro n
      exact .bitLit (allNone_unused n)
  | bit i =>
      intro n
      exact hcurrent n
  | not e ih =>
      intro n
      exact .ite (split_unused n) (ih n)
        (.bitLit (allNone_unused n)) (.bitLit (allNone_unused n))
  | and e₁ e₂ ih₁ ih₂ =>
      intro n
      exact .ite (split_unused n) (ih₁ n) (ih₂ n)
        (.bitLit (allNone_unused n))
  | or e₁ e₂ ih₁ ih₂ =>
      intro n
      exact .ite (split_unused n) (ih₁ n)
        (.bitLit (allNone_unused n)) (ih₂ n)
  | xor e₁ e₂ ih₁ ih₂ =>
      intro n
      have hnot :
          HasType (.bit :: Γ) (unused n)
            (.ite (quoteCExpr current e₂) (.bitLit false) (.bitLit true)) .bit :=
        .ite (split_unused n) (ih₂ n)
          (.bitLit (allNone_unused n)) (.bitLit (allNone_unused n))
      exact .ite (split_unused n) (ih₁ n) hnot (ih₂ n)

/-- Apply a unary source primitive to one component of a two-qubit tensor. -/
def unaryRegister (p : Prim) (w : Fin quantumSize) : Term :=
  .lam .lin qubitRegisterTy <|
    .unpair (.var .lin 0) <|
      .lam .lin .qubit <|
        .lam .lin .qubit <|
          if w = 0 then
            .pair (.app (.prim p) (.var .lin 1)) (.var .lin 0)
          else
            .pair (.var .lin 1) (.app (.prim p) (.var .lin 0))

/-- Apply `cx`, restoring canonical register order in the reverse orientation. -/
def cxRegister (control target : Fin quantumSize) : Term :=
  .lam .lin qubitRegisterTy <|
    .unpair (.var .lin 0) <|
      .lam .lin .qubit <|
        .lam .lin .qubit <|
          if control = target then
            .pair (.var .lin 1) (.var .lin 0)
          else if control = 0 then
            .app (.app (.prim .cx) (.var .lin 1)) (.var .lin 0)
          else
            .unpair
              (.app (.app (.prim .cx) (.var .lin 0)) (.var .lin 1))
              (.lam .lin .qubit <|
                .lam .lin .qubit <|
                  .pair (.var .lin 0) (.var .lin 1))

private theorem unaryRegister_infer (p : Prim)
    (hp : primTy p = .arrow .lin .qubit .qubit)
    (w : Fin quantumSize) :
    infer [] [] (unaryRegister p w) =
      some (.arrow .lin qubitRegisterTy qubitRegisterTy, []) := by
  cases p <;> simp [primTy] at hp
  all_goals
    fin_cases w <;>
      simp [unaryRegister, qubitRegisterTy, infer, Ty.admissible,
        Ty.admissibleAt, Ty.wellScopedAt, Ty.positiveRec,
        primTy, mark, zipOr]

private theorem cxRegister_infer (control target : Fin quantumSize) :
    infer [] [] (cxRegister control target) =
      some (.arrow .lin qubitRegisterTy qubitRegisterTy, []) := by
  fin_cases control <;> fin_cases target <;>
    rfl

private theorem closed_typed_any {M : Term} {A : Ty}
    (h : HasType [] [] M A) :
    ∀ (Γ : List Ty) (n : Nat), HasType Γ (unused n) M A := by
  have hΓ : ∀ Γ : List Ty, HasType Γ [] M A := by
    intro Γ
    induction Γ with
    | nil => exact h
    | cons B Γ ih =>
        have hw := weakenUnres (C := B) ih
        simpa [shiftUnres_closed_typed h] using hw
  intro Γ n
  induction n with
  | zero => simpa [unused] using hΓ Γ
  | succ n ih =>
      have hw := weakenLinNone ih
      simpa [unused, List.replicate_succ, shiftLin_closed_typed h] using hw

private theorem unaryRegister_typed (p : Prim)
    (hp : primTy p = .arrow .lin .qubit .qubit)
    (w : Fin quantumSize) (Γ : List Ty) (n : Nat) :
    HasType Γ (unused n) (unaryRegister p w)
      (.arrow .lin qubitRegisterTy qubitRegisterTy) := by
  exact closed_typed_any (infer_sound (unaryRegister_infer p hp w)).1 Γ n

private theorem cxRegister_typed (control target : Fin quantumSize)
    (Γ : List Ty) (n : Nat) :
    HasType Γ (unused n) (cxRegister control target)
      (.arrow .lin qubitRegisterTy qubitRegisterTy) := by
  exact closed_typed_any (infer_sound (cxRegister_infer control target)).1 Γ n

def bindRegister (next body : Term) : Term :=
  .app (.lam .lin qubitRegisterTy body) next

def continueWith (k : Term → Term) (current register : Term) : Term :=
  bindRegister register (k current)

/-- Measurement of either wire.  The measurement continuation is linearly
closed and returns a function waiting for the untouched wire. -/
def measureRegister (qbit : Fin quantumSize)
    (k : Term → Term) : Term :=
  .unpair (.var .lin 0) <|
    .lam .lin .qubit <|
      .lam .lin .qubit <|
        if qbit = 0 then
          .app
            (.measure (.var .lin 1) <|
              .lam .unres .bit <|
                .lam .lin .qubit <|
                  .lam .lin .qubit <|
                    continueWith k (.var .unres 0)
                      (.pair (.var .lin 1) (.var .lin 0)))
            (.var .lin 0)
        else
          .app
            (.measure (.var .lin 0) <|
              .lam .unres .bit <|
                .lam .lin .qubit <|
                  .lam .lin .qubit <|
                    continueWith k (.var .unres 0)
                      (.pair (.var .lin 0) (.var .lin 1)))
            (.var .lin 1)

def quoteBody
    (C : Command quantumSize classicalSize)
    (current : Term) (k : Term → Term) : Term :=
  match C with
  | .skip => k current
  | .x w =>
      bindRegister
        (.app (unaryRegister .x w) (.var .lin 0)) (k current)
  | .h w =>
      bindRegister
        (.app (unaryRegister .h w) (.var .lin 0)) (k current)
  | .t w =>
      bindRegister
        (.app (unaryRegister .t w) (.var .lin 0)) (k current)
  | .ry θ w =>
      let r := match θ with
        | .rational r => r
        | .coin p => p.val
      bindRegister
        (.app (unaryRegister (.ry r) w) (.var .lin 0)) (k current)
  | .cx control target =>
      bindRegister
        (.app (cxRegister control target) (.var .lin 0)) (k current)
  | .measure qbit _ => measureRegister qbit k
  | .reset qbit =>
      bindRegister
        (.app (unaryRegister .reset qbit) (.var .lin 0)) (k current)
  | .store _ e => k (quoteCExpr current e)
  | .seq A B =>
      quoteBody A current (fun next => quoteBody B next k)
  | .branch guard yes no =>
      .ite (quoteCExpr current guard)
        (quoteBody yes current k) (quoteBody no current k)

private def ContinuationTyped (k : Term → Term) : Prop :=
  ∀ (Γ : List Ty) (n : Nat) (current : Term),
    (∀ m, HasType (.bit :: Γ) (unused m) current .bit) →
    HasType (.bit :: Γ) (liveRegister n) (k current) resultTy

private theorem transformedRegister_typed
    {Γ : List Ty} {n : Nat} {F : Term}
    (hF : HasType Γ (unused (n + 1)) F
      (.arrow .lin qubitRegisterTy qubitRegisterTy)) :
    HasType Γ (liveRegister n)
      (.app F (.var .lin 0)) qubitRegisterTy := by
  exact .appL (split_live_right n) hF (typed_register_var Γ n)

private theorem bindRegister_typed
    {Γ : List Ty} {n : Nat} {next body : Term} {A : Ty}
    (hbody : HasType Γ (liveRegister (n + 1)) body A)
    (hnext : HasType Γ (liveRegister n) next qubitRegisterTy) :
    HasType Γ (liveRegister n) (bindRegister next body) A := by
  exact .appL (split_live_right n)
    (.lamL register_admissible hbody) hnext

private theorem two_qubit_pair_typed (Γ : List Ty) (n : Nat) :
    HasType Γ
      (some .qubit :: some .qubit :: unused n)
      (.pair (.var .lin 1) (.var .lin 0)) qubitRegisterTy := by
  apply HasType.pair
      (OSplit.right (OSplit.left (split_unused n)))
  · exact .varL (.succ .zero) (allNone_unused n)
  · exact .varL .zero (by
      change AllNone (none :: unused n)
      exact allNone_unused (n + 1))

private theorem two_qubit_pair_swapped_typed (Γ : List Ty) (n : Nat) :
    HasType Γ
      (some .qubit :: some .qubit :: unused n)
      (.pair (.var .lin 0) (.var .lin 1)) qubitRegisterTy := by
  apply HasType.pair
      (OSplit.left (OSplit.right (split_unused n)))
  · exact .varL .zero (by
      change AllNone (none :: unused n)
      exact allNone_unused (n + 1))
  · exact .varL (.succ .zero) (allNone_unused n)

private theorem continueWith_typed {k : Term → Term}
    (hk : ContinuationTyped k) (Γ : List Ty) (n : Nat)
    (register : Term)
    (hregister : HasType (.bit :: .bit :: Γ)
      (some .qubit :: some .qubit :: unused n)
      register qubitRegisterTy) :
    HasType (.bit :: .bit :: Γ)
      (some .qubit :: some .qubit :: unused n)
      (continueWith k (.var .unres 0) register) resultTy := by
  unfold continueWith
  apply HasType.appL
      (OSplit.right (OSplit.right (split_unused n)))
  · apply HasType.lamL register_admissible
    apply hk (.bit :: Γ) (n + 2) (.var .unres 0)
    intro m
    exact typed_bit_var (.bit :: Γ) m
  · exact hregister

private theorem measureRegister_typed {k : Term → Term}
    (hk : ContinuationTyped k) (qbit : Fin quantumSize)
    (Γ : List Ty) (n : Nat) :
    HasType (.bit :: Γ) (liveRegister n)
      (measureRegister qbit k) resultTy := by
  unfold measureRegister
  apply HasType.unpair (split_live_left n)
  · exact typed_register_var (.bit :: Γ) n
  · apply HasType.lamL qubit_admissible
    apply HasType.lamL qubit_admissible
    fin_cases qbit
    · simp only [Fin.isValue]
      apply HasType.appL
          (OSplit.right (OSplit.left (split_unused (n + 1))))
      · apply HasType.measure
            (OSplit.none (OSplit.left (split_unused (n + 1))))
        · exact .varL (.succ .zero) (allNone_unused (n + 1))
        · apply HasType.lamU bit_admissible bit_duplicable
              (by
                exact allNone_unused (n + 3))
          apply HasType.lamL qubit_admissible
          apply HasType.lamL qubit_admissible
          exact continueWith_typed hk Γ (n + 3)
            _ (two_qubit_pair_typed (.bit :: .bit :: Γ) (n + 3))
      · exact .varL .zero (by
          change AllNone (none :: unused (n + 1))
          exact allNone_unused (n + 2))
    · simp only [Fin.isValue]
      apply HasType.appL
          (OSplit.left (OSplit.right (split_unused (n + 1))))
      · apply HasType.measure
            (OSplit.left (OSplit.none (split_unused (n + 1))))
        · exact .varL .zero (by
            change AllNone (none :: unused (n + 1))
            exact allNone_unused (n + 2))
        · apply HasType.lamU bit_admissible bit_duplicable
              (by
                exact allNone_unused (n + 3))
          apply HasType.lamL qubit_admissible
          apply HasType.lamL qubit_admissible
          exact continueWith_typed hk Γ (n + 3)
            _ (two_qubit_pair_swapped_typed (.bit :: .bit :: Γ) (n + 3))
      · exact .varL (.succ .zero) (allNone_unused (n + 1))

private theorem quoteBody_typed
    {C : Command quantumSize classicalSize}
    (hC : Quotable C) {k : Term → Term}
    (hk : ContinuationTyped k) :
    ∀ (Γ : List Ty) (n : Nat) (current : Term),
      (∀ m, HasType (.bit :: Γ) (unused m) current .bit) →
      HasType (.bit :: Γ) (liveRegister n)
        (quoteBody C current k) resultTy := by
  induction hC generalizing k with
  | skip =>
      intro Γ n current hcurrent
      exact hk Γ n current hcurrent
  | x =>
      intro Γ n current hcurrent
      apply bindRegister_typed (hk Γ (n + 1) current hcurrent)
      apply transformedRegister_typed
      exact unaryRegister_typed .x rfl _ (.bit :: Γ) (n + 1)
  | h =>
      intro Γ n current hcurrent
      apply bindRegister_typed (hk Γ (n + 1) current hcurrent)
      apply transformedRegister_typed
      exact unaryRegister_typed .h rfl _ (.bit :: Γ) (n + 1)
  | t =>
      intro Γ n current hcurrent
      apply bindRegister_typed (hk Γ (n + 1) current hcurrent)
      apply transformedRegister_typed
      exact unaryRegister_typed .t rfl _ (.bit :: Γ) (n + 1)
  | ry hθ =>
      cases hθ with
      | rational r =>
          intro Γ n current hcurrent
          apply bindRegister_typed (hk Γ (n + 1) current hcurrent)
          apply transformedRegister_typed
          exact unaryRegister_typed (.ry r) rfl _ (.bit :: Γ) (n + 1)
  | cx hne =>
      intro Γ n current hcurrent
      apply bindRegister_typed (hk Γ (n + 1) current hcurrent)
      apply transformedRegister_typed
      exact cxRegister_typed _ _ (.bit :: Γ) (n + 1)
  | measure =>
      intro Γ n current hcurrent
      exact measureRegister_typed hk _ Γ n
  | reset =>
      intro Γ n current hcurrent
      apply bindRegister_typed (hk Γ (n + 1) current hcurrent)
      apply transformedRegister_typed
      exact unaryRegister_typed .reset rfl _ (.bit :: Γ) (n + 1)
  | store =>
      rename_i cbit e
      intro Γ n current hcurrent
      simpa [quoteBody] using
        hk Γ n (quoteCExpr current e)
          (fun m => quoteCExpr_typed hcurrent e m)
  | seq hA hB ihA ihB =>
      intro Γ n current hcurrent
      apply ihA
      · intro Γ' n' next hnext
        exact ihB hk Γ' n' next hnext
      · exact hcurrent
  | branch hy hn ihy ihn =>
      intro Γ n current hcurrent
      apply HasType.ite (split_live_right n)
      · exact quoteCExpr_typed hcurrent _ (n + 1)
      · exact ihy hk Γ n current hcurrent
      · exact ihn hk Γ n current hcurrent

/-- Canonical lambda quotation with one unrestricted classical binder and two
curried linear qubit binders. -/
def quote (C : Command quantumSize classicalSize) : Term :=
  .lam .unres .bit <|
    .lam .lin .qubit <|
      .lam .lin .qubit <|
        bindRegister
          (.pair (.var .lin 1) (.var .lin 0))
          (quoteBody C (.var .unres 0)
            (fun current => .pair (.var .lin 0) current))

/-- Every command in the declared fragment has a well-typed source term. -/
theorem quote_typed
    {C : Command quantumSize classicalSize} (hC : Quotable C) :
    HasType [] [] (quote C) quotationTy := by
  unfold quote quotationTy
  apply HasType.lamU bit_admissible bit_duplicable
      (show AllNone [] from trivial)
  apply HasType.lamL qubit_admissible
  apply HasType.lamL qubit_admissible
  unfold bindRegister
  apply HasType.appL
      (OSplit.right (OSplit.right OSplit.nil))
  · apply HasType.lamL register_admissible
    change HasType [.bit] (liveRegister 2)
      (quoteBody C (.var .unres 0)
        (fun current => .pair (.var .lin 0) current)) resultTy
    apply quoteBody_typed hC
    · intro Γ n current hcurrent
      exact HasType.pair (split_live_left n)
        (typed_register_var (.bit :: Γ) n) (hcurrent (n + 1))
    · intro m
      exact typed_bit_var [] m
  · exact two_qubit_pair_typed [.bit] 0

/-- A certified canonical source quotation of a `Command 2 1`. -/
structure Quotation where
  command : Command quantumSize classicalSize
  quotable : Quotable command

namespace Quotation

def term (Q : Quotation) : Term :=
  quote Q.command

theorem typing (Q : Quotation) :
    HasType [] [] Q.term quotationTy :=
  quote_typed Q.quotable

/-- Exact extraction of the represented finite-register command. -/
def compile (Q : Quotation) : Command quantumSize classicalSize :=
  Q.command

/-- Exact command-to-canonical-source reflection. -/
def reflect (C : Command quantumSize classicalSize)
    (hC : Quotable C) : Quotation :=
  ⟨C, hC⟩

@[simp] theorem compile_reflect
    (C : Command quantumSize classicalSize) (hC : Quotable C) :
    (reflect C hC).compile = C :=
  rfl

@[simp] theorem reflect_compile_term (Q : Quotation) :
    (reflect Q.compile Q.quotable).term = Q.term :=
  rfl

/-- The CQ meaning is exactly that of the represented command. -/
noncomputable def denote
    (model : Composer.Model quantumSize classicalSize)
    (Q : Quotation) : CQ.Sem quantumSize classicalSize :=
  Q.command.denote model

/-- Compilation preserves exact CQ denotation. -/
theorem denote_compile
    (model : Composer.Model quantumSize classicalSize) (Q : Quotation) :
    CQ.Eq (Q.denote model) (Q.compile.denote model) :=
  CQ.Eq.refl _

/-- Reflection preserves exact CQ denotation. -/
theorem denote_reflect
    (model : Composer.Model quantumSize classicalSize)
    (C : Command quantumSize classicalSize) (hC : Quotable C) :
    CQ.Eq ((reflect C hC).denote model) (C.denote model) :=
  CQ.Eq.refl _

/-- The full capstone packages typing, exact compilation, reflection, and CQ
denotation for every command in the finite fragment. -/
theorem quotation_capstone
    (model : Composer.Model quantumSize classicalSize)
    (C : Command quantumSize classicalSize) (hC : Quotable C) :
    HasType [] [] (reflect C hC).term quotationTy ∧
    (reflect C hC).compile = C ∧
    CQ.Eq ((reflect C hC).denote model) (C.denote model) := by
  exact ⟨(reflect C hC).typing, rfl, CQ.Eq.refl _⟩

end Quotation

end GeneralQuotation

end Command

end QLambda.Linear
