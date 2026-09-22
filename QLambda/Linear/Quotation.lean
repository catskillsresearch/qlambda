/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.Circuit
import QLambda.Linear.Typing

/-!
# Certified lambda quotation of the one-wire circuit fragment

This module gives the largest register fragment that can be quoted by the
current source calculus without adding a register allocator or changing its
measurement rule: one live qubit and one classical slot, with rational-angle
`ry`.  In particular this includes arbitrary sequencing, measurement, reset,
classical assignment, and classical branching.  A well-formed `cx` cannot
occur because its two `Fin 1` operands would coincide.  Composer's
probability-derived `coin` angle has no source `Prim` counterpart and is
therefore excluded rather than silently approximated.

The quotation has the closed type

```
Bit →ω Qubit →¹ (Qubit ⊗ Bit)
```

so the classical register is an unrestricted binder and the wire is a
curried linear binder.  Translation is continuation based.  This is essential
for measurement: the unrestricted measurement continuation is closed over
linear resources, exactly as required by `HasType.measure`.

`Quotation` is a certified canonical term, rather than an arbitrary source
term.  Consequently compilation is total on precisely this documented
fragment and reflection is canonical.  Its denotation is the existing ideal
CQ denotation of the represented command; no independent source denotation is
invented here.
-/

namespace QLambda.Linear

open QLambda.CQ

namespace Command

private def unused (n : Nat) : List (Option Ty) :=
  List.replicate n none

private def liveQubit (n : Nat) : List (Option Ty) :=
  some .qubit :: unused n

/-- Exact command fragment represented by the current source primitives. -/
inductive Quotable : Command 1 1 → Prop where
  | skip : Quotable .skip
  | x {w} : Quotable (.x w)
  | h {w} : Quotable (.h w)
  | t {w} : Quotable (.t w)
  | ry {r w} : Quotable (.ry (.rational r) w)
  | measure {qbit cbit} : Quotable (.measure qbit cbit)
  | reset {qbit} : Quotable (.reset qbit)
  | store {cbit e} : Quotable (.store cbit e)
  | seq {A B} : Quotable A → Quotable B → Quotable (.seq A B)
  | branch {guard yes no} :
      Quotable yes → Quotable no → Quotable (.branch guard yes no)

theorem Quotable.wellFormed {C : Command 1 1} (hC : Quotable C) :
    C.WellFormed := by
  induction hC with
  | skip => exact .skip
  | x => exact .x
  | h => exact .h
  | t => exact .t
  | ry => exact .ry
  | measure => exact .measure
  | reset => exact .reset
  | store => exact .store
  | seq _ _ ihA ihB => exact .seq ihA ihB
  | branch _ _ ihYes ihNo => exact .branch ihYes ihNo

private theorem allNone_unused (n : Nat) : AllNone (unused n) := by
  induction n with
  | zero => trivial
  | succ n =>
      simpa [unused, List.replicate_succ, AllNone] using allNone_unused n

private theorem split_unused (n : Nat) :
    OSplit (unused n) (unused n) (unused n) := by
  induction n with
  | zero => exact .nil
  | succ n =>
      simpa [unused, List.replicate_succ] using
        (OSplit.none (split_unused n))

private theorem split_live_left (n : Nat) :
    OSplit (liveQubit n) (liveQubit n) (unused (n + 1)) := by
  simpa [liveQubit, unused, List.replicate_succ] using
    (OSplit.left (split_unused n))

private theorem split_live_right (n : Nat) :
    OSplit (liveQubit n) (unused (n + 1)) (liveQubit n) :=
  (split_live_left n).symm

private theorem typed_live_var (Γ : List Ty) (n : Nat) :
    HasType Γ (liveQubit n) (.var .lin 0) .qubit := by
  exact .varL .zero (allNone_unused n)

private theorem typed_bit_var (Γ : List Ty) (n : Nat) :
    HasType (.bit :: Γ) (unused n) (.var .unres 0) .bit := by
  exact .varU .zero (by rfl) (allNone_unused n)

/-- Interpret a one-bit classical expression as a pure source bit term.
The supplied term is the current value of the sole classical slot. -/
private def quoteCExpr (current : Term) : Composer.CExpr 1 → Term
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
    ∀ (e : Composer.CExpr 1) (n : Nat),
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

/-- CPS quotation of a command body.  The current wire is always linear
index zero; `current` is a pure term denoting the current classical slot. -/
private def quoteBody (C : Command 1 1) (current : Term)
    (k : Term → Term) : Term :=
  match C with
  | .skip => k current
  | .x _ =>
      .app (.lam .lin .qubit (k current))
        (.app (.prim .x) (.var .lin 0))
  | .h _ =>
      .app (.lam .lin .qubit (k current))
        (.app (.prim .h) (.var .lin 0))
  | .t _ =>
      .app (.lam .lin .qubit (k current))
        (.app (.prim .t) (.var .lin 0))
  | .ry θ _ =>
      let angle :=
        match θ with
        | .rational r => r
        | .coin p => p.val
      .app (.lam .lin .qubit (k current))
        (.app (.prim (.ry angle)) (.var .lin 0))
  | .cx _ _ => k current
  | .measure _ _ =>
      .measure (.var .lin 0)
        (.lam .unres .bit (.lam .lin .qubit (k (.var .unres 0))))
  | .reset _ =>
      .app (.lam .lin .qubit (k current))
        (.app (.prim .reset) (.var .lin 0))
  | .store _ e => k (quoteCExpr current e)
  | .seq A B =>
      quoteBody A current (fun next => quoteBody B next k)
  | .branch guard yes no =>
      .ite (quoteCExpr current guard)
        (quoteBody yes current k) (quoteBody no current k)

private def ContinuationTyped (k : Term → Term) : Prop :=
  ∀ (Γ : List Ty) (n : Nat) (current : Term),
    (∀ m, HasType (.bit :: Γ) (unused m) current .bit) →
    HasType (.bit :: Γ) (liveQubit n) (k current)
      (.tensor .qubit .bit)

private theorem gateArg_typed (Γ : List Ty) (n : Nat) (p : Prim)
    (hp : primTy p = .arrow .lin .qubit .qubit) :
    HasType Γ (liveQubit n)
      (.app (.prim p) (.var .lin 0)) .qubit := by
  apply HasType.appL (split_live_right n)
  · simpa [hp] using
      (HasType.prim (Γ := Γ) (Δ := unused (n + 1)) (p := p)
        (allNone_unused (n + 1)))
  · exact typed_live_var Γ n

private theorem quoteBody_typed {C : Command 1 1}
    (hC : C.Quotable) {k : Term → Term}
    (hk : ContinuationTyped k) :
    ∀ (Γ : List Ty) (n : Nat) (current : Term),
      (∀ m, HasType (.bit :: Γ) (unused m) current .bit) →
      HasType (.bit :: Γ) (liveQubit n) (quoteBody C current k)
        (.tensor .qubit .bit) := by
  induction hC generalizing k with
  | skip =>
      intro Γ n current hcurrent
      exact hk Γ n current hcurrent
  | x =>
      intro Γ n current hcurrent
      apply HasType.appL (split_live_right n)
      · apply HasType.lamL
        exact hk Γ (n + 1) current hcurrent
      · exact gateArg_typed (.bit :: Γ) n .x rfl
  | h =>
      intro Γ n current hcurrent
      apply HasType.appL (split_live_right n)
      · apply HasType.lamL
        exact hk Γ (n + 1) current hcurrent
      · exact gateArg_typed (.bit :: Γ) n .h rfl
  | t =>
      intro Γ n current hcurrent
      apply HasType.appL (split_live_right n)
      · apply HasType.lamL
        exact hk Γ (n + 1) current hcurrent
      · exact gateArg_typed (.bit :: Γ) n .t rfl
  | ry =>
      intro Γ n current hcurrent
      apply HasType.appL (split_live_right n)
      · apply HasType.lamL
        exact hk Γ (n + 1) current hcurrent
      · exact gateArg_typed (.bit :: Γ) n (.ry _) rfl
  | measure =>
      intro Γ n current hcurrent
      apply HasType.measure (split_live_left n)
      · exact typed_live_var (.bit :: Γ) n
      · apply HasType.lamU (by rfl) (allNone_unused (n + 1))
        apply HasType.lamL
        apply hk (.bit :: Γ) (n + 1) (.var .unres 0)
        intro m
        exact typed_bit_var (.bit :: Γ) m
  | reset =>
      intro Γ n current hcurrent
      apply HasType.appL (split_live_right n)
      · apply HasType.lamL
        exact hk Γ (n + 1) current hcurrent
      · exact gateArg_typed (.bit :: Γ) n .reset rfl
  | store =>
      intro Γ n current hcurrent
      apply hk Γ n (quoteCExpr current ‹Composer.CExpr 1›)
      exact quoteCExpr_typed hcurrent
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

/-- The closed source type of one-wire, one-bit canonical quotations. -/
def quotationTy : Ty :=
  .arrow .unres .bit
    (.arrow .lin .qubit (.tensor .qubit .bit))

/-- Canonical lambda quotation.  The classical slot is bound unrestrictedly
and the quantum wire is bound linearly. -/
def quote (C : Command 1 1) : Term :=
  .lam .unres .bit <|
    .lam .lin .qubit <|
      quoteBody C (.var .unres 0)
        (fun current => .pair (.var .lin 0) current)

/-- Every supported command in the exact one-wire/one-bit fragment has a
well-typed canonical lambda quotation. -/
theorem quote_typed {C : Command 1 1} (hC : C.Quotable) :
    HasType [] [] C.quote quotationTy := by
  apply HasType.lamU (by rfl) trivial
  apply HasType.lamL
  apply quoteBody_typed hC
  · intro Γ n current hcurrent
    exact HasType.pair (split_live_left n)
      (typed_live_var (.bit :: Γ) n) (hcurrent (n + 1))
  · intro m
    exact typed_bit_var [] m

/-- A term in the canonical compilable fragment.  The proof field certifies
both source typing (via `quote_typed`) and the static `cx` side condition. -/
structure Quotation where
  command : Command 1 1
  quotable : command.Quotable

namespace Quotation

/-- The actual linear lambda term represented by a certified quotation. -/
def term (Q : Quotation) : Term :=
  Q.command.quote

theorem typing (Q : Quotation) :
    HasType [] [] Q.term quotationTy :=
  quote_typed Q.quotable

/-- Term-to-command compilation, total on the certified canonical fragment. -/
def compile (Q : Quotation) : Command 1 1 :=
  Q.command

/-- Command-to-term reflection. -/
def reflect (C : Command 1 1) (hC : C.Quotable) : Quotation :=
  ⟨C, hC⟩

/-- Reflection followed by compilation is exact, preserving the pre-existing
circuit-to-circuit roundtrip rather than merely normalizing it. -/
@[simp] theorem compile_reflect (C : Command 1 1) (hC : C.Quotable) :
    (reflect C hC).compile = C :=
  rfl

/-- Compilation followed by reflection returns the same canonical term. -/
@[simp] theorem reflect_compile_term (Q : Quotation) :
    (reflect Q.compile Q.quotable).term = Q.term :=
  rfl

/-- The ideal CQ meaning of a certified canonical lambda quotation.  At this
stage boundary it is deliberately inherited from the represented command. -/
noncomputable def denote (model : Composer.Model 1 1)
    (Q : Quotation) : CQ.Sem 1 1 :=
  Q.command.denote model

/-- Compilation preserves ideal CQ denotation. -/
theorem denote_compile (model : Composer.Model 1 1) (Q : Quotation) :
    CQ.Eq (Q.denote model) (Q.compile.denote model) :=
  CQ.Eq.refl _

/-- Reflection preserves ideal CQ denotation. -/
theorem denote_reflect (model : Composer.Model 1 1)
    (C : Command 1 1) (hC : C.Quotable) :
    CQ.Eq ((reflect C hC).denote model) (C.denote model) :=
  CQ.Eq.refl _

/-- A command context observes its hole through sequencing and branching. -/
inductive Context where
  | hole
  | seqLeft : Context → Command 1 1 → Context
  | seqRight : Command 1 1 → Context → Context
  | branchYes : Composer.CExpr 1 → Context → Command 1 1 → Context
  | branchNo : Composer.CExpr 1 → Command 1 1 → Context → Context

def Context.plug : Context → Command 1 1 → Command 1 1
  | .hole, C => C
  | .seqLeft K B, C => .seq (K.plug C) B
  | .seqRight A K, C => .seq A (K.plug C)
  | .branchYes guard K no, C => .branch guard (K.plug C) no
  | .branchNo guard yes K, C => .branch guard yes (K.plug C)

/-- Contextual equivalence is observational equality in every command
context and every ideal Composer model. -/
def ContextuallyEq (Q R : Quotation) : Prop :=
  ∀ (K : Context) (model : Composer.Model 1 1),
    CQ.Eq ((K.plug Q.compile).denote model)
      ((K.plug R.compile).denote model)

/-- Honest denotational/contextual `reflect_compile`: the reflected command is
literally the same canonical program, hence no unsupported source full
abstraction claim is used. -/
theorem reflect_compile (Q : Quotation) :
    ContextuallyEq (reflect Q.compile Q.quotable) Q := by
  intro K model
  exact CQ.Eq.refl _

end Quotation

end Command

end QLambda.Linear
