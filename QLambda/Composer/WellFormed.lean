/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Composer.Syntax

@[expose] public section

/-!
# Static well-formedness of frozen Composer circuits

`Fin` indices enforce register bounds intrinsically. This judgment adds
distinct CX operands and structured control checks. `break` and `continue`
have no constructors here: the verified normalized core rejects them.
-/

namespace QLambda.Composer

/-- Static gate side conditions not enforced by `Fin` indices. -/
def Gate.WellFormed {q : ℕ} : Gate q → Prop
  | .cx control target => control ≠ target
  | _ => True

/-- Which judgment a `WellFormedAt` constructor inhabits. -/
inductive WFArm where
  | instr
  | block

/-- Payload of one `WellFormedAt` arm. -/
abbrev WFTarget (q c : ℕ) : WFArm → Type
  | .instr => Instr q c
  | .block => List (Instr q c)

/-- Instruction and block well-formedness at a structured-loop depth.

The two judgments mention each other, including through the `switch`
quantifier. They are one inductive indexed by `WFArm`, rather than a mutual
block. -/
inductive WellFormedAt {q c : ℕ} : (arm : WFArm) → Nat → WFTarget q c arm → Prop where
  | gate {depth g} :
      g.WellFormed →
      WellFormedAt .instr depth (.gate g)
  | measure {depth qbit cbit} :
      WellFormedAt .instr depth (.measure qbit cbit)
  | reset {depth qbit} :
      WellFormedAt .instr depth (.reset qbit)
  | store {depth cbit e} :
      WellFormedAt .instr depth (.store cbit e)
  | barrier {depth qs} :
      qs.Nodup →
      WellFormedAt .instr depth (.barrier qs)
  | delay {depth duration qs} :
      qs.Nodup →
      WellFormedAt .instr depth (.delay duration qs)
  | ite {depth guard yes no} :
      WellFormedAt .block depth yes →
      WellFormedAt .block depth no →
      WellFormedAt .instr depth (.ite guard yes no)
  | switch {depth guard cases} :
      (cases.map Prod.fst).Nodup →
      (∀ branch ∈ cases, WellFormedAt .block depth branch.2) →
      WellFormedAt .instr depth (.switch guard cases)
  | forLoop {depth count body} :
      WellFormedAt .block (depth + 1) body →
      WellFormedAt .instr depth (.forLoop count body)
  | whileLoop {depth fuel guard body} :
      WellFormedAt .block (depth + 1) body →
      WellFormedAt .instr depth (.whileLoop fuel guard body)
  | box {depth label body} :
      label ≠ "" →
      WellFormedAt .block depth body →
      WellFormedAt .instr depth (.box label body)
  | nil {depth} :
      WellFormedAt .block depth []
  | cons {depth i is} :
      WellFormedAt .instr depth i →
      WellFormedAt .block depth is →
      WellFormedAt .block depth (i :: is)

/-- Instruction well-formedness at a given structured-loop depth. -/
abbrev Instr.WellFormedAt {q c : ℕ} (depth : Nat) (i : Instr q c) : Prop :=
  QLambda.Composer.WellFormedAt WFArm.instr depth i

/-- Every instruction of a block is well formed at the same loop depth. -/
abbrev Block.WellFormedAt {q c : ℕ} (depth : Nat) (is : List (Instr q c)) : Prop :=
  QLambda.Composer.WellFormedAt WFArm.block depth is

/-- A top-level program has no unhandled structured-control transfer. -/
def Program.WellFormed {v q c} (P : Program v q c) : Prop :=
  Block.WellFormedAt 0 P.body

end QLambda.Composer
