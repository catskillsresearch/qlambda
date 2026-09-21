/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Composer.Syntax

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

mutual

  /-- Instruction well-formedness at a given structured-loop depth. -/
  inductive Instr.WellFormedAt {q c : ℕ} : Nat → Instr q c → Prop
    | gate {depth g} :
        g.WellFormed →
        Instr.WellFormedAt depth (.gate g)
    | measure {depth qbit cbit} :
        Instr.WellFormedAt depth (.measure qbit cbit)
    | reset {depth qbit} :
        Instr.WellFormedAt depth (.reset qbit)
    | store {depth cbit e} :
        Instr.WellFormedAt depth (.store cbit e)
    | barrier {depth qs} :
        qs.Nodup →
        Instr.WellFormedAt depth (.barrier qs)
    | delay {depth duration qs} :
        qs.Nodup →
        Instr.WellFormedAt depth (.delay duration qs)
    | ite {depth guard yes no} :
        Block.WellFormedAt depth yes →
        Block.WellFormedAt depth no →
        Instr.WellFormedAt depth (.ite guard yes no)
    | switch {depth guard cases} :
        (cases.map Prod.fst).Nodup →
        (∀ branch ∈ cases, Block.WellFormedAt depth branch.2) →
        Instr.WellFormedAt depth (.switch guard cases)
    | forLoop {depth count body} :
        Block.WellFormedAt (depth + 1) body →
        Instr.WellFormedAt depth (.forLoop count body)
    | whileLoop {depth fuel guard body} :
        Block.WellFormedAt (depth + 1) body →
        Instr.WellFormedAt depth (.whileLoop fuel guard body)
    | box {depth label body} :
        label ≠ "" →
        Block.WellFormedAt depth body →
        Instr.WellFormedAt depth (.box label body)
  /-- Every instruction of a block is well formed at the same loop depth. -/
  inductive Block.WellFormedAt {q c : ℕ} : Nat → List (Instr q c) → Prop
    | nil {depth} : Block.WellFormedAt depth []
    | cons {depth i is} :
        Instr.WellFormedAt depth i →
        Block.WellFormedAt depth is →
        Block.WellFormedAt depth (i :: is)

end

/-- A top-level program has no unhandled structured-control transfer. -/
def Program.WellFormed {v q c} (P : Program v q c) : Prop :=
  Block.WellFormedAt 0 P.body

end QLambda.Composer
