/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import QLambda.Composer.Probability

/-!
# Frozen IBM Composer / OpenQASM inductive syntax
-/

namespace QLambda

namespace Composer

/-- External syntax contract frozen for this development. -/
inductive Version where
  | openQASM3_0_ibmComposer_2026_09
  deriving DecidableEq, Repr

/-- Classical Boolean expressions over the fixed classical register. -/
inductive CExpr (c : ℕ) where
  | lit : Bool → CExpr c
  | bit : Fin c → CExpr c
  | not : CExpr c → CExpr c
  | and : CExpr c → CExpr c → CExpr c
  | or : CExpr c → CExpr c → CExpr c
  | xor : CExpr c → CExpr c → CExpr c
  deriving DecidableEq, Repr

namespace CExpr

/-- Evaluate a classical expression in a finite bit store. -/
def eval {c : ℕ} : CExpr c → (Fin c → Bool) → Bool
  | .lit b, _ => b
  | .bit i, s => s i
  | .not e, s => !(eval e s)
  | .and e₁ e₂, s => eval e₁ s && eval e₂ s
  | .or e₁ e₂, s => eval e₁ s || eval e₂ s
  | .xor e₁ e₂, s => Bool.xor (eval e₁ s) (eval e₂ s)

end CExpr
/-- Typed angle expressions admitted by the normalized target. -/
inductive AngleExpr where
  | rational : ℚ → AngleExpr
  /-- `2 * acos (sqrt p)`, so RY followed by Z measurement returns zero
  with probability `p`. -/
  | coin : Probability → AngleExpr
  deriving DecidableEq, Repr

namespace AngleExpr

/-- Real-valued ideal interpretation of an angle expression. -/
noncomputable def eval : AngleExpr → ℝ
  | .rational r => r
  | .coin p => 2 * Real.arccos (Real.sqrt p.real)

end AngleExpr

/-- Typed gates in the verified normalized Composer core. -/
inductive Gate (q : ℕ) where
  | x : Fin q → Gate q
  | h : Fin q → Gate q
  | t : Fin q → Gate q
  | ry : AngleExpr → Fin q → Gate q
  | cx : Fin q → Fin q → Gate q
  deriving DecidableEq, Repr

namespace Gate

/-- Rename wires while preserving gate structure. -/
def mapWires {q q' : ℕ} (f : Fin q → Fin q') : Gate q → Gate q'
  | .x w => .x (f w)
  | .h w => .h (f w)
  | .t w => .t (f w)
  | .ry θ w => .ry θ (f w)
  | .cx control target => .cx (f control) (f target)

end Gate

/-- Instructions accepted by the versioned circuit container.

`whileLoop fuel` is the statically bounded Composer fragment. `break` and
`continue` remain representable for imported syntax but are rejected by the
normalized-core well-formedness judgment. -/
inductive Instr (q c : ℕ) where
  | gate : Gate q → Instr q c
  | measure : Fin q → Fin c → Instr q c
  | reset : Fin q → Instr q c
  | store : Fin c → CExpr c → Instr q c
  | barrier : List (Fin q) → Instr q c
  | delay : Nat → List (Fin q) → Instr q c
  | ite : CExpr c → List (Instr q c) → List (Instr q c) → Instr q c
  | switch : CExpr c → List (Bool × List (Instr q c)) → Instr q c
  | forLoop : Nat → List (Instr q c) → Instr q c
  | whileLoop : Nat → CExpr c → List (Instr q c) → Instr q c
  | box : String → List (Instr q c) → Instr q c
  | break
  | continue
  deriving Nonempty

end Composer

end QLambda
