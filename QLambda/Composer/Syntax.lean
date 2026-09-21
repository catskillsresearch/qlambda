/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Data.Fin.Basic

/-!
# Frozen IBM Composer / OpenQASM circuit syntax

This is the versioned, first-order target syntax used by the verified
translation.  It models one circuit with fixed quantum and classical
registers.  It is not the Qiskit Python API.

The initial version intentionally uses a generic gate record: the versioned
operation manifest, rather than the inductive datatype, decides which gate
names and arities are accepted.  Control loops carry a static iteration bound,
matching the compiler's finite-circuit requirement.
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

/-- OpenQASM gate modifiers supported by the frozen target. -/
inductive Modifier where
  | ctrl : Nat → Modifier
  | inv
  | pow : Int → Modifier
  deriving DecidableEq, Repr

/-- A gate occurrence. Parameters are retained as normalized OpenQASM text.
Their numerical interpretation is supplied by a `Composer.Model`. -/
structure GateApp (q : ℕ) where
  name : String
  params : List String := []
  qubits : List (Fin q)
  modifiers : List Modifier := []
  deriving DecidableEq, Repr

/-- Instructions accepted by the versioned circuit container.

`whileLoop fuel` is the statically bounded Composer fragment. `break` and
`continue` are represented explicitly and are interpreted by the block
semantics only inside a loop. -/
inductive Instr (q c : ℕ) where
  | gate : GateApp q → Instr q c
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

/-- One complete fixed-register circuit. -/
structure Program (v : Version) (q c : ℕ) where
  body : List (Instr q c)

/-- Manifest entry used to validate generic gates. -/
structure GateSpec where
  name : String
  qubits : Nat
  params : Nat
  deriving DecidableEq, Repr

/-- Frozen built-in gate manifest for the first Composer target. -/
def builtinManifest : List GateSpec :=
  [ ⟨"id", 1, 0⟩, ⟨"x", 1, 0⟩, ⟨"y", 1, 0⟩, ⟨"z", 1, 0⟩,
    ⟨"h", 1, 0⟩, ⟨"s", 1, 0⟩, ⟨"sdg", 1, 0⟩,
    ⟨"t", 1, 0⟩, ⟨"tdg", 1, 0⟩,
    ⟨"rx", 1, 1⟩, ⟨"ry", 1, 1⟩, ⟨"rz", 1, 1⟩,
    ⟨"p", 1, 1⟩, ⟨"u", 1, 3⟩,
    ⟨"cx", 2, 0⟩, ⟨"cy", 2, 0⟩, ⟨"cz", 2, 0⟩,
    ⟨"ch", 2, 0⟩, ⟨"swap", 2, 0⟩, ⟨"ecr", 2, 0⟩,
    ⟨"ccx", 3, 0⟩, ⟨"cswap", 3, 0⟩ ]

end Composer

end QLambda
