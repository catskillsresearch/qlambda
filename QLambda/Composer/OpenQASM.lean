/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Composer.WellFormed

/-!
# OpenQASM 3 presentation

The circuit AST is normative and its denotation is defined separately.
This module is only a deterministic textual export for IBM Composer.
-/

namespace QLambda.Composer

private def comma (xs : List String) : String :=
  String.intercalate ", " xs

private def lines (xs : List String) : String :=
  String.intercalate "\n" xs

private def qref {q : ℕ} (i : Fin q) : String :=
  "q[" ++ toString i.val ++ "]"

private def cref {c : ℕ} (i : Fin c) : String :=
  "c[" ++ toString i.val ++ "]"

def CExpr.toOpenQASM {c : ℕ} : CExpr c → String
  | .lit true => "true"
  | .lit false => "false"
  | .bit i => cref i
  | .not e => "!(" ++ e.toOpenQASM ++ ")"
  | .and e₁ e₂ => "(" ++ e₁.toOpenQASM ++ " && " ++ e₂.toOpenQASM ++ ")"
  | .or e₁ e₂ => "(" ++ e₁.toOpenQASM ++ " || " ++ e₂.toOpenQASM ++ ")"
  | .xor e₁ e₂ => "(" ++ e₁.toOpenQASM ++ " != " ++ e₂.toOpenQASM ++ ")"

def AngleExpr.toOpenQASM : AngleExpr → String
  | .rational r => toString r
  | .coin p => "2*acos(sqrt(" ++ toString p.val ++ "))"

def Gate.toOpenQASM {q : ℕ} : Gate q → String
  | .x w => "x " ++ qref w ++ ";"
  | .h w => "h " ++ qref w ++ ";"
  | .ry θ w => "ry(" ++ θ.toOpenQASM ++ ") " ++ qref w ++ ";"
  | .cx control target => "cx " ++ qref control ++ ", " ++ qref target ++ ";"

mutual

  private partial def blockToOpenQASM {q c : ℕ} : List (Instr q c) → List String
    | [] => []
    | i :: is => instrToOpenQASM i :: blockToOpenQASM is

  private partial def instrToOpenQASM {q c : ℕ} : Instr q c → String
    | .gate g => g.toOpenQASM
    | .measure qbit cbit => cref cbit ++ " = measure " ++ qref qbit ++ ";"
    | .reset qbit => "reset " ++ qref qbit ++ ";"
    | .store cbit e => cref cbit ++ " = " ++ e.toOpenQASM ++ ";"
    | .barrier qs => "barrier " ++ comma (qs.map qref) ++ ";"
    | .delay duration qs =>
        "delay[" ++ toString duration ++ "dt] " ++ comma (qs.map qref) ++ ";"
    | .ite guard yes no =>
        "if (" ++ guard.toOpenQASM ++ ") {\n" ++
          lines (blockToOpenQASM yes) ++
        "\n} else {\n" ++ lines (blockToOpenQASM no) ++ "\n}"
    | .switch guard cases =>
        "switch (" ++ guard.toOpenQASM ++ ") {\n" ++
          lines (cases.map fun branch =>
            "case " ++ toString branch.1 ++ " {\n" ++
              lines (blockToOpenQASM branch.2) ++ "\n}") ++
        "\n}"
    | .forLoop 0 _ => "// zero-iteration for loop"
    | .forLoop (count + 1) body =>
        "for uint _i in [0:" ++ toString count ++ "] {\n" ++
          lines (blockToOpenQASM body) ++ "\n}"
    | .whileLoop fuel guard body =>
        boundedWhileToOpenQASM fuel guard body
    | .box label body =>
        "box { // " ++ label ++ "\n" ++ lines (blockToOpenQASM body) ++ "\n}"
    | .break => "break;"
    | .continue => "continue;"

  /-- Bounded while is exported by finite unrolling, so QASM execution and
  denotation have the same iteration cap. -/
  private partial def boundedWhileToOpenQASM {q c : ℕ} :
      Nat → CExpr c → List (Instr q c) → String
    | 0, _, _ => "// bounded while exhausted"
    | fuel + 1, guard, body =>
        "if (" ++ guard.toOpenQASM ++ ") {\n" ++
          lines (blockToOpenQASM body) ++ "\n" ++
          boundedWhileToOpenQASM fuel guard body ++ "\n}"

end

/-- Export a well-formed normalized program as OpenQASM 3 text. -/
def Program.toOpenQASM {v q c} (P : Program v q c)
    (_hP : P.WellFormed) : String :=
  lines
    [ "OPENQASM 3.0;",
      "include \"stdgates.inc\";",
      "qubit[" ++ toString q ++ "] q;",
      "bit[" ++ toString c ++ "] c;",
      lines (blockToOpenQASM P.body) ]

end QLambda.Composer
