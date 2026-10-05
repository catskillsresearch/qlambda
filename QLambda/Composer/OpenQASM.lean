/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Composer.WellFormed

@[expose] public section

/-!
# OpenQASM 3 presentation

The circuit AST is normative and its denotation is defined separately.
This module is only a deterministic textual export for IBM Composer.
-/

namespace QLambda.Composer

def commaGo (acc : String) : List String → String
  | [] => acc
  | s :: ss => commaGo (acc ++ ", " ++ s) ss

def comma : List String → String
  | [] => ""
  | s :: ss => commaGo s ss

def linesGo (acc : String) : List String → String
  | [] => acc
  | s :: ss => linesGo (acc ++ "\n" ++ s) ss

def lines : List String → String
  | [] => ""
  | s :: ss => linesGo s ss

/-- Decimal digits. `Nat.repr` is hidden behind `implemented_by`, so the kernel
cannot compare it with a string literal. -/
def digitChar : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | 9 => '9'
  | _ => '0'

def natStrGo : Nat → Nat → String
  | 0, _ => ""
  | fuel + 1, n =>
    if n < 10 then String.singleton (digitChar n)
    else natStrGo fuel (n / 10) ++ String.singleton (digitChar (n % 10))

def natStr (n : Nat) : String :=
  natStrGo (n + 1) n

def boolStr : Bool → String
  | true => "true"
  | false => "false"

def qref {q : ℕ} (i : Fin q) : String :=
  "q[" ++ natStr i.val ++ "]"

def cref {c : ℕ} (i : Fin c) : String :=
  "c[" ++ natStr i.val ++ "]"

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
  | .t w => "t " ++ qref w ++ ";"
  | .ry θ w => "ry(" ++ θ.toOpenQASM ++ ") " ++ qref w ++ ";"
  | .cx control target => "cx " ++ qref control ++ ", " ++ qref target ++ ";"

/-- One fuel-indexed recursion. Mutual recursion on the AST is compiled to an
irreducible fixpoint, which the kernel will not unfold. -/
inductive RenderTok (q c : ℕ) where
  | block : List (Instr q c) → RenderTok q c
  | instr : Instr q c → RenderTok q c
  | cases : List (Bool × List (Instr q c)) → RenderTok q c

inductive RenderRes where
  | lines : List String → RenderRes
  | line : String → RenderRes

def unrollWhile (guardText bodyText : String) : Nat → String
  | 0 => "// bounded while exhausted"
  | fuel + 1 =>
      "if (" ++ guardText ++ ") {\n" ++ bodyText ++ "\n" ++
        unrollWhile guardText bodyText fuel ++ "\n}"

def renderGo {q c : ℕ} : Nat → RenderTok q c → RenderRes
  | 0, _ => .lines []
  | _ + 1, .block [] => .lines []
  | fuel + 1, .block (i :: is) =>
    match renderGo fuel (.instr i), renderGo fuel (.block is) with
    | .line s, .lines ss => .lines (s :: ss)
    | _, _ => .lines []
  | _ + 1, .instr (.gate g) => .line g.toOpenQASM
  | _ + 1, .instr (.measure qbit cbit) =>
    .line (cref cbit ++ " = measure " ++ qref qbit ++ ";")
  | _ + 1, .instr (.reset qbit) => .line ("reset " ++ qref qbit ++ ";")
  | _ + 1, .instr (.store cbit e) => .line (cref cbit ++ " = " ++ e.toOpenQASM ++ ";")
  | _ + 1, .instr (.barrier qs) => .line ("barrier " ++ comma (qs.map qref) ++ ";")
  | _ + 1, .instr (.delay duration qs) =>
    .line ("delay[" ++ natStr duration ++ "dt] " ++ comma (qs.map qref) ++ ";")
  | fuel + 1, .instr (.ite guard yes no) =>
    match renderGo fuel (.block yes), renderGo fuel (.block no) with
    | .lines ys, .lines ns =>
      .line ("if (" ++ guard.toOpenQASM ++ ") {\n" ++ lines ys ++
        "\n} else {\n" ++ lines ns ++ "\n}")
    | _, _ => .lines []
  | fuel + 1, .instr (.switch guard cases) =>
    match renderGo fuel (.cases cases) with
    | .lines ss => .line ("switch (" ++ guard.toOpenQASM ++ ") {\n" ++ lines ss ++ "\n}")
    | .line s => .line ("switch (" ++ guard.toOpenQASM ++ ") {\n" ++ s ++ "\n}")
  | _ + 1, .instr (.forLoop 0 _) => .line "// zero-iteration for loop"
  | fuel + 1, .instr (.forLoop (count + 1) body) =>
    match renderGo fuel (.block body) with
    | .lines ss =>
      .line ("for uint _i in [0:" ++ natStr count ++ "] {\n" ++ lines ss ++ "\n}")
    | .line s =>
      .line ("for uint _i in [0:" ++ natStr count ++ "] {\n" ++ s ++ "\n}")
  | fuel + 1, .instr (.whileLoop n guard body) =>
    match renderGo fuel (.block body) with
    | .lines ss => .line (unrollWhile guard.toOpenQASM (lines ss) n)
    | .line s => .line (unrollWhile guard.toOpenQASM s n)
  | fuel + 1, .instr (.box label body) =>
    match renderGo fuel (.block body) with
    | .lines ss => .line ("box { // " ++ label ++ "\n" ++ lines ss ++ "\n}")
    | .line s => .line ("box { // " ++ label ++ "\n" ++ s ++ "\n}")
  | _ + 1, .instr .break => .line "break;"
  | _ + 1, .instr .continue => .line "continue;"
  | _ + 1, .cases [] => .lines []
  | fuel + 1, .cases ((b, body) :: rest) =>
    match renderGo fuel (.block body), renderGo fuel (.cases rest) with
    | .lines ss, .lines more =>
      .lines (("case " ++ boolStr b ++ " {\n" ++ lines ss ++ "\n}") :: more)
    | _, _ => .lines []

noncomputable def instrFuel {q c : ℕ} (i : Instr q c) : Nat :=
  Instr.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat) (motive_4 := fun _ => Nat)
    (fun _ => 4) (fun _ _ => 4) (fun _ => 4) (fun _ _ => 4) (fun _ => 4) (fun _ _ => 4)
    (fun _ _ _ yes no => 4 + yes + no)
    (fun _ _ cases => 4 + cases)
    (fun _ _ body => 4 + body)
    (fun n _ _ body => 4 + n + body)
    (fun _ _ body => 4 + body)
    4 4
    2
    (fun _ _ head tail => 2 + head + tail)
    2
    (fun _ _ head tail => 2 + head + tail)
    (fun _ _ body => 2 + body)
    i

noncomputable def blockFuel {q c : ℕ} : List (Instr q c) → Nat
  | [] => 2
  | i :: is => instrFuel i + blockFuel is + 2

noncomputable def blockToOpenQASM {q c : ℕ} (is : List (Instr q c)) : List String :=
  match renderGo (blockFuel is + 2) (.block is) with
  | .lines ss => ss
  | .line _ => []

noncomputable def instrToOpenQASM {q c : ℕ} (i : Instr q c) : String :=
  match renderGo (instrFuel i + 2) (.instr i) with
  | .line s => s
  | .lines ss => lines ss

/-- Bounded while is exported by finite unrolling, so QASM execution and
denotation have the same iteration cap. -/
noncomputable def boundedWhileToOpenQASM {q c : ℕ} (fuel : Nat) (guard : CExpr c)
    (body : List (Instr q c)) : String :=
  unrollWhile guard.toOpenQASM (lines (blockToOpenQASM body)) fuel

noncomputable def caseBranchesToOpenQASM {q c : ℕ}
    (cases : List (Bool × List (Instr q c))) : List String :=
  match renderGo (cases.foldl (fun n branch => n + blockFuel branch.2 + 2) 2 + 2) (.cases cases) with
  | .lines ss => ss
  | .line _ => []

/-- Render a program.  This proof-free form is also used by the parser's
canonicality check; clients should normally use `Program.toOpenQASM`. -/
noncomputable def Program.renderOpenQASM {v q c} (P : Program v q c) : String :=
  lines
    [ "OPENQASM 3.0;",
      "include \"stdgates.inc\";",
      "qubit[" ++ natStr q ++ "] q;",
      "bit[" ++ natStr c ++ "] c;",
      lines (blockToOpenQASM P.body) ]

/-- Export a well-formed normalized program as OpenQASM 3 text. -/
noncomputable def Program.toOpenQASM {v q c} (P : Program v q c)
    (_hP : P.WellFormed) : String :=
  P.renderOpenQASM

end QLambda.Composer
