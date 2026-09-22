/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Composer.OpenQASM

/-!
# Parser for the flat OpenQASM interchange fragment

The parser accepts the exact OpenQASM emitted for `x`, `h`, `t`, `ry`, `cx`,
measurement, and reset. Structured control remains represented by the typed
Composer AST; it is deliberately outside this small textual interchange
parser.
-/

namespace QLambda.Composer

private def parseFin (bound : ℕ) (pre : String) (s : String) :
    Option (Fin bound) := do
  if !(s.startsWith (pre ++ "[")) || !(s.endsWith "]") then
    none
  else
    let digits := ((s.drop (pre.length + 1)).toString.dropEnd 1).toString
    let n ← digits.toNat?
    if h : n < bound then some ⟨n, h⟩ else none

private def parseQRef (q : ℕ) : String → Option (Fin q) :=
  parseFin q "q"

private def parseCRef (c : ℕ) : String → Option (Fin c) :=
  parseFin c "c"

private def parseRat (s : String) : Option ℚ :=
  match s.splitOn "/" with
  | [n] => Rat.ofInt <$> n.toInt?
  | [n, d] => do
      let numerator ← n.toInt?
      let denominator ← d.toNat?
      if h : denominator = 0 then none
      else some (Rat.normalize numerator denominator h)
  | _ => none

private def parseAngle (s : String) : Option AngleExpr :=
  if s.startsWith "2*acos(sqrt(" && s.endsWith "))" then do
    let body := ((s.drop 12).toString.dropEnd 2).toString
    let p ← parseRat body
    if h0 : 0 ≤ p then
      if h1 : p ≤ 1 then some (.coin ⟨p, h0, h1⟩) else none
    else none
  else
    .rational <$> parseRat s

private def withoutSemi (s : String) : Option String :=
  if s.endsWith ";" then some (s.dropEnd 1).toString else none

/-- Parse one instruction of the flat interchange fragment. -/
def parseFlatInstr (q c : ℕ) (line : String) : Option (Instr q c) := do
  let s ← withoutSemi line.trimAscii.toString
  match s.splitOn " " with
  | ["x", w] => return .gate (.x (← parseQRef q w))
  | ["h", w] => return .gate (.h (← parseQRef q w))
  | ["t", w] => return .gate (.t (← parseQRef q w))
  | ["reset", w] => return .reset (← parseQRef q w)
  | ["cx", control, target] =>
      if !control.endsWith "," then none
      else
        return .gate (.cx
          (← parseQRef q (control.dropEnd 1).toString)
          (← parseQRef q target))
  | [lhs, "=", "measure", rhs] =>
      return .measure (← parseQRef q rhs) (← parseCRef c lhs)
  | _ =>
      if s.startsWith "ry(" then
        match s.splitOn ") " with
        | [angle, w] =>
            return .gate (.ry
              (← parseAngle (angle.dropPrefix "ry(").toString)
              (← parseQRef q w))
        | _ => none
      else none

private def parseFlatLines (q c : ℕ) :
    List String → Option (List (Instr q c))
  | [] => some []
  | line :: lines => do
      let i ← parseFlatInstr q c line
      let is ← parseFlatLines q c lines
      pure (i :: is)

/-- Parse a complete program emitted by `Program.toOpenQASM` when its body is
in the flat interchange fragment. Register sizes are checked against the
typed result indices. -/
def parseFlatProgram (q c : ℕ) (text : String) :
    Option (Program .openQASM3_0_ibmComposer_2026_09 q c) :=
  match text.splitOn "\n" with
  | version :: includeLine :: qdecl :: cdecl :: body =>
      if version = "OPENQASM 3.0;" ∧
          includeLine = "include \"stdgates.inc\";" ∧
          qdecl = "qubit[" ++ toString q ++ "] q;" ∧
          cdecl = "bit[" ++ toString c ++ "] c;" then do
        let instructions ← parseFlatLines q c body
        pure ⟨instructions⟩
      else none
  | _ => none

end QLambda.Composer
