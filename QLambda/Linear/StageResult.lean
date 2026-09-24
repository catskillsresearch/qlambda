/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.StagedValue

/-!
# Internal staging-pass results
-/

namespace QLambda.Linear

namespace Command

/-- Omit administrative skips while retaining source evaluation order. -/
def andThen {q c : ℕ} (A B : Command q c) : Command q c :=
  match A, B with
  | .skip, B => B
  | A, .skip => A
  | A, B => .seq A B

end Command

/-- Internal output of one staging pass. -/
structure StageResult (q c : ℕ) where
  value : StagedValue q c
  command : Command q c
  regs : RegFile q c

namespace StageResult

def pure {q c : ℕ} (ρ : RegFile q c) (V : StagedValue q c) :
    StageResult q c :=
  ⟨V, .skip, ρ⟩

def prepend {q c : ℕ} (A : Command q c) (r : StageResult q c) :
    StageResult q c :=
  { r with command := A.andThen r.command }

end StageResult

end QLambda.Linear
