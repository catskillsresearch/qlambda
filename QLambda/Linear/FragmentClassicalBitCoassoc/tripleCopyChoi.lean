/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentClassicalBitChannels

/-!
# Triple-copy classical Choi formula
-/

namespace QLambda.Linear

/-- Closed Choi formula for classical triple copy on `Fin 8 × Fin 2`. -/
def tripleCopyChoi (a b : Fin 8) (i j : Fin 2) : ℂ :=
  if i = j ∧ a.val = i.val * 7 ∧ b.val = j.val * 7 then 1 else 0

end QLambda.Linear
