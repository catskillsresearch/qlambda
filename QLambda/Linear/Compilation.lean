/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.StageResult

/-!
# Proof-carrying first-order compilations
-/

namespace QLambda.Linear

/-- A successful compilation is proof-carrying: source typing, first-order
boundary typing, allocated output resources, and target well-formedness are
all retained independently of the evaluator implementation. -/
structure Compilation (q c : ℕ) (M : Term) where
  sourceTy : Ty
  result : StagedValue q c
  command : Command q c
  finalRegs : RegFile q c
  source_typed : infer [] [] M = some (sourceTy, [])
  result_typed : result.ty = sourceTy
  first_order : Ty.FirstOrder sourceTy
  resources_preserved : result.Respects finalRegs
  command_wellFormed : command.WellFormed

end QLambda.Linear
