/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Composer.CircuitSyntax

/-!
# Fixed-register Composer programs
-/

namespace QLambda

namespace Composer

/-- One complete fixed-register circuit. -/
structure Program (v : Version) (q c : ℕ) where
  body : List (Instr q c)

end Composer

end QLambda
