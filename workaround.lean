/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

@[expose] public section

/-!
Same statement as `problem.lean`, proved by kernel reduction.
`decide +kernel` adds no axiom.
-/

theorem t : True := by
  decide +kernel
