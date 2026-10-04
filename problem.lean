/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

@[expose] public section

/-!
Smallest proof the Lean kernel accepts and `con-ron --verified` declines.
`native_decide` adds an axiom `decide True = true`.
-/

theorem t : True := by
  native_decide
