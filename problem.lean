/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

@[expose] public section

/-!
Smallest true mutual induction Lean accepts and the toolchain `con-ron --verified` declines.
`I.sw` takes a function returning `B`, and `B.b` takes an `I`, so neither can be defined first.
-/

mutual
  inductive I : Prop where
    | sw : (Nat → B) → I
  inductive B : Prop where
    | b : I → B
end
