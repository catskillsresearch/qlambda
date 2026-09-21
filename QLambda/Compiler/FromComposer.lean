/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Source.Syntax

/-!
# Total Composer-to-qλ embedding

Every frozen Composer instruction embeds as one `emit`. A block embeds as a
right-associated source sequence. This direction is structural and total; it
does not guess high-level choice constructs from circuit patterns.
-/

namespace QLambda.Compiler

def embedInstr {q c : ℕ} (i : Composer.Instr q c) : Source.Command q c :=
  .emit i

def embed {q c : ℕ} : List (Composer.Instr q c) → Source.Command q c
  | [] => .skip
  | i :: is => .seq (embedInstr i) (embed is)

@[simp] theorem embed_nil {q c : ℕ} :
    embed ([] : List (Composer.Instr q c)) = .skip :=
  rfl

@[simp] theorem embed_cons {q c : ℕ} (i : Composer.Instr q c)
    (is : List (Composer.Instr q c)) :
    embed (i :: is) = .seq (.emit i) (embed is) :=
  rfl

end QLambda.Compiler
