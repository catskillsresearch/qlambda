/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Enriched

/-!
# Cartesian closed structure on an enriched category
-/

namespace QLambda.Domain

universe u v

open OmegaCategory

/-- Cartesian closed structure on an enriched category. -/
structure CartesianClosed (C : OmegaCategory.{u, v}) where
  terminal : C.Obj
  product : C.Obj → C.Obj → C.Obj
  exponential : C.Obj → C.Obj → C.Obj
  terminate : {A : C.Obj} → C.Hom A terminal
  fst : {A B : C.Obj} → C.Hom (product A B) A
  snd : {A B : C.Obj} → C.Hom (product A B) B
  pair :
    {X A B : C.Obj} → C.Hom X A → C.Hom X B → C.Hom X (product A B)
  eval :
    {A B : C.Obj} → C.Hom (product (exponential A B) A) B
  curry :
    {X A B : C.Obj} → C.Hom (product X A) B → C.Hom X (exponential A B)
  terminal_unique : ∀ {A : C.Obj} (f : C.Hom A terminal), f = terminate
  fst_pair :
    ∀ {X A B : C.Obj} (f : C.Hom X A) (g : C.Hom X B),
      C.comp fst (pair f g) = f
  snd_pair :
    ∀ {X A B : C.Obj} (f : C.Hom X A) (g : C.Hom X B),
      C.comp snd (pair f g) = g
  pair_eta :
    ∀ {X A B : C.Obj} (f : C.Hom X (product A B)),
      pair (C.comp fst f) (C.comp snd f) = f
  beta :
    ∀ {X A B : C.Obj} (f : C.Hom (product X A) B),
      C.comp eval (pair (C.comp (curry f) fst) snd) = f
  curry_mono :
    ∀ {X A B : C.Obj}, Monotone (@curry X A B)
  curry_ωSup :
    ∀ {X A B : C.Obj} (c : ℕ → C.Hom (product X A) B) (hc : Monotone c),
      curry (OmegaComplete.ωSup c hc) =
        OmegaComplete.ωSup (fun n => curry (c n)) (curry_mono.comp hc)

end QLambda.Domain
