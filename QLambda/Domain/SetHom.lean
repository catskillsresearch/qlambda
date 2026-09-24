/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Enriched

/-!
# Discrete-order set homs
-/

namespace QLambda.Domain

universe u

/-- An ordinary function equipped with the discrete equality order. -/
structure SetHom (A B : Type u) where
  toFun : A → B

end QLambda.Domain
