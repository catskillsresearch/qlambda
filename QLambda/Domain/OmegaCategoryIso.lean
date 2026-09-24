/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.OmegaCategory

/-!
# Isomorphisms in an ωCPO-enriched category
-/

namespace QLambda.Domain

universe u v

namespace OmegaCategory

/-- Isomorphisms in an enriched category. -/
structure Iso (C : OmegaCategory) (A B : C.Obj) where
  hom : C.Hom A B
  inv : C.Hom B A
  hom_inv : C.comp hom inv = C.id
  inv_hom : C.comp inv hom = C.id

end OmegaCategory

end QLambda.Domain
