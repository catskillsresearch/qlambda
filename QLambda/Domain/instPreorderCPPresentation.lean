/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.CPPresentation

/-!
# Instance `instPreorderCPPresentation`
-/

namespace QLambda.Domain

open scoped BigOperators ComplexConjugate MatrixOrder

noncomputable instance instPreorderCPPresentation (n m : ℕ) :
    Preorder (CPPresentation n m) where
  le K L := KrausFamily.ResidualRefines K.kraus L.kraus
  lt K L :=
    KrausFamily.ResidualRefines K.kraus L.kraus ∧
      ¬ KrausFamily.ResidualRefines L.kraus K.kraus
  le_refl K := KrausFamily.residualRefines_refl K.kraus
  le_trans _ _ _ := KrausFamily.residualRefines_trans
  lt_iff_le_not_ge _ _ := Iff.rfl

end QLambda.Domain
