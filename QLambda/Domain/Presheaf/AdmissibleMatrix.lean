/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.PseudoBasis

/-!
# Admissible matrices over pseudo-representable bases
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped ComplexOrder MatrixOrder

namespace SuperoperatorModule

universe u

namespace PseudoBasis

/-- A CP matrix is admissible precisely when its induced countable family of
rank-one module maps has a specified sum.  Keeping the sum as data avoids
hiding a convergence premise behind choice. -/
structure AdmissibleMatrix {M N : Module.{u}}
    (bM : PseudoBasis M) (bN : PseudoBasis N) where
  entry :
    ∀ i j, Hom (bM.coeff i).module (bN.coeff j).module
  total : Hom M N
  hasSum :
    Hom.HasSum (matrixTerm bM bN entry) total

/-- Every module map has its canonical admissible matrix. -/
noncomputable def matrixOfHom {M N : Module.{u}}
    (bM : PseudoBasis M) (bN : PseudoBasis N)
    (f : Hom M N) : AdmissibleMatrix bM bN where
  entry := bM.coefficient bN f
  total := f
  hasSum := by
    intro n x
    apply
      ((N.obj n).summation.flatten
        (fun i j =>
          (matrixTerm bM bN
            (bM.coefficient bN f) ⟨i, j⟩).app n x)
        (f.app n x)).mpr
    refine ⟨fun i => f.app n ((bM.ket i).app n ((bM.bra i).app n x)),
      ?_, ?_⟩
    · intro i
      simpa [matrixTerm, coefficient, Hom.comp_app] using
        bN.resolves n
          (f.app n ((bM.ket i).app n ((bM.bra i).app n x)))
    · exact f.map_sum (bM.resolves n x)

@[simp]
theorem matrixOfHom_total {M N : Module.{u}}
    (bM : PseudoBasis M) (bN : PseudoBasis N) (f : Hom M N) :
    (matrixOfHom bM bN f).total = f :=
  rfl

/-- Identity matrix, represented canonically by the identity module map. -/
noncomputable def AdmissibleMatrix.identity {M : Module.{u}}
    (bM : PseudoBasis M) : AdmissibleMatrix bM bM :=
  matrixOfHom bM bM (Hom.id M)

/-- Composition of admissible matrices.  Canonicalization through the total
module maps is essential: for generalized bases, an arbitrary displayed
matrix is not unique even when its induced morphism is. -/
noncomputable def AdmissibleMatrix.comp
    {L M N : Module.{u}}
    {bL : PseudoBasis L} {bM : PseudoBasis M}
    {bN : PseudoBasis N}
    (g : AdmissibleMatrix bM bN)
    (f : AdmissibleMatrix bL bM) :
    AdmissibleMatrix bL bN :=
  matrixOfHom bL bN (Hom.comp g.total f.total)

@[simp]
theorem AdmissibleMatrix.comp_total
    {L M N : Module.{u}}
    {bL : PseudoBasis L} {bM : PseudoBasis M}
    {bN : PseudoBasis N}
    (g : AdmissibleMatrix bM bN)
    (f : AdmissibleMatrix bL bM) :
    (g.comp f).total = Hom.comp g.total f.total :=
  rfl

@[simp]
theorem AdmissibleMatrix.identity_comp
    {M N : Module.{u}} {bM : PseudoBasis M} {bN : PseudoBasis N}
    (f : AdmissibleMatrix bM bN) :
    ((AdmissibleMatrix.identity bN).comp f).total = f.total := by
  simp [AdmissibleMatrix.comp, AdmissibleMatrix.identity]

@[simp]
theorem AdmissibleMatrix.comp_identity
    {M N : Module.{u}} {bM : PseudoBasis M} {bN : PseudoBasis N}
    (f : AdmissibleMatrix bM bN) :
    (f.comp (AdmissibleMatrix.identity bM)).total = f.total := by
  simp [AdmissibleMatrix.comp, AdmissibleMatrix.identity]

@[simp]
theorem AdmissibleMatrix.comp_assoc
    {K L M N : Module.{u}}
    {bK : PseudoBasis K} {bL : PseudoBasis L}
    {bM : PseudoBasis M} {bN : PseudoBasis N}
    (h : AdmissibleMatrix bM bN)
    (g : AdmissibleMatrix bL bM)
    (f : AdmissibleMatrix bK bL) :
    ((h.comp g).comp f).total = (h.comp (g.comp f)).total := by
  simp [AdmissibleMatrix.comp, Hom.comp_assoc]

end PseudoBasis

end SuperoperatorModule

end QLambda.Domain.Presheaf
