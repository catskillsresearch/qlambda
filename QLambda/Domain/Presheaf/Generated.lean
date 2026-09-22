/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Yoneda

/-!
# Basis-generated superoperator modules

This file formalizes the generalized basis equation used by the
Tsukada--Asada route and shows that representables carry such a basis.  Since
the coefficient modules below are unrestricted, this wrapper alone is not a
subcategory restriction (every module has its identity one-element basis).
`ClosedGenerated.lean` adds an actual generated coefficient restriction.
Neither class is the paper's classical subcategory: double-dual reflexivity is
an additional requirement.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u

/-- A countable dual basis.  Coefficients are themselves concrete specialized
modules, and the resolution equation uses the pointwise partial-sum relation
on natural transformations. -/
structure Basis (M : Module.{u}) where
  Index : Type
  countableIndex : Countable Index
  coeff : Index → Module.{u}
  ket : ∀ i, Hom (coeff i) M
  bra : ∀ i, Hom M (coeff i)
  resolves :
    Hom.HasSum
      (fun i : Index => Hom.comp (ket i) (bra i))
      (Hom.id M)

attribute [instance] Basis.countableIndex

/-- A specialized module together with an exhibited generalized countable
basis.  This data is useful for coefficient calculations but is not by itself
a generated-subcategory predicate. -/
structure BasisGenerated where
  module : Module.{u}
  basis : Basis module

/-- Every representable has the one-element identity basis. -/
noncomputable def representableBasis (A : ℕ) : Basis (representable A) where
  Index := PUnit
  countableIndex := inferInstance
  coeff := fun _ => representable A
  ket := fun _ => Hom.id _
  bra := fun _ => Hom.id _
  resolves := by
    have h :
        Hom.HasSum
          (fun _ : PUnit => Hom.id (representable A))
          (Hom.id (representable A)) :=
      Hom.hasSum_singleton _
    simpa using h

/-- A representable as a basis-generated object. -/
noncomputable def generatedRepresentable (A : ℕ) :
    BasisGenerated.{0} where
  module := representable A
  basis := representableBasis A

/-- Matrix coefficient of a map relative to two chosen bases. -/
def Basis.coefficient {M : Module.{u}} {N : Module.{u}}
    (bM : Basis M) (bN : Basis N)
    (f : Hom M N) (i : bM.Index) (j : bN.Index) :
    Hom (bM.coeff i) (bN.coeff j) :=
  Hom.comp (bN.bra j) (Hom.comp f (bM.ket i))

@[simp]
theorem Basis.coefficient_id {M : Module.{u}} (b : Basis M)
    (i j) :
    b.coefficient b (Hom.id M) i j =
      Hom.comp (b.bra j) (b.ket i) := by
  ext n x
  rfl

/-- Coefficients respect composition before summing over the intermediate
basis.  This equation is the concrete algebraic part of matrix composition;
existence of the intermediate countable sum is a separate convergence
obligation. -/
theorem Basis.coefficient_comp {L M N : Module.{u}}
    (bL : Basis L) (_bM : Basis M)
    (bN : Basis N) (g : Hom M N) (f : Hom L M)
    (i : bL.Index) (j : bN.Index) :
    bL.coefficient bN (Hom.comp g f) i j =
      Hom.comp (bN.bra j)
        (Hom.comp g (Hom.comp f (bL.ket i))) := by
  ext n x
  rfl

/-- The representable basis coefficient is exactly the original Yoneda map. -/
@[simp]
theorem representable_coefficient {A B : ℕ}
    (f : Superoperator A B) :
    (representableBasis A).coefficient (representableBasis B)
        (yonedaMap f) PUnit.unit PUnit.unit =
      yonedaMap f := by
  ext n x
  rfl

end SuperoperatorModule

end QLambda.Domain.Presheaf
