/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.PseudoRepresentable

/-!
# Pseudo-representable bases
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped ComplexOrder MatrixOrder

namespace SuperoperatorModule

universe u

/-- A countable generalized basis whose coefficient objects are
pseudo-representable modules. -/
structure PseudoBasis (M : Module.{u}) where
  Index : Type
  countableIndex : Countable Index
  coeff : Index → PseudoRepresentable.{u}
  ket : ∀ i, Hom (coeff i).module M
  bra : ∀ i, Hom M (coeff i).module
  resolves :
    Hom.HasSum
      (fun i : Index => Hom.comp (ket i) (bra i))
      (Hom.id M)

attribute [instance] PseudoBasis.countableIndex

/-- A positive-dimensional representable has the canonical one-coordinate
pseudo-basis.  This is the basic source constructor required by the
biorthogonal presentation; unlike the unrestricted `Basis` wrapper, its
coefficient carries the hereditary and bounded pseudo-representability
witnesses. -/
noncomputable def representablePseudoBasis (A : ℕ) (hA : 0 < A) :
    PseudoBasis (representable A) where
  Index := PUnit
  countableIndex := inferInstance
  coeff := fun _ => PseudoRepresentable.representable A hA
  ket := fun _ => Hom.id _
  bra := fun _ => Hom.id _
  resolves := by
    have h := Hom.hasSum_singleton (Hom.id (representable A))
    convert h using 1
    funext i
    apply Hom.ext
    intro n x
    rfl

namespace PseudoBasis

/-- Matrix coefficient of a module morphism between based modules. -/
def coefficient {M N : Module.{u}} (bM : PseudoBasis M)
    (bN : PseudoBasis N) (f : Hom M N)
    (i : bM.Index) (j : bN.Index) :
    Hom (bM.coeff i).module (bN.coeff j).module :=
  Hom.comp (bN.bra j) (Hom.comp f (bM.ket i))

/-- The rank-one module map induced by one matrix entry. -/
def matrixTerm {M N : Module.{u}} (bM : PseudoBasis M)
    (bN : PseudoBasis N)
    (entry : ∀ i j,
      Hom (bM.coeff i).module (bN.coeff j).module)
    (p : Σ _ : bM.Index, bN.Index) : Hom M N :=
  Hom.comp (bN.ket p.2)
    (Hom.comp (entry p.1 p.2) (bM.bra p.1))

end PseudoBasis

end SuperoperatorModule

end QLambda.Domain.Presheaf
