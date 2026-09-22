/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Generated

/-!
# Pseudo-representable coefficients and admissible matrices

This file formalizes the object-level hypotheses used by the matrix
presentation of the Tsukada--Asada superoperator-module model.

A pseudo-representable coefficient is not merely a module with a chosen
basis.  It is exhibited as a hereditary submodule of `CPMap (-, ℓ)`, is
uniformly bounded in input effect, and contains a positive multiple of the
identity.  A pseudo-representable basis resolves the identity through such
coefficients.  Matrices are admissible only when their induced countable
family of rank-one module maps has a sum.
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped ComplexOrder MatrixOrder

namespace SuperoperatorModule

universe u

/-- A module exhibited as a hereditary, uniformly bounded submodule of
unrestricted completely positive maps into one finite-dimensional object. -/
structure PseudoRepresentable where
  module : Module.{u}
  dimension : ℕ
  dimension_pos : 0 < dimension
  embed :
    ∀ n, (module.obj n).Carrier → CPMap n dimension
  embed_injective :
    ∀ n, Function.Injective (embed n)
  embed_zero :
    ∀ n, embed n 0 = 0
  embed_act :
    ∀ {m n} (x : (module.obj n).Carrier)
      (f : Superoperator m n),
      embed m (module.act x f) =
        CPMap.comp (embed n x) f.cp
  embed_sum :
    ∀ {ι : Type} [Countable ι] {n}
      {f : ι → (module.obj n).Carrier} {x : (module.obj n).Carrier},
      (module.obj n).HasSum f x →
        _root_.HasSum (fun i => (embed n (f i)).choi)
          (embed n x).choi
  hereditary :
    ∀ {n} (x : (module.obj n).Carrier) (Φ : CPMap n dimension),
      Φ ≤ embed n x →
        ∃ y : (module.obj n).Carrier, embed n y = Φ
  bound : NNReal
  bound_pos : 0 < bound
  bounded :
    ∀ n (x : (module.obj n).Carrier),
      (embed n x).effect ≤
        (bound : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
  radius : NNReal
  radius_pos : 0 < radius
  pseudoUniversal :
    ∃ x : (module.obj dimension).Carrier,
      embed dimension x = radius • CPMap.identity dimension

namespace PseudoRepresentable

/-- The exhibited inclusion into the ambient unrestricted CPM module. -/
def toAmbient (L : PseudoRepresentable.{u}) :
    Hom L.module (cpmModule L.dimension) where
  app := L.embed
  map_zero := L.embed_zero
  map_sum := fun h => L.embed_sum h
  naturality := by
    intro m n x f
    exact L.embed_act x f

theorem toAmbient_injective (L : PseudoRepresentable.{u}) (n : ℕ) :
    Function.Injective ((L.toAmbient).app n) :=
  L.embed_injective n

/-- The representable `Q(-, A)` is pseudo-representable inside
`CPMap(-, A)`. -/
noncomputable def representable (A : ℕ) (hA : 0 < A) :
    PseudoRepresentable where
  module := SuperoperatorModule.representable A
  dimension := A
  dimension_pos := hA
  embed := fun _ Φ => Φ.cp
  embed_injective := by
    intro n Φ Ψ h
    exact Superoperator.ext h
  embed_zero := by
    intro n
    rfl
  embed_act := by
    intro m n x f
    exact Superoperator.cp_comp x f
  embed_sum := by
    intro ι _ n f x h
    exact h
  hereditary := by
    intro n x Φ h
    exact ⟨Superoperator.ofLE Φ x h, rfl⟩
  bound := 1
  bound_pos := zero_lt_one
  bounded := by
    intro n x
    simpa using CPMap.effect_le_one_of_trace_nonincreasing
      x.cp x.trace_nonincreasing
  radius := 1
  radius_pos := zero_lt_one
  pseudoUniversal := ⟨Superoperator.identity A, by
    rw [one_smul]
    rfl⟩

end PseudoRepresentable

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

/-- Orthogonality is an optional strengthening of a pseudo-representable
basis; it does not imply diagonal normalization. -/
structure OrthogonalPseudoBasis (M : Module.{u}) where
  basis : PseudoBasis M
  orthogonal :
    ∀ i j, i ≠ j →
      Hom.comp (basis.bra i) (basis.ket j) = 0

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
