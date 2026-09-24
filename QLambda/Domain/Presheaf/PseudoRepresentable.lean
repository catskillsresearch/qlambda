/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.Generated

/-!
# Pseudo-representable coefficients
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

end SuperoperatorModule

end QLambda.Domain.Presheaf
