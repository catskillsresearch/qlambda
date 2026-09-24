/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.OmegaCartesianClosed
import QLambda.Domain.SymmetricMonoidalClosed

/-!
# Symmetric monoidal closed structure on pointed ωCPOs
-/

namespace QLambda.Domain

universe u

set_option linter.checkUnivs false

open OmegaCategory

/-- The Cartesian tensor also gives the ωCPO category a symmetric
monoidal closed structure. -/
noncomputable def omegaSymmetricMonoidalClosed :
    SymmetricMonoidalClosed (omegaMapCategory.{u}) where
  unit := omegaTerminal
  tensor := omegaProduct
  internalHom := omegaExponential
  tensorMap := fun f g =>
    OmegaMap.pair (f.comp OmegaMap.fst) (g.comp OmegaMap.snd)
  tensorMap_mono_left := by
    intro A B C D g f₁ f₂ h p
    exact ⟨h p.1, le_rfl⟩
  tensorMap_mono_right := by
    intro A B C D f g₁ g₂ h p
    exact ⟨le_rfl, h p.2⟩
  tensorMap_id := by
    intro A B
    apply OmegaMap.ext
    intro p
    exact Prod.eta _
  tensorMap_comp := by
    intro A B C D E F f₂ f₁ g₂ g₁
    apply OmegaMap.ext
    intro p
    rfl
  leftUnitor := fun A =>
    { hom := OmegaMap.snd
      inv :=
        { toFun := fun a => (PUnit.unit, a)
          monotone := fun _ _ h => ⟨le_rfl, h⟩
          map_ωSup := by
            intro c hc
            apply Prod.ext
            · exact (OmegaComplete.ωSup_const PUnit.unit).symm
            · rfl }
      hom_inv := by
        apply OmegaMap.ext
        intro a
        rfl
      inv_hom := by
        apply OmegaMap.ext
        intro p
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · rfl }
  rightUnitor := fun A =>
    { hom := OmegaMap.fst
      inv :=
        { toFun := fun a => (a, PUnit.unit)
          monotone := fun _ _ h => ⟨h, le_rfl⟩
          map_ωSup := by
            intro c hc
            apply Prod.ext
            · rfl
            · exact (OmegaComplete.ωSup_const PUnit.unit).symm }
      hom_inv := by
        apply OmegaMap.ext
        intro a
        rfl
      inv_hom := by
        apply OmegaMap.ext
        intro p
        apply Prod.ext
        · rfl
        · exact Subsingleton.elim _ _ }
  associator := fun A B C =>
    { hom :=
        { toFun := fun p => (p.1.1, (p.1.2, p.2))
          monotone := fun _ _ h =>
            ⟨h.1.1, h.1.2, h.2⟩
          map_ωSup := fun _ _ => rfl }
      inv :=
        { toFun := fun p => ((p.1, p.2.1), p.2.2)
          monotone := fun _ _ h =>
            ⟨⟨h.1, h.2.1⟩, h.2.2⟩
          map_ωSup := fun _ _ => rfl }
      hom_inv := by
        apply OmegaMap.ext
        intro p
        rcases p with ⟨a, b, c⟩
        rfl
      inv_hom := by
        apply OmegaMap.ext
        intro p
        rcases p with ⟨⟨a, b⟩, c⟩
        rfl }
  braiding := fun A B =>
    { hom := OmegaMap.pair OmegaMap.snd OmegaMap.fst
      inv := OmegaMap.pair OmegaMap.snd OmegaMap.fst
      hom_inv := by
        apply OmegaMap.ext
        intro p
        exact Prod.eta _
      inv_hom := by
        apply OmegaMap.ext
        intro p
        exact Prod.eta _ }
  eval := OmegaMap.eval
  curry := OmegaMap.curry
  uncurry := OmegaMap.uncurry
  curry_uncurry := OmegaMap.curry_uncurry
  uncurry_curry := OmegaMap.uncurry_curry
  curry_mono := by
    intro X A B f g h x a
    exact h (x, a)
  curry_ωSup := by
    intro X A B c hc
    apply OmegaMap.ext
    intro x
    apply OmegaMap.ext
    intro a
    rfl

end QLambda.Domain
