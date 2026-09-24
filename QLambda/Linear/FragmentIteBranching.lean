/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentIteBeta

/-!
# Fragment `iteElim` and Route A denotation

Recursive `iteElimFragment`, `routeAFragmentBranching`, and
`FragCert.denote`.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000
open Domain.Presheaf
open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf.SigmaMon
open DayTensor
open scoped ComplexOrder MatrixOrder BigOperators

/-- Transport an `ite` eliminator along a result isomorphism. -/
noncomputable def iteElimCongr {Bit A A' : Module}
    (e : Iso A A')
    (ite : Hom (dayTensor Bit (additiveProduct A A)) A) :
    Hom (dayTensor Bit (additiveProduct A' A')) A' :=
  Hom.comp e.hom
    (Hom.comp ite
      (DayTensor.map (Hom.id Bit)
        (additivePair
          (Hom.comp e.inv (additiveFst A' A'))
          (Hom.comp e.inv (additiveSnd A' A')))))

/-- Lift an eliminator on `N` to one on `[X, N]` via Day closedness. -/
noncomputable def iteElimInternalHom {X N : Module}
    (iteN :
      Hom (dayTensor (representable 2) (additiveProduct N N)) N) :
    Hom
      (dayTensor (representable 2)
        (additiveProduct (dayInternalHom X N) (dayInternalHom X N)))
      (dayInternalHom X N) :=
  let P := dayInternalHom X N
  let pairEval :
      Hom (dayTensor (additiveProduct P P) X) (additiveProduct N N) :=
    additivePair
      (Hom.comp (FragmentContext.dayEval X N)
        (DayTensor.map (additiveFst P P) (Hom.id X)))
      (Hom.comp (FragmentContext.dayEval X N)
        (DayTensor.map (additiveSnd P P) (Hom.id X)))
  let uncurried :
      Hom
        (dayTensor
          (dayTensor (representable 2) (additiveProduct P P)) X)
        N :=
    Hom.comp iteN
      (Hom.comp (DayTensor.map (Hom.id _) pairEval)
        (DayTensor.associator (representable 2) (additiveProduct P P) X))
  dayClosedPresentation.closed
    (dayTensor (representable 2) (additiveProduct P P)) X N uncurried

private noncomputable def castIte {Bit A B : Module}
    (hA : A = B)
    (ite : Hom (dayTensor Bit (additiveProduct A A)) A) :
    Hom (dayTensor Bit (additiveProduct B B)) B := by
  subst hA
  exact ite

/-- Empty combined discard agrees with the closed collapse. -/
theorem combinedAllDiscard_nil (hΓ : CtxUAllBit []) (hΔ : AllNone []) :
    FragmentContext.combinedAllDiscard hΓ hΔ =
      FragmentContext.combinedClosedCollapse := by
  simp only [FragmentContext.combinedAllDiscard,
    FragmentContext.combinedClosedCollapse]
  -- On `[]`, both discard maps are identity by construction.
  have hu : FragmentContext.unrestrictedAllBitDiscard hΓ =
      Hom.id dayTensorUnit := rfl
  have hl : FragmentContext.linearAllNoneCollapse hΔ =
      Hom.id dayTensorUnit := rfl
  simp only [hu, hl]

private theorem semanticFragment_firstOrder_of
    {A : Ty} (hA : Ty.SemanticFragment A)
    (h : ∀ {B C}, A ≠ .arrow .lin B C)
    (h' : ∀ {C}, A ≠ .arrow .unres .bit C) :
    Ty.FirstOrder A := by
  cases hA with
  | ofFirstOrder hFO => exact hFO
  | arrowLin => exact (h rfl).elim
  | arrowUnresBit => exact (h' rfl).elim

/-- Recursively build `iteElim` by inspecting the result type. -/
noncomputable def iteElimFragment : ∀ {A : Ty}, Ty.SemanticFragment A →
    Hom
      (dayTensor (fragmentModule .bit)
        (additiveProduct (fragmentModule A) (fragmentModule A)))
      (fragmentModule A)
  | .unit, hA => by
      have hFO : Ty.FirstOrder .unit := .unit
      simpa [fragmentModule_bit, fragmentModule_of_firstOrder hFO] using
        iteElimRepresentable hFO.dimension
  | .bit, hA => by
      have hFO : Ty.FirstOrder .bit := .bit
      simpa [fragmentModule_bit, fragmentModule_of_firstOrder hFO] using
        iteElimRepresentable hFO.dimension
  | .qubit, hA => by
      have hFO : Ty.FirstOrder .qubit := .qubit
      simpa [fragmentModule_bit, fragmentModule_of_firstOrder hFO] using
        iteElimRepresentable hFO.dimension
  | .tensor A B, hA => by
      have hFO : Ty.FirstOrder (.tensor A B) :=
        semanticFragment_firstOrder_of hA (by intro _ _ h; cases h)
          (by intro _ h; cases h)
      simpa [fragmentModule_bit, fragmentModule_of_firstOrder hFO] using
        iteElimRepresentable hFO.dimension
  | .arrow .lin A B, hA => by
      have hDom : Ty.FirstOrder A := by
        cases hA with
        | arrowLin hDom _ => exact hDom
        | ofFirstOrder hFO => cases hFO
      have hCod : Ty.SemanticFragment B := by
        cases hA with
        | arrowLin _ hCod => exact hCod
        | ofFirstOrder hFO => cases hFO
      let d : ℕ := A.hilbertDim
      have hd : hDom.dimension = d := rfl
      let N := fragmentModule B
      let iteN :
          Hom (dayTensor (representable 2) (additiveProduct N N)) N := by
        simpa [fragmentModule_bit] using iteElimFragment hCod
      let iteDay :=
        iteElimInternalHom (X := representable d) (N := N) iteN
      simpa [fragmentModule_bit, fragmentModule, hd] using
        iteElimCongr (dayInternalHomRepresentableIso d N) iteDay
  | .arrow .unres .bit B, hA => by
      have hCod : Ty.SemanticFragment B := by
        cases hA with
        | arrowUnresBit hCod => exact hCod
        | ofFirstOrder hFO => cases hFO
      let N := fragmentModule B
      let iteN :
          Hom (dayTensor (representable 2) (additiveProduct N N)) N := by
        simpa [fragmentModule_bit] using iteElimFragment hCod
      simpa [fragmentModule_bit, fragmentModule] using
        iteElimInternalHom (X := classicalBitModule) (N := N) iteN
  | .arrow .unres .unit C, hA =>
      (Ty.SemanticFragment.not_arrow_unres_unit C hA).elim
  | .arrow .unres .qubit C, hA =>
      (Ty.SemanticFragment.not_arrow_unres_non_bit
        (by intro h; cases h) hA).elim
  | .arrow .unres (.var n) C, hA =>
      (Ty.SemanticFragment.not_arrow_unres_non_bit
        (by intro h; cases h) hA).elim
  | .arrow .unres (.tensor A B) C, hA =>
      (Ty.SemanticFragment.not_arrow_unres_non_bit
        (by intro h; cases h) hA).elim
  | .arrow .unres (.arrow m A B) C, hA =>
      (Ty.SemanticFragment.not_arrow_unres_non_bit
        (by intro h; cases h) hA).elim
  | .arrow .unres (.mu A) C, hA =>
      (Ty.SemanticFragment.not_arrow_unres_non_bit
        (by intro h; cases h) hA).elim
  | .var n, hA => (Ty.SemanticFragment.not_var (n := n) hA).elim
  | .mu A, hA => (Ty.SemanticFragment.not_mu (A := A) hA).elim

/-- Compiling inhabitant of `FragmentBranching`. -/
noncomputable def routeAFragmentBranching : FragmentBranching where
  iteElim := fun {_A} hA => iteElimFragment hA

/-- Full Route-A compositional denotation. -/
noncomputable def FragCert.denote {Γ Δ M A} (c : FragCert Γ Δ M A) :
    Hom (FragmentContext.combined Γ Δ) (fragmentModule A) :=
  FragCert.denoteWith routeAFragmentBranching c


end QLambda.Linear
