/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentDenotation
import QLambda.Domain.Presheaf.ClassicalMonoidal

/-!
# Controlled `ite` eliminator for Route A

Binary branch selection is realized by the jointly TNI instrument
`Ψₜ ∘ (⟨0| ∘ Φ ⊗ id) + Ψₑ ∘ (⟨1| ∘ Φ ⊗ id)`, lifted through the Day coend.
This avoids summing arbitrary Bool-indexed TNI families, which the Module
carrier rejects.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

open Domain.Presheaf
open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf.SigmaMon
open DayTensor
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable def prepBra (i : Fin 2) {m n : ℕ}
    (Φ : Superoperator m 2) : Superoperator (m * n) n :=
  Superoperator.comp (Superoperator.tensorLeftUnitor n)
    (Superoperator.tensor
      (Superoperator.comp (ChoiSum.complementaryBasisEffect i) Φ)
      (Superoperator.identity n))

theorem prepBra_zero {m n : ℕ} (i : Fin 2) :
    prepBra i (n := n) (0 : Superoperator m 2) = 0 := by
  simp only [prepBra]
  rw [Superoperator.comp_zero_right, Superoperator.tensor_zero_left,
    Superoperator.comp_zero_right]

theorem prepBra_hasSum {ι : Type} [Countable ι] {m n : ℕ}
    (i : Fin 2) {Φs : ι → Superoperator m 2} {Φ : Superoperator m 2}
    (h : ChoiSum.HasSum Φs Φ) :
    ChoiSum.HasSum (fun j => prepBra i (n := n) (Φs j))
      (prepBra i (n := n) Φ) := by
  have hcomp := ChoiSum.comp_left (ChoiSum.complementaryBasisEffect i) h
  have hten := ChoiSum.tensor_hasSum_left hcomp (Superoperator.identity n)
  exact ChoiSum.comp_left (Superoperator.tensorLeftUnitor n) hten

theorem prepBra_add_cp {m n : ℕ} (Φ : Superoperator m 2) :
    (prepBra 0 (n := n) Φ).cp + (prepBra 1 (n := n) Φ).cp =
      (Superoperator.comp (Superoperator.tensorLeftUnitor n)
        (Superoperator.tensor
          (Superoperator.comp ChoiSum.discardTwo Φ)
          (Superoperator.identity n))).cp := by
  simp only [prepBra, Superoperator.cp_comp]
  have hdistrib :=
    CPMap.comp_add_left (Superoperator.tensorLeftUnitor n).cp
      (Superoperator.tensor
        (Superoperator.comp ChoiSum.e0 Φ)
        (Superoperator.identity n)).cp
      (Superoperator.tensor
        (Superoperator.comp ChoiSum.e1 Φ)
        (Superoperator.identity n)).cp
  change
      CPMap.comp (Superoperator.tensorLeftUnitor n).cp
          (Superoperator.tensor
            (Superoperator.comp ChoiSum.e0 Φ)
            (Superoperator.identity n)).cp +
        CPMap.comp (Superoperator.tensorLeftUnitor n).cp
          (Superoperator.tensor
            (Superoperator.comp ChoiSum.e1 Φ)
            (Superoperator.identity n)).cp =
      _
  rw [← hdistrib]
  congr 1
  simp only [Superoperator.cp_tensor, Superoperator.cp_comp]
  rw [← CPMap.tensor_add_left, ← CPMap.comp_add_right,
    ChoiSum.e0_add_e1_cp_eq_discardTwo]

theorem prepBra_sum_tni {m n : ℕ} (Φ : Superoperator m 2) :
    TraceNonincreasing
      ((prepBra 0 (n := n) Φ).cp + (prepBra 1 (n := n) Φ).cp) := by
  rw [prepBra_add_cp]
  exact (Superoperator.comp (Superoperator.tensorLeftUnitor n)
    (Superoperator.tensor
      (Superoperator.comp ChoiSum.discardTwo Φ)
      (Superoperator.identity n))).trace_nonincreasing

theorem prepBra_naturality (i : Fin 2) {m' m n' n : ℕ}
    (Φ : Superoperator m 2) (f : Superoperator m' m)
    (g : Superoperator n' n) :
    Superoperator.comp (prepBra i (n := n) Φ) (Superoperator.tensor f g) =
      Superoperator.comp g
        (prepBra i (n := n') (Superoperator.comp Φ f)) := by
  simp only [prepBra]
  have hten :
      Superoperator.comp
          (Superoperator.tensor
            (Superoperator.comp (ChoiSum.complementaryBasisEffect i) Φ)
            (Superoperator.identity n))
          (Superoperator.tensor f g) =
        Superoperator.tensor
          (Superoperator.comp
            (Superoperator.comp (ChoiSum.complementaryBasisEffect i) Φ) f)
          (Superoperator.comp (Superoperator.identity n) g) :=
    (Superoperator.tensor_comp _ _ _ _).symm
  have hlhs :
      Superoperator.comp
          (Superoperator.comp (Superoperator.tensorLeftUnitor n)
            (Superoperator.tensor
              (Superoperator.comp (ChoiSum.complementaryBasisEffect i) Φ)
              (Superoperator.identity n)))
          (Superoperator.tensor f g) =
        Superoperator.comp (Superoperator.tensorLeftUnitor n)
          (Superoperator.tensor
            (Superoperator.comp (ChoiSum.complementaryBasisEffect i)
              (Superoperator.comp Φ f))
            g) := by
    rw [← Superoperator.comp_assoc, hten]
    simp only [Superoperator.identity_comp, Superoperator.comp_assoc]
  have hfactor :
      Superoperator.tensor
          (Superoperator.comp (ChoiSum.complementaryBasisEffect i)
            (Superoperator.comp Φ f))
          g =
        Superoperator.comp
          (Superoperator.tensor (Superoperator.identity 1) g)
          (Superoperator.tensor
            (Superoperator.comp (ChoiSum.complementaryBasisEffect i)
              (Superoperator.comp Φ f))
            (Superoperator.identity n')) := by
    have h :=
      Superoperator.tensor_comp
        (Superoperator.identity 1)
        (Superoperator.comp (ChoiSum.complementaryBasisEffect i)
          (Superoperator.comp Φ f))
        g (Superoperator.identity n')
    simp only [Superoperator.identity_comp, Superoperator.comp_identity] at h
    exact h
  rw [hlhs, hfactor, Superoperator.comp_assoc,
    Superoperator.tensorLeftUnitor_naturality g]
  simp only [Superoperator.comp_assoc]

private abbrev PairCarrier (d n : ℕ) :=
  Superoperator n d × Superoperator n d

theorem iteBranches_addable {m n d : ℕ}
    (Φ : Superoperator m 2) (pair : PairCarrier d n) :
    TraceNonincreasing
      ((Superoperator.comp pair.1 (prepBra 0 (n := n) Φ)).cp +
        (Superoperator.comp pair.2 (prepBra 1 (n := n) Φ)).cp) := by
  intro ρ hρ
  have hpos0 : ((prepBra 0 (n := n) Φ).cp.applyMat ρ).PosSemidef :=
    CPMap.applyMat_posSemidef _ hρ
  have hpos1 : ((prepBra 1 (n := n) Φ).cp.applyMat ρ).PosSemidef :=
    CPMap.applyMat_posSemidef _ hρ
  rw [CPMap.applyMat_add_map, Matrix.trace_add, Complex.add_re]
  have h0 :
      (Matrix.trace
          (CPMap.applyMat
            (Superoperator.comp pair.1 (prepBra 0 (n := n) Φ)).cp ρ)).re ≤
        (Matrix.trace
          (CPMap.applyMat (prepBra 0 (n := n) Φ).cp ρ)).re := by
    simp only [Superoperator.cp_comp, CPMap.applyMat_comp]
    exact pair.1.trace_nonincreasing _ hpos0
  have h1 :
      (Matrix.trace
          (CPMap.applyMat
            (Superoperator.comp pair.2 (prepBra 1 (n := n) Φ)).cp ρ)).re ≤
        (Matrix.trace
          (CPMap.applyMat (prepBra 1 (n := n) Φ).cp ρ)).re := by
    simp only [Superoperator.cp_comp, CPMap.applyMat_comp]
    exact pair.2.trace_nonincreasing _ hpos1
  refine (add_le_add h0 h1).trans ?_
  have hbras :
      (Matrix.trace (CPMap.applyMat (prepBra 0 (n := n) Φ).cp ρ)).re +
          (Matrix.trace (CPMap.applyMat (prepBra 1 (n := n) Φ).cp ρ)).re =
        (Matrix.trace
          (CPMap.applyMat
            ((prepBra 0 (n := n) Φ).cp +
              (prepBra 1 (n := n) Φ).cp) ρ)).re := by
    rw [CPMap.applyMat_add_map, Matrix.trace_add, Complex.add_re]
  rw [hbras]
  exact prepBra_sum_tni Φ ρ hρ

noncomputable def iteRepresentableBilinear (d : ℕ) :
    Bilinear (representable 2)
      (additiveProduct (representable d) (representable d))
      (representable d) where
  app := fun {m n} Φ pair =>
    let p : PairCarrier d n := pair
    ⟨(Superoperator.comp p.1 (prepBra 0 (n := n) Φ)).cp +
        (Superoperator.comp p.2 (prepBra 1 (n := n) Φ)).cp,
      iteBranches_addable Φ p⟩
  map_zero_left := by
    intro m n pair
    let p : PairCarrier d n := pair
    apply Superoperator.ext
    change
      (Superoperator.comp p.1 (prepBra 0 (n := n) (0 : Superoperator m 2))).cp +
          (Superoperator.comp p.2 (prepBra 1 (n := n) (0 : Superoperator m 2))).cp =
        (0 : Superoperator (m * n) d).cp
    rw [prepBra_zero, prepBra_zero, Superoperator.comp_zero_right,
      Superoperator.comp_zero_right, Superoperator.cp_zero, add_zero]
  map_zero_right := by
    intro m n Φ
    apply Superoperator.ext
    change
      (Superoperator.comp (0 : Superoperator n d) (prepBra 0 (n := n) Φ)).cp +
          (Superoperator.comp (0 : Superoperator n d) (prepBra 1 (n := n) Φ)).cp =
        (0 : Superoperator (m * n) d).cp
    rw [Superoperator.comp_zero_left, Superoperator.comp_zero_left,
      Superoperator.cp_zero, add_zero]
  map_sum_left := by
    intro ι _ m n Φs Φ pair hΦ
    let p : PairCarrier d n := pair
    change _root_.HasSum
      (fun i =>
        ((Superoperator.comp p.1 (prepBra 0 (n := n) (Φs i))).cp +
          (Superoperator.comp p.2 (prepBra 1 (n := n) (Φs i))).cp).choi)
      ((Superoperator.comp p.1 (prepBra 0 (n := n) Φ)).cp +
        (Superoperator.comp p.2 (prepBra 1 (n := n) Φ)).cp).choi
    simp only [CPMap.choi_add]
    exact (ChoiSum.comp_left p.1 (prepBra_hasSum 0 hΦ)).add
      (ChoiSum.comp_left p.2 (prepBra_hasSum 1 hΦ))
  map_sum_right := by
    intro ι _ m n Φ pairs pairSum hpair
    have hp1 : ChoiSum.HasSum (fun i => (pairs i : PairCarrier d n).1)
        (pairSum : PairCarrier d n).1 := hpair.1
    have hp2 : ChoiSum.HasSum (fun i => (pairs i : PairCarrier d n).2)
        (pairSum : PairCarrier d n).2 := hpair.2
    change _root_.HasSum
      (fun i =>
        ((Superoperator.comp (pairs i : PairCarrier d n).1
            (prepBra 0 (n := n) Φ)).cp +
          (Superoperator.comp (pairs i : PairCarrier d n).2
            (prepBra 1 (n := n) Φ)).cp).choi)
      ((Superoperator.comp (pairSum : PairCarrier d n).1
          (prepBra 0 (n := n) Φ)).cp +
        (Superoperator.comp (pairSum : PairCarrier d n).2
          (prepBra 1 (n := n) Φ)).cp).choi
    simp only [CPMap.choi_add]
    exact (ChoiSum.comp_right (prepBra 0 (n := n) Φ) hp1).add
      (ChoiSum.comp_right (prepBra 1 (n := n) Φ) hp2)
  naturality := by
    intro m' m n' n Φ pair f g
    let p : PairCarrier d n := pair
    apply Superoperator.ext
    have hbranch (i : Fin 2)
        (ψ : Superoperator n d) :
        Superoperator.comp (Superoperator.comp ψ g)
            (prepBra i (n := n') (Superoperator.comp Φ f)) =
          Superoperator.comp
            (Superoperator.comp ψ (prepBra i (n := n) Φ))
            (Superoperator.tensor f g) := by
      have h := prepBra_naturality i Φ f g
      calc
        Superoperator.comp (Superoperator.comp ψ g)
            (prepBra i (n := n') (Superoperator.comp Φ f)) =
          Superoperator.comp ψ
            (Superoperator.comp g
              (prepBra i (n := n') (Superoperator.comp Φ f))) := by
            rw [Superoperator.comp_assoc]
        _ = Superoperator.comp ψ
            (Superoperator.comp (prepBra i (n := n) Φ)
              (Superoperator.tensor f g)) := by rw [← h]
        _ = Superoperator.comp
            (Superoperator.comp ψ (prepBra i (n := n) Φ))
            (Superoperator.tensor f g) := by
            rw [← Superoperator.comp_assoc]
    have h0 := congrArg Superoperator.cp (hbranch 0 p.1)
    have h1 := congrArg Superoperator.cp (hbranch 1 p.2)
    have hrhs :
        (Superoperator.comp
            ⟨(Superoperator.comp p.1 (prepBra 0 (n := n) Φ)).cp +
                (Superoperator.comp p.2 (prepBra 1 (n := n) Φ)).cp,
              iteBranches_addable Φ p⟩
            (Superoperator.tensor f g)).cp =
          (Superoperator.comp
              (Superoperator.comp p.1 (prepBra 0 (n := n) Φ))
              (Superoperator.tensor f g)).cp +
            (Superoperator.comp
              (Superoperator.comp p.2 (prepBra 1 (n := n) Φ))
              (Superoperator.tensor f g)).cp := by
      simp only [Superoperator.cp_comp, CPMap.comp_add_right]
    -- Unfold app action on the left
    change
      (Superoperator.comp (Superoperator.comp p.1 g)
            (prepBra 0 (n := n') (Superoperator.comp Φ f))).cp +
          (Superoperator.comp (Superoperator.comp p.2 g)
            (prepBra 1 (n := n') (Superoperator.comp Φ f))).cp =
        (Superoperator.comp
            ⟨(Superoperator.comp p.1 (prepBra 0 (n := n) Φ)).cp +
                (Superoperator.comp p.2 (prepBra 1 (n := n) Φ)).cp,
              iteBranches_addable Φ p⟩
            (Superoperator.tensor f g)).cp
    rw [hrhs, h0, h1]

noncomputable def iteElimRepresentable (d : ℕ) :
    Hom
      (dayTensor (representable 2)
        (additiveProduct (representable d) (representable d)))
      (representable d) :=
  DayCoend.lift (iteRepresentableBilinear d)


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

/-! ## Constructor computation equations -/

theorem FragCert.denote_unit_eq {Γ Δ}
    (hΓ : CtxUAllBit Γ) (hL : CtxLAllSomeFragment Δ) (hΔ : AllNone Δ) :
    FragCert.denote (.unit hΓ hL hΔ) =
      FragmentContext.combinedPoint hΓ hΔ routeAFragmentModel.unitIntro :=
  rfl

theorem FragCert.denote_bitLit_eq {Γ Δ b}
    (hΓ : CtxUAllBit Γ) (hL : CtxLAllSomeFragment Δ) (hΔ : AllNone Δ) :
    FragCert.denote (.bitLit hΓ hL b hΔ) =
      FragmentContext.combinedPoint hΓ hΔ (routeAFragmentModel.bitLit b) :=
  rfl

theorem FragCert.denote_prim_eq {Γ Δ p}
    (hΓ : CtxUAllBit Γ) (hL : CtxLAllSomeFragment Δ) (hΔ : AllNone Δ) :
    FragCert.denote (.prim hΓ hL p hΔ) =
      FragmentContext.combinedPoint hΓ hΔ (FragCert.denotePrimPoint p) :=
  rfl

theorem FragCert.denote_ite_eq {Γ Δ Δ₁ Δ₂ A B T E}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
    (cB : FragCert Γ Δ₁ B .bit) (cT : FragCert Γ Δ₂ T A)
    (cE : FragCert Γ Δ₂ E A) :
    FragCert.denote (.ite hΓ hΔ hs hA cB cT cE) =
      Hom.comp (routeAFragmentBranching.iteElim hA)
        (Hom.comp
          (DayTensor.map (FragCert.denote cB)
            (additivePair (FragCert.denote cT) (FragCert.denote cE)))
          (FragmentContext.combinedOSplit hΓ hs)) :=
  rfl

theorem FragCert.denote_measure_eq {Γ Δ Δ₁ Δ₂ A Q K}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.SemanticFragment A)
    (cQ : FragCert Γ Δ₁ Q .qubit)
    (cK : FragCert Γ Δ₂ K (.arrow .unres .bit (.arrow .lin .qubit A))) :
    FragCert.denote (.measure hΓ hΔ hs hA cQ cK) =
      Hom.comp (FragCert.measureElim _)
        (Hom.comp
          (DayTensor.map (FragCert.denote cQ) (FragCert.denote cK))
          (FragmentContext.combinedOSplit hΓ hs)) :=
  rfl

/-! ## Proof-witness independence -/

theorem FragCert.denote_unit_proof_independent {Γ Δ}
    (hΓ hΓ' : CtxUAllBit Γ) (hL hL' : CtxLAllSomeFragment Δ)
    (hΔ hΔ' : AllNone Δ) :
    FragCert.denote (.unit hΓ hL hΔ) =
      FragCert.denote (.unit hΓ' hL' hΔ') := by
  simp only [FragCert.denote_unit_eq, FragmentContext.combinedPoint]
  congr

theorem FragCert.denote_bitLit_proof_independent {Γ Δ b}
    (hΓ hΓ' : CtxUAllBit Γ) (hL hL' : CtxLAllSomeFragment Δ)
    (hΔ hΔ' : AllNone Δ) :
    FragCert.denote (.bitLit hΓ hL b hΔ) =
      FragCert.denote (.bitLit hΓ' hL' b hΔ') := by
  simp only [FragCert.denote_bitLit_eq, FragmentContext.combinedPoint]
  congr

/-- Full Route-A denotation model. -/
noncomputable def routeAFragmentDenotationModel : FragmentDenotationModel where
  denote := FragCert.denote
  denote_unit := by
    intro c
    cases c with
    | unit hΓ _ hΔ =>
        change FragmentContext.combinedPoint hΓ hΔ
            routeAFragmentModel.unitIntro =
          FragmentContext.closedPoint routeAFragmentModel.unitIntro
        simp only [FragmentContext.combinedPoint, FragmentContext.closedPoint,
          combinedAllDiscard_nil]
  denote_bitLit := by
    intro b c
    cases c with
    | bitLit hΓ _ _ hΔ =>
        change FragmentContext.combinedPoint hΓ hΔ
            (routeAFragmentModel.bitLit b) =
          FragmentContext.closedPoint (routeAFragmentModel.bitLit b)
        simp only [FragmentContext.combinedPoint, FragmentContext.closedPoint,
          combinedAllDiscard_nil]

/-- Route A supplies compositional open-term denotation for every `FragCert`. -/
theorem routeA_fragment_denotation_exists :
    Nonempty FragmentDenotationModel :=
  ⟨routeAFragmentDenotationModel⟩

end QLambda.Linear
