/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentDenotation
import QLambda.Domain.Presheaf.ClassicalMonoidal

/-!
# Controlled bit preparation for fragment `ite`

`prepBra`, representable bilinear branch pairing, and
`iteElimRepresentable`.
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

/-- Matching preparation: `prepBra i ∘ |i⟩` is the left unitor `1⊗n → n`. -/
theorem prepBra_isometricBasisPrep (i : Fin 2) {n : ℕ} :
    prepBra i (n := n) (ChoiSum.isometricBasisPrep i) =
      Superoperator.tensorLeftUnitor n := by
  simp only [prepBra, ChoiSum.complementaryBasisEffect_comp_isometricBasisPrep,
    Superoperator.tensor_identity, Superoperator.comp_identity]

/-- Cross preparation: `prepBra i ∘ |j⟩ = 0` when `i ≠ j`. -/
theorem prepBra_isometricBasisPrep_of_ne {i j : Fin 2} (h : i ≠ j) {n : ℕ} :
    prepBra i (n := n) (ChoiSum.isometricBasisPrep j) = 0 := by
  simp only [prepBra,
    ChoiSum.complementaryBasisEffect_comp_isometricBasisPrep_of_ne h,
    Superoperator.tensor_zero_left, Superoperator.comp_zero_right]

/-- Boolean literal index: `true ↦ 1`, `false ↦ 0`. -/
def bitFin (b : Bool) : Fin 2 := if b then 1 else 0

theorem bitPrepare_eq (b : Bool) :
    bitPrepare b = ChoiSum.isometricBasisPrep (bitFin b) := by
  cases b <;> rfl

private abbrev PairCarrier (d n : ℕ) :=
  Superoperator n d × Superoperator n d

/-- Then-branch uses outcome `1` (`true`); else-branch uses `0` (`false`). -/
theorem iteBranches_addable {m n d : ℕ}
    (Φ : Superoperator m 2) (pair : PairCarrier d n) :
    TraceNonincreasing
      ((Superoperator.comp pair.1 (prepBra 1 (n := n) Φ)).cp +
        (Superoperator.comp pair.2 (prepBra 0 (n := n) Φ)).cp) := by
  intro ρ hρ
  have hpos1 : ((prepBra 1 (n := n) Φ).cp.applyMat ρ).PosSemidef :=
    CPMap.applyMat_posSemidef _ hρ
  have hpos0 : ((prepBra 0 (n := n) Φ).cp.applyMat ρ).PosSemidef :=
    CPMap.applyMat_posSemidef _ hρ
  rw [CPMap.applyMat_add_map, Matrix.trace_add, Complex.add_re]
  have h1 :
      (Matrix.trace
          (CPMap.applyMat
            (Superoperator.comp pair.1 (prepBra 1 (n := n) Φ)).cp ρ)).re ≤
        (Matrix.trace
          (CPMap.applyMat (prepBra 1 (n := n) Φ).cp ρ)).re := by
    simp only [Superoperator.cp_comp, CPMap.applyMat_comp]
    exact pair.1.trace_nonincreasing _ hpos1
  have h0 :
      (Matrix.trace
          (CPMap.applyMat
            (Superoperator.comp pair.2 (prepBra 0 (n := n) Φ)).cp ρ)).re ≤
        (Matrix.trace
          (CPMap.applyMat (prepBra 0 (n := n) Φ).cp ρ)).re := by
    simp only [Superoperator.cp_comp, CPMap.applyMat_comp]
    exact pair.2.trace_nonincreasing _ hpos0
  refine (add_le_add h1 h0).trans ?_
  have hbras :
      (Matrix.trace (CPMap.applyMat (prepBra 1 (n := n) Φ).cp ρ)).re +
          (Matrix.trace (CPMap.applyMat (prepBra 0 (n := n) Φ).cp ρ)).re =
        (Matrix.trace
          (CPMap.applyMat
            ((prepBra 0 (n := n) Φ).cp +
              (prepBra 1 (n := n) Φ).cp) ρ)).re := by
    rw [CPMap.applyMat_add_map, Matrix.trace_add, Complex.add_re, add_comm]
  rw [hbras]
  exact prepBra_sum_tni Φ ρ hρ
noncomputable def iteRepresentableBilinear (d : ℕ) :
    Bilinear (representable 2)
      (additiveProduct (representable d) (representable d))
      (representable d) where
  app := fun {m n} Φ pair =>
    let p : PairCarrier d n := pair
    ⟨(Superoperator.comp p.1 (prepBra 1 (n := n) Φ)).cp +
        (Superoperator.comp p.2 (prepBra 0 (n := n) Φ)).cp,
      iteBranches_addable Φ p⟩
  map_zero_left := by
    intro m n pair
    let p : PairCarrier d n := pair
    apply Superoperator.ext
    change
      (Superoperator.comp p.1 (prepBra 1 (n := n) (0 : Superoperator m 2))).cp +
          (Superoperator.comp p.2 (prepBra 0 (n := n) (0 : Superoperator m 2))).cp =
        (0 : Superoperator (m * n) d).cp
    rw [prepBra_zero, prepBra_zero, Superoperator.comp_zero_right,
      Superoperator.comp_zero_right, Superoperator.cp_zero, add_zero]
  map_zero_right := by
    intro m n Φ
    apply Superoperator.ext
    change
      (Superoperator.comp (0 : Superoperator n d) (prepBra 1 (n := n) Φ)).cp +
          (Superoperator.comp (0 : Superoperator n d) (prepBra 0 (n := n) Φ)).cp =
        (0 : Superoperator (m * n) d).cp
    rw [Superoperator.comp_zero_left, Superoperator.comp_zero_left,
      Superoperator.cp_zero, add_zero]
  map_sum_left := by
    intro ι _ m n Φs Φ pair hΦ
    let p : PairCarrier d n := pair
    change _root_.HasSum
      (fun i =>
        ((Superoperator.comp p.1 (prepBra 1 (n := n) (Φs i))).cp +
          (Superoperator.comp p.2 (prepBra 0 (n := n) (Φs i))).cp).choi)
      ((Superoperator.comp p.1 (prepBra 1 (n := n) Φ)).cp +
        (Superoperator.comp p.2 (prepBra 0 (n := n) Φ)).cp).choi
    simp only [CPMap.choi_add]
    exact (ChoiSum.comp_left p.1 (prepBra_hasSum 1 hΦ)).add
      (ChoiSum.comp_left p.2 (prepBra_hasSum 0 hΦ))
  map_sum_right := by
    intro ι _ m n Φ pairs pairSum hpair
    have hp1 : ChoiSum.HasSum (fun i => (pairs i : PairCarrier d n).1)
        (pairSum : PairCarrier d n).1 := hpair.1
    have hp2 : ChoiSum.HasSum (fun i => (pairs i : PairCarrier d n).2)
        (pairSum : PairCarrier d n).2 := hpair.2
    change _root_.HasSum
      (fun i =>
        ((Superoperator.comp (pairs i : PairCarrier d n).1
            (prepBra 1 (n := n) Φ)).cp +
          (Superoperator.comp (pairs i : PairCarrier d n).2
            (prepBra 0 (n := n) Φ)).cp).choi)
      ((Superoperator.comp (pairSum : PairCarrier d n).1
          (prepBra 1 (n := n) Φ)).cp +
        (Superoperator.comp (pairSum : PairCarrier d n).2
          (prepBra 0 (n := n) Φ)).cp).choi
    simp only [CPMap.choi_add]
    exact (ChoiSum.comp_right (prepBra 1 (n := n) Φ) hp1).add
      (ChoiSum.comp_right (prepBra 0 (n := n) Φ) hp2)
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
    have h1 := congrArg Superoperator.cp (hbranch 1 p.1)
    have h0 := congrArg Superoperator.cp (hbranch 0 p.2)
    have hrhs :
        (Superoperator.comp
            ⟨(Superoperator.comp p.1 (prepBra 1 (n := n) Φ)).cp +
                (Superoperator.comp p.2 (prepBra 0 (n := n) Φ)).cp,
              iteBranches_addable Φ p⟩
            (Superoperator.tensor f g)).cp =
          (Superoperator.comp
              (Superoperator.comp p.1 (prepBra 1 (n := n) Φ))
              (Superoperator.tensor f g)).cp +
            (Superoperator.comp
              (Superoperator.comp p.2 (prepBra 0 (n := n) Φ))
              (Superoperator.tensor f g)).cp := by
      simp only [Superoperator.cp_comp, CPMap.comp_add_right]
    -- Unfold app action on the left
    change
      (Superoperator.comp (Superoperator.comp p.1 g)
            (prepBra 1 (n := n') (Superoperator.comp Φ f))).cp +
          (Superoperator.comp (Superoperator.comp p.2 g)
            (prepBra 0 (n := n') (Superoperator.comp Φ f))).cp =
        (Superoperator.comp
            ⟨(Superoperator.comp p.1 (prepBra 1 (n := n) Φ)).cp +
                (Superoperator.comp p.2 (prepBra 0 (n := n) Φ)).cp,
              iteBranches_addable Φ p⟩
            (Superoperator.tensor f g)).cp
    rw [hrhs, h1, h0]

noncomputable def iteElimRepresentable (d : ℕ) :
    Hom
      (dayTensor (representable 2)
        (additiveProduct (representable d) (representable d)))
      (representable d) :=
  DayCoend.lift (iteRepresentableBilinear d)


end QLambda.Linear
