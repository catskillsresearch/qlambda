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

/-! ## Representable `ite` β on bit literals -/

private theorem bitLitHom_app_true {m : ℕ}
    (q : (dayTensorUnit.obj m).Carrier) :
    (bitLitHom true).app m q =
      Superoperator.comp (ChoiSum.isometricBasisPrep 1)
        (q : Superoperator m 1) := by
  change (yonedaMap (ChoiSum.isometricBasisPrep 1)).app m q = _
  exact yonedaMap_app (ChoiSum.isometricBasisPrep 1) (q : Superoperator m 1)

private theorem bitLitHom_app_false {m : ℕ}
    (q : (dayTensorUnit.obj m).Carrier) :
    (bitLitHom false).app m q =
      Superoperator.comp (ChoiSum.isometricBasisPrep 0)
        (q : Superoperator m 1) := by
  change (yonedaMap (ChoiSum.isometricBasisPrep 0)).app m q = _
  exact yonedaMap_app (ChoiSum.isometricBasisPrep 0) (q : Superoperator m 1)

private theorem hom_unit_act_as_comp {n n' d : ℕ}
    (y : (dayTensorUnit.obj n).Carrier)
    (T : Hom dayTensorUnit (representable d))
    (g : Superoperator n' n) :
    T.app n' (dayTensorUnit.act y g) =
      (Superoperator.comp (T.app n y : Superoperator n d) g :
        (representable d).obj n' |>.Carrier) := by
  have h := (T.naturality y g).symm
  have hact :
      (representable d).act (T.app n y) g =
        Superoperator.comp (T.app n y : Superoperator n d) g :=
    representable_act (T.app n y : Superoperator n d) g
  exact h.symm.trans hact

private theorem iteElimRepresentable_bitLit_aux (d : ℕ) (b : Bool)
    (T E : Hom dayTensorUnit (representable d))
    (hThen :
      Hom.comp (iteElimRepresentable d)
        (DayTensor.map (bitLitHom b) (additivePair T E)) =
          Hom.comp (bif b then T else E)
            (DayTensor.leftUnitor dayTensorUnit)) :
    Hom.comp (iteElimRepresentable d)
      (Hom.comp
        (DayTensor.map (bitLitHom b) (additivePair T E))
        (DayTensor.leftUnitorInv dayTensorUnit)) =
      (bif b then T else E) := by
  have h :=
    congrArg (fun f => Hom.comp f (DayTensor.leftUnitorInv dayTensorUnit)) hThen
  calc
    Hom.comp (iteElimRepresentable d)
          (Hom.comp (DayTensor.map (bitLitHom b) (additivePair T E))
            (DayTensor.leftUnitorInv dayTensorUnit)) =
        Hom.comp
          (Hom.comp (iteElimRepresentable d)
            (DayTensor.map (bitLitHom b) (additivePair T E)))
          (DayTensor.leftUnitorInv dayTensorUnit) := by
      rw [Hom.comp_assoc]
    _ = Hom.comp
          (Hom.comp (bif b then T else E)
            (DayTensor.leftUnitor dayTensorUnit))
          (DayTensor.leftUnitorInv dayTensorUnit) := h
    _ = Hom.comp (bif b then T else E)
          (Hom.comp (DayTensor.leftUnitor dayTensorUnit)
            (DayTensor.leftUnitorInv dayTensorUnit)) := by
      rw [Hom.comp_assoc]
    _ = Hom.comp (bif b then T else E) (Hom.id _) := by
      rw [DayTensor.leftUnitor_hom_inv]
    _ = bif b then T else E := Hom.comp_id _

theorem iteElimRepresentable_comp_bitLit_true (d : ℕ)
    (T E : Hom dayTensorUnit (representable d)) :
    Hom.comp (iteElimRepresentable d)
      (DayTensor.map (bitLitHom true) (additivePair T E)) =
      Hom.comp T (DayTensor.leftUnitor dayTensorUnit) := by
  apply DayTensor.hom_ext
  intro m n q0 y0
  change Superoperator m 1 at q0
  change Superoperator n 1 at y0
  let qC : (dayTensorUnit.obj m).Carrier := q0
  let yC : (dayTensorUnit.obj n).Carrier := y0
  let ψT : Superoperator n d := T.app n yC
  let ψE : Superoperator n d := E.app n yC
  let g : Superoperator (m * n) n :=
    Superoperator.comp (Superoperator.tensorLeftUnitor n)
      (Superoperator.tensor q0 (Superoperator.identity n))
  simp only [Hom.comp_app]
  rw [DayTensor.map_intro (bitLitHom true) (additivePair T E) qC yC]
  rw [DayTensor.leftUnitor_intro (M := dayTensorUnit) qC yC]
  change
      DayCoend.evaluate (representable d) (iteRepresentableBilinear d)
          ((DayCoend.intro (representable 2)
              (additiveProduct (representable d) (representable d))).app
            ((bitLitHom true).app m qC) ((additivePair T E).app n yC)) =
        T.app (m * n) (dayTensorUnit.act yC g)
  rw [DayCoend.evaluate_intro]
  have hψT :
      ((additivePair T E).app n yC).1 = ψT :=
    congrArg (fun f => f.app n yC) (additiveFst_pair T E)
  have hψE :
      ((additivePair T E).app n yC).2 = ψE :=
    congrArg (fun f => f.app n yC) (additiveSnd_pair T E)
  have hq : (bitLitHom true).app m qC =
      Superoperator.comp (ChoiSum.isometricBasisPrep 1) q0 :=
    bitLitHom_app_true qC
  have hnat1 :=
    prepBra_naturality (1 : Fin 2) (ChoiSum.isometricBasisPrep 1) q0
      (Superoperator.identity n)
  have hnat0 :=
    prepBra_naturality (0 : Fin 2) (ChoiSum.isometricBasisPrep 1) q0
      (Superoperator.identity n)
  have hnat1' :
      prepBra 1 (n := n)
          (Superoperator.comp (ChoiSum.isometricBasisPrep 1) q0) =
        Superoperator.comp (prepBra 1 (ChoiSum.isometricBasisPrep 1))
          (Superoperator.tensor q0 (Superoperator.identity n)) := by
    simpa [Superoperator.comp_identity, Superoperator.identity_comp] using
      hnat1.symm
  have hnat0' :
      prepBra 0 (n := n)
          (Superoperator.comp (ChoiSum.isometricBasisPrep 1) q0) =
        Superoperator.comp (prepBra 0 (ChoiSum.isometricBasisPrep 1))
          (Superoperator.tensor q0 (Superoperator.identity n)) := by
    simpa [Superoperator.comp_identity, Superoperator.identity_comp] using
      hnat0.symm
  apply Superoperator.ext
  calc
    (Superoperator.comp
            (((additivePair T E).app n yC).1 : Superoperator n d)
            (prepBra 1 (n := n) ((bitLitHom true).app m qC))).cp +
          (Superoperator.comp
            (((additivePair T E).app n yC).2 : Superoperator n d)
            (prepBra 0 (n := n) ((bitLitHom true).app m qC))).cp =
        (Superoperator.comp ψT
            (prepBra 1 (n := n)
              (Superoperator.comp (ChoiSum.isometricBasisPrep 1) q0))).cp +
          (Superoperator.comp ψE
            (prepBra 0 (n := n)
              (Superoperator.comp (ChoiSum.isometricBasisPrep 1) q0))).cp := by
      rw [hψT, hψE, hq]
    _ = (Superoperator.comp ψT
            (Superoperator.comp (prepBra 1 (ChoiSum.isometricBasisPrep 1))
              (Superoperator.tensor q0 (Superoperator.identity n)))).cp +
          (Superoperator.comp ψE
            (Superoperator.comp (prepBra 0 (ChoiSum.isometricBasisPrep 1))
              (Superoperator.tensor q0 (Superoperator.identity n)))).cp := by
      rw [hnat1', hnat0']
    _ = (Superoperator.comp ψT g).cp +
          (Superoperator.comp ψE
            (Superoperator.comp (0 : Superoperator (1 * n) n)
              (Superoperator.tensor q0 (Superoperator.identity n)))).cp := by
      rw [prepBra_isometricBasisPrep 1,
        prepBra_isometricBasisPrep_of_ne (by decide : (0 : Fin 2) ≠ 1)]
    _ = (Superoperator.comp ψT g).cp := by
      simp [Superoperator.comp_zero_left, Superoperator.comp_zero_right,
        Superoperator.cp_zero, add_zero]
    _ = (T.app (m * n) (dayTensorUnit.act yC g) :
          Superoperator (m * n) d).cp := by
      exact congrArg Superoperator.cp (hom_unit_act_as_comp yC T g).symm

theorem iteElimRepresentable_comp_bitLit_false (d : ℕ)
    (T E : Hom dayTensorUnit (representable d)) :
    Hom.comp (iteElimRepresentable d)
      (DayTensor.map (bitLitHom false) (additivePair T E)) =
      Hom.comp E (DayTensor.leftUnitor dayTensorUnit) := by
  apply DayTensor.hom_ext
  intro m n q0 y0
  change Superoperator m 1 at q0
  change Superoperator n 1 at y0
  let qC : (dayTensorUnit.obj m).Carrier := q0
  let yC : (dayTensorUnit.obj n).Carrier := y0
  let ψT : Superoperator n d := T.app n yC
  let ψE : Superoperator n d := E.app n yC
  let g : Superoperator (m * n) n :=
    Superoperator.comp (Superoperator.tensorLeftUnitor n)
      (Superoperator.tensor q0 (Superoperator.identity n))
  simp only [Hom.comp_app]
  rw [DayTensor.map_intro (bitLitHom false) (additivePair T E) qC yC]
  rw [DayTensor.leftUnitor_intro (M := dayTensorUnit) qC yC]
  change
      DayCoend.evaluate (representable d) (iteRepresentableBilinear d)
          ((DayCoend.intro (representable 2)
              (additiveProduct (representable d) (representable d))).app
            ((bitLitHom false).app m qC) ((additivePair T E).app n yC)) =
        E.app (m * n) (dayTensorUnit.act yC g)
  rw [DayCoend.evaluate_intro]
  have hψT :
      ((additivePair T E).app n yC).1 = ψT :=
    congrArg (fun f => f.app n yC) (additiveFst_pair T E)
  have hψE :
      ((additivePair T E).app n yC).2 = ψE :=
    congrArg (fun f => f.app n yC) (additiveSnd_pair T E)
  have hq : (bitLitHom false).app m qC =
      Superoperator.comp (ChoiSum.isometricBasisPrep 0) q0 :=
    bitLitHom_app_false qC
  have hnat1 :=
    prepBra_naturality (1 : Fin 2) (ChoiSum.isometricBasisPrep 0) q0
      (Superoperator.identity n)
  have hnat0 :=
    prepBra_naturality (0 : Fin 2) (ChoiSum.isometricBasisPrep 0) q0
      (Superoperator.identity n)
  have hnat1' :
      prepBra 1 (n := n)
          (Superoperator.comp (ChoiSum.isometricBasisPrep 0) q0) =
        Superoperator.comp (prepBra 1 (ChoiSum.isometricBasisPrep 0))
          (Superoperator.tensor q0 (Superoperator.identity n)) := by
    simpa [Superoperator.comp_identity, Superoperator.identity_comp] using
      hnat1.symm
  have hnat0' :
      prepBra 0 (n := n)
          (Superoperator.comp (ChoiSum.isometricBasisPrep 0) q0) =
        Superoperator.comp (prepBra 0 (ChoiSum.isometricBasisPrep 0))
          (Superoperator.tensor q0 (Superoperator.identity n)) := by
    simpa [Superoperator.comp_identity, Superoperator.identity_comp] using
      hnat0.symm
  apply Superoperator.ext
  calc
    (Superoperator.comp
            (((additivePair T E).app n yC).1 : Superoperator n d)
            (prepBra 1 (n := n) ((bitLitHom false).app m qC))).cp +
          (Superoperator.comp
            (((additivePair T E).app n yC).2 : Superoperator n d)
            (prepBra 0 (n := n) ((bitLitHom false).app m qC))).cp =
        (Superoperator.comp ψT
            (prepBra 1 (n := n)
              (Superoperator.comp (ChoiSum.isometricBasisPrep 0) q0))).cp +
          (Superoperator.comp ψE
            (prepBra 0 (n := n)
              (Superoperator.comp (ChoiSum.isometricBasisPrep 0) q0))).cp := by
      rw [hψT, hψE, hq]
    _ = (Superoperator.comp ψT
            (Superoperator.comp (prepBra 1 (ChoiSum.isometricBasisPrep 0))
              (Superoperator.tensor q0 (Superoperator.identity n)))).cp +
          (Superoperator.comp ψE
            (Superoperator.comp (prepBra 0 (ChoiSum.isometricBasisPrep 0))
              (Superoperator.tensor q0 (Superoperator.identity n)))).cp := by
      rw [hnat1', hnat0']
    _ = (Superoperator.comp ψT
            (Superoperator.comp (0 : Superoperator (1 * n) n)
              (Superoperator.tensor q0 (Superoperator.identity n)))).cp +
          (Superoperator.comp ψE g).cp := by
      rw [prepBra_isometricBasisPrep 0,
        prepBra_isometricBasisPrep_of_ne (by decide : (1 : Fin 2) ≠ 0)]
    _ = (Superoperator.comp ψE g).cp := by
      simp [Superoperator.comp_zero_left, Superoperator.comp_zero_right,
        Superoperator.cp_zero, zero_add]
    _ = (E.app (m * n) (dayTensorUnit.act yC g) :
          Superoperator (m * n) d).cp := by
      exact congrArg Superoperator.cp (hom_unit_act_as_comp yC E g).symm

theorem iteElimRepresentable_comp_bitLit (d : ℕ) (b : Bool)
    (T E : Hom dayTensorUnit (representable d)) :
    Hom.comp (iteElimRepresentable d)
      (DayTensor.map (bitLitHom b) (additivePair T E)) =
      Hom.comp (bif b then T else E)
        (DayTensor.leftUnitor dayTensorUnit) := by
  cases b with
  | true => exact iteElimRepresentable_comp_bitLit_true d T E
  | false => exact iteElimRepresentable_comp_bitLit_false d T E

theorem iteElimRepresentable_bitLit_true (d : ℕ)
    (T E : Hom dayTensorUnit (representable d)) :
    Hom.comp (iteElimRepresentable d)
      (Hom.comp
        (DayTensor.map (bitLitHom true) (additivePair T E))
        (DayTensor.leftUnitorInv dayTensorUnit)) =
      T :=
  iteElimRepresentable_bitLit_aux d true T E
    (iteElimRepresentable_comp_bitLit d true T E)

theorem iteElimRepresentable_bitLit_false (d : ℕ)
    (T E : Hom dayTensorUnit (representable d)) :
    Hom.comp (iteElimRepresentable d)
      (Hom.comp
        (DayTensor.map (bitLitHom false) (additivePair T E))
        (DayTensor.leftUnitorInv dayTensorUnit)) =
      E :=
  iteElimRepresentable_bitLit_aux d false T E
    (iteElimRepresentable_comp_bitLit d false T E)



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

/-! ## Closed first-order `ite` helpers -/

/-- Closed bit-literal certificates denote as `closedPoint (bitLitHom _)`. -/
theorem FragCert.closed_bitLit_denote_eq (b : Bool) :
    FragCert.denote (FragCert.closed_bitLit_cert b) =
      FragmentContext.closedPoint (bitLitHom b) := by
  simp only [FragmentContext.closedPoint]
  rfl

theorem additivePair_comp {L M N P : Module}
    (f : Hom L M) (g : Hom L N) (h : Hom P L) :
    Hom.comp (additivePair f g) h =
      additivePair (Hom.comp f h) (Hom.comp g h) := by
  ext n x
  rfl

/-- Day-unit inverse unitor as a map into the empty combined context. -/
noncomputable def FragmentContext.closedLeftUnitorInv :
    Hom dayTensorUnit (FragmentContext.combined [] []) :=
  DayTensor.leftUnitorInv dayTensorUnit

theorem FragmentContext.closedLeftUnitorInv_eq :
    FragmentContext.closedLeftUnitorInv =
      DayTensor.leftUnitorInv dayTensorUnit :=
  rfl

theorem FragmentContext.combinedClosedCollapse_leftUnitorInv :
    Hom.comp FragmentContext.combinedClosedCollapse
      FragmentContext.closedLeftUnitorInv =
    Hom.id dayTensorUnit := by
  change Hom.comp
      (Hom.comp (DayTensor.leftUnitor dayTensorUnit)
        (DayTensor.map (Hom.id dayTensorUnit) (Hom.id dayTensorUnit)))
      (DayTensor.leftUnitorInv dayTensorUnit) =
    Hom.id dayTensorUnit
  rw [DayTensor.map_id, Hom.comp_id, DayTensor.leftUnitor_hom_inv]

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

/-! ## Closed first-order `ite` Step soundness -/

/-- Representable-level closed `ite` β after packing through `λ⁻¹ ⊗ λ⁻¹`. -/
private theorem iteElimRepresentable_closed_bitLit_aux (d : ℕ) (b : Bool)
    (T E : Hom (FragmentContext.combined [] []) (representable d)) :
    Hom.comp (iteElimRepresentable d)
      (Hom.comp
        (DayTensor.map
          (Hom.comp (bitLitHom b) FragmentContext.combinedClosedCollapse)
          (additivePair T E))
        (DayTensor.map FragmentContext.closedLeftUnitorInv
          FragmentContext.closedLeftUnitorInv)) =
      (bif b then T else E) := by
  have hsplit :
      Hom.comp
          (DayTensor.map
            (Hom.comp (bitLitHom b) FragmentContext.combinedClosedCollapse)
            (additivePair T E))
          (DayTensor.map FragmentContext.closedLeftUnitorInv
            FragmentContext.closedLeftUnitorInv) =
        DayTensor.map (bitLitHom b)
          (additivePair
            (Hom.comp T FragmentContext.closedLeftUnitorInv)
            (Hom.comp E FragmentContext.closedLeftUnitorInv)) := by
    have h :=
      (DayTensor.map_comp
        (Hom.comp (bitLitHom b) FragmentContext.combinedClosedCollapse)
        FragmentContext.closedLeftUnitorInv
        (additivePair T E)
        FragmentContext.closedLeftUnitorInv).symm
    refine h.trans ?_
    have hb :
        Hom.comp
            (Hom.comp (bitLitHom b) FragmentContext.combinedClosedCollapse)
            FragmentContext.closedLeftUnitorInv =
          bitLitHom b := by
      change Hom.comp (bitLitHom b)
          (Hom.comp FragmentContext.combinedClosedCollapse
            FragmentContext.closedLeftUnitorInv) =
        bitLitHom b
      rw [FragmentContext.combinedClosedCollapse_leftUnitorInv, Hom.comp_id]
    have hp :
        Hom.comp (additivePair T E) FragmentContext.closedLeftUnitorInv =
          additivePair
            (Hom.comp T FragmentContext.closedLeftUnitorInv)
            (Hom.comp E FragmentContext.closedLeftUnitorInv) :=
      additivePair_comp T E _
    rw [hb, hp]
  rw [hsplit, iteElimRepresentable_comp_bitLit d b
    (Hom.comp T FragmentContext.closedLeftUnitorInv)
    (Hom.comp E FragmentContext.closedLeftUnitorInv)]
  have hinj :
      Hom.comp FragmentContext.closedLeftUnitorInv
        (DayTensor.leftUnitor dayTensorUnit) =
      Hom.id (FragmentContext.combined [] []) :=
    (DayTensor.leftUnitorIso dayTensorUnit).inv_hom
  cases b with
  | true =>
      have h1 :
          Hom.comp T
              (Hom.comp FragmentContext.closedLeftUnitorInv
                (DayTensor.leftUnitor dayTensorUnit)) =
            Hom.comp T (Hom.id _) :=
        congrArg (Hom.comp T) hinj
      have h2 :
          Hom.comp
              (Hom.comp T FragmentContext.closedLeftUnitorInv)
              (DayTensor.leftUnitor dayTensorUnit) =
            Hom.comp T
              (Hom.comp FragmentContext.closedLeftUnitorInv
                (DayTensor.leftUnitor dayTensorUnit)) :=
        (Hom.comp_assoc _ _ _).symm
      exact h2.trans (h1.trans (Hom.comp_id T))
  | false =>
      have h1 :
          Hom.comp E
              (Hom.comp FragmentContext.closedLeftUnitorInv
                (DayTensor.leftUnitor dayTensorUnit)) =
            Hom.comp E (Hom.id _) :=
        congrArg (Hom.comp E) hinj
      have h2 :
          Hom.comp
              (Hom.comp E FragmentContext.closedLeftUnitorInv)
              (DayTensor.leftUnitor dayTensorUnit) =
            Hom.comp E
              (Hom.comp FragmentContext.closedLeftUnitorInv
                (DayTensor.leftUnitor dayTensorUnit)) :=
        (Hom.comp_assoc _ _ _).symm
      exact h2.trans (h1.trans (Hom.comp_id E))

/-- Unconditional closed FO `ite true` Step soundness. -/
theorem FragCert.denote_ite_true_closed {A : Ty}
    (hFO : Ty.FirstOrder A)
    {T E : Term}
    (cT : FragCert.Closed T A) (cE : FragCert.Closed E A) :
    FragCert.denote
        (.ite CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
          (Ty.SemanticFragment.ofFirstOrder hFO)
          (FragCert.closed_bitLit_cert true) cT cE) =
      FragCert.denote cT := by
  rw [FragCert.denote_ite_eq, FragCert.closed_bitLit_denote_eq,
    FragmentContext.combinedOSplit_nil, FragmentContext.closedPoint,
    routeAFragmentBranching]
  change Hom.comp (iteElimFragment (Ty.SemanticFragment.ofFirstOrder hFO))
      (Hom.comp
        (DayTensor.map
          (Hom.comp (bitLitHom true) FragmentContext.combinedClosedCollapse)
          (additivePair (FragCert.denote cT) (FragCert.denote cE)))
        (DayTensor.map FragmentContext.closedLeftUnitorInv
          FragmentContext.closedLeftUnitorInv)) =
    FragCert.denote cT
  cases hFO with
  | unit =>
      change Hom.comp (iteElimRepresentable 1)
          (Hom.comp
            (DayTensor.map
              (Hom.comp (bitLitHom true) FragmentContext.combinedClosedCollapse)
              (additivePair (FragCert.denote cT) (FragCert.denote cE)))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv)) =
        FragCert.denote cT
      exact iteElimRepresentable_closed_bitLit_aux 1 true
        (FragCert.denote cT) (FragCert.denote cE)
  | bit =>
      change Hom.comp (iteElimRepresentable 2)
          (Hom.comp
            (DayTensor.map
              (Hom.comp (bitLitHom true) FragmentContext.combinedClosedCollapse)
              (additivePair (FragCert.denote cT) (FragCert.denote cE)))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv)) =
        FragCert.denote cT
      exact iteElimRepresentable_closed_bitLit_aux 2 true
        (FragCert.denote cT) (FragCert.denote cE)
  | qubit =>
      change Hom.comp (iteElimRepresentable 2)
          (Hom.comp
            (DayTensor.map
              (Hom.comp (bitLitHom true) FragmentContext.combinedClosedCollapse)
              (additivePair (FragCert.denote cT) (FragCert.denote cE)))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv)) =
        FragCert.denote cT
      exact iteElimRepresentable_closed_bitLit_aux 2 true
        (FragCert.denote cT) (FragCert.denote cE)
  | tensor hA hB =>
      change Hom.comp
          (iteElimRepresentable (Ty.FirstOrder.dimension (.tensor hA hB)))
          (Hom.comp
            (DayTensor.map
              (Hom.comp (bitLitHom true) FragmentContext.combinedClosedCollapse)
              (additivePair (FragCert.denote cT) (FragCert.denote cE)))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv)) =
        FragCert.denote cT
      exact iteElimRepresentable_closed_bitLit_aux _
        true (FragCert.denote cT) (FragCert.denote cE)

/-- Unconditional closed FO `ite false` Step soundness. -/
theorem FragCert.denote_ite_false_closed {A : Ty}
    (hFO : Ty.FirstOrder A)
    {T E : Term}
    (cT : FragCert.Closed T A) (cE : FragCert.Closed E A) :
    FragCert.denote
        (.ite CtxUAllBit.nil CtxLAllSomeFragment.nil OSplit.nil
          (Ty.SemanticFragment.ofFirstOrder hFO)
          (FragCert.closed_bitLit_cert false) cT cE) =
      FragCert.denote cE := by
  rw [FragCert.denote_ite_eq, FragCert.closed_bitLit_denote_eq,
    FragmentContext.combinedOSplit_nil, FragmentContext.closedPoint,
    routeAFragmentBranching]
  change Hom.comp (iteElimFragment (Ty.SemanticFragment.ofFirstOrder hFO))
      (Hom.comp
        (DayTensor.map
          (Hom.comp (bitLitHom false) FragmentContext.combinedClosedCollapse)
          (additivePair (FragCert.denote cT) (FragCert.denote cE)))
        (DayTensor.map FragmentContext.closedLeftUnitorInv
          FragmentContext.closedLeftUnitorInv)) =
    FragCert.denote cE
  cases hFO with
  | unit =>
      change Hom.comp (iteElimRepresentable 1)
          (Hom.comp
            (DayTensor.map
              (Hom.comp (bitLitHom false) FragmentContext.combinedClosedCollapse)
              (additivePair (FragCert.denote cT) (FragCert.denote cE)))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv)) =
        FragCert.denote cE
      exact iteElimRepresentable_closed_bitLit_aux 1 false
        (FragCert.denote cT) (FragCert.denote cE)
  | bit =>
      change Hom.comp (iteElimRepresentable 2)
          (Hom.comp
            (DayTensor.map
              (Hom.comp (bitLitHom false) FragmentContext.combinedClosedCollapse)
              (additivePair (FragCert.denote cT) (FragCert.denote cE)))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv)) =
        FragCert.denote cE
      exact iteElimRepresentable_closed_bitLit_aux 2 false
        (FragCert.denote cT) (FragCert.denote cE)
  | qubit =>
      change Hom.comp (iteElimRepresentable 2)
          (Hom.comp
            (DayTensor.map
              (Hom.comp (bitLitHom false) FragmentContext.combinedClosedCollapse)
              (additivePair (FragCert.denote cT) (FragCert.denote cE)))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv)) =
        FragCert.denote cE
      exact iteElimRepresentable_closed_bitLit_aux 2 false
        (FragCert.denote cT) (FragCert.denote cE)
  | tensor hA hB =>
      change Hom.comp
          (iteElimRepresentable (Ty.FirstOrder.dimension (.tensor hA hB)))
          (Hom.comp
            (DayTensor.map
              (Hom.comp (bitLitHom false) FragmentContext.combinedClosedCollapse)
              (additivePair (FragCert.denote cT) (FragCert.denote cE)))
            (DayTensor.map FragmentContext.closedLeftUnitorInv
              FragmentContext.closedLeftUnitorInv)) =
        FragCert.denote cE
      exact iteElimRepresentable_closed_bitLit_aux _
        false (FragCert.denote cT) (FragCert.denote cE)

/-- Legacy alias retained for citations that still mention the gap packaging. -/
theorem FragCert.denote_ite_true_closed_gap (d : ℕ) :
    (FragmentContext.combinedOSplit CtxUAllBit.nil OSplit.nil =
        DayTensor.map (DayTensor.leftUnitorInv dayTensorUnit)
          (DayTensor.leftUnitorInv dayTensorUnit)) →
      ∀ (T E : Hom dayTensorUnit (representable d)),
        Hom.comp (iteElimRepresentable d)
            (Hom.comp
              (DayTensor.map (bitLitHom true) (additivePair T E))
              (DayTensor.leftUnitorInv dayTensorUnit)) =
          T := fun _ T E =>
  iteElimRepresentable_bitLit_true d T E

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

theorem FragCert.denote_varU_eq {Γ Δ n A}
    (hΓ : CtxUAllBit Γ) (hL : CtxLAllSomeFragment Δ)
    (hl : Lookup Γ n A) (hD : Ty.Duplicable A) (hΔ : AllNone Δ)
    (hA : Ty.SemanticFragment A) :
    FragCert.denote (.varU hΓ hL hl hD hΔ hA) =
      FragmentContext.combinedLookupUnrestricted hΓ hl hΔ :=
  rfl

theorem FragCert.denote_varL_eq {Γ Δ n A}
    (hΓ : CtxUAllBit Γ) (hL : CtxLAllSomeFragment Δ)
    (hl : Lookup Δ n (some A)) (ho : OnlySomeAt Δ n)
    (hA : Ty.SemanticFragment A) :
    FragCert.denote (.varL hΓ hL hl ho hA) =
      FragmentContext.combinedLookupLinear hΓ hl ho :=
  rfl

theorem FragCert.denote_lamL_eq {Γ Δ A B M}
    (hΓ : CtxUAllBit Γ) (hL : CtxLAllSomeFragment Δ)
    (hAd : Ty.Admissible A) (hFO : Ty.FirstOrder A)
    (hB : Ty.SemanticFragment B) (c : FragCert Γ (some A :: Δ) M B) :
    FragCert.denote (.lamL hΓ hL hAd hFO hB c) =
      FragmentContext.abstractLinear hFO (FragCert.denote c) :=
  rfl

theorem FragCert.denote_lamU_eq {Γ Δ B M}
    (hΓ : CtxUAllBit Γ) (hL : CtxLAllSomeFragment Δ)
    (hAd : Ty.Admissible .bit) (hDup : Ty.Duplicable .bit)
    (hΔ : AllNone Δ) (hArr : Ty.SemanticFragment (.arrow .unres .bit B))
    (c : FragCert (.bit :: Γ) Δ M B) :
    FragCert.denote (.lamU hΓ hL hAd hDup hΔ hArr c) =
      FragmentContext.abstractUnrestricted (FragCert.denote c) :=
  rfl

theorem FragCert.denote_appL_eq {Γ Δ Δ₁ Δ₂ A B F X}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hFO : Ty.FirstOrder A)
    (hB : Ty.SemanticFragment B)
    (cF : FragCert Γ Δ₁ F (.arrow .lin A B)) (cX : FragCert Γ Δ₂ X A) :
    FragCert.denote (.appL hΓ hΔ hs hFO hB cF cX) =
      Hom.comp (FragmentContext.evalFragmentFirstOrder hFO _)
        (Hom.comp
          (DayTensor.map (FragCert.denote cF) (FragCert.denote cX))
          (FragmentContext.combinedOSplit hΓ hs)) :=
  rfl

theorem FragCert.denote_appU_eq {Γ Δ ΔF ΔX B F X}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ ΔF ΔX) (hN : AllNone ΔX) (hB : Ty.SemanticFragment B)
    (cF : FragCert Γ ΔF F (.arrow .unres .bit B))
    (cX : FragCert Γ ΔX X .bit) :
    FragCert.denote (.appU hΓ hΔ hs hN hB cF cX) =
      Hom.comp (FragmentContext.evalUnrestrictedBit _)
        (Hom.comp
          (DayTensor.map (FragCert.denote cF) (FragCert.denote cX))
          (FragmentContext.combinedOSplit hΓ hs)) :=
  rfl

theorem FragCert.denote_pair_eq {Γ Δ Δ₁ Δ₂ A B M N}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B)
    (cM : FragCert Γ Δ₁ M A) (cN : FragCert Γ Δ₂ N B) :
    FragCert.denote (.pair hΓ hΔ hs hA hB cM cN) =
      Hom.comp (FragmentContext.tensorIntro hA hB)
        (Hom.comp
          (DayTensor.map (FragCert.denote cM) (FragCert.denote cN))
          (FragmentContext.combinedOSplit hΓ hs)) :=
  rfl

theorem FragCert.denote_unpair_eq {Γ Δ Δ₁ Δ₂ A B C M K}
    (hΓ : CtxUAllBit Γ) (hΔ : CtxLAllSomeFragment Δ)
    (hs : OSplit Δ Δ₁ Δ₂) (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B)
    (hC : Ty.SemanticFragment C)
    (cM : FragCert Γ Δ₁ M (.tensor A B))
    (cK : FragCert Γ Δ₂ K (.arrow .lin A (.arrow .lin B C))) :
    FragCert.denote (.unpair hΓ hΔ hs hA hB hC cM cK) =
      Hom.comp (FragmentContext.unpairApply hA hB _)
        (Hom.comp
          (DayTensor.map (FragCert.denote cM) (FragCert.denote cK))
          (FragmentContext.combinedOSplit hΓ hs)) :=
  rfl

/-! ## Proof-witness independence -/

theorem FragCert.denote_unit_proof_independent {Γ Δ}
    (hΓ hΓ' : CtxUAllBit Γ) (hL hL' : CtxLAllSomeFragment Δ)
    (hΔ hΔ' : AllNone Δ) :
    FragCert.denote (.unit hΓ hL hΔ) =
      FragCert.denote (.unit hΓ' hL' hΔ') := by
  congr

theorem FragCert.denote_bitLit_proof_independent {Γ Δ b}
    (hΓ hΓ' : CtxUAllBit Γ) (hL hL' : CtxLAllSomeFragment Δ)
    (hΔ hΔ' : AllNone Δ) :
    FragCert.denote (.bitLit hΓ hL b hΔ) =
      FragCert.denote (.bitLit hΓ' hL' b hΔ') := by
  congr

theorem FragCert.denote_prim_proof_independent {Γ Δ p}
    (hΓ hΓ' : CtxUAllBit Γ) (hL hL' : CtxLAllSomeFragment Δ)
    (hΔ hΔ' : AllNone Δ) :
    FragCert.denote (.prim hΓ hL p hΔ) =
      FragCert.denote (.prim hΓ' hL' p hΔ') := by
  congr

theorem FragCert.denote_varU_proof_independent {Γ Δ n A}
    (hΓ hΓ' : CtxUAllBit Γ) (hL hL' : CtxLAllSomeFragment Δ)
    (hl hl' : Lookup Γ n A) (hD hD' : Ty.Duplicable A)
    (hΔ hΔ' : AllNone Δ) (hA hA' : Ty.SemanticFragment A) :
    FragCert.denote (.varU hΓ hL hl hD hΔ hA) =
      FragCert.denote (.varU hΓ' hL' hl' hD' hΔ' hA') := by
  congr

theorem FragCert.denote_varL_proof_independent {Γ Δ n A}
    (hΓ hΓ' : CtxUAllBit Γ) (hL hL' : CtxLAllSomeFragment Δ)
    (hl hl' : Lookup Δ n (some A)) (ho ho' : OnlySomeAt Δ n)
    (hA hA' : Ty.SemanticFragment A) :
    FragCert.denote (.varL hΓ hL hl ho hA) =
      FragCert.denote (.varL hΓ' hL' hl' ho' hA') := by
  congr

theorem FragCert.denote_lamL_proof_independent {Γ Δ A B M}
    (hΓ hΓ' : CtxUAllBit Γ) (hL hL' : CtxLAllSomeFragment Δ)
    (hAd hAd' : Ty.Admissible A) (hFO hFO' : Ty.FirstOrder A)
    (hB hB' : Ty.SemanticFragment B)
    (c : FragCert Γ (some A :: Δ) M B) :
    FragCert.denote (.lamL hΓ hL hAd hFO hB c) =
      FragCert.denote (.lamL hΓ' hL' hAd' hFO' hB' c) := by
  congr

theorem FragCert.denote_lamU_proof_independent {Γ Δ B M}
    (hΓ hΓ' : CtxUAllBit Γ) (hL hL' : CtxLAllSomeFragment Δ)
    (hAd hAd' : Ty.Admissible .bit) (hDup hDup' : Ty.Duplicable .bit)
    (hΔ hΔ' : AllNone Δ)
    (hArr hArr' : Ty.SemanticFragment (.arrow .unres .bit B))
    (c : FragCert (.bit :: Γ) Δ M B) :
    FragCert.denote (.lamU hΓ hL hAd hDup hΔ hArr c) =
      FragCert.denote (.lamU hΓ' hL' hAd' hDup' hΔ' hArr' c) := by
  congr

theorem FragCert.denote_appL_proof_independent {Γ Δ Δ₁ Δ₂ A B F X}
    (hΓ hΓ' : CtxUAllBit Γ) (hΔ hΔ' : CtxLAllSomeFragment Δ)
    (hs hs' : OSplit Δ Δ₁ Δ₂) (hFO hFO' : Ty.FirstOrder A)
    (hB hB' : Ty.SemanticFragment B)
    (cF : FragCert Γ Δ₁ F (.arrow .lin A B)) (cX : FragCert Γ Δ₂ X A) :
    FragCert.denote (.appL hΓ hΔ hs hFO hB cF cX) =
      FragCert.denote (.appL hΓ' hΔ' hs' hFO' hB' cF cX) := by
  congr

theorem FragCert.denote_appU_proof_independent {Γ Δ ΔF ΔX B F X}
    (hΓ hΓ' : CtxUAllBit Γ) (hΔ hΔ' : CtxLAllSomeFragment Δ)
    (hs hs' : OSplit Δ ΔF ΔX) (hN hN' : AllNone ΔX)
    (hB hB' : Ty.SemanticFragment B)
    (cF : FragCert Γ ΔF F (.arrow .unres .bit B))
    (cX : FragCert Γ ΔX X .bit) :
    FragCert.denote (.appU hΓ hΔ hs hN hB cF cX) =
      FragCert.denote (.appU hΓ' hΔ' hs' hN' hB' cF cX) := by
  congr

theorem FragCert.denote_pair_proof_independent {Γ Δ Δ₁ Δ₂ A B M N}
    (hΓ hΓ' : CtxUAllBit Γ) (hΔ hΔ' : CtxLAllSomeFragment Δ)
    (hs hs' : OSplit Δ Δ₁ Δ₂) (hA hA' : Ty.FirstOrder A)
    (hB hB' : Ty.FirstOrder B)
    (cM : FragCert Γ Δ₁ M A) (cN : FragCert Γ Δ₂ N B) :
    FragCert.denote (.pair hΓ hΔ hs hA hB cM cN) =
      FragCert.denote (.pair hΓ' hΔ' hs' hA' hB' cM cN) := by
  congr

theorem FragCert.denote_unpair_proof_independent {Γ Δ Δ₁ Δ₂ A B C M K}
    (hΓ hΓ' : CtxUAllBit Γ) (hΔ hΔ' : CtxLAllSomeFragment Δ)
    (hs hs' : OSplit Δ Δ₁ Δ₂) (hA hA' : Ty.FirstOrder A)
    (hB hB' : Ty.FirstOrder B) (hC hC' : Ty.SemanticFragment C)
    (cM : FragCert Γ Δ₁ M (.tensor A B))
    (cK : FragCert Γ Δ₂ K (.arrow .lin A (.arrow .lin B C))) :
    FragCert.denote (.unpair hΓ hΔ hs hA hB hC cM cK) =
      FragCert.denote (.unpair hΓ' hΔ' hs' hA' hB' hC' cM cK) := by
  congr

theorem FragCert.denote_ite_proof_independent {Γ Δ Δ₁ Δ₂ A B T E}
    (hΓ hΓ' : CtxUAllBit Γ) (hΔ hΔ' : CtxLAllSomeFragment Δ)
    (hs hs' : OSplit Δ Δ₁ Δ₂) (hA hA' : Ty.SemanticFragment A)
    (cB : FragCert Γ Δ₁ B .bit) (cT : FragCert Γ Δ₂ T A)
    (cE : FragCert Γ Δ₂ E A) :
    FragCert.denote (.ite hΓ hΔ hs hA cB cT cE) =
      FragCert.denote (.ite hΓ' hΔ' hs' hA' cB cT cE) := by
  congr

theorem FragCert.denote_measure_proof_independent {Γ Δ Δ₁ Δ₂ A Q K}
    (hΓ hΓ' : CtxUAllBit Γ) (hΔ hΔ' : CtxLAllSomeFragment Δ)
    (hs hs' : OSplit Δ Δ₁ Δ₂) (hA hA' : Ty.SemanticFragment A)
    (cQ : FragCert Γ Δ₁ Q .qubit)
    (cK : FragCert Γ Δ₂ K (.arrow .unres .bit (.arrow .lin .qubit A))) :
    FragCert.denote (.measure hΓ hΔ hs hA cQ cK) =
      FragCert.denote (.measure hΓ' hΔ' hs' hA' cQ cK) := by
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
