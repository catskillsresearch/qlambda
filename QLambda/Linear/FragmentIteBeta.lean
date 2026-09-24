/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentItePrep

/-!
# Representable `ite` β on bit literals

Selection equations for `iteElimRepresentable` on `bitLit true/false`.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000
open Domain.Presheaf
open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf.SigmaMon
open DayTensor
open scoped ComplexOrder MatrixOrder BigOperators

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




end QLambda.Linear
