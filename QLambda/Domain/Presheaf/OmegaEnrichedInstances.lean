/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.OmegaEnriched
import QLambda.Domain.Presheaf.instPartialOrderSuperoperator
import QLambda.Domain.Presheaf.instOrderBotSuperoperator
import QLambda.Domain.Presheaf.omegaComplete
import QLambda.Domain.Presheaf.unitHomPartialOrder
import QLambda.Domain.Presheaf.unitHomOrderBot
import QLambda.Domain.Presheaf.unitHomOmegaComplete
import QLambda.Domain.Presheaf.classicalHomPartialOrder
import QLambda.Domain.Presheaf.classicalHomOrderBot
import QLambda.Domain.Presheaf.classicalHomOmegaComplete
import QLambda.Domain.Presheaf.biorthogonalHomPartialOrder
import QLambda.Domain.Presheaf.biorthogonalHomOrderBot
import QLambda.Domain.Presheaf.biorthogonalHomOmegaComplete

/-!
# Instances from `OmegaEnriched`
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

theorem unitHom_precomp_mono {P Q : Module} (u : Hom P Q) :
    Monotone (fun f : Hom Q dayTensorUnit => Hom.comp f u) := by
  intro f g h n x
  exact h n (u.app n x)

/-- Precomposition preserves pointwise increasing suprema. -/
theorem unitHom_precomp_omegaSup {P Q : Module}
    (c : ℕ → Hom Q dayTensorUnit) (hc : Monotone c) (u : Hom P Q) :
    Hom.comp (QLambda.Domain.OmegaComplete.ωSup c hc) u =
      QLambda.Domain.OmegaComplete.ωSup
        (fun k => Hom.comp (c k) u)
        ((unitHom_precomp_mono u).comp hc) := by
  apply Hom.ext
  intro n x
  rfl

set_option maxHeartbeats 800000

/-! ## Postcomposition continuity on maps into the tensor unit

Postcomposition by `v : Hom(I,I)` acts fiberwise as left Superoperator
composition with `v.app 1 id`, by naturality of `v` on the representable
unit.  Continuity then follows from `Superoperator.comp_omegaSup_right`.
-/

/-- On the Day unit, every endomorphism acts by ordinary superoperator
composition with its value at the identity. -/
theorem unitHom_app_eq_comp
    (v : Hom dayTensorUnit dayTensorUnit) {n : ℕ}
    (z : Superoperator n 1) :
    (v.app n z : Superoperator n 1) =
      Superoperator.comp
        (v.app 1 (Superoperator.identity 1) : Superoperator 1 1) z := by
  have hnat :
      (v.app n (Superoperator.comp (Superoperator.identity 1) z) :
          Superoperator n 1) =
        Superoperator.comp
          (v.app 1 (Superoperator.identity 1) : Superoperator 1 1) z :=
    v.naturality (Superoperator.identity 1) z
  rwa [Superoperator.identity_comp] at hnat

/-- Postcomposition by a fixed map of the tensor unit is monotone. -/
theorem unitHom_postcomp_mono {P : Module}
    (v : Hom dayTensorUnit dayTensorUnit) :
    Monotone (fun f : Hom P dayTensorUnit => Hom.comp v f) := by
  intro f g hfg n x
  change
    (show Superoperator n 1 from v.app n (f.app n x)) ≤
      (show Superoperator n 1 from v.app n (g.app n x))
  rw [unitHom_app_eq_comp v (show Superoperator n 1 from f.app n x),
    unitHom_app_eq_comp v (show Superoperator n 1 from g.app n x)]
  exact Superoperator.comp_mono_right _ (hfg n x)

/-- Postcomposition preserves pointwise increasing suprema into the unit. -/
theorem unitHom_postcomp_omegaSup {P : Module}
    (v : Hom dayTensorUnit dayTensorUnit)
    (c : ℕ → Hom P dayTensorUnit) (hc : Monotone c) :
    Hom.comp v (QLambda.Domain.OmegaComplete.ωSup c hc) =
      QLambda.Domain.OmegaComplete.ωSup
        (fun k => Hom.comp v (c k))
        ((unitHom_postcomp_mono v).comp hc) := by
  apply Hom.ext
  intro n x
  let φ : Superoperator 1 1 := v.app 1 (Superoperator.identity 1)
  let d : ℕ → Superoperator n 1 := fun k => (c k).app n x
  have hd : Monotone d := fun _ _ h => hc h n x
  let z : Superoperator n 1 :=
    (QLambda.Domain.OmegaComplete.ωSup c hc).app n x
  have hz : z = Superoperator.omegaSup d hd := rfl
  let e : ℕ → Superoperator n 1 :=
    fun k => v.app n ((c k).app n x)
  have he : Monotone e := fun _ _ h =>
    (unitHom_postcomp_mono v).comp hc h n x
  have hL : (v.app n z : Superoperator n 1) =
      Superoperator.comp φ (Superoperator.omegaSup d hd) := by
    rw [← hz]
    exact unitHom_app_eq_comp v z
  have hMid :
      Superoperator.comp φ (Superoperator.omegaSup d hd) =
        Superoperator.omegaSup (fun k => Superoperator.comp φ (d k))
          ((Superoperator.comp_mono_right φ).comp hd) :=
    Superoperator.comp_omegaSup_right φ d hd
  have hR :
      Superoperator.omegaSup (fun k => Superoperator.comp φ (d k))
          ((Superoperator.comp_mono_right φ).comp hd) =
        Superoperator.omegaSup e he := by
    apply le_antisymm
    · apply Superoperator.omegaSup_le
      intro k
      have hk : Superoperator.comp φ (d k) = e k :=
        (unitHom_app_eq_comp v (d k)).symm
      rw [hk]
      exact Superoperator.le_omegaSup e he k
    · apply Superoperator.omegaSup_le
      intro k
      have hk : e k = Superoperator.comp φ (d k) :=
        unitHom_app_eq_comp v (d k)
      rw [hk]
      exact Superoperator.le_omegaSup
        (fun r => Superoperator.comp φ (d r)) _ k
  -- Both sides of the Hom.ext goal are the Carrier (= Superoperator) values.
  exact (hL.trans (hMid.trans hR))

theorem classicalHom_precomp_mono {M M' : Module}
    (N : BiorthogonalObject) (u : Hom M' M) :
    Monotone (fun f : Hom M N.module => Hom.comp f u) := by
  intro f g hfg
  change
    UnitHomLE (dayTensor M' (DayNegation.neg N.module))
      (closedPairingEquiv M' N (Hom.comp f u))
      (closedPairingEquiv M' N (Hom.comp g u))
  rw [closedPairingEquiv_comp_left, closedPairingEquiv_comp_left]
  exact unitHom_precomp_mono
    (DayTensor.map u (Hom.id (DayNegation.neg N.module))) hfg

theorem classicalHom_precomp_omegaSup {M M' : Module}
    (N : BiorthogonalObject)
    (c : ℕ → Hom M N.module) (hc : Monotone c) (u : Hom M' M) :
    Hom.comp (QLambda.Domain.OmegaComplete.ωSup c hc) u =
      QLambda.Domain.OmegaComplete.ωSup
        (fun k => Hom.comp (c k) u)
        ((classicalHom_precomp_mono N u).comp hc) := by
  apply (closedPairingEquiv M' N).injective
  have hpair :
      closedPairingEquiv M N
          (QLambda.Domain.OmegaComplete.ωSup c hc) =
        QLambda.Domain.OmegaComplete.ωSup
          (fun k => closedPairingEquiv M N (c k))
          (classicalHom_paired_mono hc) :=
    Equiv.apply_symm_apply (closedPairingEquiv M N) _
  have hpair' :
      closedPairingEquiv M' N
          (QLambda.Domain.OmegaComplete.ωSup
            (fun k => Hom.comp (c k) u)
            ((classicalHom_precomp_mono N u).comp hc)) =
        QLambda.Domain.OmegaComplete.ωSup
          (fun k => closedPairingEquiv M' N (Hom.comp (c k) u))
          (classicalHom_paired_mono
            ((classicalHom_precomp_mono N u).comp hc)) :=
    Equiv.apply_symm_apply (closedPairingEquiv M' N) _
  rw [closedPairingEquiv_comp_left, hpair, hpair']
  refine (unitHom_precomp_omegaSup
      (fun k => closedPairingEquiv M N (c k))
      (classicalHom_paired_mono hc)
      (DayTensor.map u (Hom.id (DayNegation.neg N.module)))).trans ?_
  congr 1
  funext k
  exact (closedPairingEquiv_comp_left N u (c k)).symm

/-- Postcomposition is monotone for the transported classical order.
Right naturality of the closed pairing reduces this to precomposition
continuity on maps into the tensor unit. -/
theorem classicalHom_postcomp_mono {M : Module}
    {N N' : BiorthogonalObject} (v : Hom N.module N'.module) :
    Monotone (fun f : Hom M N.module => Hom.comp v f) := by
  intro f g hfg
  change
    UnitHomLE (dayTensor M (DayNegation.neg N'.module))
      (closedPairingEquiv M N' (Hom.comp v f))
      (closedPairingEquiv M N' (Hom.comp v g))
  rw [closedPairingEquiv_comp_right, closedPairingEquiv_comp_right]
  exact unitHom_precomp_mono
    (DayTensor.map (Hom.id M) (DayNegation.map v)) hfg

/-- Postcomposition preserves ω-suprema of classical homs. -/
theorem classicalHom_postcomp_omegaSup {M : Module}
    {N N' : BiorthogonalObject} (v : Hom N.module N'.module)
    (c : ℕ → Hom M N.module) (hc : Monotone c) :
    Hom.comp v (QLambda.Domain.OmegaComplete.ωSup c hc) =
      QLambda.Domain.OmegaComplete.ωSup
        (fun k => Hom.comp v (c k))
        ((classicalHom_postcomp_mono (N := N) (N' := N') v).comp hc) := by
  apply (closedPairingEquiv M N').injective
  have hpair :
      closedPairingEquiv M N
          (QLambda.Domain.OmegaComplete.ωSup c hc) =
        QLambda.Domain.OmegaComplete.ωSup
          (fun k => closedPairingEquiv M N (c k))
          (classicalHom_paired_mono hc) :=
    Equiv.apply_symm_apply (closedPairingEquiv M N) _
  have hpair' :
      closedPairingEquiv M N'
          (QLambda.Domain.OmegaComplete.ωSup
            (fun k => Hom.comp v (c k))
            ((classicalHom_postcomp_mono (N := N) (N' := N') v).comp hc)) =
        QLambda.Domain.OmegaComplete.ωSup
          (fun k => closedPairingEquiv M N' (Hom.comp v (c k)))
          (classicalHom_paired_mono
            ((classicalHom_postcomp_mono (N := N) (N' := N') v).comp
              hc)) :=
    Equiv.apply_symm_apply (closedPairingEquiv M N') _
  rw [closedPairingEquiv_comp_right, hpair, hpair']
  refine (unitHom_precomp_omegaSup
      (fun k => closedPairingEquiv M N (c k))
      (classicalHom_paired_mono hc)
      (DayTensor.map (Hom.id M) (DayNegation.map v))).trans ?_
  congr 1
  funext k
  exact (closedPairingEquiv_comp_right v (c k)).symm

/-- Day-biorthogonal classical objects form an ωCPO-enriched category. -/
noncomputable def biorthogonalOmegaCategory :
    QLambda.Domain.OmegaCategory where
  Obj := ClassicalObject DayNegation.data
  hom A B :=
    { Carrier := ClassicalObject.Hom A B
      partialOrder := biorthogonalHomPartialOrder A B
      omegaComplete := biorthogonalHomOmegaComplete A B }
  id := ClassicalObject.id _
  comp := ClassicalObject.comp
  comp_mono_left := fun {_ _ C} g =>
    classicalHom_precomp_mono C g
  comp_mono_right := fun {_ B C} f =>
    classicalHom_postcomp_mono (N := B) (N' := C) f
  comp_ωSup_left := fun {_ _ C} c hc g =>
    classicalHom_precomp_omegaSup C c hc g
  comp_ωSup_right := fun {_ B C} f c hc =>
    classicalHom_postcomp_omegaSup (N := B) (N' := C) f c hc
  id_comp := ClassicalObject.id_comp
  comp_id := ClassicalObject.comp_id
  assoc := fun h g f => (ClassicalObject.comp_assoc h g f).symm

end SuperoperatorModule

/-- Finite dimensions and TNI superoperators, enriched over pointed ωCPOs
by Choi refinement. -/
noncomputable def superoperatorOmegaCategory :
    QLambda.Domain.OmegaCategory where
  Obj := ℕ
  hom n m :=
    { Carrier := Superoperator n m
      partialOrder := inferInstance
      omegaComplete := inferInstance }
  id := Superoperator.identity _
  comp := Superoperator.comp
  comp_mono_left := Superoperator.comp_mono_left
  comp_mono_right := Superoperator.comp_mono_right
  comp_ωSup_left := Superoperator.comp_omegaSup_left
  comp_ωSup_right := Superoperator.comp_omegaSup_right
  id_comp := Superoperator.identity_comp
  comp_id := Superoperator.comp_identity
  assoc := fun h g f => (Superoperator.comp_assoc h g f).symm

end QLambda.Domain.Presheaf
