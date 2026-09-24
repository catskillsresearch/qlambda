/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.CanonicalReflexivity

/-!
# Reflexivity of the tensor-unit representable `y(1)`
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u

/-- Concrete module-level description of the first Day negation of a
representable. -/
noncomputable def dayNegationRepresentableIso (A : ℕ) :
    Iso (DayNegation.neg (representable A))
      (internalHomRepresentable A dayTensorUnit) :=
  dayInternalHomRepresentableIso A dayTensorUnit

/-- Explicit fibers of representable Day negation:
`¬y(A)(n) ≃ Superoperator (n*A) 1`. -/
noncomputable def dayNegationRepresentableFiberEquiv (A n : ℕ) :
    ((DayNegation.neg (representable A)).obj n).Carrier ≃
      Superoperator (n * A) 1 :=
  (dayInternalHomRepresentableFiberEquiv A dayTensorUnit n).trans
    (Equiv.refl _)

/-- The tensor pairing is the distinguished element of `¬y(1)(1)`. -/
noncomputable def dayNegationOneProbe :
    ((DayNegation.neg (representable 1)).obj 1).Carrier :=
  dayTensorIntro 1 1

@[simp]
theorem dayNegationOneProbe_app {m n : ℕ}
    (x : Superoperator m 1) (y : Superoperator n 1) :
    dayNegationOneProbe.app x y = Superoperator.tensor x y :=
  rfl

/-- Evaluation at the tensor pairing gives a concrete inverse candidate
from `¬¬y(1)` to `y(1)`. -/
noncomputable def representableOneDoubleDualEvaluation :
    Hom (DayNegation.neg (DayNegation.neg (representable 1)))
      (representable 1) where
  app := fun n F =>
    Superoperator.comp
      (F.app (Superoperator.identity n) dayNegationOneProbe)
      (Superoperator.tensorRightUnitorInv n)
  map_zero := by
    intro n
    change Superoperator.comp 0
      (Superoperator.tensorRightUnitorInv n) = 0
    rw [Superoperator.comp_zero_left]
  map_sum := by
    intro ι _ n f s h
    exact SigmaMon.ChoiSum.comp_right
      (Superoperator.tensorRightUnitorInv n)
      (h n 1 (Superoperator.identity n) dayNegationOneProbe)
  naturality := by
    intro m n F f
    change
      Superoperator.comp
          (F.app
            (Superoperator.comp f (Superoperator.identity m))
            dayNegationOneProbe)
          (Superoperator.tensorRightUnitorInv m) =
        Superoperator.comp
          (Superoperator.comp
            (F.app (Superoperator.identity n) dayNegationOneProbe)
            (Superoperator.tensorRightUnitorInv n))
          f
    rw [Superoperator.comp_identity]
    have hF := F.naturality (Superoperator.identity n)
      dayNegationOneProbe f (Superoperator.identity 1)
    change
      F.app
          (Superoperator.comp (Superoperator.identity n) f)
          ((DayNegation.neg (representable 1)).act
            dayNegationOneProbe (Superoperator.identity 1)) =
        Superoperator.comp
          (F.app (Superoperator.identity n) dayNegationOneProbe)
          (Superoperator.tensor f (Superoperator.identity 1)) at hF
    rw [Superoperator.identity_comp,
      (DayNegation.neg (representable 1)).act_id] at hF
    rw [hF]
    calc
      Superoperator.comp
          (Superoperator.comp
            (F.app (Superoperator.identity n) dayNegationOneProbe)
            (Superoperator.tensor f (Superoperator.identity 1)))
          (Superoperator.tensorRightUnitorInv m) =
        Superoperator.comp
          (F.app (Superoperator.identity n) dayNegationOneProbe)
          (Superoperator.comp
            (Superoperator.tensor f (Superoperator.identity 1))
            (Superoperator.tensorRightUnitorInv m)) :=
              (Superoperator.comp_assoc _ _ _).symm
      _ = Superoperator.comp
          (F.app (Superoperator.identity n) dayNegationOneProbe)
          (Superoperator.comp
            (Superoperator.tensorRightUnitorInv n) f) := by
              rw [Superoperator.tensorRightUnitorInv_naturality]
      _ = Superoperator.comp
          (Superoperator.comp
            (F.app (Superoperator.identity n) dayNegationOneProbe)
            (Superoperator.tensorRightUnitorInv n))
          f :=
            Superoperator.comp_assoc _ _ _

@[simp]
theorem representableOneDoubleDualEvaluation_app
    (n : ℕ)
    (F : ((DayNegation.neg (DayNegation.neg (representable 1))).obj n).Carrier) :
    representableOneDoubleDualEvaluation.app n F =
      Superoperator.comp
        (F.app (Superoperator.identity n) dayNegationOneProbe)
        (Superoperator.tensorRightUnitorInv n) :=
  rfl

@[simp]
theorem representableOne_unit_app_app
    {n p q : ℕ} (x : Superoperator n 1)
    (r : Superoperator p n)
    (b : ((DayNegation.neg (representable 1)).obj q).Carrier) :
    ((DayNegation.unit (representable 1)).app n x).app r b =
      dayTensorUnit.act
        (b.app (Superoperator.identity q)
          ((representable 1).act x r))
        (Superoperator.tensorSwap p q) :=
  rfl

private theorem tensorSwap_one_one :
    Superoperator.tensorSwap 1 1 = Superoperator.identity 1 := by
  rw [show Superoperator.tensorSwap 1 1 =
    Superoperator.ofEquivalence (Superoperator.tensorSwapEquiv 1 1) from rfl]
  have h : Superoperator.tensorSwapEquiv 1 1 =
      Equiv.refl (Fin 1) := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    omega
  rw [h, Superoperator.ofEquivalence_refl]

private theorem tensorRightUnitorInv_one :
    Superoperator.tensorRightUnitorInv 1 =
      Superoperator.identity 1 := by
  rw [show Superoperator.tensorRightUnitorInv 1 =
    Superoperator.ofEquivalence
      (Superoperator.tensorRightUnitorEquiv 1).symm from rfl]
  have h : (Superoperator.tensorRightUnitorEquiv 1).symm =
      Equiv.refl (Fin 1) := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    omega
  rw [h, Superoperator.ofEquivalence_refl]

/-- Evaluation at the tensor probe is a retraction of the canonical unit for
`y(1)`.  The converse is precisely the remaining bipolar-surjectivity
direction. -/
theorem representableOneDoubleDualEvaluation_unit :
    Hom.comp representableOneDoubleDualEvaluation
      (DayNegation.unit (representable 1)) =
        Hom.id (representable 1) := by
  apply Hom.ext
  intro n x
  rw [Hom.comp_app, representableOneDoubleDualEvaluation_app, Hom.id_app]
  change Superoperator n 1 at x
  rw [representableOne_unit_app_app]
  unfold dayNegationOneProbe dayTensorIntro
  simp only [representable_act, Superoperator.comp_identity]
  change
    Superoperator.comp
        (Superoperator.comp
          (Superoperator.tensor (Superoperator.identity 1) x)
          (Superoperator.tensorSwap n 1))
        (Superoperator.tensorRightUnitorInv n) = x
  rw [← Superoperator.tensorSwap_naturality x
      (Superoperator.identity 1),
    tensorSwap_one_one, Superoperator.identity_comp,
    Superoperator.tensorRightUnitorInv_naturality,
    tensorRightUnitorInv_one, Superoperator.identity_comp]

/-- The canonical double-negation unit is fiberwise injective for `y(1)`. -/
theorem representableOne_unit_injective (n : ℕ) :
    Function.Injective
      ((DayNegation.unit (representable 1)).app n) := by
  intro x y hxy
  have hret (z : Superoperator n 1) :
      representableOneDoubleDualEvaluation.app n
          ((DayNegation.unit (representable 1)).app n z) = z := by
    have h := congrArg
      (fun f : Hom (representable 1) (representable 1) => f.app n z)
      representableOneDoubleDualEvaluation_unit
    exact h
  rw [← hret x, hxy, hret y]

/-- For `y(1)`, fiberwise bipolar surjectivity alone completes the concrete
reflexivity witness: the required sum-preserving inverse is the explicit
evaluation map above. -/
noncomputable def representableOneReflexivityOfSurjective
    (h : ∀ n, Function.Surjective
      ((DayNegation.unit (representable 1)).app n)) :
    RepresentableReflexivity 1 where
  inv := representableOneDoubleDualEvaluation
  hom_inv := by
    apply Hom.ext
    intro n F
    obtain ⟨x, rfl⟩ := h n F
    have hret := congrArg
      (fun f : Hom (representable 1) (representable 1) => f.app n x)
      representableOneDoubleDualEvaluation_unit
    exact congrArg ((DayNegation.unit (representable 1)).app n) hret
  inv_hom := representableOneDoubleDualEvaluation_unit

/-- Every map `(q*1) → 1` factors as `(χ ∘ ρ⁻¹) ⊗ id₁`. -/
theorem tensor_comp_rightUnitorInv_identity (q : ℕ)
    (χ : Superoperator (q * 1) 1) :
    Superoperator.tensor
      (Superoperator.comp χ (Superoperator.tensorRightUnitorInv q))
      (Superoperator.identity 1) = χ := by
  set f := Superoperator.comp χ (Superoperator.tensorRightUnitorInv q)
  have hnat := Superoperator.tensorRightUnitor_naturality f
  have htensor :
      Superoperator.tensor f (Superoperator.identity 1) =
        Superoperator.comp (Superoperator.tensorRightUnitorInv 1)
          (Superoperator.comp f (Superoperator.tensorRightUnitor q)) := by
    have h :=
      congrArg (Superoperator.comp (Superoperator.tensorRightUnitorInv 1)) hnat
    simpa [Superoperator.comp_assoc, Superoperator.tensorRightUnitor_inv_hom,
      Superoperator.identity_comp] using h
  rw [htensor]
  change
    Superoperator.comp (Superoperator.tensorRightUnitorInv 1)
        (Superoperator.comp
          (Superoperator.comp χ (Superoperator.tensorRightUnitorInv q))
          (Superoperator.tensorRightUnitor q)) =
      χ
  rw [← Superoperator.comp_assoc, Superoperator.tensorRightUnitor_inv_hom,
    Superoperator.comp_identity, tensorRightUnitorInv_one,
    Superoperator.identity_comp]

/-- Reconstruct a functional in `¬y(1)_q` from its value on the two identities. -/
theorem dayNegationOne_app_eq {q p q' : ℕ}
    (b : ((DayNegation.neg (representable 1)).obj q).Carrier)
    (r : Superoperator p q) (s : Superoperator q' 1) :
    b.app r s =
      dayTensorUnit.act
        (b.app (Superoperator.identity q) (Superoperator.identity 1))
        (Superoperator.tensor r s) := by
  have hb := b.naturality (Superoperator.identity q) (Superoperator.identity 1) r s
  simpa [Superoperator.identity_comp] using hb

/-- Convert the tensor-unit action to ordinary superoperator composition. -/
theorem dayTensorUnit_act_eq_comp {m n : ℕ}
    (x : Superoperator n 1) (f : Superoperator m n) :
    dayTensorUnit.act x f = Superoperator.comp x f :=
  representable_act x f

/-- The probe generates every fiber of `¬y(1)` after right-unitor transport. -/
theorem dayNegationOneProbe_generates {q : ℕ}
    (b : ((DayNegation.neg (representable 1)).obj q).Carrier) :
    (DayNegation.neg (representable 1)).act dayNegationOneProbe
        (Superoperator.comp
          (b.app (Superoperator.identity q) (Superoperator.identity 1))
          (Superoperator.tensorRightUnitorInv q)) =
      b := by
  apply Bilinear.ext
  intro p q' r s
  change Superoperator p q at r
  change Superoperator q' 1 at s
  set χ : Superoperator (q * 1) 1 :=
    b.app (Superoperator.identity q) (Superoperator.identity 1)
  have hχ := tensor_comp_rightUnitorInv_identity q χ
  -- LHS is definitionally `tensor (comp (comp χ ρ⁻¹) r) s`.
  have hLHS :
      ((DayNegation.neg (representable 1)).act dayNegationOneProbe
            (Superoperator.comp χ (Superoperator.tensorRightUnitorInv q))).app
          r s =
        Superoperator.tensor
          (Superoperator.comp
            (Superoperator.comp χ (Superoperator.tensorRightUnitorInv q)) r)
          s :=
    rfl
  have hRHS :
      Superoperator.tensor
          (Superoperator.comp
            (Superoperator.comp χ (Superoperator.tensorRightUnitorInv q)) r)
          s =
        b.app r s := by
    have hfactor :
        Superoperator.tensor
            (Superoperator.comp
              (Superoperator.comp χ (Superoperator.tensorRightUnitorInv q)) r)
            s =
          Superoperator.comp
            (Superoperator.tensor
              (Superoperator.comp χ (Superoperator.tensorRightUnitorInv q))
              (Superoperator.identity 1))
            (Superoperator.tensor r s) := by
      conv_lhs => rw [← Superoperator.identity_comp s]
      rw [Superoperator.tensor_comp]
    rw [hfactor, hχ, ← dayTensorUnit_act_eq_comp]
    simpa [χ] using (dayNegationOne_app_eq (q := q) b r s).symm
  exact hLHS.trans hRHS

/-- Probe action evaluates as a tensor after precomposition. -/
theorem dayNegationOneProbe_act_app {q p q' : ℕ}
    (f : Superoperator q 1) (r : Superoperator p q)
    (s : Superoperator q' 1) :
    ((DayNegation.neg (representable 1)).act dayNegationOneProbe f).app r s =
      Superoperator.tensor (Superoperator.comp f r) s :=
  rfl

/-- Naturality of a double dual in the first argument. -/
theorem representableOne_doubleDual_app_identity
    {n p q : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable 1))).obj n).Carrier)
    (r : Superoperator p n)
    (b : ((DayNegation.neg (representable 1)).obj q).Carrier) :
    F.app r b =
      dayTensorUnit.act (F.app (Superoperator.identity n) b)
        (Superoperator.tensor r (Superoperator.identity q)) := by
  have hF := F.naturality (Superoperator.identity n) b r (Superoperator.identity q)
  simpa [Superoperator.identity_comp,
    (DayNegation.neg (representable 1)).act_id] using hF

/-- Naturality of a double dual against probe action. -/
theorem representableOne_doubleDual_app_probe
    {n q : ℕ}
    (F : ((DayNegation.neg (DayNegation.neg (representable 1))).obj n).Carrier)
    (f : Superoperator q 1) :
    F.app (Superoperator.identity n)
        ((DayNegation.neg (representable 1)).act dayNegationOneProbe f) =
      dayTensorUnit.act
        (F.app (Superoperator.identity n) dayNegationOneProbe)
        (Superoperator.tensor (Superoperator.identity n) f) := by
  have hF := F.naturality (Superoperator.identity n) dayNegationOneProbe
    (Superoperator.identity n) f
  simpa [Superoperator.comp_identity] using hF

/-- Evaluation is a section of the canonical unit for `y(1)`. -/
theorem representableOne_unit_eval :
    Hom.comp (DayNegation.unit (representable 1))
      representableOneDoubleDualEvaluation =
        Hom.id (DayNegation.neg (DayNegation.neg (representable 1))) := by
  apply Hom.ext
  intro n F
  apply Bilinear.ext
  intro p q r b
  change Superoperator p n at r
  rw [Hom.comp_app, Hom.id_app, representableOneDoubleDualEvaluation_app]
  set χ : Superoperator (n * 1) 1 :=
    F.app (Superoperator.identity n) dayNegationOneProbe
  set x : Superoperator n 1 :=
    Superoperator.comp χ (Superoperator.tensorRightUnitorInv n)
  -- Leap to the Superoperator form; `dayTensorUnit.act` is defeq `comp`.
  change
    Superoperator.comp
        (b.app (Superoperator.identity q) (Superoperator.comp x r))
        (Superoperator.tensorSwap p q) =
      F.app r b
  set f : Superoperator q 1 :=
    Superoperator.comp
      (b.app (Superoperator.identity q) (Superoperator.identity 1))
      (Superoperator.tensorRightUnitorInv q)
  have hb :
      (DayNegation.neg (representable 1)).act dayNegationOneProbe f = b :=
    dayNegationOneProbe_generates b
  -- Avoid rewriting `b` under `.app` (Carrier/Bilinear opacity); use congrArg.
  have happ_b :
      b.app (Superoperator.identity q) (Superoperator.comp x r) =
        Superoperator.tensor f (Superoperator.comp x r) := by
    have h :=
      congrArg
        (fun β : ((DayNegation.neg (representable 1)).obj q).Carrier =>
          β.app (Superoperator.identity q) (Superoperator.comp x r))
        hb
    rw [← h, dayNegationOneProbe_act_app, Superoperator.comp_identity]
  rw [happ_b]
  have hswap :
      Superoperator.comp
          (Superoperator.tensor f (Superoperator.comp x r))
          (Superoperator.tensorSwap p q) =
        Superoperator.tensor (Superoperator.comp x r) f := by
    have hnat :=
      Superoperator.tensorSwap_naturality (Superoperator.comp x r) f
    simpa [tensorSwap_one_one, Superoperator.identity_comp] using hnat.symm
  rw [hswap]
  have htensor :
      Superoperator.tensor (Superoperator.comp x r) f =
        Superoperator.comp χ (Superoperator.tensor r f) := by
    have hfactor :
        Superoperator.tensor (Superoperator.comp x r) f =
          Superoperator.comp
            (Superoperator.tensor
              (Superoperator.comp χ (Superoperator.tensorRightUnitorInv n))
              (Superoperator.identity 1))
            (Superoperator.tensor r f) := by
      change Superoperator.tensor
          (Superoperator.comp
            (Superoperator.comp χ (Superoperator.tensorRightUnitorInv n)) r)
          f =
        _
      conv_lhs => rw [← Superoperator.identity_comp f]
      rw [Superoperator.tensor_comp]
    rw [hfactor, tensor_comp_rightUnitorInv_identity]
  rw [htensor]
  -- RHS: replace `b` by probe action via congrArg (Carrier-safe).
  have hF_b :
      F.app r b =
        F.app r
          ((DayNegation.neg (representable 1)).act dayNegationOneProbe f) :=
    congrArg (F.app r) hb.symm
  have hF_exp :
      F.app r
          ((DayNegation.neg (representable 1)).act dayNegationOneProbe f) =
        Superoperator.comp
          (Superoperator.comp χ
            (Superoperator.tensor (Superoperator.identity n) f))
          (Superoperator.tensor r (Superoperator.identity q)) := by
    have h1 := representableOne_doubleDual_app_identity F r
      ((DayNegation.neg (representable 1)).act dayNegationOneProbe f)
    have h2 := representableOne_doubleDual_app_probe F f
    rw [h1, h2]
    -- `dayTensorUnit.act` is defeq `Superoperator.comp`; `χ` abbreviates the probe value.
    change
      Superoperator.comp
          (Superoperator.comp χ
            (Superoperator.tensor (Superoperator.identity n) f))
          (Superoperator.tensor r (Superoperator.identity q)) =
        Superoperator.comp
          (Superoperator.comp χ
            (Superoperator.tensor (Superoperator.identity n) f))
          (Superoperator.tensor r (Superoperator.identity q))
    rfl
  rw [hF_b, hF_exp]
  -- Remaining coherence: `χ ∘ (r ⊗ f) = (χ ∘ (id ⊗ f)) ∘ (r ⊗ id)`.
  rw [← Superoperator.comp_assoc]
  congr 1
  rw [← Superoperator.tensor_comp, Superoperator.identity_comp,
    Superoperator.comp_identity]

/-- Fiberwise surjectivity of the canonical unit of `y(1)`. -/
theorem representableOne_unit_surjective (n : ℕ) :
    Function.Surjective
      ((DayNegation.unit (representable 1)).app n) := by
  intro F
  refine ⟨representableOneDoubleDualEvaluation.app n F, ?_⟩
  have h := congrArg
    (fun g : Hom
        (DayNegation.neg (DayNegation.neg (representable 1)))
        (DayNegation.neg (DayNegation.neg (representable 1))) =>
      g.app n F)
    representableOne_unit_eval
  exact h

/-- Unconditional reflexivity of the tensor unit representable. -/
noncomputable def representableOneReflexivity : RepresentableReflexivity 1 :=
  representableOneReflexivityOfSurjective representableOne_unit_surjective

/-- A representable source constructor, once its concrete finite-dimensional
biorthogonality theorem is supplied. -/
noncomputable def representableBiorthogonalObject
    (A : ℕ) (hA : 0 < A) (h : RepresentableReflexivity A) :
    ClassicalObject (DayNegation.data) where
  module := representable A
  basis := representablePseudoBasis A hA
  reflexive := h.iso
  canonical := rfl

/-- The tensor unit representable is a classical object. -/
noncomputable def representableOneClassicalObject :
    ClassicalObject (DayNegation.data) :=
  representableBiorthogonalObject 1 (by decide) representableOneReflexivity


end SuperoperatorModule

end QLambda.Domain.Presheaf
