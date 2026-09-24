/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.DayTensorRepresentable

/-!
# Representable internal hom and closed adjunction
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

universe u

/-- Concrete right adjoint to tensoring by a representable:
`[y(A), N](n) = N(n*A)`. -/
noncomputable def internalHomRepresentable (A : ℕ) (N : Module.{u}) :
    Module.{u} where
  obj n := N.obj (n * A)
  act := fun x f =>
    N.act x (Superoperator.tensor f (Superoperator.identity A))
  act_zero_element := by
    intro m n f
    exact N.act_zero_element _
  act_zero_map := by
    intro m n x
    rw [Superoperator.tensor_zero_left]
    exact N.act_zero_map x
  act_id := by
    intro n x
    rw [Superoperator.tensor_identity]
    exact N.act_id x
  act_comp := by
    intro ℓ m n x f g
    rw [N.act_comp, ← Superoperator.tensor_comp,
      Superoperator.comp_identity]
  act_sum_element := by
    intro ι _ m n x s f h
    exact N.act_sum_element _ h
  act_sum_map := by
    intro ι _ m n x f s h
    exact N.act_sum_map x
      (SigmaMon.ChoiSum.tensor_hasSum_left h
        (Superoperator.identity A))
  act_sum_from_one := by
    intro ι _ m x s f h
    exact N.act_sum_tensor_from_one f h
  act_sum_tensor_from_one := by
    intro ι _ m B x s f h
    -- Reassociate `(f ⊗ id_B) ⊗ id_A` via the tensor associator, then apply
    -- `N.act_sum_tensor_from_one` at ancillary dimension `B * A`.
    let α₁ : Superoperator (1 * (B * A)) ((1 * B) * A) :=
      Superoperator.tensorAssociatorInv 1 B A
    let α₂ : Superoperator ((m * B) * A) (m * (B * A)) :=
      Superoperator.tensorAssociator m B A
    let x' : ι → (N.obj (1 * (B * A))).Carrier :=
      fun i => N.act (x i) α₁
    let s' : (N.obj (1 * (B * A))).Carrier := N.act s α₁
    have hs' : (N.obj (1 * (B * A))).HasSum x' s' :=
      N.act_sum_element α₁ h
    obtain ⟨z', hz'⟩ := N.act_sum_tensor_from_one (A := B * A) f hs'
    refine ⟨N.act z' α₂, ?_⟩
    have hten (g : Superoperator m 1) :
        Superoperator.tensor
            (Superoperator.tensor g (Superoperator.identity B))
            (Superoperator.identity A) =
          Superoperator.comp α₁
            (Superoperator.comp
              (Superoperator.tensor g (Superoperator.identity (B * A)))
              α₂) := by
      have hnat :=
        Superoperator.tensorAssociator_naturality g
          (Superoperator.identity B) (Superoperator.identity A)
      -- `α₂' ∘ ((g ⊗ id_B) ⊗ id_A) = (g ⊗ (id_B ⊗ id_A)) ∘ α₂`
      -- with `α₂' = tensorAssociator 1 B A`.
      have h :=
        congrArg (Superoperator.comp
          (Superoperator.tensorAssociatorInv 1 B A)) hnat
      simpa [Superoperator.comp_assoc,
        Superoperator.tensorAssociator_inv_hom,
        Superoperator.identity_comp, Superoperator.tensor_identity,
        α₁, α₂] using h
    have hfam :
        (fun i =>
          N.act (x i)
            (Superoperator.tensor
              (Superoperator.tensor (f i) (Superoperator.identity B))
              (Superoperator.identity A))) =
          fun i =>
            N.act
              (N.act (x' i)
                (Superoperator.tensor (f i)
                  (Superoperator.identity (B * A))))
              α₂ := by
      funext i
      -- `act x (α₁ ∘ (f⊗id) ∘ α₂) = act (act (act x α₁) (f⊗id)) α₂`
      rw [hten, ← N.act_comp, ← N.act_comp]
    have hzα :
        (N.obj ((m * B) * A)).HasSum
          (fun i =>
            N.act
              (N.act (x' i)
                (Superoperator.tensor (f i)
                  (Superoperator.identity (B * A))))
              α₂)
          (N.act z' α₂) :=
      N.act_sum_element α₂ hz'
    rw [hfam]
    exact hzα

/-- Closed adjunction on representable left arguments. -/
noncomputable def closedRepresentableEquiv
    (X A : ℕ) (N : Module.{u}) :
    Hom (dayTensorRepresentable X A) N ≃
      Hom (representable X) (internalHomRepresentable A N) :=
  (yonedaEquiv N (X * A)).trans
    (yonedaEquiv (internalHomRepresentable A N) X).symm

/-- Currying is evaluation of the two Yoneda correspondences. -/
noncomputable def curryRepresentable {X A : ℕ} {N : Module.{u}}
    (f : Hom (dayTensorRepresentable X A) N) :
    Hom (representable X) (internalHomRepresentable A N) :=
  closedRepresentableEquiv X A N f

/-- Uncurrying is the inverse closed correspondence. -/
noncomputable def uncurryRepresentable {X A : ℕ} {N : Module.{u}}
    (f : Hom (representable X) (internalHomRepresentable A N)) :
    Hom (dayTensorRepresentable X A) N :=
  (closedRepresentableEquiv X A N).symm f

@[simp]
theorem curry_uncurry_representable {X A : ℕ} {N : Module.{u}}
    (f : Hom (representable X) (internalHomRepresentable A N)) :
    curryRepresentable (uncurryRepresentable f) = f :=
  (closedRepresentableEquiv X A N).apply_symm_apply f

@[simp]
theorem uncurry_curry_representable {X A : ℕ} {N : Module.{u}}
    (f : Hom (dayTensorRepresentable X A) N) :
    uncurryRepresentable (curryRepresentable f) = f :=
  (closedRepresentableEquiv X A N).symm_apply_apply f

end SuperoperatorModule

end QLambda.Domain.Presheaf
