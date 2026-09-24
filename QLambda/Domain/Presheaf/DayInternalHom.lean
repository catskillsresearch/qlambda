/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.BilinearSums

/-!
# Day internal hom and closed presentation
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule
open Classical

namespace DayInternalHom

/-- Precomposition in the representable argument of a bilinear map. -/
noncomputable def precompose {A N : Module} {m n : ℕ}
    (f : Superoperator m n)
    (b : Bilinear (representable n) A N) :
    Bilinear (representable m) A N where
  app := fun x y => b.app (Superoperator.comp f x) y
  map_zero_left := by
    intro p q y
    change b.app (Superoperator.comp f (0 : Superoperator p m)) y = 0
    rw [Superoperator.comp_zero_right]
    exact b.map_zero_left y
  map_zero_right := by
    intro p q x
    exact b.map_zero_right _
  map_sum_left := by
    intro ι _ p q x s y h
    exact b.map_sum_left y (SigmaMon.ChoiSum.comp_left f h)
  map_sum_right := by
    intro ι _ p q x y s h
    exact b.map_sum_right _ h
  naturality := by
    intro p' p q' q x y g h
    change Superoperator p m at x
    change
      b.app (Superoperator.comp f (Superoperator.comp x g)) (A.act y h) =
        N.act (b.app (Superoperator.comp f x) y)
          (Superoperator.tensor g h)
    rw [Superoperator.comp_assoc]
    exact b.naturality (Superoperator.comp f x) y g h

/-- The closed object `[A,N]`, represented pointwise by bilinear maps out of
a representable. -/
noncomputable def module (A N : Module) : Module where
  obj n :=
    { Carrier := Bilinear (representable n) A N
      zero := Bilinear.zero _ _ _
      summation := Bilinear.partialCountableSum _ _ _ }
  act := fun b f => precompose f b
  act_zero_element := by
    intro m n f
    apply Bilinear.ext
    intro p q x y
    rfl
  act_zero_map := by
    intro m n b
    apply Bilinear.ext
    intro p q x y
    change Superoperator p m at x
    change b.app (Superoperator.comp (0 : Superoperator m n) x) y = 0
    rw [Superoperator.comp_zero_left]
    exact b.map_zero_left y
  act_id := by
    intro n b
    apply Bilinear.ext
    intro p q x y
    change Superoperator p n at x
    change b.app (Superoperator.comp (Superoperator.identity n) x) y =
      b.app x y
    rw [Superoperator.identity_comp]
  act_comp := by
    intro ℓ m n b f g
    apply Bilinear.ext
    intro p q x y
    change Superoperator p ℓ at x
    simp only [precompose]
    rw [Superoperator.comp_assoc]
  act_sum_element := by
    intro ι _ m n b s f h p q x y
    exact h p q (Superoperator.comp f x) y
  act_sum_map := by
    intro ι _ m n b f s h p q x y
    exact b.map_sum_left y (SigmaMon.ChoiSum.comp_right x h)
  act_sum_from_one := by
    intro ι _ m bx bs f hs
    have hadm :
        ∀ p q (r : Superoperator p m) (y : (A.obj q).Carrier),
          ∃ z, (N.obj (p * q)).HasSum
            (fun i =>
              (precompose (f i) (bx i)).app r y) z := by
      intro p q r y
      have h1 :
          (N.obj (1 * q)).HasSum
            (fun i =>
              (bx i).app (Superoperator.identity 1) y)
            (bs.app (Superoperator.identity 1) y) :=
        hs 1 q (Superoperator.identity 1) y
      obtain ⟨z0, hz0⟩ := N.act_sum_tensor_from_one (A := q) f h1
      have hnat (i : ι) :
          (bx i).app (Superoperator.comp (f i) r) y =
            N.act
              (N.act ((bx i).app (Superoperator.identity 1) y)
                (Superoperator.tensor (f i)
                  (Superoperator.identity q)))
              (Superoperator.tensor r (Superoperator.identity q)) := by
        have hf :
            (bx i).app (f i) y =
              N.act ((bx i).app (Superoperator.identity 1) y)
                (Superoperator.tensor (f i)
                  (Superoperator.identity q)) := by
          simpa [Superoperator.identity_comp, A.act_id] using
            (bx i).naturality (Superoperator.identity 1) y (f i)
              (Superoperator.identity q)
        have hfr :
            (bx i).app (Superoperator.comp (f i) r) y =
              N.act ((bx i).app (f i) y)
                (Superoperator.tensor r
                  (Superoperator.identity q)) := by
          simpa [A.act_id] using
            (bx i).naturality (f i) y r (Superoperator.identity q)
        rw [hfr, hf, N.act_comp]
      refine
        ⟨N.act z0 (Superoperator.tensor r (Superoperator.identity q)),
          ?_⟩
      have hz :=
        N.act_sum_element
          (Superoperator.tensor r (Superoperator.identity q)) hz0
      have hfam :
          (fun i => (precompose (f i) (bx i)).app r y) =
            fun i =>
              N.act
                (N.act ((bx i).app (Superoperator.identity 1) y)
                  (Superoperator.tensor (f i)
                    (Superoperator.identity q)))
                (Superoperator.tensor r (Superoperator.identity q)) := by
        funext i
        simpa [precompose] using hnat i
      rwa [hfam]
    exact
      ⟨Bilinear.sumOf (fun i => precompose (f i) (bx i)) hadm,
        Bilinear.sumOf_hasSum _ hadm⟩
  act_sum_tensor_from_one := by
    intro ι _ m B bx bs f hs
    have hadm :
        ∀ p q (r : Superoperator p (m * B)) (y : (A.obj q).Carrier),
          ∃ z, (N.obj (p * q)).HasSum
            (fun i =>
              (precompose
                  (Superoperator.tensor (f i)
                    (Superoperator.identity B))
                  (bx i)).app
                r y) z := by
      intro p q r y
      have h1 :
          (N.obj ((1 * B) * q)).HasSum
            (fun i =>
              (bx i).app (Superoperator.identity (1 * B)) y)
            (bs.app (Superoperator.identity (1 * B)) y) :=
        hs (1 * B) q (Superoperator.identity (1 * B)) y
      let α₁ : Superoperator (1 * (B * q)) ((1 * B) * q) :=
        Superoperator.tensorAssociatorInv 1 B q
      let α₂ : Superoperator ((m * B) * q) (m * (B * q)) :=
        Superoperator.tensorAssociator m B q
      let x' : ι → (N.obj (1 * (B * q))).Carrier :=
        fun i =>
          N.act ((bx i).app (Superoperator.identity (1 * B)) y) α₁
      let s' : (N.obj (1 * (B * q))).Carrier :=
        N.act (bs.app (Superoperator.identity (1 * B)) y) α₁
      have hs' : (N.obj (1 * (B * q))).HasSum x' s' :=
        N.act_sum_element α₁ h1
      obtain ⟨z0, hz0⟩ :=
        N.act_sum_tensor_from_one (A := B * q) f hs'
      have hten (g : Superoperator m 1) :
          Superoperator.tensor
              (Superoperator.tensor g (Superoperator.identity B))
              (Superoperator.identity q) =
            Superoperator.comp α₁
              (Superoperator.comp
                (Superoperator.tensor g
                  (Superoperator.identity (B * q)))
                α₂) := by
        have hnat :=
          Superoperator.tensorAssociator_naturality g
            (Superoperator.identity B) (Superoperator.identity q)
        have h :=
          congrArg (Superoperator.comp
            (Superoperator.tensorAssociatorInv 1 B q)) hnat
        simpa [Superoperator.comp_assoc,
          Superoperator.tensorAssociator_inv_hom,
          Superoperator.identity_comp, Superoperator.tensor_identity,
          α₁, α₂] using h
      have hnat (i : ι) :
          (bx i).app
              (Superoperator.comp
                (Superoperator.tensor (f i)
                  (Superoperator.identity B))
                r)
              y =
            N.act
              (N.act (x' i)
                (Superoperator.tensor (f i)
                  (Superoperator.identity (B * q))))
              (Superoperator.comp α₂
                (Superoperator.tensor r
                  (Superoperator.identity q))) := by
        have hf :
            (bx i).app
                (Superoperator.tensor (f i)
                  (Superoperator.identity B))
                y =
              N.act
                ((bx i).app (Superoperator.identity (1 * B)) y)
                (Superoperator.tensor
                  (Superoperator.tensor (f i)
                    (Superoperator.identity B))
                  (Superoperator.identity q)) := by
          simpa [Superoperator.identity_comp, A.act_id] using
            (bx i).naturality (Superoperator.identity (1 * B)) y
              (Superoperator.tensor (f i) (Superoperator.identity B))
              (Superoperator.identity q)
        have hfr :
            (bx i).app
                (Superoperator.comp
                  (Superoperator.tensor (f i)
                    (Superoperator.identity B))
                  r)
                y =
              N.act
                ((bx i).app
                  (Superoperator.tensor (f i)
                    (Superoperator.identity B))
                  y)
                (Superoperator.tensor r
                  (Superoperator.identity q)) := by
          simpa [A.act_id] using
            (bx i).naturality
              (Superoperator.tensor (f i) (Superoperator.identity B))
              y r (Superoperator.identity q)
        rw [hfr, hf, hten, ← N.act_comp, ← N.act_comp, ← N.act_comp]
      refine
        ⟨N.act z0
            (Superoperator.comp α₂
              (Superoperator.tensor r (Superoperator.identity q))),
          ?_⟩
      have hz :=
        N.act_sum_element
          (Superoperator.comp α₂
            (Superoperator.tensor r (Superoperator.identity q)))
          hz0
      have hfam :
          (fun i =>
            (precompose
                (Superoperator.tensor (f i)
                  (Superoperator.identity B))
                (bx i)).app
              r y) =
            fun i =>
              N.act
                (N.act (x' i)
                  (Superoperator.tensor (f i)
                    (Superoperator.identity (B * q))))
                (Superoperator.comp α₂
                  (Superoperator.tensor r
                    (Superoperator.identity q))) := by
        funext i
        simpa [precompose] using hnat i
      rwa [hfam]
    exact
      ⟨Bilinear.sumOf
          (fun i =>
            precompose
              (Superoperator.tensor (f i) (Superoperator.identity B))
              (bx i))
          hadm,
        Bilinear.sumOf_hasSum _ hadm⟩


noncomputable def curry {X A N : Module} (b : Bilinear X A N) :
    Hom X (module A N) where
  app := fun n x =>
    { app := fun r y => b.app (X.act x r) y
      map_zero_left := by
        intro p q y
        change b.app (X.act x (0 : Superoperator p n)) y = 0
        rw [X.act_zero_map]
        exact b.map_zero_left y
      map_zero_right := by
        intro p q r
        exact b.map_zero_right _
      map_sum_left := by
        intro ι _ p q r s y h
        exact b.map_sum_left y (X.act_sum_map x h)
      map_sum_right := by
        intro ι _ p q r y s h
        exact b.map_sum_right _ h
      naturality := by
        intro p' p q' q r y f g
        change Superoperator p n at r
        change
          b.app (X.act x (Superoperator.comp r f)) (A.act y g) =
            N.act (b.app (X.act x r) y) (Superoperator.tensor f g)
        rw [← X.act_comp]
        exact b.naturality (X.act x r) y f g }
  map_zero := by
    intro n
    apply Bilinear.ext
    intro p q r y
    change Superoperator p n at r
    change b.app (X.act (0 : (X.obj n).Carrier) r) y = 0
    rw [X.act_zero_element]
    exact b.map_zero_left y
  map_sum := by
    intro ι _ n x s h p q r y
    exact b.map_sum_left y (X.act_sum_element r h)
  naturality := by
    intro m n x f
    apply Bilinear.ext
    intro p q r y
    change Superoperator p m at r
    simp only [module, precompose]
    rw [X.act_comp]

/-- Uncurry a map into the pointwise internal hom. -/
noncomputable def uncurry {X A N : Module}
    (η : Hom X (module A N)) : Bilinear X A N where
  app := fun {m n} x y =>
    (η.app m x).app (Superoperator.identity m) y
  map_zero_left := by
    intro m n y
    rw [η.map_zero]
    rfl
  map_zero_right := by
    intro m n x
    exact (η.app m x).map_zero_right _
  map_sum_left := by
    intro ι _ m n x s y h
    exact η.map_sum h m n (Superoperator.identity m) y
  map_sum_right := by
    intro ι _ m n x y s h
    exact (η.app m x).map_sum_right _ h
  naturality := by
    intro m' m n' n x y f g
    have hη := η.naturality x f
    have happ := congrArg
      (fun b : Bilinear (representable m') A N =>
        b.app (Superoperator.identity m') (A.act y g)) hη
    simp only [module, precompose] at happ
    rw [Superoperator.comp_identity] at happ
    rw [happ]
    have hb := (η.app m x).naturality
      (Superoperator.identity m) y f g
    change
      (η.app m x).app
          (Superoperator.comp (Superoperator.identity m) f) (A.act y g) =
        N.act ((η.app m x).app (Superoperator.identity m) y)
          (Superoperator.tensor f g) at hb
    rw [Superoperator.identity_comp] at hb
    exact hb

noncomputable def curryEquiv (X A N : Module) :
    Bilinear X A N ≃ Hom X (module A N) where
  toFun := curry
  invFun := uncurry
  left_inv := by
    intro b
    apply Bilinear.ext
    intro m n x y
    change b.app (X.act x (Superoperator.identity m)) y = b.app x y
    rw [X.act_id]
  right_inv := by
    intro η
    apply Hom.ext
    intro n x
    apply Bilinear.ext
    intro p q r y
    change Superoperator p n at r
    change
      (η.app p (X.act x r)).app (Superoperator.identity p) y =
        (η.app n x).app r y
    have hη := η.naturality x r
    have happ := congrArg
      (fun b : Bilinear (representable p) A N =>
        b.app (Superoperator.identity p) y) hη
    change
      (η.app p (X.act x r)).app (Superoperator.identity p) y =
        (η.app n x).app
          (Superoperator.comp r (Superoperator.identity p)) y at happ
    rw [Superoperator.comp_identity] at happ
    exact happ

end DayInternalHom

/-- Genuine internal hom for arbitrary specialized modules. -/
noncomputable abbrev dayInternalHom (A N : Module) : Module :=
  DayInternalHom.module A N

/-- The concrete same-universe Day closed structure. -/
noncomputable def dayClosedPresentation : DayClosedPresentation where
  tensor := dayTensorPresentation
  internalHom := dayInternalHom
  closed := fun X A N =>
    (DayCoend.universalEquiv X A N).trans
      (DayInternalHom.curryEquiv X A N)

/-- Any two Day tensor presentations of the same pair are canonically
isomorphic. -/
noncomputable def dayPresentationIso {M N : Module}
    (P Q : DayTensorPresentation M N) : Iso P.object Q.object where
  hom := (P.universal Q.object).symm Q.intro
  inv := (Q.universal P.object).symm P.intro
  hom_inv := by
    apply (Q.universal Q.object).injective
    rw [Q.universal_apply, Q.universal_apply]
    apply Bilinear.ext
    intro m n x y
    have hi := (Q.universal P.object).apply_symm_apply P.intro
    rw [Q.universal_apply] at hi
    have hh := (P.universal Q.object).apply_symm_apply Q.intro
    rw [P.universal_apply] at hh
    have hiapp := congrArg (fun b => b.app x y) hi
    have hhapp := congrArg (fun b => b.app x y) hh
    exact congrArg
      (fun z => ((P.universal Q.object).symm Q.intro).app _ z)
      hiapp |>.trans hhapp
  inv_hom := by
    apply (P.universal P.object).injective
    rw [P.universal_apply, P.universal_apply]
    apply Bilinear.ext
    intro m n x y
    have hh := (P.universal Q.object).apply_symm_apply Q.intro
    rw [P.universal_apply] at hh
    have hi := (Q.universal P.object).apply_symm_apply P.intro
    rw [Q.universal_apply] at hi
    have hhapp := congrArg (fun b => b.app x y) hh
    have hiapp := congrArg (fun b => b.app x y) hi
    exact congrArg
      (fun z => ((Q.universal P.object).symm P.intro).app _ z)
      hhapp |>.trans hiapp

/-- The coend tensor agrees canonically with the existing representable
tensor. -/
noncomputable def dayTensorRepresentableIso (A B : ℕ) :
    Iso (dayTensor (representable A) (representable B))
      (dayTensorRepresentable A B) :=
  dayPresentationIso (dayTensorPresentation _ _)
    (dayTensorRepresentablePresentation A B)

/-- Fiberwise agreement of the general internal hom with the existing
representable formula `[y(A),N](n)=N(n*A)`. -/
noncomputable def dayInternalHomRepresentableFiberEquiv
    (A : ℕ) (N : Module) (n : ℕ) :
    ((dayInternalHom (representable A) N).obj n).Carrier ≃
      ((internalHomRepresentable A N).obj n).Carrier :=
  (dayTensorRepresentableEquiv n A N).symm.trans (yonedaEquiv N (n * A))

/-- Module-level agreement of the general internal hom with the existing
representable formula. -/
noncomputable def dayInternalHomRepresentableIso
    (A : ℕ) (N : Module) :
    Iso (dayInternalHom (representable A) N)
      (internalHomRepresentable A N) where
  hom :=
    { app := fun n b =>
        b.app (Superoperator.identity n) (Superoperator.identity A)
      map_zero := by
        intro n
        rfl
      map_sum := by
        intro ι _ n f s h
        exact h n A (Superoperator.identity n) (Superoperator.identity A)
      naturality := by
        intro m n b f
        change
          b.app (Superoperator.comp f (Superoperator.identity m))
              (Superoperator.identity A) =
            N.act
              (b.app (Superoperator.identity n) (Superoperator.identity A))
              (Superoperator.tensor f (Superoperator.identity A))
        rw [Superoperator.comp_identity]
        have hb := b.naturality (Superoperator.identity n)
          (Superoperator.identity A) f (Superoperator.identity A)
        change
          b.app
              (Superoperator.comp (Superoperator.identity n) f)
              (Superoperator.comp (Superoperator.identity A)
                (Superoperator.identity A)) =
            N.act
              (b.app (Superoperator.identity n) (Superoperator.identity A))
              (Superoperator.tensor f (Superoperator.identity A)) at hb
        simpa only [Superoperator.identity_comp] using hb }
  inv :=
    { app := fun n z =>
        { app := fun r s => N.act z (Superoperator.tensor r s)
          map_zero_left := by
            intro p q s
            change (N.obj (n * A)).Carrier at z
            change Superoperator q A at s
            change
              N.act z
                (Superoperator.tensor (0 : Superoperator p n) s) = 0
            rw [Superoperator.tensor_zero_left]
            exact N.act_zero_map z
          map_zero_right := by
            intro p q r
            change (N.obj (n * A)).Carrier at z
            change Superoperator p n at r
            change
              N.act z
                (Superoperator.tensor r (0 : Superoperator q A)) = 0
            rw [Superoperator.tensor_zero_right]
            exact N.act_zero_map z
          map_sum_left := by
            intro ι _ p q r t s h
            exact N.act_sum_map z
              (SigmaMon.ChoiSum.tensor_hasSum_left h s)
          map_sum_right := by
            intro ι _ p q r s t h
            exact N.act_sum_map z
              (SigmaMon.ChoiSum.tensor_hasSum_right r h)
          naturality := by
            intro p' p q' q r s f g
            change (N.obj (n * A)).Carrier at z
            change Superoperator p n at r
            change Superoperator q A at s
            change
              N.act z
                  (Superoperator.tensor (Superoperator.comp r f)
                    (Superoperator.comp s g)) =
                N.act (N.act z (Superoperator.tensor r s))
                  (Superoperator.tensor f g)
            rw [N.act_comp, Superoperator.tensor_comp] }
      map_zero := by
        intro n
        apply Bilinear.ext
        intro p q r s
        exact N.act_zero_element _
      map_sum := by
        intro ι _ n f z h p q r s
        exact N.act_sum_element (Superoperator.tensor r s) h
      naturality := by
        intro m n z f
        apply Bilinear.ext
        intro p q r s
        change (N.obj (n * A)).Carrier at z
        change Superoperator p m at r
        change Superoperator q A at s
        simp only [internalHomRepresentable, dayInternalHom,
          DayInternalHom.module, DayInternalHom.precompose]
        rw [N.act_comp, ← Superoperator.tensor_comp,
          Superoperator.identity_comp] }
  hom_inv := by
    apply Hom.ext
    intro n z
    change (N.obj (n * A)).Carrier at z
    change
      N.act z
        (Superoperator.tensor (Superoperator.identity n)
          (Superoperator.identity A)) = z
    rw [Superoperator.tensor_identity, N.act_id]
  inv_hom := by
    apply Hom.ext
    intro n b
    apply Bilinear.ext
    intro p q r s
    change Superoperator p n at r
    change Superoperator q A at s
    change
      N.act
          (b.app (Superoperator.identity n) (Superoperator.identity A))
          (Superoperator.tensor r s) =
        b.app r s
    symm
    have hb := b.naturality (Superoperator.identity n)
      (Superoperator.identity A) r s
    change
      b.app
          (Superoperator.comp (Superoperator.identity n) r)
          (Superoperator.comp (Superoperator.identity A) s) =
        N.act
          (b.app (Superoperator.identity n) (Superoperator.identity A))
          (Superoperator.tensor r s) at hb
    simpa only [Superoperator.identity_comp] using hb

end SuperoperatorModule
end QLambda.Domain.Presheaf
