/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.ModuleChoiSum

/-!
# Fiber of a specialized superoperator module
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SuperoperatorModule

universe u

/-- A carrier equipped with a relational partial countable sum. -/
structure Fiber where
  Carrier : Type u
  zero : Carrier
  summation : @SigmaMon.PartialCountableSum Carrier ⟨zero⟩

instance (X : Fiber) : Zero X.Carrier := ⟨X.zero⟩

/-- The relation saying that a family has the indicated partial sum in a
fiber. -/
abbrev Fiber.HasSum (X : Fiber) {ι : Type} [Countable ι]
    (f : ι → X.Carrier) (x : X.Carrier) : Prop :=
  X.summation.HasSum f x

/-- The constantly-zero family has a sum over every countable index type. -/
theorem Fiber.hasSum_zero (X : Fiber.{u}) {ι : Type} [Countable ι] :
    X.HasSum (fun _ : ι => 0) 0 := by
  have hEmpty :
      X.HasSum (fun i : (∅ : Set ι) => 0) 0 := by
    convert ((X.summation.reindex (Equiv.Set.empty ι)
      (fun i : Empty => nomatch i) 0).mpr
        X.summation.empty) using 1
    funext i
    exact i.property.elim
  exact (X.summation.remove_zero
    (fun _ : ι => 0) ∅ 0 (by simp)).mp hEmpty

theorem Fiber.hasSum_congr (X : Fiber.{u}) {ι : Type} [Countable ι]
    {f g : ι → X.Carrier} {x : X.Carrier}
    (h : ∀ i, f i = g i) :
    X.HasSum f x ↔ X.HasSum g x := by
  have hfg : f = g := funext h
  subst g
  rfl

/-- Binary (Bool-split) sums: any two carriers admit a joint sum.  Together with
`empty` / `singleton` / `flatten` this yields `hasSum_fin` / `hasSum_fintype`. -/
def Fiber.HasSumAdd (X : Fiber.{u}) : Prop :=
  ∀ (a b : X.Carrier),
    ∃ c, X.HasSum (fun i : Bool => bif i then a else b) c

theorem Fiber.hasSum_fin_zero (X : Fiber.{u}) (f : Fin 0 → X.Carrier) :
    X.HasSum f 0 := by
  have h :=
    (X.summation.reindex (Equiv.equivEmpty (Fin 0))
      (fun i : Empty => nomatch i) 0).mpr X.summation.empty
  refine (Fiber.hasSum_congr X ?_).mpr h
  intro i; exact (isEmptyElim i : False).elim

theorem Fiber.hasSum_fin_one (X : Fiber.{u}) (f : Fin 1 → X.Carrier) :
    X.HasSum f (f 0) := by
  have h :=
    (X.summation.reindex (Equiv.ofUnique (Fin 1) PUnit)
      (fun _ : PUnit => f 0) (f 0)).mpr (X.summation.singleton (f 0))
  refine (Fiber.hasSum_congr X ?_).mpr h
  intro i; exact congrArg f (Subsingleton.elim _ _)

/-- Glue a summable `α`-family with a value at `none` via Bool-add + flatten. -/
theorem Fiber.hasSum_option_of_add (X : Fiber.{u}) (hadd : Fiber.HasSumAdd X)
    {α : Type} [Countable α]
    {g : Option α → X.Carrier} {sα : X.Carrier}
    (hα : X.HasSum (fun a : α => g (some a)) sα) :
    ∃ s, X.HasSum g s := by
  obtain ⟨s, hs⟩ := hadd sα (g none)
  let κ : Bool → Type := fun b => match b with | true => α | false => PUnit
  have : ∀ b : Bool, Countable (κ b) := fun b => by cases b <;> infer_instance
  let row : (b : Bool) → κ b → X.Carrier := fun b j =>
    match b, j with
    | true, a => g (some a)
    | false, _ => g none
  have hrows (b : Bool) : X.HasSum (row b) (bif b then sα else g none) := by
    cases b with
    | true => exact hα
    | false => exact X.summation.singleton (g none)
  have hflat :
      X.HasSum (fun p : (b : Bool) × κ b => row p.1 p.2) s :=
    (X.summation.flatten row s).mpr
      ⟨fun b => bif b then sα else g none, hrows, hs⟩
  let e : ((b : Bool) × κ b) ≃ Option α :=
    { toFun := fun | ⟨true, a⟩ => some a | ⟨false, _⟩ => none
      invFun := fun | some a => ⟨true, a⟩ | none => ⟨false, ⟨⟩⟩
      left_inv := fun | ⟨true, _⟩ => rfl | ⟨false, ⟨⟩⟩ => rfl
      right_inv := fun | some _ => rfl | none => rfl }
  have hge : (fun p : (b : Bool) × κ b => g (e p)) =
      (fun p => row p.1 p.2) := by
    funext p; rcases p with ⟨b, j⟩; cases b <;> rfl
  have hrow : X.HasSum (fun p => g (e p)) s := hge ▸ hflat
  exact ⟨s, (X.summation.reindex e g s).mp hrow⟩

/-- Finite `Fin n` families admit sums under Bool-add (induction + flatten). -/
theorem Fiber.hasSum_fin (X : Fiber.{u}) (hadd : Fiber.HasSumAdd X)
    (n : ℕ) (f : Fin n → X.Carrier) : ∃ s, X.HasSum f s := by
  induction n with
  | zero => exact ⟨0, Fiber.hasSum_fin_zero X f⟩
  | succ n ih =>
    let e : Fin (n + 1) ≃ Option (Fin n) := finSuccEquivLast
    obtain ⟨s_n, hs_n⟩ := ih (fun i => f (e.symm (some i)))
    obtain ⟨s, hs⟩ :=
      Fiber.hasSum_option_of_add X hadd (g := fun o => f (e.symm o)) hs_n
    refine ⟨s, ?_⟩
    have h := (X.summation.reindex e (fun o => f (e.symm o)) s).mpr hs
    refine (Fiber.hasSum_congr X ?_).mpr h
    intro i; simp

/-- Fintype-indexed families admit sums under Bool-add. -/
theorem Fiber.hasSum_fintype (X : Fiber.{u}) (hadd : Fiber.HasSumAdd X)
    {ι : Type} [Fintype ι] (f : ι → X.Carrier) : ∃ s, X.HasSum f s := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  obtain ⟨s, hs⟩ := Fiber.hasSum_fin X hadd _ (fun i => f (e.symm i))
  refine ⟨s, ?_⟩
  have h := (X.summation.reindex e (fun i => f (e.symm i)) s).mpr hs
  refine (Fiber.hasSum_congr X ?_).mpr h
  intro i; simp

/-- Finset-indexed families admit sums under Bool-add. -/
theorem Fiber.hasSum_finset (X : Fiber.{u}) (hadd : Fiber.HasSumAdd X)
    {ι : Type} [DecidableEq ι] (f : ι → X.Carrier) (t : Finset ι) :
    ∃ s, X.HasSum (fun i : t => f (i : ι)) s :=
  Fiber.hasSum_fintype X hadd _

end SuperoperatorModule

end QLambda.Domain.Presheaf
