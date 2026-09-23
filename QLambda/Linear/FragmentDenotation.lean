/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentModel
import QLambda.Linear.Operational
import QLambda.Domain.Presheaf.Yoneda

/-!
# Concrete fragment denotation (Route A)

Type-valued typing certificates for the minimum fragment, together with a
compositional denotation of closed unit/bit observations into
`routeAFragmentModel`.  Certificates are data; `HasType` remains a `Prop`.
-/

namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf

/-- Type-valued fragment typing certificate (canonical derivation shape). -/
inductive FragCert : List Ty → List (Option Ty) → Term → Ty → Type where
  | unit {Γ Δ} : AllNone Δ → FragCert Γ Δ .unit .unit
  | bitLit {Γ Δ} (b : Bool) : AllNone Δ → FragCert Γ Δ (.bitLit b) .bit
  | prim {Γ Δ} (p : Prim) : AllNone Δ → FragCert Γ Δ (.prim p) (primTy p)
  | varU {Γ Δ n A} :
      Lookup Γ n A → Ty.Duplicable A → AllNone Δ → Ty.SemanticFragment A →
      FragCert Γ Δ (.var .unres n) A
  | varL {Γ Δ n A} :
      Lookup Δ n (some A) → OnlySomeAt Δ n → Ty.SemanticFragment A →
      FragCert Γ Δ (.var .lin n) A
  | lamU {Γ Δ A B M} :
      Ty.Admissible A → Ty.Duplicable A → AllNone Δ →
      Ty.SemanticFragment (.arrow .unres A B) →
      FragCert (A :: Γ) Δ M B →
      FragCert Γ Δ (.lam .unres A M) (.arrow .unres A B)
  | lamL {Γ Δ A B M} :
      Ty.Admissible A → Ty.FirstOrder A → Ty.SemanticFragment B →
      FragCert Γ (some A :: Δ) M B →
      FragCert Γ Δ (.lam .lin A M) (.arrow .lin A B)
  | appL {Γ Δ Δ₁ Δ₂ A B F X} :
      OSplit Δ Δ₁ Δ₂ → Ty.FirstOrder A → Ty.SemanticFragment B →
      FragCert Γ Δ₁ F (.arrow .lin A B) → FragCert Γ Δ₂ X A →
      FragCert Γ Δ (.app F X) B
  | appU {Γ Δ ΔF ΔX B F X} :
      OSplit Δ ΔF ΔX → AllNone ΔX → Ty.SemanticFragment B →
      FragCert Γ ΔF F (.arrow .unres .bit B) → FragCert Γ ΔX X .bit →
      FragCert Γ Δ (.app F X) B
  | pair {Γ Δ Δ₁ Δ₂ A B M N} :
      OSplit Δ Δ₁ Δ₂ → Ty.FirstOrder A → Ty.FirstOrder B →
      FragCert Γ Δ₁ M A → FragCert Γ Δ₂ N B →
      FragCert Γ Δ (.pair M N) (.tensor A B)
  | unpair {Γ Δ Δ₁ Δ₂ A B C M K} :
      OSplit Δ Δ₁ Δ₂ → Ty.FirstOrder A → Ty.FirstOrder B →
      Ty.SemanticFragment C →
      FragCert Γ Δ₁ M (.tensor A B) →
      FragCert Γ Δ₂ K (.arrow .lin A (.arrow .lin B C)) →
      FragCert Γ Δ (.unpair M K) C
  | ite {Γ Δ Δ₁ Δ₂ A B T E} :
      OSplit Δ Δ₁ Δ₂ → Ty.SemanticFragment A →
      FragCert Γ Δ₁ B .bit → FragCert Γ Δ₂ T A → FragCert Γ Δ₂ E A →
      FragCert Γ Δ (.ite B T E) A
  | measure {Γ Δ Δ₁ Δ₂ A Q K} :
      OSplit Δ Δ₁ Δ₂ → Ty.SemanticFragment A →
      FragCert Γ Δ₁ Q .qubit →
      FragCert Γ Δ₂ K (.arrow .unres .bit (.arrow .lin .qubit A)) →
      FragCert Γ Δ (.measure Q K) A

namespace FragCert

/-- Every certificate implies ordinary `HasType`. -/
def toHasType {Γ Δ M A} : FragCert Γ Δ M A → HasType Γ Δ M A
  | .unit h => .unit h
  | .bitLit _ h => .bitLit h
  | .prim _ h => .prim h
  | .varU hL hD hN _ => .varU hL hD hN
  | .varL hL hO _ => .varL hL hO
  | .lamU hAd hDup hN _ c => .lamU hAd hDup hN c.toHasType
  | .lamL hAd _ _ c => .lamL hAd c.toHasType
  | .appL hS _ _ cF cX => .appL hS cF.toHasType cX.toHasType
  | .appU hS hN _ cF cX => .appU hS hN cF.toHasType cX.toHasType
  | .pair hS _ _ cM cN => .pair hS cM.toHasType cN.toHasType
  | .unpair hS _ _ _ cM cK => .unpair hS cM.toHasType cK.toHasType
  | .ite hS _ cB cT cE => .ite hS cB.toHasType cT.toHasType cE.toHasType
  | .measure hS _ cQ cK => .measure hS cQ.toHasType cK.toHasType

/-- Every certificate result type lies in the semantic fragment. -/
def result_fragment {Γ Δ M A} : FragCert Γ Δ M A → Ty.SemanticFragment A
  | .unit _ => Ty.SemanticFragment.unit
  | .bitLit _ _ => Ty.SemanticFragment.bit
  | .prim p _ => Ty.SemanticFragment.primTy_fragment p
  | .varU _ _ _ h => h
  | .varL _ _ h => h
  | .lamU _ _ _ hArr _ => hArr
  | .lamL _ hA hB _ => .arrowLin hA hB
  | .appL _ _ hB _ _ => hB
  | .appU _ _ hB _ _ => hB
  | .pair _ hA hB _ _ => Ty.SemanticFragment.tensor hA hB
  | .unpair _ _ _ hC _ _ => hC
  | .ite _ hA _ _ _ => hA
  | .measure _ hA _ _ => hA

/-- Closed fragment certificate: empty contexts. -/
abbrev Closed (M : Term) (A : Ty) := FragCert [] [] M A

/-- Denotation of closed unit certificates. -/
noncomputable def denoteUnit
    (c : Closed .unit .unit) :
    Hom dayTensorUnit (representable 1) :=
  routeAFragmentModel.unitIntro

/-- Denotation of closed bit-literal certificates. -/
noncomputable def denoteBitLit {b : Bool}
    (c : Closed (.bitLit b) .bit) :
    Hom dayTensorUnit (representable 2) :=
  routeAFragmentModel.bitLit b

theorem denoteUnit_eq (c : Closed .unit .unit) :
    denoteUnit c = routeAFragmentModel.unitIntro :=
  rfl

theorem denoteBitLit_eq {b : Bool} (c : Closed (.bitLit b) .bit) :
    denoteBitLit c = routeAFragmentModel.bitLit b :=
  rfl

/-- Closed unit certificate. -/
def closed_unit_cert : Closed .unit .unit :=
  .unit trivial

/-- Closed bit-literal certificate. -/
def closed_bitLit_cert (b : Bool) : Closed (.bitLit b) .bit :=
  .bitLit b trivial

end FragCert

/-- Exact agreement of Route A primitive maps with `Prim.superoperator`. -/
theorem fragment_prim_superoperator (p : Prim) :
    routeAFragmentModel.primMap p = yonedaMap (Prim.superoperator p) :=
  routeAFragmentModel.prim_agrees p

/-- Exact agreement of Route A primitives with Kraus/`CompletedCP` presentations. -/
theorem fragment_prim_completedCP (p : Prim) :
    (Prim.superoperator p).cp = CPMap.ofKraus p.kraus :=
  Prim.cp_superoperator p

end QLambda.Linear
