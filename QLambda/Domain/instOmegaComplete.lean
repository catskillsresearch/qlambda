/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.ScottFunction
import QLambda.Domain.instCoeScottFunction
import QLambda.Domain.instLEScottFunction
import QLambda.Domain.instPartialOrderScottFunction

/-!
# Instance `instOmegaComplete`
-/

namespace QLambda.Domain
namespace ScottFunction

variable {P Q R : QuantumCPO}



/-- Proposition 3.3.1: the limit of a chain of Scott-continuous functions
is Scott continuous. -/
noncomputable def scottLimit
    (K : ℕ → ScottFunction P Q) (hK : Monotone K) :
    ScottFunction P Q where
  toQuantumFunction :=
    functionLimit (fun n => (K n).toQuantumFunction) (by
      intro n m hnm
      exact hK hnm)
  continuous := by
    intro d L Linf hL hLinf
    let c : ℕ → QuantumFunction P.poset Q.poset :=
      fun n => (K n).toQuantumFunction
    have hc : Monotone c := by
      intro n m hnm
      exact hK hnm
    have hhom :
        Q.poset.order.comp (functionLimit c hc).rel =
          ⨅ n, Q.poset.order.comp (c n).rel :=
      functionLimit_tends c hc
    have hcont :
        ∀ n,
          (Q.poset.order.comp (c n).rel).comp Linf.rel =
            ⨅ m, (Q.poset.order.comp (c n).rel).comp (L m).rel := by
      intro n
      have hn := (K n).continuous d L Linf hL hLinf
      change
        Q.poset.order.comp ((c n).rel.comp Linf.rel) =
          ⨅ m, Q.poset.order.comp ((c n).rel.comp (L m).rel) at hn
      simpa only [QuantumRel.assoc] using hn
    change
      Q.poset.order.comp ((functionLimit c hc).rel.comp Linf.rel) =
        ⨅ m, Q.poset.order.comp
          ((functionLimit c hc).rel.comp (L m).rel)
    calc
      Q.poset.order.comp ((functionLimit c hc).rel.comp Linf.rel) =
          (Q.poset.order.comp (functionLimit c hc).rel).comp Linf.rel :=
        (QuantumRel.assoc _ _ _).symm
      _ = (⨅ n, Q.poset.order.comp (c n).rel).comp Linf.rel :=
        congrArg (fun S => S.comp Linf.rel) hhom
      _ = ⨅ n, (Q.poset.order.comp (c n).rel).comp Linf.rel :=
        QuantumRel.iInf_comp_of_function
          (fun n => Q.poset.order.comp (c n).rel)
          Linf.rel Linf.isFunction
      _ = ⨅ n, ⨅ m,
          (Q.poset.order.comp (c n).rel).comp (L m).rel := by
        congr 1
        funext n
        exact hcont n
      _ = ⨅ m, ⨅ n,
          (Q.poset.order.comp (c n).rel).comp (L m).rel :=
        iInf_comm
      _ = ⨅ m, (⨅ n, Q.poset.order.comp (c n).rel).comp (L m).rel := by
        congr 1
        funext m
        exact (QuantumRel.iInf_comp_of_function
          (fun n => Q.poset.order.comp (c n).rel)
          (L m).rel (L m).isFunction).symm
      _ = ⨅ m,
          (Q.poset.order.comp (functionLimit c hc).rel).comp (L m).rel := by
        rw [hhom]
      _ = ⨅ m, Q.poset.order.comp
          ((functionLimit c hc).rel.comp (L m).rel) := by
        simp only [QuantumRel.assoc]

theorem scottLimit_tends
    (K : ℕ → ScottFunction P Q) (hK : Monotone K) :
    Q.poset.order.comp (scottLimit K hK).rel =
      ⨅ n, Q.poset.order.comp (K n).rel :=
  functionLimit_tends (fun n => (K n).toQuantumFunction) hK

theorem scottLimit_isLUB
    (K : ℕ → ScottFunction P Q) (hK : Monotone K) :
    IsLUB (Set.range K) (scottLimit K hK) := by
  have hq := functionLimit_isLUB
    (fun n => (K n).toQuantumFunction) hK
  constructor
  · rintro F ⟨n, rfl⟩
    exact hq.1 ⟨n, rfl⟩
  · intro F hF
    apply hq.2
    rintro _ ⟨n, rfl⟩
    exact hF ⟨n, rfl⟩


noncomputable instance instOmegaComplete
    (P Q : QuantumCPO) : OmegaComplete (ScottFunction P Q) where
  ωSup := scottLimit
  le_ωSup K hK n := (scottLimit_isLUB K hK).1 ⟨n, rfl⟩
  ωSup_le K hK F hF := (scottLimit_isLUB K hK).2 (by
    rintro _ ⟨n, rfl⟩
    exact hF n)

end ScottFunction
end QLambda.Domain
