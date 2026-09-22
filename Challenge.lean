/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda

/-!
# Palomar statement surface for the typed linear redesign

Challenge contains only theorem holes.  `Solution.lean` proves the same
statements from the active typed `QLambda` root.
-/

namespace QLambda.Palomar

open Domain
open Linear

/-- A concrete quantum linear/nonlinear model exists. -/
theorem quantum_lnl_model :
    Nonempty LNLModel.{1, 0} := by
  sorry

/-- Quantum CPOs and Scott-continuous quantum functions form an
omega-CPO-enriched category. -/
theorem quantum_cpo_enriched_category :
    Nonempty OmegaCategory.{1, 0} := by
  sorry

/-- Every command in the declared two-wire quotation fragment has a canonical
typed lambda representative with exact compilation and CQ denotation. -/
theorem two_wire_circuit_completeness
    (model : Composer.Model
      Linear.Command.GeneralQuotation.quantumSize
      Linear.Command.GeneralQuotation.classicalSize)
    (C : Linear.Command
      Linear.Command.GeneralQuotation.quantumSize
      Linear.Command.GeneralQuotation.classicalSize)
    (hC : Linear.Command.GeneralQuotation.Quotable C) :
    Linear.HasType [] []
        (Linear.Command.GeneralQuotation.Quotation.reflect C hC).term
        Linear.Command.GeneralQuotation.quotationTy ∧
      (Linear.Command.GeneralQuotation.Quotation.reflect C hC).compile = C ∧
      CQ.Eq
        ((Linear.Command.GeneralQuotation.Quotation.reflect C hC).denote model)
        (C.denote model) := by
  sorry

end QLambda.Palomar
