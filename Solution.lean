/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda

/-! # Sorry-free solutions to the typed-linear Palomar challenge. -/

namespace QLambda.Palomar

open Domain
open Linear

theorem quantum_lnl_model :
    Nonempty LNLModel.{1, 0} :=
  ⟨quantumLNL⟩

theorem quantum_cpo_enriched_category :
    Nonempty OmegaCategory.{1, 0} :=
  ⟨qCPOCategory⟩

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
        (C.denote model) :=
  Linear.Command.GeneralQuotation.Quotation.quotation_capstone model C hC

end QLambda.Palomar
