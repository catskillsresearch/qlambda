/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.OmegaComplete
import QLambda.Domain.instOmegaCompleteOfCompleteLattice

/-!
# Instance `instOmegaCompleteProd`
-/

namespace QLambda.Domain

universe u v

noncomputable instance instOmegaCompleteProd
    {D : Type u} {E : Type v}
    [PartialOrder D] [OmegaComplete D]
    [PartialOrder E] [OmegaComplete E] :
    OmegaComplete (D × E) where
  ωSup c hc :=
    (OmegaComplete.ωSup (fun n => (c n).1)
      (fun _ _ h => (hc h).1),
    OmegaComplete.ωSup (fun n => (c n).2)
      (fun _ _ h => (hc h).2))
  le_ωSup c hc n :=
    ⟨OmegaComplete.le_ωSup (fun k => (c k).1)
        (fun _ _ h => (hc h).1) n,
      OmegaComplete.le_ωSup (fun k => (c k).2)
        (fun _ _ h => (hc h).2) n⟩
  ωSup_le c hc x hx :=
    ⟨OmegaComplete.ωSup_le (fun k => (c k).1)
        (fun _ _ h => (hc h).1) x.1
        (fun n => (hx n).1),
      OmegaComplete.ωSup_le (fun k => (c k).2)
        (fun _ _ h => (hc h).2) x.2
        (fun n => (hx n).2)⟩


end QLambda.Domain
