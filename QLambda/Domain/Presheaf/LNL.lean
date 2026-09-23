/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.LinearNonlinear
import QLambda.Domain.Presheaf.ClassicalMonoidal
import QLambda.Domain.Presheaf.OmegaEnriched
import QLambda.Domain.Presheaf.Comonoid

/-!
# Presheaf linear/nonlinear sketch (plan gate 4)

Honest packaging of the CP-presheaf sides of a prospective `LNLModel`.
Only kernel-proved ingredients are named; there is **no** fake
`presheafQuantumLNL : LNLModel` instance and **no** `sorry`.

## Kernel-proved building blocks reused here

* `biorthogonalOmegaCategory` — Day-biorthogonal classical objects with
  Choi-order ωCPO enrichment (`OmegaEnriched`)
* Representable classical objects `unitClassicalObject`,
  `representableClassicalObject`, `bitClassicalObject`,
  `classicalRepresentableTensor` (`ClassicalMonoidal`)
* Bang comonoid + cofree UP for `A ≤ 1`, with co-Kleisli promotion
  `bangPromote` / functorial `bangMap` (`Comonoid`)

## Missing for a full `presheafQuantumLNL : LNLModel`

Fill these before packaging an `LNLModel` record (see
`QLambda.Domain.LinearNonlinear.LNLModel`):

1. **`CartesianClosed` on the nonlinear side** — products and exponentials of
   `ClassicalObject`s (additive product `hom_inv`, internal-hom classicality),
   with Scott-continuous `curry`.
2. **`SymmetricMonoidalClosed` on the linear side** — Day tensor / internal
   hom as operations on `biorthogonalOmegaCategory.Obj`, with Seely/monoidal
   coherence and ωCPO enrichment of `tensorMap` / `curry`.
3. **Adjunction `F ⊣ G`** — unrestricted bang as a functor on the linear
   category (presently only `bangMap` for representable dimensions `A ≤ 1`);
   order-monotone co-Kleisli / state-hom adjunction data
   `toLinear` / `toNonlinear`.
4. **Strong monoidal structure** — `F_unit` and `F_tensor` Seely isomorphisms
   relating bang of products to tensors of bangs.
5. **General cofree bang** — `BangComultComponentsAdmissible` / cofree UP for
   `A ≥ 2`, and digging `!A → !!A` once bang is extended beyond `ℕ`-indexing.
   Path 2's proposed `Module.act_sum_from_dim` is false for TNI representables
   (`d ≥ 2`); only `CPMapSum.comp_from_dim` / `HasActSumFromDim` on ambient CP
   closed. All-A admissibility remains open.

Until those close, use `presheafLinear` / `presheafNonlinear` as named
ωCPO-enriched categories and the bang comonad interface in `Comonoid`.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

/-- Linear side of the prospective presheaf LNL model: Day-biorthogonal
classical objects enriched over pointed ωCPOs in Choi order. -/
noncomputable abbrev presheafLinear :
    QLambda.Domain.OmegaCategory :=
  biorthogonalOmegaCategory

/-- Nonlinear side sketch: the same biorthogonal ωCPO category.

A finished LNL model may refine this to a Cartesian-closed full subcategory
of based/classical objects; that packaging is not yet kernel-proved, so we
do not fabricate a different category or a `CartesianClosed` instance. -/
noncomputable abbrev presheafNonlinear :
    QLambda.Domain.OmegaCategory :=
  biorthogonalOmegaCategory

/-- Terminal / tensor-unit classical object available on both sides. -/
noncomputable abbrev presheafUnitObject : BiorthogonalObject :=
  unitClassicalObject

/-- Representable classical object `y(A)` for `A > 0`. -/
noncomputable abbrev presheafRepresentable (A : ℕ) (hA : 0 < A) :
    BiorthogonalObject :=
  representableClassicalObject A hA

/-- Bang comonoid on dimension `A ≤ 1` (linear exponential carrier). -/
noncomputable abbrev presheafBangComonoid (A : ℕ) (hA : A ≤ 1) : Comonoid :=
  bangComonoid A hA

/-- Co-Kleisli promotion for `A,B ≤ 1` (from the cofree UP). -/
noncomputable abbrev presheafBangPromote {A B : ℕ} (hA : A ≤ 1) (hB : B ≤ 1) :=
  @bangPromote A B hA hB

/-- Functorial bang on maps of representables (`A,B ≤ 1`). -/
noncomputable abbrev presheafBangMap {A B : ℕ} (hA : A ≤ 1) (hB : B ≤ 1) :=
  @bangMap A B hA hB

end SuperoperatorModule

end QLambda.Domain.Presheaf
