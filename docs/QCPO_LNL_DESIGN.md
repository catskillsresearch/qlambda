# Published qCPO LNL route and remaining model boundary

The checked `quantumLNL` declaration is the ordinary compact-closed
`Set ⊣ qRel` state adjunction. It is useful for relation algebra, but it is
not the recursive LNL model of *Quantum CPOs* or *Categories of Quantum CPOs*.

## Literature-supported construction

The recursive model should use:

1. pointed classical omega-CPOs and continuous maps;
2. quantum CPOs and Scott-continuous quantum functions, ordered by
   `F ⊑ G ↔ G ≤ S ∘ F`, not by relation inclusion;
3. the quantum lift monad;
4. its Kleisli category `qCPO⊥!`;
5. the strong-monoidal classical quantization functor and state right adjoint.

The intended adjunction is therefore

```text
omegaCPO  ⟷  Kleisli(qCPO, lift)
```

not a graph functor from pointwise-ordered continuous maps into `qRel`.
Ordinary graphs are not monotone for relation inclusion: distinct constant
functions may be pointwise comparable while their graphs are disjoint.

## Required Lean bundles

The existing `QuantumCPOCategory.lean` supplies the published pointwise order,
arbitrary-domain limits, Scott maps, omega-complete homs, and enriched
composition. The remaining construction requires:

- the lift quantum CPO, unit, map, and join;
- monad and omega-continuity laws;
- the Kleisli enriched category and its hom bottoms;
- qCPO tensor, double strength, and Kleisli internal hom;
- classical ordered quantization, with graph monotonicity proved against the
  lifted codomain order;
- state currying/uncurrying and strong-monoidal adjunction laws;
- algebraic compactness or the exact locally continuous recursive-type
  theorem needed by source `mu`.

`ProjectionChain.shiftIso` proves a generic continuous shift isomorphism once
an appropriate chain is supplied; it does not construct these qCPO source-type
chains by itself.

## Physical primitive boundary

`QuantumRel.bot` is not a quantum function and cannot be used as the bottom
Scott map. General completed CP maps also do not embed as Weaver quantum
functions. In particular, fresh-state preparation, reset, and arbitrary
instruments are outside the pure qCPO-function category.

Consequently the published lifted-qCPO LNL construction can support the
categorical and recursive core, but it does not by itself instantiate the
current `DenotationModel` for every physical primitive and measurement branch.
That requires an additional probabilistic/CP monad or a different
CP-enriched model, such as the enriched-presheaf direction.

No release claim should identify the existing ordinary `Set ⊣ qRel` instance
with the published qCPO LNL model, or claim unrestricted adequacy before this
boundary is resolved.
