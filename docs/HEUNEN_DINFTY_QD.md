# From the discarded `D∞` / `Q(D)` presentation to typed qCPO semantics

This note records the old-to-new correspondence for direct discussion with
Chris Heunen. It is not part of the paper.

## What the old objects were

The previous untyped development used a universal reflexive domain. Its
finite stages were

`D₀ = PUnit`, `Dₙ₊₁ = ScottMap Dₙ (Q Dₙ)`,

and `D∞` was their inverse limit. Thus an element of `D∞` was concretely a
compatible sequence of finite-stage approximants. The implementation is in
`QLambda/QDomain.lean`.

The corresponding continuation power was

`Qₙ(D) = [[D → Rₙ] → Rₙ]`.

It was therefore concrete as a Scott-continuation domain. It was not the set
of finite quantum instruments, nor did it itself provide the linear quantum
category required by the present calculus. The implementation is in
`QLambda/TTContinuationMonad.lean`.

## Why those objects are no longer central

The source language is now typed and linear. A universal untyped reflexive
object obscures both the interpretation of individual types and the
no-cloning discipline. Likewise, a single continuation monad makes quantum
effects look like a source-level effect construction, whereas gates and
measurement belong in the linear semantic category.

The replacement vocabulary is:

- each source type `A` has its own qCPO object `⟦A⟧`;
- a judgment `Γ ; Δ ⊢ M : A` denotes a morphism
  `F⟦Γ⟧ ⊗ ⟦Δ⟧ ⟶ ⟦A⟧` in a linear/nonlinear model;
- gates denote completely positive morphisms;
- measurement denotes a finite instrument, and is the only source of
  probabilistic branching;
- an admissible recursive type `μα.A` is solved by the bilimit of its own
  finite unfolding chain, so its elements are compatible sequences of
  type-specific finite approximants.

The formal replacement foundations are in `QLambda/Domain/OmegaCPO.lean`,
`Enriched.lean`, `LinearNonlinear.lean`, `QuantumCPO.lean`, and
`RecursiveTypes.lean`.

If a classical computational monad is later extracted from the LNL
adjunction, it should be named as that induced monad. It should not be
identified with the discarded continuation power `Q(D)`.
