# Language Semantics Plan

## Progress

Completed:

- recursive semantic β;
- abstract `Step` and `Reduces` soundness;
- separate abstract specifications for weighted branches and external
  selection;
- exact top-level external-selection soundness;
- top-level probabilistic branch theorems retaining their weights;
- full abstract `WeightedStep` soundness under explicit application-closure
  laws;
- TT internal choice as pointwise join, including algebra laws and exact bind
  compatibility;
- embedded qubit return, Pauli-X, and Z-measurement primitive examples;
- Scott-continuous weighted TT result aggregation (physical coin, not join);
- pointwise probabilistic choice on TT continuations, with bind laws and a
  concrete `weightedBranch` relation;
- branch-tagged external choice with exact Boolean selectors, not identified
  with internal choice;
- lawful tagged `HasComputationChoice`, `HasExternalSelection`,
  `HasWeightedBranchSemantics`, and `HasWeightedApplicationClosure`;
- token-by-token adequacy for return, Pauli-X, Z measurement, finite bind,
  interior weighted traces, and external selection on finitely presented
  continuations;
- a finite-instrument representation of every rational
  `CodedTestRepresentation`, giving unconditional recovery of finitary TT
  refinement from embedding order;
- a concrete directed dyadic-prefix family whose supremum leaves the finite
  physical image, proving unconditional nonexistence of a finite-image Scott
  retraction;
- a hardware-faithful qubit CEK machine with normalized density states,
  runtime logical relations, and exact Born-normalized positive transitions;
- a separate proof-only subnormalized channel-tree semantics which retains
  zero branches and has exact finite-instrument/token correspondence;
- finite-iterate approximation of recursive Scott fixed points.

Remaining boundary:

- general closed-term adequacy is reduced to `ChannelTreeCompleteness`, the CEK
  fundamental lemma identifying the interpreter with the supremum of
  branch-complete subnormalized channel-tree instruments. It no longer assumes
  that a recursive denotation is one finite physical embedding. A formal
  counterexample rules out deriving state-independent TT completeness from a
  single arbitrary normalized hardware run.

## Goal

Connect the computation-valued interpretation to the operational semantics,
then instantiate the abstract choice interface for the TT continuation model.
Keep internal, probabilistic, and external choice distinct rather than
asserting soundness laws unsupported by the current interface.

## Phase 1: Recursive β

Prove `interp_rec_beta` for:

```lean
Step
  (.app (.recLam self arg M) V)
  (subst arg V (subst self (.recLam self arg M) M))
```

under `self ≠ arg` and `Value V`.

Use:

- `recLambdaValue_unfold`;
- `interp_subst_value` twice;
- environment shadowing and commutation;
- purity of recursive abstractions.

The target should be semantic equality.

## Phase 2: Abstract Internal-Step Soundness

Add `QLambda/Soundness.lean` and prove the direction:

```lean
Step M N → interp primitive N ρ ≤ interp primitive M ρ
```

Expected rule behavior:

- `beta`: equality via `interp_beta`;
- `rec_beta`: equality via `interp_rec_beta`;
- `intern_left` and `intern_right`: existing branch-to-choice inequalities;
- `app_left` and `app_right`: monotonicity of `applyComp`.

Lift the theorem to `Reduces`.

Do not include `WeightedStep` or `ExternalStep` in this theorem.

## Phase 3: Specify Missing Choice Laws

Strengthen or supplement `HasComputationChoice` with laws sufficient to state
soundness for the other operational relations.

### Probabilistic choice

First define what a weighted transition means denotationally. A theorem about
`WeightedStep M p N` must account for the weight `p`; comparing `interp N`
directly with `interp M` discards essential information.

Specify a Scott-continuous weighting or branch-contribution operation and the
laws relating it to `HasComputationChoice.prob`.

### External choice

Specify how a Boolean environment selection observes or resolves
`HasComputationChoice.extern`. Add explicit left- and right-selection laws.

Avoid identifying external choice with internal nondeterminism merely to make
the proof easy.

## Phase 4: Concrete TT Choice Semantics

Construct Scott-continuous probabilistic, internal, and external choice
operations on `TTContinuationPower`.

Prove:

- the interface laws from Phase 3;
- `left_le_intern` and `right_le_intern`;
- compatibility with continuation `unit` and `bind` where required;
- finite-instrument compatibility for represented continuations.

Register the resulting `HasComputationChoice` instance only after these laws
are established.

## Phase 5: Weighted and External Soundness

Using the strengthened interface and TT implementation, prove:

- weighted-step soundness with the transition probability retained in the
  semantic statement;
- external-step soundness parameterized by the Boolean environment action;
- compatible application-context rules.

Lift each relation to its appropriate multi-step or trace semantics if one is
introduced.

## Phase 6: Physical Primitive Examples

Define representative primitive symbols and interpret them through
`TTPhysicalEmbedding.embed`.

Show that:

- primitive terms denote their embedded finite TNI instruments;
- application and finite bind agree on represented continuations;
- examples involving choice use the concrete TT choice operations.

## Phase 7: Adequacy

After soundness and the concrete TT instance:

1. formulate a value-observation or termination relation;
2. prove partial adequacy for closed terms;
3. identify any additional density or separation assumptions needed for full
   adequacy.

Do not claim full adequacy until the observation relation separates the
relevant TT denotations.

## Documentation

Update `HANDOFF.md` to:

- mark weighted aggregation, tagged external choice, and the concrete TT
  computation-choice instances complete;
- record token-by-token adequacy of the finitely presented primitive
  fragment;
- record unconditional rational coded-test separation and the concrete
  directed-sup non-closure witness.

## Verification

At each phase:

```text
lake build QLambda Challenge Solution
bash scripts/compare_challenge_solution_types.sh
```

All new proof modules must remain free of `sorry`, `admit`, and extra axioms.
