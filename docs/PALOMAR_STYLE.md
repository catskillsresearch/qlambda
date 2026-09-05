# Palomar Challenge/Comparator style

Palomar compares elaborated Lean constants, not merely mathematical
equivalence or ordinary pretty-printed declarations. A `definition_names`
entry is intentionally a definition hole: Challenge may give it a `sorry`
body, while Solution supplies the implementation. Comparator checks the
declaration name and kind, universe/safety level, type, allowed axiom closure,
and kernel acceptance. It does not require the Challenge `sorryAx` value to
equal the Solution implementation. Run this before every submission:

```bash
scripts/palomar_preflight.sh
```

## Compared declarations

- Pin explicit universe arity (`Type u`, `Type v`) and inspect the exported
  levels; pretty-printer-generated `u_1`/`u_3` labels are presentation noise.
- Keep instance paths explicit where elaboration could choose different
  equivalent instances.
- A `theorem_names` entry must be a theorem; a `definition_names` entry must be
  a definition-valued constant (an ordinary definition or named instance),
  not a structure declaration or theorem.
- List every material opaque Challenge definition reachable from the selected
  statement. Give each hole a precise docstring describing the intended
  construction; the Solution implementation is what Comparator kernel-checks.
- Keep concrete (non-hole) definitions used by the statement identical between
  Challenge and Solution.
- Write order operations with explicit `@LE.le` instance paths when Challenge
  and Solution import graphs can elaborate `≤` through different parent
  structures. This repository is exposed to that failure mode wherever a
  Boolean-algebra or linear-order instance can be reached by two routes.

## Definition-hole boundary

Prefer a compact, semantically strong type. For example, the type of
`canonicalQDomainProjection` fixes both directions and both projection laws;
its Challenge body may be `sorry`, and the name belongs in
`definition_names`. Do not compare a `#print`ed Challenge body against the
Solution body: that would compare `sorryAx` with real code and always reject a
valid definition-hole submission.

## Submission checklist

The preflight must confirm:

1. the full project builds;
2. compared theorem and definition-hole names, kinds, universe structures, and
   types match;
3. every material Challenge hole is listed in `definition_names`;
4. Solution sources contain no `sorry`;
5. Solution theorem axioms are permitted by `comparator.json`; and
6. the patch has no whitespace errors.

For registry submission, also run the full editorial audit
(`docs/PALOMAR_EDITORIAL_AUDIT.md`):

```bash
bash scripts/palomar_preflight.sh              # mechanical + LLM audit
bash scripts/palomar_preflight.sh --mechanical-only   # CI / routine edits
python3 ../palomar-preflight/palomar_editorial_checks.py      # packaging pre-checks only
```

Treat a green `lake build` alone as insufficient.
