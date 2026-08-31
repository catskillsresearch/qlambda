#!/usr/bin/env bash
# Diff Challenge vs Solution declaration types for every comparator.json name.
# Palomar Comparator looks up those names in two lean4export environments
# and compares theorem constants directly. Entries in `definition_names` are
# deliberate definition holes: Challenge leaves their values as `sorry`, while
# Solution supplies checked implementations. Comparator matches their names,
# kinds, universe/safety levels, and types and checks their axiom closure; it
# does not require the Challenge's `sorryAx` body to equal the Solution body.
# A green `lake build` alone does not imply a match.
#
# Gotchas this script is meant to catch:
# - instance-path mismatch (e.g. ConditionallyCompletePartialOrder.toSupSet
#   vs ScottMap.instSupSet)
# - pretty-printer hiding a module prefix (`Challenge.Foo` vs `Foo`)
# - a `def` listed under theorem_names (Comparator then throws
#   "constant kind don't match")
# - a non-definition listed under definition_names
# - universe arity/type mismatches hidden by ordinary pretty printing.
set -euo pipefail
cd "$(dirname "$0")/.."

mapfile -t NAMES < <(python3 - <<'PY'
import json
cfg = json.load(open("comparator.json"))
for n in cfg["theorem_names"] + cfg.get("definition_names", []):
    print(n)
PY
)

mapfile -t THEOREM_NAMES < <(python3 - <<'PY'
import json
cfg = json.load(open("comparator.json"))
for n in cfg["theorem_names"]:
    print(n)
PY
)

mapfile -t DEFINITION_NAMES < <(python3 - <<'PY'
import json
cfg = json.load(open("comparator.json"))
for n in cfg.get("definition_names", []):
    print(n)
PY
)

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

write_lean() {
  local module="$1" out="$2"
  {
    echo "import ${module}"
    echo "set_option pp.all true"
    echo "set_option pp.explicit true"
    echo "set_option pp.universes true"
    echo "set_option pp.fullNames true"
    echo "set_option pp.funBinderTypes true"
    for n in "${NAMES[@]}"; do
      echo "#check ${n}"
    done
  } >"${out}"
}

write_lean Challenge "${tmp}/ChallengeTypes.lean"
write_lean Solution "${tmp}/SolutionTypes.lean"

write_kind_lean() {
  local module="$1" out="$2"
  {
    echo "import ${module}"
    cat <<'LEAN'
open Lean Elab Command
elab "#assert_theorem " n:ident : command => do
  match (← getEnv).find? n.getId with
  | some (.thmInfo _) => pure ()
  | some _ => throwError "{n.getId} is not a theorem"
  | none => throwError "unknown declaration {n.getId}"
elab "#assert_definition " n:ident : command => do
  match (← getEnv).find? n.getId with
  | some (.defnInfo _) => pure ()
  | some _ => throwError "{n.getId} is not a definition"
  | none => throwError "unknown declaration {n.getId}"
LEAN
    for n in "${THEOREM_NAMES[@]}"; do
      echo "#assert_theorem ${n}"
    done
    for n in "${DEFINITION_NAMES[@]}"; do
      echo "#assert_definition ${n}"
    done
  } >"${out}"
}

write_kind_lean Challenge "${tmp}/ChallengeKinds.lean"
write_kind_lean Solution "${tmp}/SolutionKinds.lean"
for module in Challenge Solution; do
  if ! lake env lean "${tmp}/${module}Kinds.lean" >"${tmp}/${module}-kinds.raw" 2>&1; then
    echo "FAIL: Comparator declaration-kind check failed in ${module}."
    cat "${tmp}/${module}-kinds.raw"
    exit 1
  fi
done
echo "OK: theorem_names and definition_names have the required declaration kinds."

# grep exits 1 on empty output, which is the normal state while comparator.json
# still lists no names. Do not let that abort the run.
if ! lake env lean "${tmp}/ChallengeTypes.lean" >"${tmp}/challenge.raw" 2>&1; then
  echo "FAIL: could not inspect Challenge declarations."
  cat "${tmp}/challenge.raw"
  exit 1
fi
if ! lake env lean "${tmp}/SolutionTypes.lean" >"${tmp}/solution.raw" 2>&1; then
  echo "FAIL: could not inspect Solution declarations."
  cat "${tmp}/solution.raw"
  exit 1
fi
grep -vE 'LEAN_PATH|trace:|warning:|declaration uses' \
  <"${tmp}/challenge.raw" >"${tmp}/challenge.txt" || true
grep -vE 'LEAN_PATH|trace:|warning:|declaration uses' \
  <"${tmp}/solution.raw" >"${tmp}/solution.txt" || true

# Lean's pretty printer renumbers imported anonymous universe names according
# to each module environment (`u_1` versus `u_3`). Comparator compares the
# exported level structure modulo those presentation names. Normalize only
# that printer noise; named universes and the full type structure remain.
normalize_pp_universes() {
  sed -E 's/\.\{u_[0-9]+(,[ ]*u_[0-9]+)*\}//g; s/u_[0-9]+/u/g'
}

if [[ "${PALOMAR_QUIET:-0}" != 1 ]]; then
  echo "== Challenge (pp.all + pp.fullNames) =="
  cat "${tmp}/challenge.txt"
  echo
  echo "== Solution (pp.all + pp.fullNames) =="
  cat "${tmp}/solution.txt"
  echo
fi
normalize_pp_universes <"${tmp}/challenge.txt" >"${tmp}/challenge.norm"
normalize_pp_universes <"${tmp}/solution.txt" >"${tmp}/solution.norm"

if diff -u "${tmp}/challenge.norm" "${tmp}/solution.norm"; then
  echo "OK: Challenge and Solution theorem/definition-hole names, universes, and types match."
else
  echo "FAIL: type/universe/instance/name mismatch — Palomar Comparator will reject this."
  echo
  diff -u "${tmp}/challenge.norm" "${tmp}/solution.norm" || true
  exit 1
fi
