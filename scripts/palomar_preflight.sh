#!/usr/bin/env bash
# Thin wrapper: Palomar local preflight lives in vendor/palomar-preflight.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
export PALOMAR_PROJECT_ROOT="$ROOT"
export PALOMAR_SORRY_PATHS="QLambda Solution.lean"
export PALOMAR_CHALLENGE_FORBIDDEN_PREFIXES="QLambda"
exec bash "$ROOT/vendor/palomar-preflight/palomar_preflight.sh" "$@"
