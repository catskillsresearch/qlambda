#!/usr/bin/env bash
set -euo pipefail
python3 - <<'PY'
import re
from pathlib import Path

frozen = Path("vendor/FROZEN.txt").read_text(encoding="utf-8")
yaml = Path("formalization.yaml").read_text(encoding="utf-8")
match = re.search(
    r"vendor/scott1972\n(?:  .*\n)*?  rev:\s+(\S+)", frozen
)
if not match:
    raise SystemExit("Could not parse vendor/scott1972 rev from vendor/FROZEN.txt")
rev = match.group(1)
if f"/tree/{rev}" not in yaml:
    raise SystemExit(
        f"formalization.yaml is missing related_formalizations tree URL for scott1972 {rev}"
    )
print(f"OK: related_formalizations revision matches vendor/FROZEN.txt ({rev[:12]}…).")
PY
