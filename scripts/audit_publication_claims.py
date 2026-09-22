#!/usr/bin/env python3
"""Check that publication theorem claims resolve to compiled Lean declarations."""

from __future__ import annotations

import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
THEOREMS = ROOT / "THEOREMS.md"
ARXIV = ROOT / "arxiv.md"

# These names describe the planned semantic capstones.  They must not enter
# the proved theorem index before matching declarations compile.
OBJECTIVE_ONLY = {
    "presheafQuantumLNL",
    "presheafSourceDenote",
    "presheafSourceAdequacy",
    "denote_compile_source",
}

PROHIBITED_PAPER_CLAIMS = {
    "staging and compilation preserve source denotation":
        "quotation currently proves inherited CQ equality only",
    "recursive types are represented by compatible chains":
        "only the generic chain construction currently compiles",
}


def main() -> None:
    theorem_text = THEOREMS.read_text(encoding="utf-8")
    paper_text = ARXIV.read_text(encoding="utf-8")
    declarations = re.findall(r"^- `([^`]+)`", theorem_text, flags=re.MULTILINE)

    if not declarations:
        raise SystemExit("error: THEOREMS.md contains no declaration bullets")

    leaked = sorted(OBJECTIVE_ONLY.intersection(declarations))
    if leaked:
        raise SystemExit(
            "error: objective-only names listed as proved: " + ", ".join(leaked)
        )

    for phrase, reason in PROHIBITED_PAPER_CLAIMS.items():
        if phrase in paper_text:
            raise SystemExit(f"error: overclaim in arxiv.md: {phrase!r} ({reason})")

    checks = "\n".join(f"#check {name}" for name in declarations)
    source = "import Solution\n\n" + checks + "\n"
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", dir=ROOT, encoding="utf-8", delete=False
    ) as handle:
        handle.write(source)
        check_file = Path(handle.name)

    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(check_file)],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
    finally:
        check_file.unlink(missing_ok=True)

    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)

    print(
        f"OK: {len(declarations)} publication declarations compile; "
        f"{len(OBJECTIVE_ONLY)} semantic capstone names remain objectives."
    )


if __name__ == "__main__":
    main()
