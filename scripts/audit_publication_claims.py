#!/usr/bin/env python3
"""Check that publication theorem claims resolve to compiled Lean declarations."""

from __future__ import annotations

import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
THEOREMS = ROOT / "THEOREMS.md"
PUBLIC_DOCS = ["arxiv.md", "README.md", "HANDOFF.md", "PROVENANCE.md",
               "THEOREMS.md", "formalization.yaml"]
PALOMAR_DOCS = ["HANDOFF.md", "PROVENANCE.md"]
PERMITTED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
# Concrete OpenQASM fixtures are evaluated by compiled code, not the kernel.
# THEOREMS.md must disclose this; no other declaration may use native axioms.
NATIVE_FIXTURES = {
    "QLambda.Composer.Fixtures.bell_openQASM_parse_succeeds",
    "QLambda.Composer.Fixtures.dynamicX_openQASM_parse_succeeds",
}
NATIVE_DISCLOSURE = "checked by `native_decide`"

# These names describe the planned semantic capstones.  They must not enter
# the proved theorem index before matching declarations compile.
OBJECTIVE_ONLY = {
    "presheafQuantumLNL",
    "presheafSourceDenote",
    "presheafSourceAdequacy",
    "denote_compile_source",
}

PROHIBITED_CLAIMS = {
    "staging and compilation preserve source denotation":
        "quotation currently proves inherited CQ equality only",
    "recursive types are represented by compatible chains":
        "only the generic chain construction currently compiles",
    "bounded repeat":
        "the circuit normal form has no repeat constructor",
}


def read(name: str) -> str:
    return (ROOT / name).read_text(encoding="utf-8")


def check_palomar_surface(theorem_text: str) -> list[str]:
    comparator = json.loads(read("comparator.json"))
    names = set(comparator["theorem_names"])
    leaked = sorted(n for n in names if n.rsplit(".", 1)[-1] in OBJECTIVE_ONLY)
    if leaked:
        raise SystemExit("error: objective-only names compared: " + ", ".join(leaked))

    indexed = set(re.findall(r"^- `(QLambda\.Palomar\.[^`]+)`", theorem_text,
                             flags=re.MULTILINE))
    yaml_names = set(re.findall(r'^\s*- declaration: "([^"]+)"',
                                read("formalization.yaml"), flags=re.MULTILINE))
    for label, found in [("THEOREMS.md", indexed),
                         ("formalization.yaml main_results", yaml_names)]:
        if found != names:
            raise SystemExit(
                f"error: {label} Palomar names {sorted(found)} differ from "
                f"comparator.json {sorted(names)}"
            )
    for doc in PALOMAR_DOCS:
        text = read(doc)
        missing = sorted(n for n in names if f"`{n}`" not in text)
        stale = sorted(set(re.findall(r"`(QLambda\.Palomar\.[^`]+)`", text)) - names)
        if missing or stale:
            raise SystemExit(
                f"error: {doc} Palomar names missing {missing}, stale {stale}"
            )
    for module in ["Challenge.lean", "Solution.lean"]:
        text = read(module)
        for name in names:
            short = name.rsplit(".", 1)[-1]
            if not re.search(rf"^theorem {re.escape(short)}\b", text, flags=re.MULTILINE):
                raise SystemExit(f"error: {module} does not state {name}")
    return sorted(names)


def main() -> None:
    theorem_text = THEOREMS.read_text(encoding="utf-8")
    declarations = re.findall(r"^- `([^`]+)`", theorem_text, flags=re.MULTILINE)

    if not declarations:
        raise SystemExit("error: THEOREMS.md contains no declaration bullets")

    leaked = sorted(OBJECTIVE_ONLY.intersection(declarations))
    if leaked:
        raise SystemExit(
            "error: objective-only names listed as proved: " + ", ".join(leaked)
        )

    for doc in PUBLIC_DOCS:
        text = " ".join(read(doc).split())
        for phrase, reason in PROHIBITED_CLAIMS.items():
            if phrase in text:
                raise SystemExit(f"error: overclaim in {doc}: {phrase!r} ({reason})")

    palomar = check_palomar_surface(theorem_text)
    if NATIVE_FIXTURES.intersection(declarations) and NATIVE_DISCLOSURE not in theorem_text:
        raise SystemExit("error: THEOREMS.md lists native_decide fixtures without disclosure")

    commands = "\n".join(
        f"#check {name}\n#print axioms {name}" for name in declarations
    )
    source = "import Solution\n\n" + commands + "\n"
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

    for name, axioms in re.findall(
        r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout
    ):
        used = {a.strip() for a in axioms.split(",") if a.strip()}
        if name in NATIVE_FIXTURES:
            used = {a for a in used if "._native.native_decide." not in a}
        if used - PERMITTED_AXIOMS:
            raise SystemExit(
                f"error: {name} uses axioms {sorted(used - PERMITTED_AXIOMS)}"
            )

    print(
        f"OK: {len(declarations)} publication declarations compile with "
        f"permitted axioms; Palomar surface {palomar} is consistent; "
        f"{len(OBJECTIVE_ONLY)} semantic capstone names remain objectives."
    )


if __name__ == "__main__":
    main()
