#!/usr/bin/env python3
"""Deterministic editorial pre-checks before Palomar LLM audit."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    yaml = None  # type: ignore[assignment]

ROOT = Path(__file__).resolve().parent.parent

AI_NAME_PATTERNS = re.compile(
    r"(?i)\b("
    r"gpt[-\s]?\d|claude|codex|openai|anthropic|chatgpt|"
    r"auto[-\s]?review|language model|llm|cursor agent|"
    r"copilot|gemini|deepseek"
    r")\b"
)

QUALIFIED_NAME = re.compile(r"[A-Za-z][A-Za-z0-9_']*\.[A-Za-z_][A-Za-z0-9_']*")

# Optional per-theorem source hints when a compared result needs an extra
# formalization.yaml sources entry beyond the primary paper record.
ALLOWED_SOURCE_TYPES = {"paper", "book", "web discussion", "folklore", "original-proof", "other"}
ORIGINAL_RELATIONSHIPS = {"background", "other"}
SUBSTANTIVE_RELATIONSHIPS = {"formalizes", "adapts", "independently-proves"}

THEOREM_BODY = re.compile(
    r"(?:/--[\s\S]*?-/\s*\n\s*)?"
    r"theorem\s+{name}\b([\s\S]*?):=\s*by\s+sorry",
    re.MULTILINE,
)

THEOREM_SOURCE_HINTS: dict[str, tuple[str, ...]] = {}

EXPECTED_CAPSTONE = (
    "Scott1972.ContinuousLattice."
    "canonical_omegaQVA_quantum_domain_equation_solved"
)

REQUIRED_DEFINITION_HOLES = {
    "Scott1972.ContinuousLattice.ScottMap.instSupSet",
    "Scott1972.ContinuousLattice.ScottMap.instCompleteLattice",
    "Scott1972.ContinuousLattice.ScottMap.idMap",
    "Scott1972.ContinuousLattice.ScottMap.comp",
    "Scott1972.ContinuousLattice.instCompleteLattice",
    "Scott1972.ContinuousLattice.embInf",
    "Scott1972.ContinuousLattice.projInf",
    "Scott1972.ContinuousLattice.omegaQVA_pUnit",
    "Scott1972.ContinuousLattice.canonicalQDomainProjection",
    "Scott1972.ContinuousLattice.qTowerProj",
    "Scott1972.ContinuousLattice.qEmbInfInf",
    "Scott1972.ContinuousLattice.qProjInfInf",
}

PROJECTION_DOCS = (
    "Challenge.lean",
    "README.md",
    "formalization.yaml",
    "arxiv.md",
    "THEOREMS.md",
    "HANDOFF.md",
    "PROVENANCE.md",
)


def check_sources(formalization: dict) -> list[str]:
    errors: list[str] = []
    sources = formalization.get("sources", [])
    if not isinstance(sources, list) or not sources:
        return ["sources must be a nonempty list"]

    has_original = False
    has_substantive = False
    for idx, source in enumerate(sources):
        if not isinstance(source, dict):
            errors.append(f"sources[{idx}] must be a mapping")
            continue
        stype = source.get("type")
        if stype is not None and stype not in ALLOWED_SOURCE_TYPES:
            errors.append(f"sources[{idx}].type {stype!r} is not in Palomar vocabulary")
        rel = source.get("relationship")
        if stype == "original-proof":
            has_original = True
            if rel != "other":
                errors.append(
                    f"sources[{idx}] with type original-proof must have relationship other"
                )
        if rel in SUBSTANTIVE_RELATIONSHIPS:
            has_substantive = True
        if has_original and rel not in ORIGINAL_RELATIONSHIPS:
            errors.append(
                f"sources[{idx}] relationship {rel!r} is incompatible with original result origin"
            )

    if has_original and has_substantive:
        errors.append(
            "sources cannot combine original-proof with formalizes/adapts/independently-proves"
        )
    elif not has_original and not has_substantive:
        errors.append(
            "sources must declare either an original-proof entry or a substantive source-based entry"
        )
    return errors


def check_frozen_revision(formalization: dict) -> list[str]:
    errors: list[str] = []
    frozen_path = ROOT / "vendor" / "FROZEN.txt"
    if not frozen_path.is_file():
        return errors
    text = frozen_path.read_text(encoding="utf-8")
    rev_match = re.search(r"vendor/scott1972\n(?:  .*\n)*?  rev:\s+(\S+)", text)
    if not rev_match:
        errors.append("could not parse vendor/scott1972 rev from vendor/FROZEN.txt")
        return errors
    rev = rev_match.group(1)
    yaml_blob = (ROOT / "formalization.yaml").read_text(encoding="utf-8")
    if f"/tree/{rev}" not in yaml_blob:
        errors.append(
            f"formalization.yaml missing related_formalizations tree URL for scott1972 {rev}"
        )
    return errors


def load_formalization(path: Path) -> dict:
    if yaml is None:
        raise SystemExit("PyYAML is required: pip install pyyaml")
    text = path.read_text(encoding="utf-8")
    doc = yaml.safe_load(text)
    if not isinstance(doc, dict):
        raise SystemExit(f"{path} must contain one top-level mapping")
    return doc


def load_comparator(path: Path) -> dict:
    with path.open(encoding="utf-8") as f:
        return json.load(f)


def check_human_only(names: list[str], field: str) -> list[str]:
    errors: list[str] = []
    for name in names:
        if not isinstance(name, str) or not name.strip():
            errors.append(f"{field} contains empty name")
        elif AI_NAME_PATTERNS.search(name):
            errors.append(f"{field} must name humans only; suspicious entry: {name!r}")
    return errors


def check_license(formalization: dict) -> list[str]:
    errors: list[str] = []
    declared = formalization.get("project", {}).get("license")
    licence_files = list(ROOT.glob("LICENSE*")) + list(ROOT.glob("Licence*"))
    if not licence_files:
        errors.append("missing root licence file")
        return errors
    if declared != "Apache-2.0":
        errors.append(f"project.license must be Apache-2.0, got {declared!r}")
    return errors


def check_required_fields(formalization: dict) -> list[str]:
    errors: list[str] = []
    if formalization.get("version") != "v0.4":
        errors.append(f"formalization.yaml version must be v0.4, got {formalization.get('version')!r}")
    project = formalization.get("project", {})
    for key in ("name", "description", "authors", "license", "responsible_maintainers"):
        if key not in project:
            errors.append(f"missing project.{key}")
    desc = project.get("description", "")
    if not isinstance(desc, str) or not desc.strip():
        errors.append("project.description must be nonempty")
    classification = formalization.get("classification", {})
    arxiv = classification.get("arxiv")
    if not isinstance(arxiv, list) or not arxiv:
        errors.append("classification.arxiv must be a nonempty list")
    automation = formalization.get("automation", {})
    methods = automation.get("methods")
    if not isinstance(methods, list) or not methods:
        errors.append("automation.methods must be a nonempty list")
    review = formalization.get("review", {})
    if not review.get("status"):
        errors.append("review.status must be nonempty")
    sources = formalization.get("sources")
    if not isinstance(sources, list) or not sources:
        errors.append("sources must be a nonempty list")
    return errors


def comparator_declarations(cfg: dict) -> list[str]:
    return list(cfg.get("theorem_names", [])) + list(cfg.get("definition_names", []))


def short_name(full: str) -> str:
    return full.split(".")[-1]


def main_result_declaration(entry: object) -> str | None:
    if isinstance(entry, dict):
        decl = entry.get("declaration")
        return decl if isinstance(decl, str) and decl else None
    if isinstance(entry, str) and entry.strip():
        return entry.strip()
    return None


def check_main_results(formalization: dict, cfg: dict) -> list[str]:
    errors: list[str] = []
    compared = set(comparator_declarations(cfg))
    for entry in formalization.get("status", {}).get("main_results", []) or []:
        if not isinstance(entry, dict):
            continue
        decl = main_result_declaration(entry)
        if not decl:
            continue
        if entry.get("comparator_config") and decl not in compared:
            errors.append(
                f"main_results declaration {decl!r} with comparator_config not in comparator.json"
            )
    return errors


def check_alignment(formalization: dict, challenge_text: str, cfg: dict) -> list[str]:
    errors: list[str] = []
    compared_short = {short_name(name) for name in comparator_declarations(cfg)}
    for entry in formalization.get("alignment", {}).get("statements", []) or []:
        lean = entry.get("lean")
        if not isinstance(lean, str) or not lean.strip():
            continue
        if " through " in lean.lower() or ";" in lean:
            continue
        token = lean.strip().split()[-1]
        if token not in compared_short:
            continue
        if token not in challenge_text:
            errors.append(
                f"alignment statement lean name {lean!r} (token {token!r}) not found in Challenge.lean"
            )
    return errors


def challenge_declarations(challenge_text: str) -> dict[str, tuple[str, str]]:
    """Return qualified Challenge declarations as name -> (kind, source block)."""
    lines = challenge_text.splitlines(keepends=True)
    scopes: list[tuple[str, str | None]] = []
    found: list[tuple[str, str, int]] = []
    offset = 0
    decl_re = re.compile(
        r"^\s*(?:@\[[^\]]+\]\s*)?(?:noncomputable\s+)?"
        r"(theorem|def|instance)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
    )
    for line in lines:
        stripped = line.strip()
        namespace = re.fullmatch(r"namespace\s+(\S+)", stripped)
        section = re.fullmatch(r"section(?:\s+\S+)?", stripped)
        end = re.fullmatch(r"end(?:\s+\S+)?", stripped)
        if namespace:
            scopes.append(("namespace", namespace.group(1)))
        elif section:
            scopes.append(("section", None))
        elif end and scopes:
            scopes.pop()
        else:
            decl = decl_re.match(line)
            if decl:
                prefix = ".".join(
                    name for kind, name in scopes if kind == "namespace" and name
                )
                full = f"{prefix}.{decl.group(2)}" if prefix else decl.group(2)
                found.append((full, decl.group(1), offset))
        offset += len(line)

    declarations: dict[str, tuple[str, str]] = {}
    for idx, (name, kind, start) in enumerate(found):
        end = found[idx + 1][2] if idx + 1 < len(found) else len(challenge_text)
        declarations[name] = (kind, challenge_text[start:end])
    return declarations


def theorem_statement(challenge_text: str, name: str) -> str | None:
    pattern = THEOREM_BODY.pattern.format(name=re.escape(name))
    match = re.search(pattern, challenge_text, re.MULTILINE)
    return match.group(0) if match else None


def compared_definition_names(cfg: dict) -> set[str]:
    return set(cfg.get("definition_names", []))


def check_sorry_definition_pinning(cfg: dict, challenge_text: str) -> list[str]:
    """Comparator definition holes must be real, explicit Challenge holes."""
    errors: list[str] = []
    declarations = challenge_declarations(challenge_text)
    pinned = compared_definition_names(cfg)
    missing_required = sorted(REQUIRED_DEFINITION_HOLES - pinned)
    extra_required = sorted(pinned - REQUIRED_DEFINITION_HOLES)
    if missing_required:
        errors.append("missing material definition holes: " + ", ".join(missing_required))
    if extra_required:
        errors.append(
            "unexpected definition holes; audit and update REQUIRED_DEFINITION_HOLES: "
            + ", ".join(extra_required)
        )
    for name in sorted(pinned):
        declaration = declarations.get(name)
        if declaration is None:
            errors.append(f"definition hole {name!r} not found in Challenge.lean")
            continue
        kind, block = declaration
        if kind not in {"def", "instance"}:
            errors.append(f"definition_names entry {name!r} has Challenge kind {kind!r}")
        if not re.search(r"\b(?:sorry|admit)\b", block):
            errors.append(f"definition_names entry {name!r} is not a Challenge proof hole")
    for name in cfg.get("theorem_names", []):
        declaration = declarations.get(name)
        if declaration is None:
            errors.append(f"compared theorem {name!r} not found in Challenge.lean")
            continue
        kind, block = declaration
        if kind != "theorem":
            errors.append(f"theorem_names entry {name!r} has Challenge kind {kind!r}")
        if not re.search(r"\b(?:sorry|admit)\b", block):
            errors.append(f"compared theorem {name!r} is not a Challenge proof hole")
    return errors


def check_scope_comparator_sync(formalization: dict, cfg: dict) -> list[str]:
    """formalization.yaml must not contradict comparator.json."""
    errors: list[str] = []
    scope = str(formalization.get("status", {}).get("scope", ""))
    theorems = cfg.get("theorem_names", [])
    main_results = [
        main_result_declaration(entry)
        for entry in formalization.get("status", {}).get("main_results", []) or []
        if isinstance(entry, dict) and entry.get("comparator_config")
    ]
    main_results = [name for name in main_results if name]
    missing_from_main = sorted(set(theorems) - set(main_results))
    if missing_from_main:
        errors.append(
            "comparator theorem_names not listed in status.main_results: "
            + ", ".join(missing_from_main)
        )

    count_match = re.search(r"(\d+)\s+compared (?:theorem|result)", scope.lower())
    if count_match:
        claimed = int(count_match.group(1))
        actual = len(theorems)
        if claimed != actual:
            errors.append(
                f"status.scope claims {claimed} compared results but comparator.json lists {actual}"
            )

    limitations = " ".join(str(x) for x in formalization.get("limitations", []) or [])
    if "Solution.lean imports" in limitations and "QLambda" not in limitations:
        errors.append("limitations should mention Solution.lean imports QLambda proofs")
    return errors


def check_canonical_capstone(formalization: dict, cfg: dict, challenge_text: str) -> list[str]:
    errors: list[str] = []
    if cfg.get("theorem_names") != [EXPECTED_CAPSTONE]:
        errors.append(
            "Palomar headline must be the sole canonical-base theorem "
            f"{EXPECTED_CAPSTONE!r}"
        )
    declaration = challenge_declarations(challenge_text).get(EXPECTED_CAPSTONE)
    if declaration is not None:
        _, block = declaration
        header = block.split(":=", 1)[0]
        if "(M : QuantumPowerModel)" not in header:
            errors.append("canonical capstone must quantify over M : QuantumPowerModel")
        if "(D₀ :" in header or "(j₀ :" in header:
            errors.append("canonical capstone must not require supplied D₀ or j₀ parameters")
    metadata = json.dumps(formalization, ensure_ascii=False)
    for token in (
        "canonical_omegaQVA_quantum_domain_equation_solved",
        "canonical one-point",
        "qEmbInfInf",
        "qProjInfInf",
    ):
        if token not in metadata:
            errors.append(f"formalization.yaml canonical metadata is missing {token!r}")
    return errors


def check_projection_direction() -> list[str]:
    errors: list[str] = []
    reversed_patterns = (
        re.compile(r"j[₀0]\s*:\s*D[₀0]\s*(?:↠|\\twoheadrightarrow)"),
        re.compile(r"projection\s+j[₀0]\s*:\s*D[₀0]\s*(?:↠|\\twoheadrightarrow)", re.I),
    )
    for relative in PROJECTION_DOCS:
        text = (ROOT / relative).read_text(encoding="utf-8")
        for pattern in reversed_patterns:
            if pattern.search(text):
                errors.append(
                    f"{relative} reverses j₀: bonding retr must map "
                    "[D₀ → Q(D₀)] to D₀"
                )
                break
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    if "retr : [D₀ → Q(D₀)] ↠ D₀" not in readme:
        errors.append("README.md must state the general bonding retraction direction")
    return errors


def check_compared_sources(formalization: dict, cfg: dict) -> list[str]:
    """Each hinted compared theorem needs a matching formalization.yaml source."""
    errors: list[str] = []
    sources_blob = json.dumps(formalization.get("sources", []), ensure_ascii=False).lower()
    for full_name in cfg.get("theorem_names", []):
        hints = THEOREM_SOURCE_HINTS.get(full_name)
        if not hints:
            continue
        if not any(h.lower() in sources_blob for h in hints):
            errors.append(
                f"compared theorem {full_name!r} requires a formalization.yaml sources entry "
                f"mentioning one of: {', '.join(hints)}"
            )
    return errors


def main() -> int:
    formalization_path = ROOT / "formalization.yaml"
    comparator_path = ROOT / "comparator.json"
    challenge_path = ROOT / "Challenge.lean"

    formalization = load_formalization(formalization_path)
    cfg = load_comparator(comparator_path)
    challenge_text = challenge_path.read_text(encoding="utf-8")

    errors: list[str] = []
    errors.extend(check_required_fields(formalization))
    errors.extend(
        check_human_only(formalization.get("project", {}).get("authors", []), "project.authors")
    )
    errors.extend(
        check_human_only(
            formalization.get("project", {}).get("responsible_maintainers", []),
            "project.responsible_maintainers",
        )
    )
    errors.extend(check_license(formalization))
    errors.extend(check_sources(formalization))
    errors.extend(check_frozen_revision(formalization))
    errors.extend(check_main_results(formalization, cfg))
    errors.extend(check_alignment(formalization, challenge_text, cfg))
    errors.extend(check_sorry_definition_pinning(cfg, challenge_text))
    errors.extend(check_scope_comparator_sync(formalization, cfg))
    errors.extend(check_canonical_capstone(formalization, cfg, challenge_text))
    errors.extend(check_projection_direction())
    errors.extend(check_compared_sources(formalization, cfg))

    if errors:
        print("FAIL: editorial pre-checks:")
        for err in errors:
            print(f"  {err}")
        return 1

    print(
        f"OK: editorial pre-checks passed "
        f"({len(comparator_declarations(cfg))} compared declarations)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
