#!/usr/bin/env python3
"""Build Fabbro-style Mathlib dependency Mermaid figures per paper section.

Amber nodes: Mathlib imports (all, including transitive via local ancestors).
Blue nodes: QLambda / Challenge / Solution modules in that section.
Outputs build/section_dep_figures/{section}.md with lean-dep-figure blocks.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DECLS = ROOT / "build" / "declarations.jsonl"
OUT_DIR = ROOT / "build" / "section_dep_figures"

IMPORT_RE = re.compile(r"^import\s+(\S+)\s*$", re.MULTILINE)

SECTION_LABELS = {
    "intro": "library root",
    "sec2": "§2 (typed linear language)",
    "sec3": "§3 (finite quantum runtime)",
    "sec4": "§4 (quantum relations and qCPOs)",
    "sec5": "§5 (fragment denotation)",
    "sec6": "§6 (staging to circuits)",
    "sec7": "§7 (quotation and completeness)",
    "sec8": "§8 (Composer / OpenQASM)",
    "sec9": "§9 (supporting primitives)",
    "palomar": "Palomar challenge / solution",
}

MATHLIB_HINTS: list[tuple[re.Pattern[str], str]] = [
    (re.compile(r"\bMatrix\b|Matrix\."), "Data.Matrix.Basic"),
    (re.compile(r"\bEuclideanSpace\b|\bInnerProductSpace\b"), "Analysis.InnerProductSpace.Basic"),
    (re.compile(r"\bComplex\b|ℂ"), "Data.Complex.Basic"),
    (re.compile(r"\bReal\b|ℝ"), "Data.Real.Basic"),
    (re.compile(r"\bNNReal\b|ℝ≥0"), "Data.Real.NNReal"),
    (re.compile(r"\bFinset\b|∑ |BigOperators"), "Algebra.BigOperators.Group.Finset.Basic"),
    (re.compile(r"\bFintype\b"), "Data.Fintype.Basic"),
    (re.compile(r"\bFin\b"), "Data.Fin.Basic"),
    (re.compile(r"\bEquiv\b"), "Logic.Equiv.Defs"),
    (re.compile(r"\bCategoryTheory\b|Category\.|MonoidalCategory"), "CategoryTheory.Category.Basic"),
    (re.compile(r"\bCompleteLattice\b|\bLattice\b"), "Order.CompleteLattice"),
    (re.compile(r"\bOrderBot\b|\bBot\b"), "Order.BoundedOrder"),
    (re.compile(r"\bOmegaCompletePartialOrder\b|\bCPO\b|ωCPO"), "Order.OmegaCompletePartialOrder"),
    (re.compile(r"\bTopology\b|\bContinuous\b"), "Topology.Basic"),
    (re.compile(r"\bMeasureTheory\b"), "MeasureTheory.Measure.MeasureSpace"),
    (re.compile(r"\bProbabilityTheory\b"), "Probability.ProbabilityMassFunction.Basic"),
    (re.compile(r"\bModule\b|→ₗ|LinearMap"), "Algebra.Module.LinearMap.Basic"),
    (re.compile(r"\bStar\b|\bStarRing\b"), "Algebra.Star.Basic"),
    (re.compile(r"\bNormedSpace\b|‖"), "Analysis.Normed.Module.Basic"),
    (re.compile(r"linarith|nlinarith"), "Tactic.Linarith"),
    (re.compile(r"\bnorm_num\b"), "Tactic.NormNum"),
    (re.compile(r"\bsimp\b"), "Tactic.Basic"),
]


def is_import_only(code: str) -> bool:
    lines = [
        ln.strip()
        for ln in code.splitlines()
        if ln.strip() and not ln.strip().startswith("--") and not ln.strip().startswith("/-")
    ]
    return bool(lines) and all(ln.startswith("import ") for ln in lines)


def parse_imports(code: str) -> list[str]:
    return IMPORT_RE.findall(code)


def infer_mathlib(code: str) -> list[str]:
    found: list[str] = []
    seen: set[str] = set()
    for pat, mod in MATHLIB_HINTS:
        if pat.search(code) and mod not in seen:
            seen.add(mod)
            found.append(mod)
    return found


def mathlib_names(code: str) -> list[str]:
    imports = [imp for imp in parse_imports(code) if imp.startswith("Mathlib")]
    if imports == ["Mathlib"]:
        return infer_mathlib(code)
    if not imports:
        return [] if is_import_only(code) else infer_mathlib(code)
    return [imp.removeprefix("Mathlib.") for imp in imports]


def lean_path(imp: str) -> str | None:
    if imp in ("QLambda", "Challenge", "Solution"):
        return f"{imp}.lean"
    if imp.startswith("QLambda.") or imp.startswith("Challenge.") or imp.startswith("Solution."):
        return imp.replace(".", "/") + ".lean"
    return None


def sid(prefix: str, name: str) -> str:
    return prefix + re.sub(r"[^A-Za-z0-9]", "", name)[:48]


def ancestors(node: str, preds: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    stack = list(preds.get(node, ()))
    while stack:
        parent = stack.pop()
        if parent in seen:
            continue
        seen.add(parent)
        stack.extend(preds.get(parent, ()))
    return seen


def module_label(rel: str) -> str:
    return Path(rel).stem


def mermaid_for(rels: list[str]) -> str:
    files = {rel: (ROOT / rel).read_text(encoding="utf-8") for rel in rels if (ROOT / rel).is_file()}
    if not files:
        return "flowchart LR\n  empty[\"(no modules)\"]\n"

    displayed = [rel for rel, code in files.items() if not is_import_only(code)]
    if not displayed:
        displayed = list(files)

    # Cap blue nodes for very large sections (Domain) to keep Mermaid/PNG readable;
    # Mathlib list still includes ALL imports from every module in the section.
    display_cap = 40
    display_set = set(displayed[:display_cap])

    preds: dict[str, set[str]] = {rel: set() for rel in files}
    mathlib_of: dict[str, set[str]] = {}
    for rel, code in files.items():
        mathlib_of[rel] = set(mathlib_names(code))
        for imp in parse_imports(code):
            dest = lean_path(imp)
            if dest in files:
                preds[rel].add(dest)

    # Union of all Mathlib names from every file in the section (required).
    all_mathlib: set[str] = set()
    for rel in files:
        all_mathlib |= mathlib_of[rel]
        for anc in ancestors(rel, preds):
            all_mathlib |= mathlib_of.get(anc, set())

    mathlib_ids = {ml: sid("L", ml) for ml in all_mathlib}
    module_ids = {rel: sid("M", Path(rel).stem) for rel in display_set}

    edges: list[tuple[str, str]] = []
    for rel in display_set:
        mid = module_ids[rel]
        inherited: set[str] = set()
        for anc in ancestors(rel, preds):
            inherited |= mathlib_of.get(anc, set())
        for ml in mathlib_of[rel]:
            if ml not in inherited and ml in mathlib_ids:
                edges.append((mathlib_ids[ml], mid))
        for dest in preds[rel]:
            if dest in module_ids:
                edges.append((module_ids[dest], mid))

    lines = [
        '%%{init: {"flowchart": {"htmlLabels": false, "nodeSpacing": 16, "rankSpacing": 36}}}%%',
        "flowchart LR",
        "  classDef project fill:#dbeafe,stroke:#1d4ed8,color:#1e3a8a,stroke-width:1.2px",
        "  classDef mathlib fill:#ffedd5,stroke:#c2410c,color:#7c2d12,stroke-width:1.2px",
        "",
        '  subgraph ML["Mathlib"]',
        "    direction TB",
        "    style ML fill:#fff7ed,stroke:#c2410c,stroke-width:2px",
    ]
    for ml, lid in sorted(mathlib_ids.items(), key=lambda kv: kv[0].lower()):
        lines.append(f'    {lid}["{ml}"]:::mathlib')
    lines += [
        "  end",
        "",
        '  subgraph SOL["Project modules"]',
        "    direction TB",
        "    style SOL fill:#eff6ff,stroke:#1d4ed8,stroke-width:2px",
    ]
    for rel in sorted(display_set):
        lines.append(f'    {module_ids[rel]}["{module_label(rel)}"]:::project')
    if len(displayed) > display_cap:
        extra = sid("M", "MoreModules")
        lines.append(
            f'    {extra}["+{len(displayed) - display_cap} more modules"]:::project'
        )
    lines.append("  end")
    lines.append("")
    seen_e: set[tuple[str, str]] = set()
    known = set(mathlib_ids.values()) | set(module_ids.values())
    for src, dst in edges:
        if src == dst or (src, dst) in seen_e or src not in known or dst not in known:
            continue
        seen_e.add((src, dst))
        lines.append(f"  {src} --> {dst}")
    return "\n".join(lines) + "\n"


def figure_block(section: str, mermaid: str, n_mathlib: int, n_mods: int) -> str:
    label = SECTION_LABELS.get(section, section)
    caption = (
        f"Lean module dependencies for {label}. "
        f"Amber box: Mathlib imports ({n_mathlib} listed). "
        f"Blue box: project modules ({n_mods})."
    )
    return (
        "<!-- lean-dep-figure -->\n"
        f"<!-- figure-caption: {caption} -->\n"
        "```mermaid\n"
        f"{mermaid}"
        "```\n"
        f"**Figure.** {caption}\n"
        "<!-- /lean-dep-figure -->\n"
    )


def modules_by_section() -> dict[str, list[str]]:
    if not DECLS.is_file():
        raise SystemExit(f"missing {DECLS}")
    by: dict[str, set[str]] = {}
    for line in DECLS.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        d = json.loads(line)
        by.setdefault(d["section"], set()).add(d["file"])
    return {k: sorted(v) for k, v in by.items()}


def count_mathlib(rels: list[str]) -> int:
    names: set[str] = set()
    for rel in rels:
        path = ROOT / rel
        if path.is_file():
            names |= set(mathlib_names(path.read_text(encoding="utf-8")))
    return len(names)


def main() -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    by_sec = modules_by_section()
    for sec, rels in sorted(by_sec.items()):
        mermaid = mermaid_for(rels)
        # Count unique Mathlib names from mermaid (all amber nodes) via re-parse
        n_ml = count_mathlib(rels)
        block = figure_block(sec, mermaid, n_ml, len(rels))
        (OUT_DIR / f"{sec}.md").write_text(block, encoding="utf-8")
        print(f"{sec}: {len(rels)} modules, ~{n_ml} Mathlib imports")
    print(f"wrote {OUT_DIR}")


if __name__ == "__main__":
    main()
