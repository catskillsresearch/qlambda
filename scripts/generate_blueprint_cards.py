#!/usr/bin/env python3
"""Generate mathematical English + Lean cards for every extracted declaration.

Reads build/declarations.jsonl and writes build/blueprint_cards/{section}.md
plus build/blueprint_thin.jsonl for cards lacking a real docstring.

Headings are English titles (not Lean FQNs). Statement / Proof prose is
mathematical, derived from docstrings, signatures, and Lean bodies—not
boilerplate about the kernel or “unfolding the excerpt.”
"""

from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DECLS = ROOT / "build" / "declarations.jsonl"
OUT_DIR = ROOT / "build" / "blueprint_cards"
THIN = ROOT / "build" / "blueprint_thin.jsonl"

SECTION_TITLES = {
    "intro": "Library root",
    "sec2": "Typed linear language",
    "sec3": "Finite quantum runtime",
    "sec4": "Quantum sets, relations, and qCPOs",
    "sec5": "Type-indexed denotation and the $N$-qubit fragment",
    "sec6": "Deterministic staging to circuits",
    "sec7": "Circuit reflection, quotation, and completeness",
    "sec8": "Composer and OpenQASM interchange",
    "sec9": "Supporting quantum primitives",
    "palomar": "Palomar challenge and solution",
}

# Domain-specific token rewrites for readable English titles.
TOKEN_MAP = {
    "new0": "fresh zero qubit",
    "new1": "fresh one qubit",
    "cx": "controlled-NOT",
    "cnot": "controlled-NOT",
    "ry": "Y-rotation",
    "rz": "Z-rotation",
    "rx": "X-rotation",
    "cp": "completely positive map",
    "cpo": "CPO",
    "qcpo": "quantum CPO",
    "qrel": "quantum relation",
    "lnl": "linear/nonlinear",
    "wf": "well-formedness",
    "eq": "equality",
    "iff": "equivalence",
    "le": "order",
    "lt": "strict order",
    "ge": "reverse order",
    "gt": "strict reverse order",
    "symm": "symmetry",
    "refl": "reflexivity",
    "trans": "transitivity",
    "assoc": "associativity",
    "comm": "commutativity",
    "id": "identity",
    "inv": "inverse",
    "inj": "injectivity",
    "surj": "surjectivity",
    "bij": "bijectivity",
    "mono": "monotonicity",
    "cont": "continuity",
    "scott": "Scott continuity",
    "denote": "denotation",
    "denotation": "denotation",
    "subst": "substitution",
    "preserves": "preservation",
    "preservation": "preservation",
    "progress": "progress",
    "sound": "soundness",
    "complete": "completeness",
    "adequacy": "adequacy",
    "quotation": "quotation",
    "quotable": "quotable commands",
    "elab": "elaboration",
    "elaborates": "successful elaboration",
    "openqasm": "OpenQASM",
    "composer": "Composer",
    "superoperator": "superoperator",
    "kraus": "Kraus operators",
    "choi": "Choi matrix",
    "born": "Born rule",
    "meas": "measurement",
    "measure": "measurement",
    "bitlit": "Boolean literal",
    "lam": "lambda",
    "app": "application",
    "ite": "conditional",
    "unpair": "pair elimination",
    "unres": "unrestricted",
    "lin": "linear",
    "frag": "fragment",
    "fragcert": "fragment certificate",
    "atmost": "at most",
    "qubits": "qubits",
    "inst": "instance",
    "anon": "anonymous",
}


def load_excerpt(d: dict) -> str:
    path = ROOT / d["file"]
    if not path.is_file():
        return d.get("signature") or ""
    lines = path.read_text(encoding="utf-8").splitlines()
    a, b = d["start_line"], d["end_line"]
    if a < 1 or b < a or b > len(lines):
        return d.get("signature") or ""
    return "\n".join(lines[a - 1 : b])


def base_name(d: dict) -> str:
    name = d.get("name") or ""
    # Drop namespace junk; prefer last dotted segment of fqn if name is anon.
    if name.startswith("anon_") or name.startswith("example_"):
        fqn = d.get("fqn") or name
        name = fqn.split(".")[-1]
    return name


def tokenize_name(name: str) -> list[str]:
    name = re.sub(r"^(inst|has|is|to|of|mk|get|set)+(?=[A-Z_])", "", name)
    name = re.sub(r"_+", " ", name)
    name = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", name)
    name = re.sub(r"(?<=[A-Z])(?=[A-Z][a-z])", " ", name)
    toks = [t for t in name.strip().split() if t]
    return toks


def gloss_token(tok: str) -> str:
    low = tok.lower()
    if low in TOKEN_MAP:
        return TOKEN_MAP[low]
    # Keep short technical tokens (x, h, t, …) as gate names when alphabetic.
    if len(tok) <= 2 and tok.isalpha():
        return tok.lower()
    return re.sub(r"(?<=[a-z])(?=[A-Z])", " ", tok).lower()


def phrase_from_name(name: str) -> str:
    toks = tokenize_name(name)
    if not toks:
        return "the declaration"
    glossed = [gloss_token(t) for t in toks]
    # Deduplicate adjacent repeats after glossing.
    out: list[str] = []
    for g in glossed:
        if not out or out[-1] != g:
            out.append(g)
    return " ".join(out)


def title_case_phrase(phrase: str) -> str:
    """Title-case for headings, keeping short particles lowercase mid-phrase."""
    small = {"of", "the", "a", "an", "and", "or", "for", "to", "in", "on", "via", "by", "with", "as"}
    words = phrase.split()
    if not words:
        return phrase
    result = [words[0][:1].upper() + words[0][1:]]
    for w in words[1:]:
        if w.lower() in small:
            result.append(w.lower())
        else:
            result.append(w[:1].upper() + w[1:] if w else w)
    return " ".join(result)


def english_title(d: dict) -> str:
    """Subsection heading: English, no Lean FQN."""
    kind = d["kind"]
    name = base_name(d)
    phrase = phrase_from_name(name)
    doc = (d.get("docstring") or "").strip()

    # Prefer a short docstring headline when it is already English prose.
    if doc:
        first = re.sub(r"\s+", " ", doc.split("\n\n", 1)[0]).strip()
        # Docstring that already looks like a sentence / definition.
        if (
            len(first) <= 110
            and not first.startswith("`")
            and ":" not in first[:20]
            and not first.startswith("theorem ")
            and not first.startswith("def ")
        ):
            # Strip trailing period for heading use.
            return first.rstrip(".")

    # Pattern-specialized titles.
    low = name.lower()
    if kind in ("def", "abbrev"):
        if low.startswith("superoperator") and "_" in low:
            # superoperator_new0 is a theorem usually; handle anyway
            pass
        if low == "superoperator":
            return "Definition of the primitive superoperator"
        return f"Definition of {phrase}"
    if kind == "structure":
        return f"Structure: {phrase}"
    if kind == "class":
        return f"Type class: {phrase}"
    if kind == "inductive":
        return f"Inductive type: {phrase}"
    if kind == "instance":
        return f"Instance for {phrase}"
    if kind == "example":
        return f"Example: {phrase}"
    if kind in ("theorem", "lemma"):
        # Equality / characterization names
        if low.endswith("_new0") or "new0" in low:
            if "superoperator" in low:
                return "Allocation of a fresh zero qubit"
            return title_case_phrase(phrase)
        if low.endswith("_refl") or low.startswith("refl"):
            return f"Reflexivity of {phrase_from_name(re.sub(r'_?refl$', '', name, flags=re.I))}"
        if low.endswith("_symm") or "symm" in low:
            return f"Symmetry of {phrase_from_name(re.sub(r'_?symm$', '', name, flags=re.I))}"
        if low.endswith("_trans") or "trans" in low:
            return f"Transitivity of {phrase_from_name(re.sub(r'_?trans$', '', name, flags=re.I))}"
        if "preserv" in low:
            return title_case_phrase(phrase)
        if "progress" in low:
            return title_case_phrase(phrase)
        if "sound" in low:
            return title_case_phrase(phrase)
        if "adequat" in low:
            return title_case_phrase(phrase)
        if kind == "lemma":
            return f"Lemma: {title_case_phrase(phrase)}"
        return title_case_phrase(phrase)
    return title_case_phrase(phrase)


def clean_math_expr(expr: str) -> str:
    expr = " ".join(expr.split())
    expr = re.sub(r"@\[[^\]]*\]\s*", "", expr)
    # Soften Lean projection noise for prose.
    expr = expr.replace(" .", " ")
    if len(expr) > 120:
        expr = expr[:117] + "…"
    return expr.strip()


def extract_claim(signature: str, excerpt: str) -> str | None:
    """Try to recover the mathematical claim (often an equality) from the type."""
    text = signature or excerpt
    one = " ".join(text.split())
    one = re.sub(r"@\[[^\]]*\]\s*", "", one)
    # Cut proof/body
    for sep in (" :=", " where"):
        if sep in one:
            one = one.split(sep, 1)[0]
    # theorem Name ... : CLAIM
    m = re.search(
        r"(?:theorem|lemma|example)\s+\S+\s*(.*?)\s*:\s*(.+)$",
        one,
    )
    if m:
        claim = m.group(2).strip().rstrip(":")
        # Drop trailing binder-only noise
        if claim and claim not in ("Prop", "Type", "Sort"):
            return clean_math_expr(claim)
    # def Name ... : TYPE
    m = re.search(r"(?:noncomputable\s+)?(?:def|abbrev)\s+\S+\s*(.*?)\s*:\s*(.+)$", one)
    if m:
        typ = m.group(2).strip().rstrip(":")
        if typ:
            return clean_math_expr(typ)
    return None


def extract_rhs(excerpt: str) -> str | None:
    """Right-hand side of a definition (match / fun / term)."""
    m = re.search(r":=\s*(.*)", excerpt, re.DOTALL)
    if not m:
        return None
    body = m.group(1).strip()
    # Drop trailing `by ...` proofs attached to theorems (handled elsewhere).
    if body.startswith("by"):
        return None
    body = " ".join(body.split())
    if len(body) > 160:
        body = body[:157] + "…"
    return body


def statement_english(d: dict, excerpt: str) -> str:
    doc = (d.get("docstring") or "").strip()
    if doc:
        para = re.sub(r"\s+", " ", doc.split("\n\n", 1)[0]).strip()
        if para:
            if not para.endswith("."):
                para += "."
            return para

    kind = d["kind"]
    name = base_name(d)
    phrase = phrase_from_name(name)
    claim = extract_claim(d.get("signature") or "", excerpt)
    rhs = extract_rhs(excerpt)

    if kind in ("theorem", "lemma"):
        if claim and "=" in claim:
            left, right = [s.strip() for s in claim.split("=", 1)]
            return (
                f"The identity `{left} = {right}` holds: both sides denote the "
                f"same mathematical object."
            )
        if claim and ("↔" in claim or " iff " in claim.lower()):
            return f"The following logical equivalence holds: `{claim}`."
        if claim and ("≤" in claim or "⊑" in claim or "≼" in claim):
            return f"The following inequality / order fact holds: `{claim}`."
        if claim:
            return f"We establish: `{claim}`."
        return f"We establish the stated property of {phrase}."

    if kind in ("def", "abbrev"):
        if "match " in (excerpt or "") or (rhs and rhs.startswith("match")):
            return (
                f"Assign to each case of {phrase} its intrinsic mathematical meaning "
                f"(by cases on the source constructors)."
            )
        if claim and rhs and not rhs.startswith("{"):
            return (
                f"Define {phrase} as an object of type `{claim}`, given explicitly by "
                f"`{clean_math_expr(rhs)}`."
            )
        if claim:
            return f"Define {phrase} as an object of type `{claim}`."
        if rhs:
            return f"Define {phrase} by `{clean_math_expr(rhs)}`."
        return f"Define {phrase}."

    if kind == "structure":
        fields = re.findall(r"^\s+(\w+)\s*:", excerpt, re.MULTILINE)
        if fields:
            shown = ", ".join(f"`{f}`" for f in fields[:8])
            more = " …" if len(fields) > 8 else ""
            return f"A record packaging {phrase}, with fields {shown}{more}."
        return f"A record packaging the data of {phrase}."

    if kind == "class":
        return (
            f"A type-class interface for {phrase}: structures that implement it "
            f"must supply the listed operations and laws."
        )

    if kind == "inductive":
        ctors = re.findall(r"^\s+\|\s+(\w+)", excerpt, re.MULTILINE)
        if ctors:
            return (
                f"An inductive type for {phrase}, generated by the constructors "
                + ", ".join(f"`{c}`" for c in ctors[:12])
                + ("…" if len(ctors) > 12 else "")
                + "."
            )
        return f"An inductive type generating the constructors of {phrase}."

    if kind == "instance":
        return f"Supply a canonical instance establishing {phrase}."

    if kind == "example":
        if claim:
            return f"A concrete check of `{claim}`."
        return f"A concrete check illustrating {phrase}."

    return f"Declare {phrase}."


def tactic_sketch(excerpt: str) -> str | None:
    """Translate the Lean proof script into a short mathematical proof sketch."""
    # Normalize
    body = excerpt
    m = re.search(r":=\s*by\b(.*)$", body, re.DOTALL)
    if m:
        script = m.group(1).strip()
    elif re.search(r"\bby\b", body):
        script = body.split("by", 1)[1].strip()
    else:
        # Pure term proof: `:= rfl` or `:= h` (possibly on the next line).
        m2 = re.search(r":=\s*(.+)\s*$", body, re.DOTALL)
        if not m2:
            return None
        term = " ".join(m2.group(1).split())
        # Decl end ranges can bleed into the next attribute / declaration.
        term = re.split(
            r"\s+(?:@\[|(?:noncomputable\s+)?(?:protected\s+)?(?:private\s+)?"
            r"(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|example)\b)",
            term,
            maxsplit=1,
        )[0].strip()
        if term == "rfl" or term.endswith(" rfl"):
            return (
                "By definitional equality: both sides reduce to the same term, "
                "so the identity is immediate."
            )
        if term in ("True.intro", "trivial", "⟨⟩"):
            return "Immediate from the definitions."
        if re.match(r"^[\w'.]+$", term):
            return f"By direct appeal to `{term}`."
        return None

    script_one = " ".join(script.split())
    low = script_one.lower()

    if script_one.strip() in ("rfl",) or low.startswith("rfl"):
        return (
            "By definitional equality: unfolding the definitions makes both sides "
            "identical."
        )

    bits: list[str] = []

    if re.search(r"\bcases\b|\binduction\b|\bmatch\b", script):
        bits.append("by case analysis (or induction) on the relevant constructors")
    if re.search(r"\brw\b|\brewrite\b|\bsimp_rw\b", script):
        # Collect a few lemma names after rw [
        lemmas = re.findall(r"rw\s*\[([^\]]+)\]", script)
        names: list[str] = []
        for block in lemmas[:2]:
            for part in block.split(","):
                part = part.strip().lstrip("←↑").strip()
                part = part.split()[0] if part else ""
                if part and part not in names:
                    names.append(part)
                if len(names) >= 4:
                    break
        if names:
            bits.append(
                "by rewriting along "
                + ", ".join(f"`{n}`" for n in names[:4])
            )
        else:
            bits.append("by rewriting with the governing equalities")
    if re.search(r"\bsimp\b", script):
        bits.append("by simplifying with the simp-set for the definitions involved")
    if re.search(r"\bext\b", script):
        bits.append("by extensionality (pointwise on the underlying data)")
    if re.search(r"\bconstructor\b|\brefine\b\s*⟨", script):
        bits.append("by assembling the required conjuncts / structure fields")
    if re.search(r"\bexact\b|\bapply\b|\brefine\b", script):
        bits.append("by applying the previously established lemmas")
    if re.search(r"\bintro\b|\brintro\b", script):
        bits.append("after introducing the ambient hypotheses")
    if re.search(r"\blinarith\b|\bnlinarith\b|\bring\b|\babel\b|\bomega\b|\bnorm_num\b", script):
        bits.append("using arithmetic / algebraic automation on the remaining numeric goals")
    if re.search(r"\bcongr\b|\bcongrm\b", script):
        bits.append("by congruence of the surrounding constructors")
    if re.search(r"\bcalc\b", script):
        bits.append("by a calculational chain of equalities")
    if re.search(r"\bfunext\b", script):
        bits.append("by function extensionality")

    if not bits:
        # Fallback: still mathematical, not kernel-speak.
        if len(script_one) < 80:
            return f"By a direct proof: `{script_one}`."
        return (
            "By a direct argument combining the definitions and lemmas appearing "
            "in the formal proof."
        )

    # De-duplicate while preserving order
    seen: set[str] = set()
    uniq: list[str] = []
    for b in bits:
        if b not in seen:
            seen.add(b)
            uniq.append(b)
    if len(uniq) == 1:
        return uniq[0][0].upper() + uniq[0][1:] + "."
    return "; ".join(uniq[:-1]).capitalize() + "; and " + uniq[-1] + "."


def construction_sketch(d: dict, excerpt: str) -> str:
    kind = d["kind"]
    name = base_name(d)
    phrase = phrase_from_name(name)
    rhs = extract_rhs(excerpt)

    if kind in ("def", "abbrev"):
        if "match " in excerpt:
            # Summarize match arms when short.
            arms = re.findall(r"\|\s*(\.[?\w]+|[?\w]+)\s*=>\s*([^\n|]+)", excerpt)
            if arms and len(arms) <= 10:
                parts = []
                for pat, val in arms:
                    parts.append(f"`{pat.strip()}` ↦ `{clean_math_expr(val.strip())}`")
                return (
                    "Defined by cases on the constructors: "
                    + "; ".join(parts)
                    + "."
                )
            return (
                f"Defined by recursion / case analysis on the constructors of the "
                f"source datatype, sending each constructor to the corresponding "
                f"intrinsic map for {phrase}."
            )
        if rhs and rhs.startswith("{"):
            return (
                f"Constructed by filling the record fields of {phrase} with the "
                f"data supplied in the definition."
            )
        if rhs and (rhs.startswith("fun ") or "=>" in rhs or "↦" in rhs):
            return f"Given explicitly as the function `{clean_math_expr(rhs)}`."
        if rhs:
            return f"Defined to be `{clean_math_expr(rhs)}`."
        return f"Introduced as the canonical construction of {phrase}."

    if kind == "structure":
        fields = re.findall(r"^\s+(\w+)\s*:", excerpt, re.MULTILINE)
        if fields:
            return (
                "The carriers and operations are the listed fields "
                + ", ".join(f"`{f}`" for f in fields[:10])
                + ("; …" if len(fields) > 10 else "")
                + "; inhabitants are tuples of such data."
            )
        return "Inhabitants are tuples of the declared fields."

    if kind == "class":
        return (
            "A type is an instance when it provides the operations and satisfies "
            "the laws listed in the class; those are what later lemmas may invoke."
        )

    if kind == "inductive":
        return (
            "Every element is obtained by finitely many applications of the "
            "listed constructors; proofs about the type proceed by induction on "
            "that construction."
        )

    if kind == "instance":
        sk = tactic_sketch(excerpt)
        if sk:
            return sk
        if rhs:
            return f"Witnessed by `{clean_math_expr(rhs)}`."
        return f"The required fields for {phrase} are discharged by the definitions above."

    if kind == "example":
        sk = tactic_sketch(excerpt)
        if sk:
            return sk
        return "Verified by evaluating / reducing the concrete terms in the example."

    return f"Constructed as stated for {phrase}."


def proof_english(d: dict, excerpt: str) -> str:
    doc = (d.get("docstring") or "").strip()
    if doc and "\n\n" in doc:
        rest = re.sub(r"\s+", " ", doc.split("\n\n", 1)[1]).strip()
        if rest:
            if not rest.endswith("."):
                rest += "."
            return rest

    kind = d["kind"]
    if kind in ("theorem", "lemma", "example"):
        sk = tactic_sketch(excerpt)
        if sk:
            return sk
        # Term-style theorem with `:= rfl` already handled inside tactic_sketch.
        return construction_sketch(d, excerpt)

    return construction_sketch(d, excerpt)


def card_markdown(d: dict) -> str:
    excerpt = load_excerpt(d)
    title = english_title(d)
    rel = d["file"]
    a, b = d["start_line"], d["end_line"]
    lines = [
        f"#### {title}",
        "",
        f"**Statement.** {statement_english(d, excerpt)}",
        "",
        f"**Proof / construction.** {proof_english(d, excerpt)}",
        "",
        f"<!-- lean: {rel}#L{a}-L{b} -->",
        "",
    ]
    return "\n".join(lines)


def main() -> None:
    if not DECLS.is_file():
        raise SystemExit(f"missing {DECLS}; run scripts/extract_declarations.py first")
    decls = [
        json.loads(line)
        for line in DECLS.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    by_sec: dict[str, list[dict]] = {}
    thin: list[dict] = []
    for d in decls:
        by_sec.setdefault(d["section"], []).append(d)
        if not (d.get("docstring") or "").strip():
            thin.append({"fqn": d["fqn"], "file": d["file"], "kind": d["kind"]})

    for sec, items in by_sec.items():
        items.sort(key=lambda x: (x["file"], x["start_line"], x["fqn"]))
        parts: list[str] = []
        title = SECTION_TITLES.get(sec, sec)
        parts.append(f"### Blueprint declarations — {title}\n\n")
        parts.append(
            f"*Auto-generated from the Lean sources ({len(items)} declarations). "
            "Each card states the claim in mathematical English and inlines the Lean gist; "
            "Lean paths appear only in the green source headers.*\n\n"
        )
        for d in items:
            parts.append(card_markdown(d))
        (OUT_DIR / f"{sec}.md").write_text("".join(parts), encoding="utf-8")

    with THIN.open("w", encoding="utf-8") as f:
        for t in thin:
            f.write(json.dumps(t) + "\n")

    # Spot-check the user's examples if present.
    for needle in ("superoperator", "superoperator_new0"):
        hits = [d for d in decls if d["name"] == needle]
        if hits:
            d = hits[0]
            print(f"SPOT {needle}: title={english_title(d)!r}")
            print(f"  stmt={statement_english(d, load_excerpt(d))[:140]!r}")
            print(f"  proof={proof_english(d, load_excerpt(d))[:140]!r}")

    print(
        f"wrote {OUT_DIR} ({len(decls)} cards across {len(by_sec)} sections); "
        f"{len(thin)} thin (no docstring) listed in {THIN}"
    )


if __name__ == "__main__":
    main()
