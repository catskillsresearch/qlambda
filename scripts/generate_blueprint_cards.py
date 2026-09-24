#!/usr/bin/env python3
"""Generate mathematical-English blueprint cards for every extracted declaration.

Reads build/declarations.jsonl and writes build/blueprint_cards/{section}.md
plus build/blueprint_thin.jsonl (declarations without a `/--` docstring).

Each card has
  * an English heading (never a Lean name),
  * a statement: the docstring when present, otherwise an English rendering of
    the hypotheses and conclusion read off the Lean signature, followed by the
    formal claim in notation,
  * a proof / construction paragraph explaining the mathematical idea of the
    Lean body (definitional unfolding, induction on a derivation, case
    analysis, rewriting with named facts, …).

The Lean excerpt itself is spliced in later from the `<!-- lean: … -->` marker.
"""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from blueprint_lexicon import (  # noqa: E402
    ARG_FORM,
    CLASS_NOUN,
    IDENT,
    MODULE_NS,
    PROPERTY_SUFFIX,
    TYPE_NS,
    WORD,
)

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

DECL_KW = (
    "theorem", "lemma", "def", "abbrev", "instance", "structure", "class",
    "inductive", "example",
)
MODIFIERS = ("noncomputable", "protected", "private", "partial", "unsafe", "scoped", "local")

# --------------------------------------------------------------------------
# Hand-written titles for declarations whose names are too terse for the
# generic grammar (keyed by "Namespace.lemma" or the bare lemma name).
# --------------------------------------------------------------------------

TITLE_OVERRIDE: dict[str, str] = {
    "OSplit.eq_right_of_allNone_left":
        "Empty left mask determines an ordered context split from the right",
    "OSplit.eq_left_of_allNone_right":
        "Empty right mask determines an ordered context split from the left",
    "OSplit.lengths":
        "Both parts of an ordered context split have the length of the whole context",
    "OSplit.symm": "Ordered context splits are symmetric in their two parts",
    "OSplit.withNoneRight":
        "Every linear context splits as itself together with an empty right mask",
    "OSplit.mem_left":
        "Every type used in the left part of a split occurs in the whole context",
    "OSplit.mem_right":
        "Every type used in the right part of a split occurs in the whole context",
    "OSplit.self_of_allNone": "An empty mask splits as itself on both sides",
    "allNone_eq_replicate": "An empty usage mask is a constant list of absent cells",
    "allNone_unique": "Empty usage masks of equal length coincide",
    "allNone_replicate_none": "A constant list of absent cells is an empty usage mask",
    "Lookup.mem": "A looked-up entry is a member of the list",
    "Lookup.lt_length": "A successful lookup position lies below the length of the list",
    "Prim.superoperator": "Definition of the primitive superoperator",
    "Prim.superoperator_new0": "Allocation of a fresh zero qubit as a primitive superoperator",
    "Prim.cp_superoperator":
        "The primitive superoperator has the Kraus presentation of its primitive",
    "step_deterministic": "One-step reduction is deterministic",
    "CompEq.refl": "Observational equality is reflexive",
    "CompEq.symm": "Observational equality is symmetric",
    "CompEq.trans": "Observational equality is transitive",
}

CTOR_GLOSS: dict[str, dict[str, str]] = {
    "OSplit": {
        "nil": "the empty split",
        "none": "an absent cell shared by both parts",
        "left": "an occupied cell sent to the left part",
        "right": "an occupied cell sent to the right part",
    },
    "List": {"nil": "the empty context", "cons": "a context extended by one cell"},
    "Option": {"none": "an absent cell", "some": "an occupied cell"},
    "Nat": {"zero": "zero", "succ": "a successor"},
    "Bool": {"true": "true", "false": "false"},
    "Lookup": {"zero": "a lookup at the head", "succ": "a lookup in the tail"},
    "Mem": {"head": "membership at the head", "tail": "membership in the tail"},
    "Prim": {
        "new0": "fresh-qubit allocation", "x": "the Pauli-X gate", "h": "the Hadamard gate",
        "t": "the T gate", "ry": "a Y-rotation", "cx": "the controlled-NOT gate",
        "reset": "reset",
    },
}

# Namespace-sensitive identifier glosses.
IDENT_NS: dict[tuple[str, str], str] = {
    ("Prim", "superoperator"): "primitive superoperator",
    ("CQ", "Eq"): "semantic equality of circuits",
    ("Prim", "kraus"): "Kraus operators",
    ("Prim", "completedCP"): "completed CP class",
    ("OSplit", "left"): "left part",
    ("OSplit", "right"): "right part",
    ("Term", "cond"): "condition",
    ("Term", "fn"): "function part",
    ("Term", "arg"): "argument",
    ("Term", "left"): "left component",
    ("Term", "right"): "right component",
    ("Term", "body"): "body",
}

# Applied heads: head identifier → English template over explicit arguments.
IDENT_APP: dict[str, str] = {
    "ofKraus": "the CP map with Kraus family {0}",
    "ofUnitary": "the map induced by the unitary {0}",
    "ofIsometry": "the map induced by the isometry {0}",
    "allocateZero": "the allocation of a fresh zero qubit beside {0} existing qubits",
    "x": "the Pauli-X gate on wire {0}",
    "h": "the Hadamard gate on wire {0}",
    "t": "the T gate on wire {0}",
    "reset": "the reset of wire {0}",
    "measure": "the measurement of wire {0}",
    "ry": "the Y-rotation by angle {0} on wire {1}",
    "cx": "the controlled-NOT gate with control {0} and target {1}",
    "identity": "the identity on dimension {0}",
    "trace": "the trace of {0}",
    "comp": "the composite of {0} after {1}",
    "tensor": "the tensor product of {0} and {1}",
    "choi": "the Choi matrix of {0}",
    "effect": "the effect of {0}",
    "applyMat": "the action of {0} on {1}",
    "linearOSplit": "the Day split selected by {0}",
    "denote": "the denotation of {0}",
    "length": "the length of {0}",
    "some": "the present value {0}",
}

# Predicates: head identifier → English template over its explicit arguments.
PRED: dict[str, str] = {
    "OSplit": "{0} splits into the left part {1} and the right part {2}",
    "AllNone": "{0} is an empty usage mask",
    "OnlySomeAt": "{0} is occupied exactly at position {1}",
    "Lookup": "position {1} of {0} holds {2}",
    "HasType": "{2} has type {3} under the unrestricted context {0} and the linear context {1}",
    "Step": "{0} reduces in one step to {1}",
    "SemanticFragment": "{0} lies in the semantic fragment",
    "ClosedSemanticFragment": "{0} is a closed term of the semantic fragment",
    "FirstOrder": "{0} is a first-order type",
    "Quotable": "{0} is quotable",
    "CtxUAllBit": "every unrestricted variable of {0} has bit type",
    "CtxLAllSomeFragment": "every cell of the linear context {0} is occupied by a fragment type",
    "CtxUAllFragment": "every unrestricted variable of {0} has a fragment type",
    "Monotone": "{0} is monotone",
    "Antitone": "{0} is antitone",
    "Injective": "{0} is injective",
    "Surjective": "{0} is surjective",
    "Bijective": "{0} is bijective",
    "Continuous": "{0} is continuous",
    "CompEq": "{0} and {1} are observationally equal",
    "SemEq": "{0} and {1} have the same semantics",
    "HasSum": "the family {0} sums to {1}",
    "Summable": "the family {0} is summable",
    "IsLUB": "{1} is a least upper bound of {0}",
    "IsGLB": "{1} is a greatest lower bound of {0}",
    "Nonempty": "{0} is inhabited",
    "Finite": "{0} is finite",
    "ResidualRefines": "{0} refines {1} residually",
    "AntisymmRel": "{1} and {2} are equivalent under {0}",
    "ContinuationTyped": "the continuation {0} is well typed",
    "MakesProgress": "{0} makes progress",
    "Admissible": "{0} is admissible",
    "UsesAtMostQubits": "{1} uses at most {0} qubits",
    "Decidable": "{0} is decidable",
    "Subsingleton": "{0} has at most one element",
    "Tendsto": "{0} converges along {1} to {2}",
}

FIELD_GLOSS: dict[str, str] = {
    "cond": "condition", "then": "then-branch", "else": "else-branch", "fn": "function part",
    "arg": "argument", "left": "left component", "right": "right component", "body": "body",
    "cont": "continuation", "qubit": "qubit argument", "fst": "first component",
    "snd": "second component", "scrutinee": "scrutinee", "value": "value",
}

PRED_NOUN: dict[str, str] = {
    "FragmentBinders": "the fragment-binder condition",
    "SemanticFragment": "membership in the semantic fragment",
    "ClosedSemanticFragment": "membership in the closed semantic fragment",
    "FirstOrder": "being first order",
    "Quotable": "quotability",
    "HasType": "typability",
    "AllNone": "emptiness of the usage mask",
    "Admissible": "admissibility",
}

POSTFIX_PRED: dict[str, str] = {
    "PosSemidef": "is positive semidefinite",
    "IsHermitian": "is self-adjoint",
    "IsFunction": "is functional",
    "WellFormed": "is well formed",
    "Admissible": "is admissible",
    "Quotable": "is quotable",
    "FirstOrder": "is first order",
    "HasSum": "has a sum",
}

TYPE_NOUN: list[tuple[str, str]] = [
    (r"List \(Option Ty\)", "linear context"),
    (r"List Ty", "unrestricted context"),
    (r"Term", "term"),
    (r"Ty", "type"),
    (r"Prim", "primitive"),
    (r"(?:ℕ|Nat)", "natural number"),
    (r"(?:ℝ|Real)", "real number"),
    (r"(?:ℂ|Complex)", "complex number"),
    (r"(?:ℚ|Rat)", "rational number"),
    (r"Bool", "bit"),
    (r"Fin .+", "index"),
    (r"Superoperator .+", "superoperator"),
    (r"CPMap .+", "completely positive map"),
    (r"KrausFamily .+", "Kraus family"),
    (r"QuantumRel .+", "quantum relation"),
    (r"Matrix .+", "matrix"),
    (r"Module(?:\.\{.*\})?", "superoperator module"),
    (r"Hom .+", "module morphism"),
    (r"Command .+", "circuit command"),
    (r"FiniteInstrumentComp .+", "finite instrument computation"),
    (r"RegisterState .+", "register state"),
    (r"Comonoid", "comonoid"),
]

# ==========================================================================
# Excerpts and Lean scanning
# ==========================================================================

END_OF_DECL = re.compile(
    r"^(?:@\[|/-|--|namespace\b|section\b|end\b|open\b|variable\b|universe\b|"
    r"set_option\b|attribute\b|#|(?:(?:" + "|".join(MODIFIERS) + r")\s+)*(?:"
    + "|".join(DECL_KW) + r")\b)"
)


def load_excerpt(d: dict) -> str:
    """Source lines of the declaration, trimmed of any trailing bleed."""
    path = ROOT / d["file"]
    if not path.is_file():
        return d.get("signature") or ""
    lines = path.read_text(encoding="utf-8").splitlines()
    a, b = d["start_line"], d["end_line"]
    if a < 1 or b < a or b > len(lines):
        return d.get("signature") or ""
    chunk = lines[a - 1 : b]
    # Skip the declaration's own leading attribute lines, then stop at the
    # first column-0 line that starts something else.
    i = 0
    while i < len(chunk) and chunk[i].startswith("@["):
        i += 1
    out = chunk[: i + 1]
    for line in chunk[i + 1 :]:
        if line and not line[0].isspace() and END_OF_DECL.match(line):
            break
        out.append(line)
    while out and not out[-1].strip():
        out.pop()
    return "\n".join(out)


OPEN = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄"}
CLOSE = set(OPEN.values())


def match_close(s: str, i: int) -> int:
    depth = 0
    for j in range(i, len(s)):
        c = s[j]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
            if depth == 0:
                return j
    return len(s) - 1


def depth_map(s: str) -> list[int]:
    out, depth = [], 0
    for c in s:
        if c in CLOSE:
            depth = max(0, depth - 1)
        out.append(depth)
        if c in OPEN:
            depth += 1
    return out


def find_top(s: str, tokens: tuple[str, ...], start: int = 0, word: bool = False) -> tuple[int, str]:
    dm = depth_map(s)
    for i in range(start, len(s)):
        if dm[i] != 0:
            continue
        for t in tokens:
            if s.startswith(t, i):
                if word:
                    before = s[i - 1] if i else " "
                    after = s[i + len(t)] if i + len(t) < len(s) else " "
                    if before.isalnum() or before in "_'." or after.isalnum() or after in "_'":
                        continue
                return i, t
    return -1, ""


def split_top(s: str, sep: str) -> list[str]:
    parts, depth, cur, i = [], 0, [], 0
    while i < len(s):
        c = s[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        if depth == 0 and s.startswith(sep, i):
            parts.append("".join(cur))
            cur = []
            i += len(sep)
            continue
        cur.append(c)
        i += 1
    parts.append("".join(cur))
    return [p.strip() for p in parts]


def strip_parens(s: str) -> str:
    s = s.strip()
    while s.startswith("(") and match_close(s, 0) == len(s) - 1:
        s = s[1:-1].strip()
    return s


def split_app(s: str) -> list[str]:
    """Split a Lean application `f a (b c) d` into head and arguments."""
    s = strip_parens(s)
    toks, depth, cur = [], 0, []
    for i, c in enumerate(s):
        if depth == 0 and not cur and (s.startswith("fun ", i) or s.startswith("λ", i)):
            toks.append(s[i:].strip())
            return toks
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        if depth == 0 and c.isspace():
            if cur:
                toks.append("".join(cur))
                cur = []
            continue
        cur.append(c)
    if cur:
        toks.append("".join(cur))
    return toks


@dataclass
class Binder:
    names: list[str]
    type: str | None
    bracket: str  # "(", "{", "[", "⦃"


@dataclass
class Parsed:
    kind: str = ""
    name: str = ""
    binders: list[Binder] = field(default_factory=list)
    type: str | None = None
    body: str | None = None
    body_kind: str = ""  # "term" | "by" | "where" | "arms" | ""


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", " ", text, flags=re.DOTALL)
    text = re.sub(r"--[^\n]*", "", text)
    return text


def parse_binder_group(inner: str, bracket: str) -> Binder:
    k, _ = find_top(inner, (":",))
    if k < 0 or bracket == "[":
        if bracket == "[":
            return Binder([], inner.strip(), "[")
        return Binder(inner.split(), None, bracket)
    names = inner[:k].split()
    typ = inner[k + 1 :].strip()
    j, _ = find_top(typ, (":=",))
    if j >= 0:
        typ = typ[:j].strip()
    return Binder(names, typ, bracket)


def parse_binders(s: str) -> tuple[list[Binder], str]:
    binders = []
    s = s.lstrip()
    while s and s[0] in "({[⦃":
        j = match_close(s, 0)
        binders.append(parse_binder_group(s[1:j], s[0]))
        s = s[j + 1 :].lstrip()
    return binders, s


def parse_decl(excerpt: str) -> Parsed:
    p = Parsed()
    text = strip_comments(excerpt)
    text = re.sub(r"@\[[^\]]*\]", " ", text).strip()
    m = re.match(
        r"(?:(?:" + "|".join(MODIFIERS) + r")\s+)*(" + "|".join(DECL_KW) + r")\b\s*",
        text,
    )
    if not m:
        return p
    p.kind = m.group(1)
    rest = text[m.end() :]
    rest = re.sub(r"^\(priority\s*:=[^)]*\)\s*", "", rest)
    nm = re.match(r"([^\s(:{\[⦃]+)\s*", rest)
    if nm and nm.group(1) not in ("where", ":="):
        p.name = nm.group(1)
        rest = rest[nm.end() :]
    p.binders, rest = parse_binders(rest)
    if rest.startswith(":") and not rest.startswith(":="):
        rest = rest[1:]
        cands = []
        for toks, kind in (((":=",), "term"), (("where",), "where")):
            i, _ = find_top(rest, toks, word=(kind == "where"))
            if i >= 0:
                cands.append((i, kind))
        am = re.search(r"\n\s*\|", rest)
        if am:
            dm = depth_map(rest)
            if dm[am.start()] == 0:
                cands.append((am.start(), "arms"))
        if cands:
            i, kind = min(cands)
            p.type = rest[:i].strip()
            tail = rest[i:]
            if kind == "term":
                tail = tail[2:]
            elif kind == "where":
                tail = tail[len("where") :]
            p.body = tail.strip("\n")
            p.body_kind = kind
        else:
            p.type = rest.strip()
    else:
        i, t = find_top(rest, (":=", "where"))
        if i >= 0:
            p.body = rest[i + len(t) :].strip("\n")
            p.body_kind = "term" if t == ":=" else "where"
        elif rest.lstrip().startswith("|"):
            p.body = rest
            p.body_kind = "arms"
    if p.body_kind == "term" and p.body is not None:
        b = p.body.strip()
        if re.match(r"by\b", b):
            p.body = b[2:]
            p.body_kind = "by"
        else:
            p.body = b
    return p


def decompose_claim(typ: str) -> tuple[list[Binder], list[str], str]:
    """Split a proposition into ∀-binders, premises, and conclusion."""
    binders: list[Binder] = []
    premises: list[str] = []
    s = " ".join(typ.split())
    while True:
        s = s.strip()
        if s.startswith("∀"):
            k, _ = find_top(s, (",",))
            if k < 0:
                break
            head = s[1:k].strip()
            bs, left = parse_binders(head)
            if left:
                g = parse_binder_group(left, "(")
                bs.append(g)
            binders.extend(bs)
            s = s[k + 1 :]
            continue
        parts = split_top(s, "→")
        if len(parts) > 1:
            premises.extend(parts[:-1])
            s = parts[-1]
            continue
        break
    return binders, premises, s.strip()


# ==========================================================================
# Nouns
# ==========================================================================

SUBSCRIPT = "₀₁₂₃₄₅₆₇₈₉"
PROPER = {"Day", "Kraus", "Choi", "Born", "Yoneda", "OpenQASM", "Hadamard", "Pauli",
          "Scott", "CP", "QASM", "Bell", "Composer", "Hilbert", "Palomar", "Lean",
          "Mathlib", "TNI", "LNL", "CPO", "CPOs"}


def lower_first(s: str) -> str:
    return s[:1].lower() + s[1:] if s else s


COMPOUND = re.compile(r"(OSplit|FragCert|CPMap|QDim|CStore|OpenQASM|QASM|ωSup|LNL|TNI)")


def camel_words(ident: str) -> list[str]:
    ident = ident.replace("_", " ")
    out: list[str] = []
    for piece in COMPOUND.split(ident):
        if not piece:
            continue
        if COMPOUND.fullmatch(piece):
            out.append(piece)
        else:
            out.extend(re.findall(r"[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z]+|[A-Z]+|\d+|[^\W\d_]+", piece))
    return out


def word_gloss(w: str) -> str:
    lw = w.lower()
    if lw in WORD:
        return WORD[lw]
    if w in IDENT and len(w) > 1:
        return IDENT[w]
    if lower_first(w) in IDENT and len(w) > 1:
        return IDENT[lower_first(w)]
    if w.isupper() and len(w) > 1:
        return w
    return lw


def noun(ident: str, ns: str | None = None) -> str:
    """English noun phrase for a Lean identifier (no Lean syntax in output)."""
    ident = ident.strip().strip("@").lstrip(".")
    if not ident:
        return ""
    prime = ident.endswith("'")
    ident = ident.rstrip("'")
    if "." in ident:
        parts = [x for x in ident.split(".") if x]
        last = parts[-1]
        owner = parts[-2] if len(parts) > 1 else ns
        return noun(last, owner) + (" (variant)" if prime else "")
    sub = ""
    m = re.match(r"^(.*?)([" + SUBSCRIPT + r"]+)$", ident)
    if m and m.group(1):
        ident = m.group(1)
        k = int(m.group(2).translate(str.maketrans(SUBSCRIPT, "0123456789")))
        sub = f"@{k}"
    if ns and (ns, ident) in IDENT_NS:
        out = IDENT_NS[(ns, ident)]
    elif ident in IDENT:
        out = IDENT[ident]
    elif lower_first(ident) in IDENT and not ident[:1].islower():
        out = IDENT[lower_first(ident)]
    elif ident in TYPE_NS:
        out = TYPE_NS[ident][0]
    elif re.match(r"^of[A-Z]", ident):
        out = "construction from " + with_article(noun(ident[2:]))
    elif re.match(r"^to[A-Z]", ident):
        out = "passage to " + noun(ident[2:])
    elif re.match(r"^is[A-Z]", ident):
        out = noun(ident[2:]) + " property"
    elif re.match(r"^inst[A-Z]", ident):
        rest = ident[4:]
        out = noun(rest)
        for key in sorted(CLASS_NOUN, key=len, reverse=True):
            if rest.startswith(key) and len(rest) > len(key):
                out = f"{CLASS_NOUN[key].lower()} on {plural(noun(rest[len(key):]))}"
                break
    elif re.match(r"^parse[A-Z]", ident):
        out = "parser for " + plural(noun(ident[5:]))
    elif re.match(r"^[a-z]\w*Expected$", ident):
        out = "expected result of the " + noun(ident[: -len("Expected")])
    else:
        words = camel_words(ident)
        if len(words) > 1 and words[-1] == "Of":
            words = words[:-1]
        out = " ".join(word_gloss(w) for w in words) if words else ident
    out = re.sub(r"\b(\w+) \1\b", r"\1", out)
    if sub:
        k = sub[1:]
        out = f"{k}×{k} matrix of the {out}"
    return out + (" (variant)" if prime else "")


def plural(np: str) -> str:
    for sing, plu in TYPE_NS.values():
        if np == sing:
            return plu
    words = np.split(" of ", 1)
    head = words[0]
    if head.endswith(("s", "x", "ch", "sh")):
        head += "es"
    elif head.endswith("y") and not head.endswith(("ay", "ey", "oy")):
        head = head[:-1] + "ies"
    else:
        head += "s"
    return head + (" of " + words[1] if len(words) > 1 else "")


def with_article(np: str) -> str:
    if not np or re.match(r"^(?:the|a|an|every|each|its)\b|^(?:zero|one|two)(?![-\w])", np):
        return np
    if np.split()[0] in PROPER and np.split()[0] not in ("CP",):
        return "the " + np
    vowel = re.match(r"^[aeiouAEIOU]", np) and not re.match(r"^(?:uni|use|usa|eu|one)", np)
    return ("an " if vowel else "a ") + np


def the(np: str) -> str:
    if not np or re.match(r"^(the|a|an|every|each|its)\b", np):
        return np
    return "the " + np


def arg_form(atom: str, ns: str | None = None) -> str:
    if atom in ARG_FORM:
        return ARG_FORM[atom]
    return with_article(noun(atom, ns))


def cap(s: str) -> str:
    s = s.strip()
    if not s or s[0] in "ωαβγδεζηθικλμνξπρστυφχψ":
        return s
    return s[:1].upper() + s[1:]


# ==========================================================================
# Declaration context
# ==========================================================================

@dataclass
class Ctx:
    d: dict
    excerpt: str
    parsed: Parsed
    ns: list[str]           # namespace path (without the leaf)
    subject: str | None     # innermost namespace naming a mathematical kind
    leaf: str               # final name segment

    @property
    def subj_noun(self) -> str | None:
        if self.subject is None:
            return None
        return TYPE_NS.get(self.subject, (noun(self.subject), plural(noun(self.subject))))[0]

    @property
    def subj_plural(self) -> str | None:
        if self.subject is None:
            return None
        return TYPE_NS.get(self.subject, (noun(self.subject), plural(noun(self.subject))))[1]


def make_ctx(d: dict) -> Ctx:
    excerpt = load_excerpt(d)
    parsed = parse_decl(excerpt)
    parts = d["fqn"].split(".")
    leaf = parts[-1]
    ns = parts[:-1]
    subject = None
    for seg in reversed(ns):
        if seg in MODULE_NS:
            continue
        if seg in TYPE_NS or seg[:1].isupper():
            subject = seg
            break
    return Ctx(d, excerpt, parsed, ns, subject, leaf)


INDEX: dict[str, list[dict]] = {}
CTX_CACHE: dict[str, Ctx] = {}


def ctx_of(d: dict) -> Ctx:
    key = f"{d['file']}#{d['start_line']}"
    if key not in CTX_CACHE:
        CTX_CACHE[key] = make_ctx(d)
    return CTX_CACHE[key]


def resolve(name: str, near: Ctx | None = None) -> dict | None:
    """Find the extracted declaration a Lean reference most likely denotes."""
    name = name.strip().lstrip("@.←").rstrip("'")
    if not name:
        return None
    cands = INDEX.get(name) or INDEX.get(name.split(".")[-1]) or []
    if not cands:
        return None
    if near is not None:
        for c in cands:
            if c["fqn"].endswith("." + name) and c["file"] == near.d["file"]:
                return c
        for c in cands:
            if c["fqn"].endswith("." + name):
                return c
        for c in cands:
            if c["file"] == near.d["file"]:
                return c
    return cands[0]


# ==========================================================================
# Rendering Lean expressions
# ==========================================================================

QUALIFIERS = re.compile(
    r"\b(?:QLambda|Linear|Domain|Presheaf|Composer|CQ|SuperoperatorModule|Function)\."
)


def pretty(expr: str) -> str:
    e = " ".join(expr.split())
    for _ in range(4):
        e2 = re.sub(r"\(([^():⟨⟩]+?) : [^():]+\)", r"\1", e)
        if e2 == e:
            break
        e = e2
    e = QUALIFIERS.sub("", e)
    e = e.replace("Matrix.trace", "tr").replace("ᴴ", "†").replace(" ⬝ᵥ ", " · ")
    e = re.sub(r"\s+", " ", e).strip()
    return e


def code(expr: str, limit: int = 90) -> str:
    e = strip_parens(pretty(expr)).replace("`", "")
    if len(e) > limit:
        return ""
    return f"`{e}`"


INFIX = (
    (" ++ ", "the concatenation of {0} and {1}"),
    (" + ", "the sum of {0} and {1}"),
    (" - ", "the difference of {0} and {1}"),
    (" • ", "{1} scaled by {0}"),
    (" * ", "the product of {0} and {1}"),
    (" ∘ ", "the composite of {0} after {1}"),
    (" ⊗ ", "the tensor product of {0} and {1}"),
    (" ≫ ", "{0} followed by {1}"),
)


def light(expr: str) -> str:
    """Whitespace, ascription and qualifier cleanup without notation changes."""
    e = " ".join(expr.split())
    for _ in range(4):
        e2 = re.sub(r"\(([^():⟨⟩]+?) : [^():]+\)", r"\1", e)
        if e2 == e:
            break
        e = e2
    return QUALIFIERS.sub("", e).strip()


def term_english(expr: str, ctx: Ctx | None = None, depth: int = 0) -> str:
    """Short English for a term: variables in code, known heads as nouns."""
    e = strip_parens(light(expr))
    if re.fullmatch(r"[\w'₀-₉]+", e) and (len(e) <= 3 or not re.search(r"[a-z][A-Z]", e)):
        return f"`{e}`"
    # projection `f.choi`
    pm = re.fullmatch(r"([\w'₀-₉]+)\.([a-z][\w']*)", e)
    if pm and len(pm.group(1)) <= 3:
        return f"{the(noun(pm.group(2)))} of `{pm.group(1)}`"
    if e.startswith("if ") or e.startswith("match "):
        return code(e, 70) or "a case distinction"
    for op, word in INFIX:
        parts = split_top(e, op)
        if len(parts) == 2 and all(parts) and depth < 2:
            a, b = (term_english(x, ctx, depth + 1) for x in parts)
            return word.format(a, b)
    toks = split_app(e)
    if not toks:
        return f"`{e}`"
    head = toks[0]
    if not re.fullmatch(r"\.?[A-Za-z][\w.'₀-₉]*", head) or len(toks) > 5:
        return code(e, 70) or "the displayed expression"
    owner = ctx.subject if ctx else None
    leaf = head.split(".")[-1].lstrip(".")

    def arg(a: str) -> str:
        a2 = strip_parens(a)
        if a2.startswith(".") and re.fullmatch(r"\.[\w']+", a2):
            return ctor_gloss(a2[1:], owner)
        if re.fullmatch(r"[\w'₀-₉]+", a2) and not re.search(r"[a-z][A-Z]", a2):
            return f"`{a2}`"
        if depth < 1:
            sub = term_english(a2, ctx, depth + 1)
            if not sub.startswith("`") and "displayed" not in sub:
                return sub
        return code(a2, 50) or "a compound term"

    args = [arg(a) for a in toks[1:]]
    if not (ctx and (ctx.subject, leaf) in IDENT_NS) and leaf in IDENT_APP:
        tmpl = IDENT_APP[leaf]
        need = max((int(x) for x in re.findall(r"\{(\d)\}", tmpl)), default=-1) + 1
        if len(args) >= need:
            return tmpl.format(*args[len(args) - need :])
    hn = noun(head, owner)
    if not args:
        return the(hn)
    if len(args) > 3:
        return code(e, 70) or the(hn)
    nums = [a for a, t in zip(args, toks[1:]) if re.fullmatch(r"\d+", strip_parens(t))]
    rest = [a for a, t in zip(args, toks[1:]) if not re.fullmatch(r"\d+", strip_parens(t))]
    out = the(hn)
    if rest:
        out += " of " + join_and(rest) if len(rest) < 3 else " of " + ", ".join(rest)
    if nums:
        out += " at " + ", ".join(nums)
    return out


FALLBACK_MARKERS = ("displayed", "a compound term", "case distinction", "its argument")


def describe(expr: str, ctx: Ctx | None) -> str:
    """term_english, falling back to the ingredients of the expression."""
    te = term_english(expr, ctx)
    if not any(m in te for m in FALLBACK_MARKERS):
        return te
    ing = ingredient_nouns(expr, ctx) if ctx is not None else []
    if ing:
        return "an explicit expression in " + join_and(ing)
    return "an explicit expression"


def ctor_gloss(ctor: str, ind: str | None) -> str:
    ctor = ctor.lstrip(".")
    base = ctor.split()[0] if ctor else ctor
    if ind and ind in CTOR_GLOSS and base in CTOR_GLOSS[ind]:
        return CTOR_GLOSS[ind][base]
    for table in CTOR_GLOSS.values():
        if base in table:
            return table[base]
    return with_article(noun(base))


RELATIONS = (" = ", " ≠ ", " ≤ ", " < ", " ≥ ", " > ", " ∈ ", " ∉ ", " ⊆ ", " ⊑ ", " ≈ ")


def prop_english(expr: str, ctx: Ctx | None = None, depth: int = 0) -> str:
    """English clause for a Lean proposition."""
    e = strip_parens(" ".join(expr.split()))
    if depth > 4 or not e:
        return code(e) or "the displayed condition"
    for sep, word in (("↔", "if and only if"), ("∧", "and"), ("∨", "or")):
        if " then " in e and sep != "↔":
            continue
        parts = split_top(e, sep)
        if len(parts) > 1:
            eng = [prop_english(x, ctx, depth + 1) for x in parts]
            if sep == "∨":
                return "either " + " or ".join(eng)
            if sep == "↔":
                return f"{eng[0]} if and only if {eng[1]}"
            return ", ".join(eng[:-1]) + " and " + eng[-1]
    parts = split_top(e, "→") if " then " not in e else [e]
    if len(parts) > 1:
        return (
            "if " + " and ".join(prop_english(x, ctx, depth + 1) for x in parts[:-1])
            + ", then " + prop_english(parts[-1], ctx, depth + 1)
        )
    if e.startswith("¬"):
        return "it is not the case that " + prop_english(e[1:], ctx, depth + 1)
    if e.startswith("∃") or e.startswith("∀"):
        k, _ = find_top(e, (",",))
        if k > 0:
            vars_ = e[1:k].strip()
            vs, rest = parse_binders(vars_)
            names = [n for b in vs for n in b.names] or rest.split(":")[0].split()
            vtxt = ", ".join(f"`{n}`" for n in names) or "a witness"
            body = prop_english(e[k + 1 :], ctx, depth + 1)
            if e.startswith("∃"):
                return f"there is {vtxt} such that {body}"
            return f"for every {vtxt}, {body}"
    for rel in RELATIONS:
        i, _ = find_top(e, (rel,))
        if i >= 0:
            lhs, rhs = e[:i].strip(), e[i + len(rel) :].strip()
            if rel == " = " and rhs in ("true", "false"):
                c = code(lhs)
                if c:
                    return f"{c} evaluates to {rhs}"
            c = code(e)
            if c:
                return c
            word = {" = ": "equals", " ≤ ": "is at most", " < ": "is less than", " ≠ ": "differs from"}.get(rel)
            if word:
                return f"{describe(lhs, ctx)} {word} {describe(rhs, ctx)}"
            return "the stated relation holds"
    toks = split_app(e)
    if toks:
        head = toks[0].split(".")[-1]
        args = [arg_text(a, ctx) for a in toks[1:]]
        if head in PRED:
            tmpl = PRED[head]
            need = max((int(x) for x in re.findall(r"\{(\d)\}", tmpl)), default=-1) + 1
            explicit = args[-need:] if need and len(args) >= need else args
            if len(explicit) >= need:
                return tmpl.format(*explicit)
        m = re.match(r"^(.+)\.([A-Z]\w*)$", e)
        if m and m.group(2) in POSTFIX_PRED:
            return f"{code(m.group(1), 50) or 'the object'} {POSTFIX_PRED[m.group(2)]}"
        if len(toks) == 1 and e in ("True", "False"):
            return "the statement is trivially true" if e == "True" else "a contradiction"
    return code(e) or "the displayed property holds"


def arg_text(a: str, ctx: Ctx | None) -> str:
    a = strip_parens(a)
    m = re.match(r"^([^:]+?)\s*:\s*.+$", a)
    if m and find_top(a, (":",))[0] >= 0:
        a = m.group(1).strip()
    return code(a, 50) or term_english(a, ctx)


def is_prop_type(t: str | None, names: list[str]) -> bool:
    if not t:
        return False
    if names and all(re.match(r"^_?h", n) for n in names):
        return True
    one = " ".join(t.split())
    if any(find_top(one, (r,))[0] >= 0 for r in RELATIONS + (" ↔ ", " ∧ ")):
        return True
    head = split_app(one)[0].split(".")[-1] if split_app(one) else ""
    if head in PRED:
        return True
    m = re.match(r"^(.+)\.([A-Z]\w*)$", one)
    return bool(m and m.group(2) in POSTFIX_PRED)


def type_noun(t: str) -> str | None:
    one = " ".join(t.split())
    for pat, nm in TYPE_NOUN:
        if re.fullmatch(pat, one):
            return nm
    return None


# ==========================================================================
# Titles
# ==========================================================================

PROPER_CAMEL = ("OpenQASM", "QLambda", "LaTeX")

CODEY = re.compile(
    r"(?:[A-Za-z]\w*\.[A-Za-z]\w*|\w_\w|[a-z][A-Z]|`[^`]*[a-z][A-Z][^`]*`|`[^`]*\.[^`]*`|:=)"
)


def is_codey(title: str) -> bool:
    t = title
    for w in PROPER_CAMEL:
        t = t.replace(w, "Proper")
    return bool(CODEY.search(t))


def clean_title(t: str) -> str:
    t = re.sub(r"\s+", " ", t).strip().rstrip(".:;,")
    t = re.sub(r"\b(\w+) \1\b", r"\1", t)
    t = re.sub(r"\b(?:the|a|an) (the|a|an)\b", r"\1", t)
    return cap(t)


def gloss_backticks(text: str, ns: str | None) -> str:
    """Replace backticked Lean identifiers/applications with English nouns."""

    def repl(m: re.Match[str]) -> str:
        inner = m.group(1).strip()
        toks = split_app(inner)
        if not toks:
            return m.group(0)
        head = toks[0]
        leanish = re.fullmatch(r"\.?[A-Za-z][\w.'₀-₉]*", head) and (
            "." in head or re.search(r"[a-z][A-Z]|_", head) or len(head) > 3
        )
        if not leanish:
            return m.group(0)
        np_ = noun(head, ns)
        if len(toks) > 1:
            args = []
            for a in toks[1:]:
                a = strip_parens(a)
                if a.startswith("."):
                    args.append(ctor_gloss(a[1:], None))
                elif re.fullmatch(r"[\w₀-₉']{1,3}", a):
                    args.append(f"`{a}`")
            if args:
                np_ += " of " + " and ".join(args)
        return np_

    return re.sub(r"`([^`]+)`", repl, text)


def doc_headline(doc: str, ns: str | None) -> str | None:
    first = re.sub(r"\s+", " ", doc.split("\n\n", 1)[0]).strip().lstrip("#").strip()
    if not first:
        return None
    sent = first
    in_code = False
    for i, ch in enumerate(first):
        if ch == "`":
            in_code = not in_code
        elif ch in ".!?" and not in_code and (i + 1 == len(first) or first[i + 1] == " "):
            sent = first[: i + 1]
            break
    sent = gloss_backticks(sent, ns)
    if len(sent) > 120:
        for sep in (" — ", "; ", ": ", ", "):
            k = sent.find(sep, 30)
            if 30 <= k <= 115:
                sent = sent[:k]
                break
        else:
            return None
    return clean_title(sent)


def hyp_phrase(atoms: list[str], ctx: Ctx) -> str:
    """English for an `of_…` hypothesis segment of a lemma name."""
    ns = ctx.subject
    if not atoms:
        return ""
    if len(atoms) == 2 and atoms[1] in ("left", "right") and ns == "OSplit":
        return f"the {atoms[1]} part is {with_article(noun(atoms[0], ns))}"
    if atoms[0] in ("le", "lt") and len(atoms) >= 2:
        rest = arg_form(atoms[1], ns) if len(atoms) == 2 else the(noun_seq(atoms[1:], ctx))
        return f"it is {'at most' if atoms[0] == 'le' else 'below'} {rest}"
    if atoms[0] == "eq" and len(atoms) >= 2:
        return f"it equals {arg_form('_'.join(atoms[1:]), ns)}"
    if atoms[0] == "ne" and len(atoms) >= 2:
        return f"it differs from {arg_form('_'.join(atoms[1:]), ns)}"
    return "assuming " + noun_seq(atoms, ctx)


def noun_seq(atoms: list[str], ctx: Ctx) -> str:
    """Mathlib reading of `f_g_h`: the f of the g of h."""
    ns = ctx.subject
    atoms = [a for a in atoms if a]
    if not atoms:
        return ""
    merged: list[str] = []
    pending = ""
    for k, a in enumerate(atoms):
        n = noun(a, ns)
        if a in PREPOSITIONS and merged:
            merged.append("@" + a)
            continue
        if k < len(atoms) - 1 and ADJ.search(n) and " " not in n:
            pending += n + " "
            continue
        merged.append(pending + n if pending else a)
        if pending:
            NOUN_OVERRIDE[pending + n] = pending + n
        pending = ""
    first = merged[0]
    out = NOUN_OVERRIDE.get(first) or noun(first, ns)
    prep = "of"
    for a in merged[1:]:
        if a.startswith("@"):
            prep = a[1:]
            continue
        if prep != "of":
            out += f" {prep} " + (ARG_FORM[a] if a in ARG_FORM else the(NOUN_OVERRIDE.get(a) or noun(a, ns)))
            prep = "of"
            continue
        if a in NOUN_OVERRIDE:
            out += " of the " + NOUN_OVERRIDE[a]
        else:
            out += " of " + (ARG_FORM[a] if a in ARG_FORM else the(noun(a, ns)))
    return out


NOUN_OVERRIDE: dict[str, str] = {}
PREPOSITIONS = {"to", "from", "with", "at", "in", "on", "by", "over", "through", "into", "along"}
ADJ = re.compile(
    r"^(?:\w+(?:al|ic|ive|ed|ar|ous)|linear|unrestricted|closed|symmetric|first|second|"
    r"left|right|inverse|dual|double|normalized|classical|physical|fresh|empty|full|total|"
    r"partial|raw|free|open|ambient|intrinsic|canonical|general|global|local|live|dead)$"
)


TWO_ATOM: dict[tuple[str, str], str] = {
    ("proof", "independent"): "{S} does not depend on the choice of proof",
    ("hom", "inv"): "{S} and its inverse compose to the identity",
    ("inv", "hom"): "{S} and its inverse compose to the identity",
    ("mul", "self"): "{S} is idempotent",
    ("le", "one"): "{S} is at most one",
    ("eq", "zero"): "{S} vanishes",
    ("ne", "zero"): "{S} is nonzero",
    ("eq", "one"): "{S} equals one",
    ("trace", "le"): "The trace of {s} is bounded",
    ("is", "function"): "{S} is functional",
}


VERB_ATOM: dict[str, str] = {
    "elaborates": "elaborates", "succeeds": "succeeds", "fails": "fails",
    "agrees": "agrees", "commutes": "commutes", "holds": "holds",
    "interprets": "is interpreted", "reflects": "reflects", "generates": "generates",
    "forces": "forces", "excludes": "excludes", "avoids": "avoids", "fixes": "fixes",
    "skips": "skips", "requires": "requires", "determined": "is determined",
    "rejected": "is rejected", "routes": "routes", "cannot": "cannot", "factors": "factors",
    "interpret": "is interpreted", "matches": "matches", "terminates": "terminates",
    "exhausted": "is exhausted", "resolved": "is resolved", "collapsed": "collapses",
    "claimed": "is as claimed", "supported": "is supported", "stationary": "is stationary",
}

VERB_OBJ: dict[str, str] = {
    "elaborates": "to", "agrees": "with", "commutes": "with", "interprets": "as",
    "interpret": "as", "routes": "through", "factors": "through", "matches": "",
    "determined": "by", "rejected": "by", "fixes": "", "reflects": "", "generates": "",
    "forces": "", "excludes": "", "avoids": "", "requires": "",
}


def compound_noun(atoms: list[str], ctx: Ctx) -> str:
    return " ".join(noun(a, ctx.subject) for a in atoms if a)


def subject_phrase(atoms: list[str], ctx: Ctx, plural_ok: bool = True) -> str:
    if atoms:
        return noun_seq(atoms, ctx)
    if ctx.subject:
        return (ctx.subj_plural if plural_ok else ctx.subj_noun) or ""
    return "the construction"


def fill(tmpl: str, subj: str) -> str:
    return tmpl.replace("{S}", cap(subj)).replace("{s}", subj)


def structural_title(ctx: Ctx) -> str | None:
    """Titles read off the shape of the claim rather than the name."""
    p = ctx.parsed
    if not p.type:
        return None
    extra, premises, concl = decompose_claim(p.type)
    hyps = [b.type for b in p.binders + extra if b.bracket in "({⦃" and is_prop_type(b.type, b.names)]
    hyps += premises
    c = strip_parens(concl)
    toks = split_app(c)
    head = toks[0].split(".")[-1] if toks else ""
    atoms = [a for a in ctx.leaf.split("_") if a]
    # Inversion: P (C …) ⊢ P X with lemma name `ctor_field`.
    if re.fullmatch(r"[A-Z]\w*", head or "") and len(atoms) == 2 and hyps:
        for h in hyps:
            ht = split_app(strip_parens(h or ""))
            if ht and ht[0].split(".")[-1] == head and len(ht) >= 2:
                inner = split_app(strip_parens(ht[-1]))
                if inner and inner[0].split(".")[-1] == atoms[0]:
                    pred = PRED_NOUN.get(head, noun(head))
                    fld = FIELD_GLOSS.get(atoms[1]) or noun(atoms[1], ctx.subject)
                    return (
                        f"{cap(pred)} passes from {with_article(noun(atoms[0], ctx.subject))} "
                        f"to its {fld}"
                    )
    if head in ("Monotone", "Antitone") and len(toks) >= 2:
        return f"{'Monotonicity' if head == 'Monotone' else 'Antitonicity'} of {the(noun_seq(atoms[:-1] or atoms, ctx))}"
    if head in ("Injective", "Surjective", "Bijective"):
        return f"{head[:-2]}ivity of {the(noun_seq(atoms[:-1] or atoms, ctx))}".replace("Injectivity", "Injectivity")
    return None


def equation_title(ctx: Ctx) -> str | None:
    """`f_ctor : f .ctor = rhs` style defining-clause lemmas."""
    p = ctx.parsed
    if not p.type:
        return None
    _, _, concl = decompose_claim(p.type)
    i, _ = find_top(concl, (" = ",))
    if i < 0:
        return None
    lhs = split_app(concl[:i])
    atoms = [a for a in ctx.leaf.split("_") if a]
    if len(lhs) >= 2 and len(atoms) == 2 and lhs[0].split(".")[-1] == atoms[0]:
        arg = strip_parens(lhs[1])
        if arg.startswith(".") or arg.split()[0].lstrip(".") == atoms[1]:
            f = noun(atoms[0], ctx.subject)
            return f"{cap(f)} of {ctor_gloss(atoms[1], ctx.subject)}"
    return None


LEAF_PATTERN: dict[str, str] = {
    "id_comp": "The identity is a left unit for composition{of}",
    "comp_id": "The identity is a right unit for composition{of}",
    "comp_assoc": "Composition{of} is associative",
    "assoc": "Associativity of composition{of}",
    "map_id": "The functorial action{of} preserves identities",
    "map_comp": "The functorial action{of} preserves composition",
    "zero_add": "Zero is a left unit for addition{of}",
    "add_zero": "Zero is a right unit for addition{of}",
    "add_comm": "Addition{of} is commutative",
    "add_assoc": "Addition{of} is associative",
    "zero_smul": "Scaling by zero gives zero{of}",
    "smul_zero": "Scaling zero gives zero{of}",
    "one_smul": "Scaling by one is the identity{of}",
    "smul_add": "Scalar multiplication distributes over addition{of}",
    "add_smul": "Scalar multiplication distributes over addition of scalars{of}",
    "mul_one": "One is a right unit for multiplication{of}",
    "one_mul": "One is a left unit for multiplication{of}",
    "ext_iff": "Extensionality criterion{of}",
    "ext": "Extensionality{of}",
    "le_iff": "Characterization of the order{of}",
    "le_def": "Definition of the order{of}",
    "le_refl": "Reflexivity of the order{of}",
    "le_trans": "Transitivity of the order{of}",
    "le_antisymm": "Antisymmetry of the order{of}",
    "bot_le": "The bottom element lies below everything{of}",
    "le_top": "Everything lies below the top element{of}",
    "hom_inv_id": "A morphism followed by its inverse is the identity{of}",
    "inv_hom_id": "The inverse followed by the morphism is the identity{of}",
    "coe_mk": "Coercion of a constructed element{of}",
    "mk_eq": "Equality of constructed elements{of}",
    "refl": "Reflexivity{of}",
    "symm": "Symmetry{of}",
    "trans": "Transitivity{of}",
    "irrel": "Proof irrelevance{of}",
}


def pattern_title(atoms: list[str], ctx: Ctx) -> str | None:
    leaf = "_".join(atoms)
    of = f" for {ctx.subj_plural}" if ctx.subject else ""
    if leaf in LEAF_PATTERN:
        return LEAF_PATTERN[leaf].replace("{of}", of)
    # f_le_f_of_le : monotonicity of f
    m = re.fullmatch(r"(\w+?)_(le|lt)_\1_of_\2", leaf)
    if m:
        return f"{'Monotonicity' if m.group(2) == 'le' else 'Strict monotonicity'} of {the(noun_seq(m.group(1).split('_'), ctx))}"
    m = re.fullmatch(r"(\w+?)_eq_true_iff", leaf) or re.fullmatch(r"(\w+?)_iff_eq_true", leaf)
    if m:
        return f"The Boolean {noun_seq(m.group(1).split('_'), ctx)} check returns true exactly when the property holds"
    m = re.fullmatch(r"(\w+?)_eq_true", leaf)
    if m:
        return f"The Boolean {noun_seq(m.group(1).split('_'), ctx)} check returns true"
    m = re.fullmatch(r"(\w+?)_le_one_(?:of_)?(\w+?)_le_one", leaf)
    if m:
        return (
            f"{cap(the(noun_seq(m.group(1).split('_'), ctx)))} is at most one when "
            f"{the(noun_seq(m.group(2).split('_'), ctx))} is at most one"
        )
    # F_id / F_comp for maps: functoriality
    if len(atoms) == 2 and re.search(r"(?:Map|^map)$", atoms[0]):
        if atoms[1] in ("id", "identity", "refl"):
            return f"{cap(the(noun(atoms[0], ctx.subject)))} preserves identities"
        if atoms[1] in ("comp", "trans"):
            return f"{cap(the(noun(atoms[0], ctx.subject)))} preserves composition"
    # property in the middle, trailing arguments: X_coassoc_one
    rng = range(len(atoms) - 2, 0, -1) if not set(atoms) & {"of", "le", "eq", "lt", "iff"} else range(0)
    for k in rng:
        a = atoms[k]
        tail = atoms[k + 1 :]
        if a in PROPERTY_SUFFIX and a not in ("eq", "le", "ne", "iff", "apply", "app") and tail and all(
            t in ARG_FORM or t.isdigit() for t in tail
        ):
            base = fill(PROPERTY_SUFFIX[a], the(noun_seq(atoms[:k], ctx)))
            return base + ", at " + join_and([ARG_FORM.get(t, t) for t in tail])
    # `X_apply_Y`: action of X on Y
    if "apply" in atoms[1:-1]:
        k = atoms.index("apply")
        return f"Action of {the(noun_seq(atoms[:k], ctx))} on {join_and([arg_form(t, ctx.subject) for t in atoms[k + 1 :]])}"
    return None


def theorem_title(ctx: Ctx) -> str:
    leaf = ctx.leaf
    key = f"{ctx.subject}.{leaf}" if ctx.subject else leaf
    for k in (key, leaf, ctx.d["name"]):
        if k in TITLE_OVERRIDE:
            return TITLE_OVERRIDE[k]
    st = structural_title(ctx)
    if st:
        return st
    et = equation_title(ctx)
    if et:
        return et

    atoms = [a for a in leaf.split("_") if a]
    if atoms and atoms[0] == "of" and len(atoms) > 1:
        who = ctx.subj_noun or "the construction"
        return f"{cap(with_article(who))} obtained from {with_article(noun_seq(atoms[1:], ctx))}"
    pt = pattern_title(atoms, ctx)
    if pt:
        return pt
    if len(atoms) >= 4 and all(re.fullmatch(r"[a-z0-9]+", a) for a in atoms) and not (
        set(atoms) & {"of", "eq", "le", "lt", "iff", "ne", "preserves"} or set(atoms) & set(VERB_ATOM)
    ):
        words = [noun(a, ctx.subject) for a in atoms]
        txt = " ".join(words)
        txt = re.sub(r"^n qubit", "N-qubit", txt)
        return cap(f"the {txt}")
    # of-hypotheses
    segs: list[list[str]] = [[]]
    for a in atoms:
        if a == "of" and segs[-1]:
            segs.append([])
        else:
            segs[-1].append(a)
    concl, hyps = segs[0], segs[1:]
    side = ""
    if len(concl) > 1 and concl[-1] in ("left", "right") and ctx.subject != "OSplit":
        side = f", in the {concl[-1]} argument"
        concl = concl[:-1]
    if len(hyps) == 1 and len(concl) >= 2 and concl[-1] in ("eq", "congr") and hyps[0]:
        subj = the(noun_seq(concl[:-1], ctx))
        rel = noun_seq(hyps[0], ctx)
        return f"{cap(subj)} respects {rel}"
    t = conclusion_title(concl, ctx) + side
    if hyps:
        hp = [hyp_phrase(h, ctx) for h in hyps if h]
        hp = [x if x.startswith("assuming") else "when " + x for x in hp]
        t += ", " + " and ".join(hp)
    return t


def conclusion_title(atoms: list[str], ctx: Ctx) -> str:
    ns = ctx.subject
    if not atoms:
        return cap(ctx.subj_noun or "the statement")
    # subject_verb_object
    for k, a in enumerate(atoms):
        if a in VERB_ATOM and k > 0:
            subj = the(compound_noun(atoms[:k], ctx))
            obj = atoms[k + 1 :]
            verb = VERB_ATOM[a]
            tail = ""
            if obj:
                tail = " " + VERB_OBJ.get(a, "for") + " " + join_and([noun(o, ns) for o in obj])
            return f"{cap(subj)} {verb}{tail}"
    # preserves_X
    if "preserves" in atoms:
        k = atoms.index("preserves")
        subj = subject_phrase(atoms[:k], ctx, plural_ok=False)
        obj = noun_seq(atoms[k + 1 :], ctx) or "the structure"
        return f"{cap(the(subj))} preserves {the(obj)}"
    # relation atoms
    for rel in ("eq", "le", "lt", "ne", "iff"):
        if rel in atoms:
            k = atoms.index(rel)
            left, right = atoms[:k], atoms[k + 1 :]
            if tuple(atoms[-2:]) in TWO_ATOM and k == len(atoms) - 2:
                break
            if not right:
                subj = subject_phrase(left, ctx, plural_ok=False)
                return fill(PROPERTY_SUFFIX.get(rel, "Formula for {s}"), the(subj))
            rtxt = noun_seq(right, ctx) if len(right) > 1 else arg_form(right[0], ns)
            if not left:
                if ns == "OSplit":
                    ltxt = "the split context"
                elif ctx.subj_noun:
                    ltxt = the(ctx.subj_noun)
                else:
                    return f"Equality with {rtxt}"
            else:
                ltxt = the(noun_seq(left, ctx))
            verb = {
                "eq": "equals", "le": "is bounded by", "lt": "is strictly below",
                "ne": "differs from", "iff": "holds exactly when",
            }[rel]
            if rel == "eq" and len(right) > 1:
                rtxt = the(rtxt)
            return f"{cap(ltxt)} {verb} {rtxt}"
    # two-atom property suffix
    if len(atoms) >= 2 and tuple(atoms[-2:]) in TWO_ATOM:
        subj = subject_phrase(atoms[:-2], ctx, plural_ok=False)
        return fill(TWO_ATOM[tuple(atoms[-2:])], the(subj))
    last = atoms[-1]
    if last in PROPERTY_SUFFIX and (len(atoms) > 1 or ctx.subject):
        subj = subject_phrase(atoms[:-1], ctx)
        subj = subj if not atoms[:-1] else the(subj)
        return fill(PROPERTY_SUFFIX[last], subj)
    phrase = noun_seq(atoms, ctx)
    if ctx.subject and ctx.subj_noun and ctx.subj_noun.split()[-1] not in phrase:
        phrase += f" for {ctx.subj_plural}"
    return cap(phrase)


def def_title(ctx: Ctx) -> str:
    leaf = ctx.leaf
    key = f"{ctx.subject}.{leaf}" if ctx.subject else leaf
    for k in (key, leaf):
        if k in TITLE_OVERRIDE:
            return TITLE_OVERRIDE[k]
    if "_" in leaf.strip("_"):
        atoms = [a for a in leaf.split("_") if a]
        segs: list[list[str]] = [[]]
        for a in atoms:
            if a == "of" and segs[-1]:
                segs.append([])
            else:
                segs[-1].append(a)
        nm = noun_seq(segs[0], ctx)
        hp = [hyp_phrase(h, ctx) for h in segs[1:] if h]
        hp = [x if x.startswith("assuming") else "when " + x for x in hp]
        return f"Definition of {the(nm)}" + (", " + " and ".join(hp) if hp else "")
    nm = noun(leaf, ctx.subject)
    if ctx.subject and ctx.subj_noun and leaf in CONSTANT_LEAF:
        return f"Definition of {the(ctx.subj_noun)} of {ARG_FORM.get(leaf) or the(nm)}"
    if ctx.subject and ctx.subj_noun and ctx.subj_noun.split()[-1] not in nm:
        nm += f" of {ctx.subj_plural}" if leaf[:1].islower() else ""
    return f"Definition of {the(nm)}"


CONSTANT_LEAF = {
    "x", "h", "t", "cx", "ry", "new0", "new1", "reset", "measure", "zero", "one", "unit",
    "bit", "qubit", "id", "identity", "bot", "top", "empty", "swap", "copy", "discard",
}


def instance_class(ctx: Ctx) -> tuple[str, str]:
    t = " ".join((ctx.parsed.type or "").split())
    toks = split_app(t)
    if not toks:
        return "", ""
    cls = toks[0].split(".")[-1]
    target = " ".join(toks[1:])
    return cls, target


def instance_title(ctx: Ctx) -> str:
    cls, target = instance_class(ctx)
    cn = CLASS_NOUN.get(cls, cap(noun(cls)) if cls else "Canonical structure")
    tt = split_app(target)
    tgt = ""
    if cls == "Decidable" and target:
        inner = split_app(strip_parens(target))
        tgt = noun(inner[0]) if inner else ""
        return clean_title(f"Decidability of {tgt}")
    if tt:
        h = strip_parens(tt[0])
        h_toks = split_app(h)
        tgt = noun(h_toks[0]) if h_toks else noun(h)
        if len(tt) == 1 and h_toks and len(h_toks) > 1:
            tgt = noun(h_toks[0])
        m = re.match(r"^\((.+)\)\.Atom$", target) or re.match(r"^(.+)\.Atom$", target)
        if m:
            inner = split_app(strip_parens(m.group(1)))
            tgt = "atoms of " + with_article(noun(inner[0])) if inner else "atoms"
    if not tgt:
        tgt = noun(ctx.leaf)
    else:
        tgt = plural(tgt) if not tgt.startswith("atoms") else tgt
    return clean_title(f"{cn} on {tgt}")


def english_title(d: dict) -> str:
    ctx = ctx_of(d)
    doc = (d.get("docstring") or "").strip()
    if doc:
        h = doc_headline(doc, ctx.subject)
        if h and not is_codey(h):
            return h
    kind = d["kind"]
    if kind in ("theorem", "lemma", "example"):
        t = theorem_title(ctx)
    elif kind in ("def", "abbrev"):
        t = def_title(ctx)
    elif kind == "instance":
        t = instance_title(ctx)
    elif kind == "structure":
        t = f"The structure of {with_article(noun(ctx.leaf, ctx.subject))}"
    elif kind == "class":
        t = f"The interface of {plural(noun(ctx.leaf, ctx.subject))}"
    elif kind == "inductive":
        t = f"The inductive definition of {plural(noun(ctx.leaf, ctx.subject))}"
    else:
        t = noun(ctx.leaf)
    t = clean_title(t)
    if is_codey(t):
        t = clean_title(de_code(t, ctx))
    return t


def de_code_text(t: str) -> str:
    """Context-free version of de_code, for prose outside the cards."""
    t = re.sub(r"`([^`]*)`", lambda m: gloss_backticks(m.group(0), None), t)
    t = re.sub(r"[A-Za-z][\w']*(?:\.[A-Za-z][\w']*)+", lambda m: noun(m.group(0)), t)
    t = re.sub(r"\b[A-Za-z]*[a-z][A-Z][\w']*\b",
               lambda m: m.group(0) if m.group(0) in PROPER_CAMEL else noun(m.group(0)), t)
    return re.sub(r"(?<=\w)_(?=\w)", " ", t)


def de_code(t: str, ctx: Ctx) -> str:
    t = re.sub(r"`([^`]*)`", lambda m: noun(m.group(1), ctx.subject), t)
    t = re.sub(r"[A-Za-z][\w']*(?:\.[A-Za-z][\w']*)+", lambda m: noun(m.group(0)), t)
    t = re.sub(r"\b[A-Za-z]*[a-z][A-Z][\w']*\b", lambda m: noun(m.group(0)), t)
    t = t.replace("_", " ")
    return t


# ==========================================================================
# Statements
# ==========================================================================

def data_intro(binders: list[Binder]) -> str:
    bucket: dict[str, list[str]] = {}
    for b in binders:
        if b.bracket == "[" or not b.names or not b.type:
            continue
        if is_prop_type(b.type, b.names):
            continue
        tn = type_noun(b.type)
        if not tn:
            continue
        bucket.setdefault(tn, []).extend(b.names)
    groups: list[str] = []
    for tn, names_ in bucket.items():
        names = ", ".join(f"`{n}`" for n in names_)
        groups.append(f"{plural(tn) if len(names_) > 1 else with_article(tn)} {names}")
    if not groups or len(groups) > 4:
        return ""
    return "For " + ", ".join(groups) + ": "


def theorem_statement(ctx: Ctx) -> str:
    p = ctx.parsed
    if not p.type:
        return ""
    extra, premises, concl = decompose_claim(p.type)
    binders = p.binders + extra
    hyps = []
    for b in binders:
        if b.bracket in "({⦃" and is_prop_type(b.type, b.names):
            hyps.append(prop_english(b.type or "", ctx))
    hyps += [prop_english(x, ctx) for x in premises]
    c = prop_english(concl, ctx)
    eq_i, _ = find_top(strip_parens(concl), (" = ",))
    if eq_i >= 0:
        cc = strip_parens(concl)
        le, re_ = describe(cc[:eq_i], ctx), describe(cc[eq_i + 3 :], ctx)
        if not (le.startswith("`") and re_.startswith("`")) and not (
            le.startswith("an explicit") and re_.startswith("an explicit")
        ):
            c = f"{le} equals {re_}"
    intro = data_intro(binders)
    if hyps:
        hs = hyps[:4]
        joined = " and ".join(hs) if len(hs) <= 2 else "; ".join(hs[:-1]) + "; and " + hs[-1]
        body = "if " + joined + ", then " + c
    else:
        body = c
    s = cap(intro + body) if not intro else intro + body
    if len(s) > 420:
        k = len(split_top(strip_parens(concl), "∧"))
        what = f"{k} properties" if k > 1 else "a single property"
        lead = f"under {len(hyps)} hypotheses, " if hyps else ""
        s = cap(f"{intro}{lead}the statement asserts {what} of the objects involved; "
                "the precise formulation is the Lean statement below")
    return cap(s).rstrip(".") + "."


def formal_line(ctx: Ctx) -> str:
    p = ctx.parsed
    if not p.type:
        return ""
    _, premises, concl = decompose_claim(p.type)
    shown = " → ".join([*premises, concl]) if premises else concl
    c = code(shown, 110)
    return f" Formally: {c}." if c else ""


def statement_english(d: dict) -> str:
    ctx = ctx_of(d)
    doc = (d.get("docstring") or "").strip()
    kind = d["kind"]
    if doc:
        paras = [re.sub(r"\s+", " ", x).strip() for x in doc.split("\n\n") if x.strip()]
        text = " ".join(paras[:2])
        if not text.endswith((".", "!", "?")):
            text += "."
        if kind in ("theorem", "lemma"):
            text += formal_line(ctx)
        return text
    if kind in ("theorem", "lemma", "example"):
        s = theorem_statement(ctx) or "The stated property holds."
        if "`" not in s or len(s) < 60:
            s += formal_line(ctx)
        return s
    if kind in ("def", "abbrev"):
        return def_statement(ctx)
    if kind == "instance":
        cls, target = instance_class(ctx)
        cn = CLASS_NOUN.get(cls, noun(cls)).lower()
        tgt = code(target, 60)
        return f"Equip {tgt or 'the type'} with its canonical {cn}."
    if kind == "structure":
        return f"A structure bundling the data of {with_article(noun(ctx.leaf, ctx.subject))}."
    if kind == "class":
        return f"An interface for {plural(noun(ctx.leaf, ctx.subject))}."
    if kind == "inductive":
        return f"The inductive family of {plural(noun(ctx.leaf, ctx.subject))}."
    return "Declared as stated."


def type_phrase(t: str) -> str | None:
    one = " ".join(t.split())
    toks = split_app(one)
    if not toks:
        return None
    head = toks[0].split(".")[-1]
    if head in ("Superoperator", "CPMap", "QuantumRel", "Hom", "KrausFamily", "ComonoidHom") and len(toks) == 3:
        a, b = code(toks[1], 30), code(toks[2], 30)
        if a and b:
            return f"{with_article(TYPE_NS.get(head, (noun(head),))[0])} from {a} to {b}"
    tn = type_noun(one)
    if tn:
        return with_article(tn)
    if find_top(one, ("→",))[0] >= 0:
        c = code(one, 60)
        return f"a function of type {c}" if c else "a function"
    if head in TYPE_NS:
        return with_article(TYPE_NS[head][0])
    c = code(one, 60)
    return f"an element of {c}" if c else None


def def_statement(ctx: Ctx) -> str:
    p = ctx.parsed
    nm = the(noun(ctx.leaf, ctx.subject))
    typ = " ".join((p.type or "").split())
    data = [n for b in p.binders if b.bracket == "(" and not is_prop_type(b.type, b.names) for n in b.names]
    if data and len(data) <= 3:
        nm += " of " + join_and([f"`{n}`" for n in data])
    if typ == "Prop" or typ.endswith("→ Prop"):
        return cap(f"{nm} is a proposition-valued predicate, defined below.")
    tp = type_phrase(typ) if typ else None
    if tp:
        return cap(f"{nm} is {tp}.")
    return cap(f"{nm} is introduced by the definition below.")


# ==========================================================================
# Proofs
# ==========================================================================

def hyp_env(ctx: Ctx) -> dict[str, str]:
    """Binder name → type, for hypotheses and data alike."""
    env: dict[str, str] = {}
    p = ctx.parsed
    extra = decompose_claim(p.type)[0] if p.type else []
    for b in p.binders + extra:
        for n in b.names:
            if b.type:
                env[n] = b.type
    return env


def reference_gloss(ref: str, ctx: Ctx, env: dict[str, str]) -> str | None:
    ref = ref.strip().lstrip("←").strip()
    ref = re.split(r"\s", ref)[0] if ref else ref
    if not ref or ref in ("*", "_", "this", "ih", "hd", "tl"):
        return None
    if ref not in env and (re.fullmatch(r"h[\w'₀-₉]{0,4}", ref) or re.fullmatch(r"[a-z][\w'₀-₉]?", ref)):
        return None
    base = ref.split(".")[0]
    if base in env:
        t = env[base]
        if is_prop_type(t, [base]):
            return "the hypothesis that " + prop_english(t, ctx)
        return None
    target = resolve(ref, ctx)
    if target is not None:
        tctx = ctx_of(target)
        if target["kind"] in ("def", "abbrev", "inductive", "structure"):
            return "the definition of " + the(noun(tctx.leaf, tctx.subject))
        if target is ctx.d:
            return None
        return fact_phrase(english_title(target))
    # Mathlib or core lemma.
    if not re.fullmatch(r"[\w.'₀-₉]+", ref):
        return None
    parts = ref.split(".")
    owner = parts[0] if len(parts) > 1 else None
    leaf = parts[-1]
    if ref in MATHLIB_GLOSS:
        return MATHLIB_GLOSS[ref]
    if leaf in MATHLIB_GLOSS:
        return MATHLIB_GLOSS[leaf]
    if leaf[:1].isupper() and not owner:
        return "the definition of " + the(noun(leaf))
    area = MATHLIB_AREA.get(owner or "")
    if area:
        return f"standard identities for {area}"
    if re.search(r"(?:^|_)(?:mul|add|sub|smul|neg|one|zero|pow|inv|div)(?:_|$)", leaf):
        return "the usual algebraic identities"
    return None


MATHLIB_AREA = {
    "List": "lists", "Matrix": "matrices", "Finset": "finite sums", "Nat": "natural numbers",
    "Fin": "finite indices", "Option": "options", "Function": "functions", "Equiv": "equivalences",
    "Complex": "complex numbers", "Real": "real numbers", "Set": "sets", "Submodule": "submodules",
    "Bool": "Booleans", "Prod": "products", "Sum": "disjoint unions", "Fintype": "finite types",
    "Mem": "list membership", "Finsupp": "finitely supported functions", "Multiset": "multisets",
    "LinearMap": "linear maps", "Module": "modules", "HasSum": "infinite sums", "tsum": "infinite sums",
    "Summable": "infinite sums", "Filter": "limits", "Real.sqrt": "square roots", "NNReal": "nonnegative reals",
    "Equiv.Perm": "permutations", "Quotient": "quotients", "Subtype": "subtypes",
}

MATHLIB_GLOSS = {
    "le_antisymm": "antisymmetry of the order",
    "le_refl": "reflexivity of the order",
    "le_trans": "transitivity of the order",
    "funext": "function extensionality",
    "congrArg": "congruence of function application",
    "congr_arg": "congruence of function application",
    "Finset.sum_comm": "interchange of finite sums",
    "Finset.sum_congr": "termwise equality of finite sums",
    "Finset.mul_sum": "distributivity of multiplication over finite sums",
    "Finset.sum_mul": "distributivity of multiplication over finite sums",
    "Matrix.trace_mul_comm": "cyclicity of the trace",
    "Matrix.mul_assoc": "associativity of matrix multiplication",
    "mul_assoc": "associativity of multiplication",
    "mul_comm": "commutativity of multiplication",
    "add_comm": "commutativity of addition",
    "Matrix.conjTranspose_mul": "the adjoint of a product",
    "List.map_append": "the fact that mapping distributes over concatenation",
    "List.replicate_succ": "the recursion equation for constant lists",
    "List.Mem.head": "membership at the head of a list",
    "List.Mem.tail": "membership in the tail of a list",
    "Subsingleton.elim": "the fact that proofs of a proposition are all equal",
    "Nat.lt_irrefl": "irreflexivity of the order on natural numbers",
    "Option.some_injective": "injectivity of the option constructor",
    "Equiv.refl": "the identity equivalence",
    "rfl": "reflexivity of equality",
    "Iff.rfl": "reflexivity of logical equivalence",
}

SENTENCE_VERB = re.compile(
    r"\b(?:is|are|equals?|preserves?|holds?|determines?|passes|occurs?|coincide|splits?|"
    r"does|vanishes|agrees?|commutes?|respects?|compose|gives?|has|have|lies|reduces|"
    r"succeeds?|fails?|elaborates?|forces?|sends?|contains?|yields?|cannot|can)\b"
)


def fact_phrase(title: str) -> str:
    t = lower_first(title)
    for w in PROPER:
        if title.startswith(w):
            t = title
    if SENTENCE_VERB.search(t):
        return "the fact that " + t
    return the(t)


def join_and(items: list[str]) -> str:
    items = [x for x in dict.fromkeys(i for i in items if i)]
    if not items:
        return ""
    if len(items) == 1:
        return items[0]
    return ", ".join(items[:-1]) + " and " + items[-1]


def list_refs(block: str) -> list[str]:
    return [x.strip() for x in split_top(block, ",") if x.strip()]


def tools_used(script: str, ctx: Ctx, env: dict[str, str]) -> list[str]:
    """Named facts the script rewrites / simplifies / applies with."""
    refs: list[str] = []
    for m in re.finditer(r"\b(?:rw|rewrite|simp_rw|simp only|simp|simpa|dsimp|dsimp only|unfold|norm_num|field_simp|erw)\s*\[([^\]]*)\]", script):
        refs.extend(list_refs(m.group(1)))
    for m in re.finditer(r"\bunfold\s+([\w.' ]+)", script):
        refs.extend(m.group(1).split())
    for m in re.finditer(r"\b(?:exact|apply|refine|exact_mod_cast|convert)\s+\(?@?([A-Za-z][\w.'₀-₉]*)", script):
        refs.append(m.group(1))
    glosses = []
    for r in refs[:12]:
        g = reference_gloss(r, ctx, env)
        if g and g not in glosses:
            glosses.append(g)
    return glosses[:4]


def closing_phrase(script: str) -> str | None:
    s = script
    if re.search(r"\bomega\b", s):
        return "the remaining arithmetic on natural numbers is linear and is settled by a decision procedure"
    if re.search(r"\bring(?:_nf)?\b", s):
        return "the remaining identity is a polynomial identity in a commutative ring"
    if re.search(r"\b(?:linarith|nlinarith)\b", s):
        return "the remaining inequalities follow by linear arithmetic"
    if re.search(r"\bpositivity\b", s):
        return "the remaining positivity goals are immediate"
    if re.search(r"\bnorm_num\b", s):
        return "the remaining numerical facts are checked by direct computation"
    if re.search(r"\b(?:decide|native_decide)\b", s):
        return "the claim is decidable and is checked by exhaustive evaluation"
    if re.search(r"\bfin_cases\b", s):
        return "every finite index is checked separately"
    return None


@dataclass
class Arm:
    ctors: list[str]
    body: str


def inline_arms(src: str) -> str:
    """Put `| c => t | d => u` written on one line onto separate lines."""
    first, _, rest = src.partition("\n")
    if "=>" not in first or not first.strip().startswith("|"):
        return src
    out, cur, seen_arrow = [], "", False
    i = 0
    dm = depth_map(first)
    while i < len(first):
        if first[i] == "|" and dm[i] == 0 and seen_arrow:
            out.append(cur.rstrip())
            cur, seen_arrow = "", False
        if first.startswith("=>", i):
            seen_arrow = True
        cur += first[i]
        i += 1
    out.append(cur.rstrip())
    return "\n".join(x.strip() for x in out) + ("\n" + rest if rest else "")


def parse_arms(script: str) -> list[Arm]:
    script = inline_arms(script.lstrip(" "))
    arms: list[Arm] = []
    cur: Arm | None = None
    base = None
    for line in script.splitlines():
        s = line.strip()
        ind = len(line) - len(line.lstrip())
        if s.startswith("|") and (base is None or ind <= base):
            base = ind if base is None else base
            head, _, rest = s.partition("=>")
            ctors = [c.strip().split()[0].lstrip(".@") for c in head.split("|") if c.strip()]
            cur = Arm(ctors, rest.strip())
            arms.append(cur)
        elif cur is not None:
            cur.body += "\n" + line
    return arms


def arm_summary(arm: Arm, ctx: Ctx, env: dict[str, str]) -> tuple[str, str | None]:
    b = arm.body.strip()
    one = " ".join(b.split())
    uses_ih = bool(re.search(r"\bih\w*\b", one))
    m = re.fullmatch(r"(?:simp[^;]*?\bat\s+(\S+)|cases\s+(\S+)|nomatch\s+(\S+)|contradiction|exact absurd .*|exact (\S+)\.elim)", one)
    if m and not uses_ih:
        h = next((g for g in m.groups() if g), None)
        if h and h in env:
            return "impossible", "it contradicts the hypothesis that " + prop_english(env[h], ctx)
        return "impossible", None
    if re.fullmatch(r"(?:rfl|trivial|exact rfl|exact \.nil|exact ⟨rfl, rfl⟩|exact \.\w+|simp|decide|exact ⟨⟩|⟨⟩|rfl\s*)", one):
        return "immediate", None
    pm = re.fullmatch(r"exact (\w[\w'₀-₉]*)", one)
    if pm and pm.group(1) not in env:
        return "premise", None
    cm = re.fullmatch(r"exact \.(\w+) \(?ih\w*[^)]*\)?", one)
    if cm:
        return "rebuild", cm.group(1)
    if uses_ih:
        return "ih", None
    return "direct", None


def induction_explanation(script: str, ctx: Ctx, env: dict[str, str]) -> str | None:
    m = re.search(r"\b(induction|cases|rcases|match)\s+([^\s,]+)(?:\s+generalizing\s+[^\n]*?)?\s+with\b", script)
    if not m:
        m2 = re.match(r"\s*(induction|cases)\s+(\S+)\s*(?:$|\n|<;>)", script)
        if not m2:
            return None
        m = m2
    kind, var = m.group(1), m.group(2)
    t = env.get(var)
    ind = None
    what = f"`{var}`"
    if t:
        head = split_app(strip_parens(t))[0].split(".")[-1] if split_app(t) else ""
        ind = head
        if is_prop_type(t, [var]):
            what = "the derivation that " + prop_english(t, ctx)
        else:
            tn = type_noun(t)
            what = f"the {tn} `{var}`" if tn else f"`{var}`"
            if t.startswith("List"):
                ind = "List"
            elif t in ("ℕ", "Nat"):
                ind = "Nat"
    verb = "induction on" if kind == "induction" else "case analysis on"
    lead = f"By {verb} {what}."
    arms = parse_arms(script[m.end():])
    if not arms:
        return lead
    groups: dict[str, list[tuple[str, str | None]]] = {}
    order: list[str] = []
    for a in arms:
        kind_s, extra = arm_summary(a, ctx, env)
        key = kind_s + "|" + (extra or "")
        if key not in groups:
            groups[key] = []
            order.append(key)
        for c in a.ctors:
            groups[key].append((c, extra))
    sentences = []
    for key in order:
        kind_s, _, extra = key.partition("|")
        cases = join_and([ctor_gloss(c, ind) for c, _ in groups[key]])
        plural_s = len(groups[key]) > 1
        noun_c = "cases" if plural_s else "case"
        if kind_s == "immediate":
            sentences.append(f"the {noun_c} of {cases} {'are' if plural_s else 'is'} immediate")
        elif kind_s == "impossible":
            why = f", since {extra}" if extra else ""
            sentences.append(f"the {noun_c} of {cases} cannot occur{why}")
        elif kind_s == "rebuild":
            same = all(c == extra for c, _ in groups[key])
            rule = "the same rule" if same else f"the rule for {ctor_gloss(extra, ind)}"
            sentences.append(f"for {cases}, applying {rule} to the induction hypothesis gives the claim")
        elif kind_s == "premise":
            if len(arms) == 1:
                sentences.append(
                    f"only the rule for {cases} can produce it, and the claim is one of that rule's premises"
                )
            else:
                sentences.append(f"for {cases}, the claim is one of the premises of the rule")
        elif kind_s == "ih":
            sentences.append(f"for {cases}, the claim follows from the induction hypothesis")
        else:
            sentences.append(f"for {cases}, the claim is checked directly")
    sentences = [lower_first(x) if not x.startswith("`") else x for x in sentences]
    return lead + " " + cap("; ".join(sentences)) + "."


def by_explanation(script: str, ctx: Ctx) -> str:
    env = hyp_env(ctx)
    s = script.strip()
    one = " ".join(s.split())
    if one in ("congr", "congr 1", "rfl_congr"):
        return (
            "Both sides apply the same construction to arguments that can differ only in "
            "proofs of the same proposition; since any two such proofs are equal, the two "
            "sides coincide by congruence."
        )
    if one in ("rfl", "exact rfl", "simp", "decide", "trivial", "norm_num", "ext; rfl"):
        if one == "simp":
            return "Both sides simplify to the same expression using the defining equations of the objects involved."
        if one in ("decide", "norm_num"):
            return "The claim is a finite computation and is checked by evaluating it."
        return definitional(ctx)
    parts: list[str] = []
    ind = induction_explanation(s, ctx, env)
    if ind:
        parts.append(ind)
    else:
        if re.search(r"\b(?:ext|funext)\b", s):
            parts.append("Both sides are compared pointwise (by extensionality).")
        if re.search(r"\bapply le_antisymm\b|\ble_antisymm\b", s):
            parts.append("Equality is proved by showing both inequalities.")
        if re.search(r"\bcalc\b", s):
            parts.append("The claim follows from a chain of equalities (or inequalities).")
        if re.search(r"\bconstructor\b|\brefine ⟨|\bexact ⟨", s):
            parts.append("Each component of the claim is established separately.")
        if re.search(r"\bby_cases\b|\bsplit_ifs\b|\bsplit\b", s):
            parts.append("The argument splits on the relevant condition.")
        if re.search(r"\b(?:cases|rcases|obtain)\b", s):
            parts.append("The hypotheses are unpacked into their constituent data.")
        if re.search(r"\binduction\b", s):
            parts.append("The argument proceeds by induction.")
        if re.search(r"\bsubst\b", s):
            parts.append("An equation between variables is used to substitute one for the other.")
    tools = tools_used(s, ctx, env)
    if tools:
        if re.search(r"\b(?:rw|simp_rw|rewrite)\b", s):
            parts.append(f"The key step rewrites with {join_and(tools)}.")
        elif re.search(r"\b(?:simp|simpa|dsimp)\b", s):
            parts.append(f"The goal is simplified using {join_and(tools)}.")
        else:
            parts.append(f"It follows from {join_and(tools)}.")
    elif re.search(r"\bsimp\b|\bsimpa\b", s) and not ind:
        parts.append("The goal is closed by simplification with the defining equations.")
    lines_ = [x for x in s.splitlines() if x.strip()]
    cl = closing_phrase(lines_[-1] if len(lines_) > 3 else s) if lines_ else None
    if cl:
        parts.append(cap(cl) + ".")
    if not parts:
        return "The claim follows directly from the definitions of the objects involved."
    return " ".join(dict.fromkeys(parts))


def definitional(ctx: Ctx) -> str:
    """Explain an `rfl` proof by describing both sides."""
    p = ctx.parsed
    if not p.type:
        return "Both sides are equal by definition."
    _, _, concl = decompose_claim(p.type)
    i, _ = find_top(concl, (" = ",))
    if i < 0:
        i2, _ = find_top(concl, (" ↔ ",))
        if i2 >= 0:
            return "Both sides are the same proposition once the definitions are unfolded."
        return "The statement holds by unfolding the definitions."
    lhs, rhs = concl[:i].strip(), concl[i + 3 :].strip()
    lt = split_app(lhs)
    head = lt[0] if lt else ""
    target = resolve(head, ctx) if head else None
    lhs_e = describe(lhs, ctx)
    rhs_e = describe(rhs, ctx)
    if target is not None and target["kind"] in ("def", "abbrev"):
        tctx = ctx_of(target)
        fn = the(noun(tctx.leaf, tctx.subject))
        clause = None
        if tctx.parsed.body and len(lt) >= 2:
            want = strip_parens(lt[1]).split()[0]
            for line in tctx.parsed.body.splitlines():
                mm = re.match(r"\s*\|\s*(\S+)[^=]*=>\s*(.+)", line)
                if mm and mm.group(1) == want:
                    clause = mm.group(2).strip()
                    break
        if clause is not None:
            same = pretty(clause) == pretty(rhs)
            return (
                f"By definition. The left-hand side is {lhs_e}; {fn} is defined by cases, and "
                f"its defining clause for {ctor_gloss(want, tctx.subject)} returns "
                f"{term_english(clause, tctx)}"
                + (", which is literally the right-hand side" if same else
                   f", which reduces to the right-hand side {rhs_e}")
                + ". No computation beyond unfolding this clause is needed."
            )
        return (
            f"By definition. Unfolding {fn} turns the left-hand side, {lhs_e}, into the "
            f"right-hand side, {rhs_e}; the two sides are the same term."
        )
    return (
        f"By definition: the left-hand side, {lhs_e}, and the right-hand side, {rhs_e}, "
        f"unfold to the same term."
    )


def term_proof_explanation(body: str, ctx: Ctx) -> str:
    env = hyp_env(ctx)
    b = " ".join(body.split())
    if b in ("rfl", "Iff.rfl", "HEq.rfl"):
        return definitional(ctx)
    if b in ("trivial", "True.intro", "⟨⟩"):
        return "The statement is trivially true."
    if b.startswith("⟨"):
        return "The witness is assembled directly from its components" + (
            f", using {join_and(tools_used('exact ' + b[1:], ctx, env))}." if tools_used('exact ' + b[1:], ctx, env) else "."
        )
    if b.startswith("fun ") or b.startswith("λ"):
        inner = tools_used("exact " + b.split("=>", 1)[-1].strip(), ctx, env)
        return "Given the data, the conclusion is produced directly" + (
            f" from {join_and(inner)}." if inner else "."
        )
    pm = re.fullmatch(r"([\w'₀-₉]+)((?:\.\d)+)", b)
    if pm and pm.group(1) in env:
        which = {"1": "first", "2": "second"}
        path = pm.group(2).split(".")[1:]
        pos = "the last" if path[-1] == "2" and len(path) > 1 else which.get(path[-1], "a")
        return (
            f"The hypothesis that {prop_english(env[pm.group(1)], ctx)} unfolds to a conjunction, "
            f"and the claim is {pos} of its components."
        )
    if b.startswith("."):
        ctor = b[1:].split()[0]
        return f"Built directly by the {ctor_gloss(ctor, ctx.subject)} rule."
    # dot-chains and applications: hs.symm.eq_right_of_allNone_left h₂
    toks = split_app(b)
    if toks:
        head = toks[0]
        chain = head.split(".")
        glosses: list[str] = []
        if chain[0] in env and len(chain) > 1:
            t = env[chain[0]]
            owner = split_app(strip_parens(t))[0].split(".")[-1] if split_app(t) else ""
            for step in chain[1:]:
                tgt = resolve(f"{owner}.{step}", ctx) or resolve(step, ctx)
                if tgt is not None and tgt is not ctx.d:
                    glosses.append(lower_first(english_title(tgt)))
            args = [a for a in toks[1:] if a in env]
            hyp = [f"the hypothesis that {prop_english(env[a], ctx)}" for a in args if is_prop_type(env[a], [a])]
            if glosses:
                txt = "Apply, in order, " + join_and([f"“{g}”" for g in glosses])
                txt += f" to the hypothesis that {prop_english(t, ctx)}"
                if hyp:
                    txt += f", together with {join_and(hyp)}"
                return txt + "."
        g = reference_gloss(head, ctx, env)
        if g:
            rest = [reference_gloss(a, ctx, env) for a in toks[1:]]
            rest = [r for r in rest if r]
            return f"This is an instance of {g}" + (f", applied to {join_and(rest)}" if rest else "") + "."
    return "The proof term combines the facts named in it directly."


def ingredient_nouns(body: str, ctx: Ctx, limit: int = 4) -> list[str]:
    """English names of the main named constructions a body is built from."""
    out: list[str] = []
    skip = {"fun", "match", "with", "if", "then", "else", "let", "have", "show", "by", "in",
            "rfl", "id", "Fin", "Nat", "true", "false", "some", "none"}
    for m in re.finditer(r"(?<![\w.'])([A-Za-z][\w']*(?:\.[A-Za-z][\w']*)*)", body):
        ident = m.group(1)
        leaf = ident.split(".")[-1]
        if leaf in skip or len(leaf) <= 2:
            continue
        if not (re.search(r"[a-z][A-Z]", leaf) or leaf in IDENT or leaf in TYPE_NS or resolve(ident, ctx)):
            continue
        n = the(noun(ident, ctx.subject))
        if n not in out:
            out.append(n)
        if len(out) >= limit:
            break
    return out


def construction_text(ctx: Ctx) -> str:
    p = ctx.parsed
    kind = ctx.d["kind"]
    body = p.body or ""
    if kind in ("def", "abbrev"):
        arms_src = body
        if p.body_kind in ("term", "") and body.lstrip().startswith("match"):
            arms_src = body.split("with", 1)[-1] if "with" in body else body
        if p.body_kind == "arms" or body.lstrip().startswith("match"):
            arms = re.findall(r"^\s*\|\s*(.+?)\s*=>\s*(.+)$", arms_src, re.MULTILINE)
            if arms:
                shown = []
                for pat, val in arms[:8]:
                    pat_s = pretty(pat)
                    val_e = describe(val, ctx)
                    shown.append(f"`{pat_s}` ↦ {val_e}")
                more = "; and so on for the remaining cases" if len(arms) > 8 else ""
                return "Defined by cases on the input: " + "; ".join(shown) + more + "."
            return "Defined by cases on the constructors of the input."
        if p.body_kind == "where" or body.lstrip().startswith("{") or body.lstrip().startswith("⟨"):
            fields = re.findall(r"^\s*(\w+)\s*:=", body, re.MULTILINE)
            if fields:
                return (
                    "Constructed by supplying each component: "
                    + join_and([noun(f) for f in fields[:8]])
                    + ("" if len(fields) <= 8 else ", among others")
                    + ". The accompanying laws are verified from the definitions."
                )
            return "Constructed by supplying each component of the structure explicitly."
        if p.body_kind == "by":
            return "Constructed interactively; " + lower_first(by_explanation(body, ctx))
        b = " ".join(body.split())
        if b.startswith("fun ") or b.startswith("λ"):
            vars_ = b[4:].split("=>", 1)[0].strip()
            res = b.split("=>", 1)[-1].strip()
            return f"The map sending {code(vars_, 40) or 'its input'} to {describe(res, ctx)}."
        if b:
            te = term_english(b, ctx)
            if te and not any(x in te for x in ("displayed", "a compound term", "case distinction")):
                return f"Defined to be {te}."
            ingredients = ingredient_nouns(b, ctx)
            if ingredients:
                return f"Defined by an explicit formula built from {join_and(ingredients)}."
            return "Defined by an explicit formula."
        return "Introduced by the definition below."
    if kind == "instance":
        fields = re.findall(r"^\s*(\w+)\s*:=", body, re.MULTILINE)
        b = " ".join(body.split())
        if "inferInstance" in b:
            return "Inherited from the corresponding structure on the underlying carrier."
        if fields:
            return (
                "The operations are given by: " + join_and([noun(f) for f in fields[:8]])
                + ". Each required law follows from the corresponding property of the underlying data."
            )
        if p.body_kind == "by":
            return by_explanation(body, ctx)
        if b:
            te = term_english(b, ctx)
            return f"Given by {te}."
        return "Given by the canonical construction on the underlying data."
    if kind == "structure":
        fields = re.findall(r"^\s+(\w+)\s*:\s*(.+)$", body, re.MULTILINE)
        if fields:
            data = [f for f, t in fields if not is_prop_type(t, [f])]
            laws = [f for f, t in fields if is_prop_type(t, [f])]
            s = "An element consists of " + join_and([f"`{f}`" for f in data[:8]] or ["its fields"])
            if laws:
                s += ", subject to the laws " + join_and([f"`{f}`" for f in laws[:6]])
            return s + "."
        return "An element consists of the listed fields."
    if kind == "class":
        return "A type belongs to the class when it supplies the listed operations and laws."
    if kind == "inductive":
        ctors = re.findall(r"^\s*\|\s*([\w']+)", body or ctx.excerpt, re.MULTILINE)
        if ctors:
            glosses = [
                f"`{c}` ({ctor_gloss(c, ctx.leaf)})" if (ctx.leaf in CTOR_GLOSS and c in CTOR_GLOSS[ctx.leaf]) else f"`{c}`"
                for c in ctors[:12]
            ]
            return (
                "Generated by the rules " + join_and(glosses)
                + ". Every element arises from finitely many applications of these rules, so "
                "properties are proved by induction over them."
            )
        return "Every element arises from finitely many applications of the constructors."
    return ""


def proof_english(d: dict) -> str:
    ctx = ctx_of(d)
    kind = d["kind"]
    p = ctx.parsed
    if kind in ("theorem", "lemma", "example"):
        if p.body_kind == "by" and p.body:
            return by_explanation(p.body, ctx)
        if p.body_kind == "term" and p.body:
            return term_proof_explanation(p.body, ctx)
        return "The claim follows from the definitions of the objects involved."
    return construction_text(ctx) or "Introduced by the definition below."


# ==========================================================================
# Cards
# ==========================================================================

LABELS = {
    "theorem": ("Statement", "Proof"),
    "lemma": ("Statement", "Proof"),
    "example": ("Statement", "Proof"),
    "def": ("Definition", "Construction"),
    "abbrev": ("Definition", "Construction"),
    "instance": ("Definition", "Construction"),
    "structure": ("Definition", "Construction"),
    "class": ("Definition", "Construction"),
    "inductive": ("Definition", "Construction"),
}


def card_markdown(d: dict) -> str:
    title = english_title(d)
    st_label, pf_label = LABELS.get(d["kind"], ("Statement", "Proof / construction"))
    rel = d["file"]
    a, b = d["start_line"], d["end_line"]
    return "\n".join(
        [
            f"#### {title}",
            "",
            f"**{st_label}.** {statement_english(d)}",
            "",
            f"**{pf_label}.** {proof_english(d)}",
            "",
            f"<!-- lean: {rel}#L{a}-L{b} -->",
            "",
        ]
    )


SPOT = (
    "QLambda.Linear.OSplit.eq_right_of_allNone_left",
    "QLambda.Linear.OSplit.eq_left_of_allNone_right",
    "QLambda.Linear.OSplit.lengths",
    "QLambda.Linear.OSplit.symm",
    "QLambda.Linear.OSplit.mem_left",
    "QLambda.Linear.Prim.superoperator",
    "QLambda.Linear.Prim.superoperator_new0",
    "QLambda.Linear.Prim.superoperator_x",
    "QLambda.Linear.Term.ite_cond",
    "QLambda.Domain.CompletedCP.ofKraus_eq_of_semEq",
    "QLambda.Domain.Presheaf.Superoperator.trace_choi_eq_trace_effect",
    "QLambda.Domain.Presheaf.CPMap.ofKraus_append",
    "QLambda.Domain.QuantumRel.uncurry_mono",
    "QLambda.Domain.Presheaf.Superoperator.tensorAssociator_inv_hom",
    "QLambda.Linear.FragmentContext.linearOSplit_proof_independent",
)


def main() -> None:
    if not DECLS.is_file():
        raise SystemExit(f"missing {DECLS}; run scripts/extract_declarations.py first")
    decls = [
        json.loads(line)
        for line in DECLS.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    for d in decls:
        parts = d["fqn"].split(".")
        for k in range(1, len(parts) + 1):
            INDEX.setdefault(".".join(parts[-k:]), []).append(d)
        INDEX.setdefault(d["name"], []).append(d)

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    by_sec: dict[str, list[dict]] = {}
    thin: list[dict] = []
    codey: list[tuple[str, str]] = []
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
            "Each card states the result in mathematical English and explains the idea "
            "of its proof or construction; the Lean source follows each card.*\n\n"
        )
        for d in items:
            parts.append(card_markdown(d))
            t = english_title(d)
            if is_codey(t):
                codey.append((d["fqn"], t))
        (OUT_DIR / f"{sec}.md").write_text("".join(parts), encoding="utf-8")

    with THIN.open("w", encoding="utf-8") as f:
        for t in thin:
            f.write(json.dumps(t) + "\n")

    by_fqn = {d["fqn"]: d for d in decls}
    for fq in SPOT:
        d = by_fqn.get(fq)
        if d is None:
            continue
        print(f"SPOT {fq.split('.', 2)[-1]}")
        print(f"  title: {english_title(d)}")
        print(f"  stmt : {statement_english(d)[:220]}")
        print(f"  proof: {proof_english(d)[:320]}")
    print(
        f"wrote {OUT_DIR} ({len(decls)} cards across {len(by_sec)} sections); "
        f"{len(thin)} thin (no docstring) listed in {THIN}; "
        f"{len(codey)} headings still look like code"
    )
    for fq, t in codey[:20]:
        print(f"  CODEY {fq}: {t}")


if __name__ == "__main__":
    main()
