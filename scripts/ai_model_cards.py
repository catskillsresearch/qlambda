"""Model-card registry for the AI-assisted development acknowledgements block.

Injected into `arxiv_with_code.md` / `arxiv.tex` by `build_arxiv_tex.py` at:
  <!-- AI_MODEL_TOOL_BULLETS --> … <!-- /AI_MODEL_TOOL_BULLETS -->
  <!-- AI_MODEL_REFERENCES --> … <!-- /AI_MODEL_REFERENCES -->
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class ModelCard:
    label: str
    cite_key: str
    tool_note: str
    reference: str


MODEL_CARDS: tuple[ModelCard, ...] = (
    ModelCard(
        label="Cursor",
        cite_key="Cur26",
        tool_note=(
            "agent-assisted editing in the Cursor IDE for the typed linear "
            "calculus, quantum-relation and qCPO developments, the CP-presheaf "
            "substrate, circuit quotation, and drafting this narrative. "
            "Generated Lean was provisional until it compiled under the pinned "
            "toolchain."
        ),
        reference=(
            "Anysphere, Inc. *Cursor: AI-native code editor and agent environment*. "
            "<https://cursor.com> (accessed 2026)."
        ),
    ),
    ModelCard(
        label="xAI Grok 4.7",
        cite_key="Grk47",
        tool_note=(
            "formalization and drafting in Cursor: typed linear syntax and "
            "metatheory, the intrinsic CP-map and superoperator-module "
            "substrate, first-order type objects, primitive agreement, and "
            "the proved-versus-objective boundary of this narrative. Every "
            "emitted proof term was checked by the Lean kernel."
        ),
        reference=(
            "xAI. *Grok 4.7*. Model documentation as integrated in Cursor, "
            "<https://cursor.com/docs/models> (accessed 2026)."
        ),
    ),
    ModelCard(
        label="OpenAI GPT 5.6",
        cite_key="Gpt56",
        tool_note=(
            "substantive Palomar editorial passes in Cursor "
            "(`statement_alignment`, `definition_fidelity`, "
            "`literature_notability`, and `synthesis`). Those passes review "
            "claims; they do not replace kernel-checked Lean."
        ),
        reference=(
            "OpenAI. *GPT 5.6*. Model documentation as integrated in Cursor, "
            "<https://cursor.com/docs/models> (accessed 2026)."
        ),
    ),
)

TOOL_BULLETS_BEGIN = "<!-- AI_MODEL_TOOL_BULLETS -->"
TOOL_BULLETS_END = "<!-- /AI_MODEL_TOOL_BULLETS -->"
REFERENCES_BEGIN = "<!-- AI_MODEL_REFERENCES -->"
REFERENCES_END = "<!-- /AI_MODEL_REFERENCES -->"


def render_tool_bullets() -> str:
    return "\n".join(
        f"- **{card.label}** **[{card.cite_key}]** — {card.tool_note}" for card in MODEL_CARDS
    )


def render_model_references() -> str:
    return "\n".join(f"- **[{card.cite_key}]** {card.reference}" for card in MODEL_CARDS)


def inject_model_cards(text: str) -> str:
    """Expand acknowledgement markers; pass through unchanged if markers absent."""
    tool_block = f"{TOOL_BULLETS_BEGIN}\n{render_tool_bullets()}\n{TOOL_BULLETS_END}"
    ref_block = f"{REFERENCES_BEGIN}\n{render_model_references()}\n{REFERENCES_END}"

    has_tools = TOOL_BULLETS_BEGIN in text
    has_references = REFERENCES_BEGIN in text
    if not has_tools and not has_references:
        return text
    if not has_tools:
        raise RuntimeError(
            f"missing {TOOL_BULLETS_BEGIN} in narrative; add markers to arxiv.md Acknowledgments"
        )
    if not has_references:
        raise RuntimeError(
            f"missing {REFERENCES_BEGIN} in narrative; add markers to arxiv.md References"
        )

    text = _replace_between(text, TOOL_BULLETS_BEGIN, TOOL_BULLETS_END, render_tool_bullets())
    text = _replace_between(text, REFERENCES_BEGIN, REFERENCES_END, render_model_references())
    return text


def _replace_between(text: str, begin: str, end: str, body: str) -> str:
    start = text.index(begin)
    stop = text.index(end, start)
    stop_end = stop + len(end)
    inner_start = start + len(begin)
    # Preserve one leading newline after begin marker when present.
    if inner_start < stop and text[inner_start : inner_start + 1] == "\n":
        inner_start += 1
    if inner_start < stop and text[stop - 1 : stop] == "\n":
        stop -= 1
    return text[:start] + begin + "\n" + body + "\n" + end + text[stop_end:]
