#!/usr/bin/env bash
# Regenerate declaration catalog, English blueprint cards, and Mathlib dep figures.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/extract_declarations.py
python3 scripts/generate_blueprint_cards.py
python3 scripts/insert_section_dep_figures.py
