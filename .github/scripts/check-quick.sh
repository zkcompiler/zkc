#!/usr/bin/env bash
# Source and harness checks only; run from the repository root.
set -euo pipefail

bash .github/scripts/public-tree-guard.sh
uv sync --locked
just --list > /dev/null
actionlint -shellcheck="" .github/workflows/*.yml
git ls-files -z '*.nix' | xargs -0 nixfmt --check
cargo fmt --all -- --check
uv run --no-sync --locked ruff check .
python3 tests/check_docs.py --all
python3 tests/run.py harness
