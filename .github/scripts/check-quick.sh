#!/usr/bin/env bash
# Source and harness checks only; run from the repository root.
set -euo pipefail

bash .github/scripts/public-tree-guard.sh
uv sync --locked
python3 common/tests/run.py style
python3 common/tests/run.py docs
python3 common/tests/run.py harness
