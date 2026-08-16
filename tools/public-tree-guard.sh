#!/usr/bin/env bash
# The public tree carries the compiler, its specification, its tests, and
# its evidence records. It deliberately does not carry development-repository
# material: research and review records, strategy and planning queues,
# session or agent process logs, and superseded archives. Those live in the
# development repository and reach the public tree only as finished
# documentation under docs/.
#
# This guard refuses that material by path, so re-adding one of these
# directories is a deliberate edit to this list rather than a quiet commit.
# It reads the tracked tree, not a diff, so the rule holds for every commit
# regardless of how a file arrived.
#
# Run it from the repository root: tools/public-tree-guard.sh
set -euo pipefail

# Directories the public tree does not carry. A path is refused when it is
# one of these or lies under it.
readonly EXCLUDED=(
  "docs/agent"
  "docs/archive"
  "docs/design"
  "docs/notes"
  "docs/plans"
  "docs/private"
  "docs/spec/archive"
)

found=0
for prefix in "${EXCLUDED[@]}"; do
  # -z/--others is deliberately absent: only tracked files are the question.
  # An ignored working copy (docs/private is a separate repository checked
  # out here) is expected and is not a finding.
  while IFS= read -r path; do
    [ -n "$path" ] || continue
    if [ "$found" -eq 0 ]; then
      echo "error: the public tree carries development-repository paths:" >&2
      found=1
    fi
    echo "  $path" >&2
  done < <(git ls-files -- "$prefix" "$prefix/**")
done

if [ "$found" -ne 0 ]; then
  cat >&2 <<'EOF'

These paths hold research records, planning queues, session or agent
process logs, or superseded archives. They belong in the development
repository. If one of them is genuinely public documentation now, move the
content under a documented docs/ path and edit the list in
tools/public-tree-guard.sh in the same change.
EOF
  exit 1
fi

echo "public tree guard: no development-repository paths tracked"
