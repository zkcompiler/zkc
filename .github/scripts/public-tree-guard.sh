#!/usr/bin/env bash
# Reject tracked paths reserved for non-public material. Inspect the whole
# tracked tree so the check also catches files introduced by earlier commits.
# Run from the repository root: .github/scripts/public-tree-guard.sh
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
  "evaluation"
)

found=0
for prefix in "${EXCLUDED[@]}"; do
  # -o/--others is deliberately absent: only tracked files are the question.
  # Ignored local material is outside the published tree.
  while IFS= read -r path; do
    [ -n "$path" ] || continue
    if [ "$found" -eq 0 ]; then
      echo "error: the public tree carries non-public paths:" >&2
      found=1
    fi
    echo "  $path" >&2
  done < <(git ls-files -- "$prefix" "$prefix/**")
done

if [ "$found" -ne 0 ]; then
  cat >&2 <<'EOF'

These paths are reserved for non-public material. Public documentation belongs
under a documented docs/ path. Update the exclusion list only when the path's
publication policy changes.
EOF
  exit 1
fi

echo "public tree guard: no non-public paths tracked"
