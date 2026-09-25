#!/usr/bin/env bash
# Retain exact shallow commit provenance without server-dependent pack layout.
set -euo pipefail
# The maintenance command also runs outside a Nix build sandbox.
export GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_COUNT=0
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES
source_dir=$(realpath "$1")
revision=$2
actual=$(git -C "$source_dir" rev-parse HEAD)
if [[ "$actual" != "$revision" ]]; then
  printf 'Expected Git revision %s, found %s\n' "$revision" "$actual" >&2
  exit 1
fi
# Git creates pack temporaries beside its object database before renaming them.
# Keep the destination on that filesystem, including in fixed-output sandboxes.
pack_dir=$(mktemp -d "$source_dir/.git-normalize-XXXXXXXX")
trap 'rm -rf "$pack_dir"' EXIT
git -C "$source_dir" rev-list --objects --no-object-names --no-walk HEAD |
  LC_ALL=C sort > "$pack_dir/objects"
git -C "$source_dir" -c pack.writeReverseIndex=true pack-objects --threads=1 --compression=6 \
  --no-reuse-object --no-reuse-delta --window=0 --index-version=2 \
  "$pack_dir/pack" < "$pack_dir/objects" > /dev/null
rm -rf "$source_dir/.git"
mkdir -p "$source_dir/.git/objects/pack" "$source_dir/.git/refs"
mv "$pack_dir"/pack-* "$source_dir/.git/objects/pack/"
printf '%s\n' "$revision" > "$source_dir/.git/HEAD"
printf '%s\n' "$revision" > "$source_dir/.git/shallow"
