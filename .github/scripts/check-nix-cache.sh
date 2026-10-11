#!/usr/bin/env bash
set -euo pipefail

# This is an explicit cache acceptance mode, not the ordinary cache-miss path.
# Before restoration, project outputs must be absent. Afterwards, require
# every selected output without permitting local or remote builders.
check_names=$(nix eval --raw .#checks.x86_64-linux --apply 'checks: builtins.concatStringsSep " " (builtins.attrNames checks)')
read -r -a checks <<< "$check_names"
targets=()
for check in "${checks[@]}"; do
  if [ "$check" != sandbox ]; then
    targets+=(".#checks.x86_64-linux.$check")
  fi
done
targets+=(".#checks.x86_64-linux.compiler.testSupport")
for package in compiler tools test-drivers zkc; do
  targets+=(".#packages.x86_64-linux.$package")
done
mkdir -p build/reports/environment
if [ "${1:-}" = --assert-empty ]; then
  for target in "${targets[@]}"; do
    output=$(nix eval --raw "$target.outPath")
    if nix-store --check-validity "$output" 2>/dev/null; then
      echo "::error::$output already exists. Run the cache scope on an ephemeral runner with a fresh project store."
      exit 1
    fi
  done
  exit 0
fi
if [ "$#" -ne 0 ]; then
  echo "usage: $0 [--assert-empty]" >&2
  exit 2
fi
nix build -L --no-link --json --max-jobs 0 --builders '' --option fallback false \
  "${targets[@]}" > build/reports/environment/cache-restored.json
