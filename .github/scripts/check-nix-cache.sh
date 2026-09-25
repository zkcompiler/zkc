#!/usr/bin/env bash
set -euo pipefail

# This is an explicit cache acceptance mode, not the ordinary cache-miss path.
# The isolation probe already ran; every other main check and the expensive
# library must be absent before we try substitution without any builders.
check_names=$(nix eval --raw .#checks.x86_64-linux --apply 'checks: builtins.concatStringsSep " " (builtins.attrNames checks)')
read -r -a checks <<< "$check_names"
targets=()
for check in "${checks[@]}"; do
  if [ "$check" != sandbox ]; then
    targets+=(".#checks.x86_64-linux.$check")
  fi
done
for package in compiler.testSupport tools tools.testSupport formal formal.library; do
  targets+=(".#packages.x86_64-linux.$package")
done
mkdir -p build/reports/environment
for target in "${targets[@]}"; do
  output=$(nix eval --raw "$target.outPath")
  if nix-store --check-validity "$output" 2>/dev/null; then
    echo "::error::$output already exists. Run the cache scope on an ephemeral runner with a fresh project store."
    exit 1
  fi
done
nix build -L --no-link --json --max-jobs 0 --builders '' --option fallback false \
  "${targets[@]}" > build/reports/environment/cache-restored.json
