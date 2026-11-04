#!/usr/bin/env bash
# After the main scope, prove that all selected outputs are reusable locally.
set -euo pipefail
check_names=$(nix eval --raw .#checks.x86_64-linux --apply 'checks: builtins.concatStringsSep " " (builtins.attrNames checks)')
read -r -a checks <<< "$check_names"
targets=()
for check in "${checks[@]}"; do
  targets+=(".#checks.x86_64-linux.$check")
done
mkdir -p build/reports/environment
for target in "${targets[@]}"; do
  output=$(nix eval --raw "$target.outPath")
  nix-store --check-validity "$output"
done
nix build --no-link --json --max-jobs 0 --builders '' --option substitute false \
  "${targets[@]}" > build/reports/environment/cache-reused.json
