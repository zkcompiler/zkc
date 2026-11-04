#!/usr/bin/env bash
# Check the service boundary before running repository code with build tools.
set -euo pipefail
: "${ZKC_CI_ROOT:?The isolated zkc CI service is required}"
[[ $(id -un) == zkc-ci ]]
[[ /nix -ef "$ZKC_CI_ROOT/store/nix" ]]
[[ $NIX_CONF_DIR == "$ZKC_CI_ROOT/config" ]]
[[ $NIX_REMOTE == daemon ]]
grep -q '/zkc.slice/zkc-ci.slice/' /proc/self/cgroup
budget=/sys/fs/cgroup/zkc.slice/zkc-ci.slice
read -r quota period < "$budget/cpu.max"
[[ $quota != max && $quota -le $((4 * period)) ]]
[[ $(cat "$budget/memory.max") -le 34359738368 ]]
[[ $(cat "$budget/memory.swap.max") == 0 ]]
nix --version
for setting in 'sandbox true' 'sandbox-fallback false' 'max-jobs 1' 'cores 4'; do
  read -r name expected <<< "$setting"
  [[ $(nix config show "$name") == "$expected" ]] || {
    echo "::error::Nix must configure $name = $expected"
    exit 1
  }
done
[[ " $(nix config show sandbox-paths) " == *" /var/cache/zkc-ccache=$ZKC_CI_ROOT/cache/ccache "* ]] || {
  echo '::error::Configure the dedicated compiler cache before running CI.'
  exit 1
}
# Nix resolves bind sources as a build user before entering its sandbox.
# Permit traversal of the cache parent; individual caches retain their owners
# and private permissions. The runner owns this parent directory.
chmod 0711 "$ZKC_CI_ROOT/cache"
df -h "$ZKC_CI_ROOT"
# Keep all scratch data on the CI volume. Refuse before a build exhausts it.
available=$(df -PB1 "$ZKC_CI_ROOT" | awk 'NR == 2 {print $4}')
[[ $available -ge 85899345920 ]] || {
  echo '::error::CI requires at least 80 GiB free on its own volume.'
  exit 1
}
