#!/usr/bin/env bash
# Check the service boundary before running repository code.
set -euo pipefail
: "${ZKC_CI_ROOT:?The isolated zkc CI service is required}"
[[ $(id -un) == zkc-ci ]]
grep -q '/zkc.slice/zkc-ci.slice/' /proc/self/cgroup
budget=/sys/fs/cgroup/zkc.slice/zkc-ci.slice
read -r quota period < "$budget/cpu.max"
[[ $quota != max && $quota -le $((4 * period)) ]]
[[ $(cat "$budget/memory.max") -le 34359738368 ]]
[[ $(cat "$budget/memory.swap.max") == 0 ]]

# The formal job provisions elan and just from the service's private Nix daemon.
if [[ ${1:-} == formal ]]; then
  [[ /nix -ef "$ZKC_CI_ROOT/store/nix" && $NIX_CONF_DIR == "$ZKC_CI_ROOT/config" && $NIX_REMOTE == daemon ]]
  [[ $HOME -ef "$ZKC_CI_ROOT/home" && $TMPDIR -ef "$ZKC_CI_ROOT/tmp" ]]
  for directory in "$GITHUB_WORKSPACE" "$RUNNER_TEMP"; do
    [[ $(realpath "$directory") == "$(realpath "$ZKC_CI_ROOT")"/work/* ]]
  done
  for setting in 'sandbox true' 'sandbox-fallback false' 'max-jobs 1' 'cores 4'; do
    read -r name expected <<< "$setting"
    [[ $(nix config show "$name") == "$expected" ]]
  done
  available=$(df -PB1 "$ZKC_CI_ROOT" | awk 'NR == 2 {print $4}')
  [[ $available -ge 85899345920 ]] || { echo 'Formal CI requires 80 GiB free on the CI volume.' >&2; exit 1; }
fi
