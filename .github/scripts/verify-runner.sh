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
