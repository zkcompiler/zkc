#!/usr/bin/env bash
# Add the compiler cache to the dedicated CI daemon, never the host daemon.
set -euo pipefail
ci_root=${1:-/ethereum/zkc-ci}
mode=${2:-configure}
[[ $EUID == 0 ]] || { echo 'Run this script with sudo.' >&2; exit 1; }
[[ $ci_root =~ ^/[-a-zA-Z0-9_/]+$ && $ci_root != / ]] || exit 1
[[ $mode == configure || $mode == restart ]] || exit 1
[[ -f $ci_root/config/nix.conf ]] || exit 1

if [[ $mode == restart ]]; then
  runner_unit=$(cat "$ci_root/runner/.service")
  [[ $runner_unit =~ ^actions\.runner\.[a-zA-Z0-9_.-]+\.service$ ]] || exit 1
  if pgrep -u zkc-ci -f '/Runner.Worker' >/dev/null; then
    echo 'A CI job is running; retry after it finishes.' >&2
    exit 1
  fi
  systemctl stop "$runner_unit"
  trap 'systemctl start "$runner_unit"' EXIT
fi

install -d -m 2770 -o zkc-ci -g zkc-ci-build "$ci_root/cache/ccache"
entry="extra-sandbox-paths = /var/cache/zkc-ccache=$ci_root/cache/ccache"
# This file belongs exclusively to this installer. Retain every other setting.
sed -i '/^extra-sandbox-paths = /d' "$ci_root/config/nix.conf"
printf '%s\n' "$entry" >> "$ci_root/config/nix.conf"
if [[ $mode == restart ]]; then
  systemctl restart zkc-ci-nix.service
  systemctl start "$runner_unit"
  trap - EXIT
  systemctl is-active --quiet zkc-ci-nix.service
  systemctl is-active --quiet "$runner_unit"
fi
echo 'Compiler cache configured for the CI daemon.'
