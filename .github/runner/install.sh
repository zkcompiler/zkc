#!/usr/bin/env bash
# Install or resume this server's runner. Read a registration token on stdin.
set -euo pipefail

ci_root=${1:-/ethereum/zkc-ci}
[[ $EUID == 0 ]] || { echo 'Run this installer with sudo.' >&2; exit 1; }
[[ $ci_root =~ ^/[-a-zA-Z0-9_/]+$ && $ci_root != / ]] || exit 1
[[ $(uname -m) == x86_64 ]] || exit 1
cd /
runner_unit=
if [[ -f $ci_root/runner/.service ]]; then
  runner_unit=$(cat "$ci_root/runner/.service")
  [[ $runner_unit =~ ^actions\.runner\.[a-zA-Z0-9_.-]+\.service$ ]] || exit 1
fi
for unit in zkc-ci-runner.service zkc-ci-register.service ${runner_unit:+"$runner_unit"}; do
  if systemctl is-active --quiet "$unit"; then
    echo "Stop $unit between jobs before changing its configuration." >&2
    exit 1
  fi
done
registration_token=
IFS= read -r registration_token || true
if [[ ! -f $ci_root/runner/.runner ]]; then
  [[ $registration_token =~ ^[a-zA-Z0-9_=-]+$ ]] || {
    echo 'A registration token is required for an unregistered runner.' >&2
    exit 1
  }
fi
nix=/nix/var/nix/profiles/default/bin/nix
nix_package=$(dirname "$(dirname "$(readlink -f "$nix")")")
[[ -x $nix_package/bin/nix-daemon ]] || exit 1
install -d -m 0755 "$ci_root"
install -d -m 0700 "$ci_root/admin"
# Retire the token file used by the earlier registration service.
rm -f "$ci_root/admin/registration.env"

if ! "$nix" path-info --store "local?root=$ci_root/store" "$nix_package" >/dev/null 2>&1; then
  "$nix" copy --from https://cache.nixos.org --to "local?root=$ci_root/store" "$nix_package"
fi
install -d "$ci_root/store/nix/var/nix/profiles" "$ci_root/store/nix/var/nix/gcroots"
ln -sfn "$nix_package" "$ci_root/store/nix/var/nix/profiles/default"
ln -sfn "$nix_package" "$ci_root/store/nix/var/nix/gcroots/bootstrap-nix"

getent group zkc-ci-build >/dev/null || groupadd --system zkc-ci-build
if ! id zkc-ci >/dev/null 2>&1; then
  useradd --system --user-group --home-dir "$ci_root/home" --shell /usr/sbin/nologin zkc-ci
fi
[[ $(getent passwd zkc-ci | cut -d: -f6) == "$ci_root/home" ]] || exit 1
for number in 1 2; do
  if ! id "zkc-ci-build$number" >/dev/null 2>&1; then
    useradd --system --gid zkc-ci-build --groups zkc-ci-build \
      --home-dir /var/empty --shell /usr/sbin/nologin "zkc-ci-build$number"
  fi
  [[ $(id -gn "zkc-ci-build$number") == zkc-ci-build ]] || exit 1
done
chgrp zkc-ci-build "$ci_root/store/nix/store"
chmod 1775 "$ci_root/store/nix/store"
install -d -m 0700 -o zkc-ci -g zkc-ci \
  "$ci_root/home" "$ci_root/runner" "$ci_root/work" "$ci_root/cache"
install -d -m 1777 "$ci_root/tmp"
install -d -m 0755 "$ci_root/config"
cat > "$ci_root/config/nix.conf" <<'EOF'
experimental-features = nix-command flakes
sandbox = true
sandbox-fallback = false
max-jobs = 1
cores = 4
build-users-group = zkc-ci-build
allowed-users = zkc-ci root
trusted-users = root
substituters = https://cache.nixos.org
min-free = 21474836480
max-free = 42949672960
EOF

if [[ ! -x $ci_root/runner/config.sh ]]; then
  archive="$ci_root/admin/runner.tar.gz"
  checksum=baebf204307bac6193480852732f0aba2ae97b6c5597c244f4d5558390147c40
  if ! echo "$checksum  $archive" | sha256sum --check --status 2>/dev/null; then
    curl --fail --location --retry 3 \
      https://github.com/actions/runner/releases/download/v2.338.2/actions-runner-linux-x64-2.338.2.tar.gz \
      --output "$archive"
  fi
  echo "$checksum  $archive" | sha256sum --check
  tar --extract --gzip --file "$archive" --directory "$ci_root/runner" --no-same-owner
  chown -R zkc-ci:zkc-ci "$ci_root/runner"
fi

# The upstream lifecycle is configure, svc.sh install, then svc.sh start.
# Registration needs no Nix daemon or special systemd unit. Pass its short-lived
# token through stdin rather than a file, command-line argument or log.
if [[ ! -f $ci_root/runner/.runner ]]; then
  # The inner shell expands its own arguments and token, not this shell.
  # shellcheck disable=SC2016
  printf '%s\n' "$registration_token" | runuser -u zkc-ci -- env -i \
    HOME="$ci_root/home" PATH=/nix/var/nix/profiles/default/bin:/usr/local/bin:/usr/bin:/bin \
    LANG=C.UTF-8 /bin/bash -c '
      set -euo pipefail
      IFS= read -r ACTIONS_RUNNER_INPUT_TOKEN
      export ACTIONS_RUNNER_INPUT_TOKEN
      cd "$1"
      exec ./config.sh --unattended --url https://github.com/zkcompiler/zkc \
        --name zkc-local-linux --labels zkc-ci --work "$2"
    ' configure "$ci_root/runner" "$ci_root/work"
fi
unset registration_token
cd "$ci_root/runner"
if [[ ! -f .service ]]; then
  ./svc.sh install zkc-ci
fi
runner_unit=$(cat .service)
[[ $runner_unit =~ ^actions\.runner\.[a-zA-Z0-9_.-]+\.service$ ]] || exit 1
[[ -x runsvc.sh ]] || { echo 'The upstream service installation is incomplete.' >&2; exit 1; }

cat > /etc/systemd/system/zkc-ci.slice <<'EOF'
[Unit]
Description=Combined resource budget for zkc CI and its Nix builds
[Slice]
CPUQuota=400%
CPUWeight=20
MemoryHigh=24G
MemoryMax=32G
MemorySwapMax=0
IOWeight=10
TasksMax=4096
EOF
cat > /etc/systemd/system/zkc-ci-nix.service <<EOF
[Unit]
Description=Nix daemon for the zkc CI store
After=network-online.target
Wants=network-online.target
RequiresMountsFor=$ci_root
[Service]
Type=simple
Slice=zkc-ci.slice
ExecStart=$nix_package/bin/nix-daemon
Environment=NIX_CONF_DIR=$ci_root/config
Environment=TMPDIR=$ci_root/tmp
BindPaths=$ci_root/store/nix:/nix
Nice=10
Restart=on-failure
[Install]
WantedBy=multi-user.target
EOF
install -d "/etc/systemd/system/$runner_unit.d"
cat > "/etc/systemd/system/$runner_unit.d/resources.conf" <<EOF
[Unit]
Requires=zkc-ci-nix.service
After=zkc-ci-nix.service
RequiresMountsFor=$ci_root
[Service]
Slice=zkc-ci.slice
Environment=HOME=$ci_root/home
Environment=NIX_CONF_DIR=$ci_root/config
Environment=NIX_REMOTE=daemon
Environment=ZKC_CI_ROOT=$ci_root
Environment=TMPDIR=$ci_root/tmp
Environment=CMAKE_BUILD_PARALLEL_LEVEL=4 CTEST_PARALLEL_LEVEL=4 CARGO_BUILD_JOBS=4 RUST_TEST_THREADS=4 PYTEST_XDIST_AUTO_NUM_WORKERS=4
BindPaths=$ci_root/store/nix:/nix
Nice=10
UMask=0077
KillMode=control-group
TimeoutStopSec=90
Restart=always
RestartSec=10
EOF
# Only obsolete units created by the earlier, incomplete installer are retired.
systemctl disable zkc-ci-runner.service 2>/dev/null || true
rm -f /etc/systemd/system/zkc-ci-runner.service /etc/systemd/system/zkc-ci-register.service
systemctl daemon-reload
systemd-analyze verify /etc/systemd/system/zkc-ci.slice \
  /etc/systemd/system/zkc-ci-nix.service "/etc/systemd/system/$runner_unit"
# The runner is still stopped, so restarting its own daemon cannot interrupt a job.
systemctl enable zkc-ci-nix.service "$runner_unit"
systemctl restart zkc-ci-nix.service
./svc.sh start
for unit in zkc-ci-nix.service "$runner_unit"; do
  systemctl is-active --quiet "$unit"
done
echo 'Runner service started. Workflow validation remains a separate step.'
