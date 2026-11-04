# Self-hosted CI

The ordinary GitHub Actions jobs run on one repository runner with labels
`self-hosted`, `linux`, `x64`, `zkc-ci`. GitHub schedules jobs and records their
results; this server supplies their compute. No Git validation hook is needed.
The workflow is still a repository change: configuring a runner does not move
the default branch's workflow until the workflow pull request lands.

## Isolation and capacity

The [installer](../../.github/runner/install.sh) provisions Ubuntu x86-64 with
a `zkc-ci` account, two dedicated Nix build accounts, and two systemd services:
the upstream `actions.runner.*` service and `zkc-ci-nix`. Both services belong to `zkc-ci.slice`:

| Resource | Policy |
|---|---|
| Running Actions jobs | One runner, one job at a time |
| Combined CPU | Four CPU equivalents; low scheduling weight |
| Combined memory | 24 GiB pressure threshold, 32 GiB hard limit, no swap |
| Processes | 4,096 across both services |
| Nix builds | One derivation at a time, four build workers |
| Build and cache outputs | Dedicated CI directories on the CI volume |
| Disk headroom | Refuse new jobs below 80 GiB free |

The budget includes Nix daemon children. Limiting only the runner would not
limit builds submitted to the development machine's shared Nix daemon.
The CI services mount their own store over `/nix`, use their own configuration,
and keep temporary files on the CI volume. They do not reconfigure or clear the
developer store. The runner uses a separate account without sudo or Docker access. Standard
Unix permissions separate it from the development account; there is no custom
home-directory or filesystem access policy. This is not an ephemeral VM.
I/O scheduling weight is a preference, not a bandwidth guarantee.

This repository is public. Require approval for **all external contributors**
in the repository's Actions settings. Do not approve external PR workflows on
this persistent development server. Review and import a contribution to a
trusted repository branch first, or validate it on disposable infrastructure.
A workflow `if` condition or a runner label is not a security boundary against
an author who can edit that workflow. No repository secrets or developer
credentials are installed in the runner home.

## Provisioning

Review the installer before running it. It creates `/ethereum/zkc-ci` by default
and reuses an incomplete installation. It refuses to reconfigure a running
runner, so stop it between jobs before maintenance. It downloads the pinned runner archive
with a SHA-256 check and obtains the host's Nix version from the signed upstream
cache into the new store. It does not install or reconfigure host Nix.
The GitHub CLI needs repository administration rights; sudo is needed only for
system accounts, the private daemon and service installation.

```sh
gh api --method POST repos/zkcompiler/zkc/actions/runners/registration-token --jq .token \
  | sudo bash .github/runner/install.sh
```

The token is short-lived and passed through stdin, without a temporary token
file. Registration uses `config.sh`, then the upstream `svc.sh install zkc-ci`
creates the service and its entry point. A systemd drop-in supplies the resource
budget and CI store. No separate registration service is needed. Repeating the
installer after a failure reuses downloaded files and accounts. Runner updates
use the upstream service mechanism. Inspect service health after an update.

```sh
systemctl status 'actions.runner.*.service' zkc-ci-nix.service
systemctl show zkc-ci.slice -p CPUUsageNSec -p MemoryCurrent -p MemoryPeak -p TasksCurrent
journalctl -u 'actions.runner.*.service' -u zkc-ci-nix.service
gh api repos/zkcompiler/zkc/actions/runners
```

Stop the runner using `sudo ./svc.sh stop` from its installation directory,
then `sudo systemctl stop zkc-ci-nix`. This does not stop the development daemon. Stop only between jobs
unless aborting a known bad job. Do not delete live stores or mutable caches.
Before decommissioning, remove its GitHub registration and disable its units;
retire its files separately after checking retained evidence.

## Cache and incremental-build boundaries

`actions/checkout` cleans the source tree on every job. Build outputs are not
preserved by disabling that cleanup. Git credentials are not persisted.

* Rust Clippy and tests use a private `CARGO_HOME` and `CARGO_TARGET_DIR` outside
  the checkout. The target directory is partitioned by the exact compiler and
  native compiler configuration. Cargo owns source, feature and dependency
  fingerprints. The all-features workspace, normal-feature benchmark tests and
  disabled execution collector remain three distinct required obligations.
* C++ packages, the installed CLI, detached C++ and Rust SDK consumers, source
  boundaries, SDK discovery, formatting and selected valid/invalid protocol
  cases retain their Nix checks. Only identical derivation inputs reuse a
  successful result. A changed C++ package rebuilds; this is package reuse,
  not persistent Ninja object reuse or reuse of a developer build tree.
* The signed upstream binary cache supplies dependencies. The private local
  store retains project outputs without uploading them to a second cache
  service. `cache` runs the main scope, then verifies reuse with both local
  builders and substitution disabled. This replaces the former acceptance
  test for GitHub cache restoration into an empty store, because that remote
  cache is no longer used.
* `fresh` gives the complete `lean` → `security` → `arklib` package chain a
  per-attempt derivation input. Each package consumes its newly built parent,
  and source builds retain the no-Lake-cache policy. Only this explicit mode
  changes package identity to prevent output reuse; ordinary jobs retain
  content-addressed input identities. It does not delete the store or impose
  bit-for-bit reproducibility on outputs that contain test timing records.

Automatic quick and native jobs run sequentially on the sole runner. Expensive
manual main/formal/adapter scopes remain explicit. Test reports and logs are
uploaded per run; cached objects are not evidence that a new check ran.
The Nix store may collect unrooted outputs under disk pressure. Mutable Cargo
caches require occasional operator cleanup while the runner is idle; they
cannot consume a developer cache and are not deleted by a workflow.

## Required checks and acceptance

Use the GitHub ruleset on the default branch to require `Required CI`, sourced
from the GitHub Actions app, with an up-to-date branch and no bypass actors.
Keep pull requests required and force pushes/deletion prohibited. An approval
from a second person is not required for a solo maintainer.

`Required CI` runs even after a dependency fails. It requires both automatic
jobs to succeed; a missing, skipped, cancelled, neutral or timed-out job cannot
satisfy it. Native change selection happens inside the native job, so a genuine
documentation-only change still has an explicit successful selection result.
Manual jobs use a different final check name and cannot satisfy the automatic
merge gate with a narrower scope. Small negative controls exercise this policy
in the harness; verify actual pending and successful PR states after changing
the ruleset. Never call the merge API as a test of whether merging is blocked.

For a runner migration, retain the server resource/mount checks, a successful
quick/native PR run, a warm-cache run and the ruleset/merge-state observations.
Do not rerun unrelated formal proofs to validate runner scheduling. If a final
check is queued because the runner is offline, the PR remains blocked.
