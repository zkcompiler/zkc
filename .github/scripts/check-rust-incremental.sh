#!/usr/bin/env bash
# Run the same Rust obligations as nix/checks/rust.nix with runner-local objects.
set -euo pipefail
: "${ZKC_CI_ROOT:?Run inside the dedicated CI service}"

export CARGO_HOME="$ZKC_CI_ROOT/cache/cargo-home"
export CARGO_INCREMENTAL=1
export CARGO_PROFILE_DEV_DEBUG=line-tables-only
export CARGO_PROFILE_TEST_DEBUG=line-tables-only
# Cargo fingerprints source, features and dependencies. Partition the mutable
# cache at the compiler/configuration boundary, not at every source revision.
toolchain_key=$({ rustc -vV; printf '%s\n' "${CC:-}" "${CXX:-}" "${RUSTFLAGS:-}" \
  "${CARGO_ENCODED_RUSTFLAGS:-}" "$CARGO_PROFILE_TEST_DEBUG"; } | sha256sum | cut -d' ' -f1)
export CARGO_TARGET_DIR="$ZKC_CI_ROOT/cache/cargo/$toolchain_key"
mkdir -p "$CARGO_HOME" "$CARGO_TARGET_DIR"
cargo fetch --locked
export CARGO_NET_OFFLINE=true
cargo clippy --workspace --locked --offline --all-targets --all-features -- -D warnings
cargo clippy --locked --offline -p zkc-runtime --all-targets -- -D warnings
python3 common/tests/run.py rust
