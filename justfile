# Everyday commands in an already prepared environment (normally nix develop).
# Nix owns tools and environment policy; native manifests own build settings.
# Tests and workspace operations have directly callable Python entry points.
set shell := ["bash", "--noprofile", "--norc", "-euo", "pipefail", "-c"]
set positional-arguments

# List the development commands.
default:
    @just --list --unsorted

# Prepare the locked development dependencies explicitly.
setup:
    python3 scripts/develop.py setup

# Report the selected toolchain and configuration.
doctor:
    python3 scripts/doctor.py

# Build the compiler and native execution toolkit incrementally.
build: (build-compiler "release") build-rust

# Configure a compiler profile from CMakePresets.json.
configure profile="release":
    python3 scripts/develop.py configure --profile "$1"

# Build the compiler with a release, dev, sanitize or shared profile.
build-compiler profile="release":
    python3 scripts/develop.py compiler --profile "$1"

# Build the product CLI with its default features.
build-rust:
    python3 scripts/develop.py rust

# Build the integration drivers with explicit test providers.
build-test-drivers:
    python3 scripts/develop.py test-drivers

# Build the optional independent Lean research package.
build-lean:
    python3 scripts/develop.py lean

# Run compiler, Rust, native integration, installation, documentation and lint checks.
test: test-compiler test-integration test-rust test-install test-docs lint demo

# Explicitly remove retained reports when no tests are using them.
clean-reports:
    python3 scripts/develop.py clean-reports

# Build and test the selected compiler profile.
test-compiler profile="release": (build-compiler profile)
    python3 tests/run.py compiler --profile "$1"

# Build and run the native C++ sanitizer tests.
test-sanitize: (test-compiler "sanitize")

# Run native compiler/Runner/Host integration and harness checks.
test-integration: build build-test-drivers
    python3 tests/run.py integration

# Test command wiring and reporting without compiled project tools.
test-harness:
    python3 tests/run.py harness

# Run Rust tests against the built components.
test-rust: build
    python3 tests/run.py rust

# Run optional formal controls and independent Lean consumers.
test-lean: build-lean
    python3 tests/run.py lean

# Fetch pinned main or ArkLib dependency objects for development.
fetch-lean deps="main":
    python3 scripts/develop.py fetch-lean --deps "$1"

# Build and check the optional ArkLib integration.
test-lean-integration: (fetch-lean "arklib")
    python3 scripts/develop.py lean-integration

# Rebuild Lean packages without prior project or dependency objects.
test-lean-fresh:
    python3 scripts/develop.py lean-fresh

# Install the compiler and build an independent SDK consumer.
test-install prefix="" profile="release": (build-compiler profile)
    python3 scripts/develop.py install --output "$1" --profile "$2"

# Check a fresh domain installation and base refusal; opt in to one linkage per run.
test-install-domain profile="release" *args:
    python3 scripts/develop.py install-domain --profile "$@"

# Check documentation links, fragments and reachability.
test-docs:
    python3 tests/run.py docs

# Compile a source Entry and produce and verify its proof.
demo: build
    python3 tests/run.py demo

# Check C++/Rust formatting, Clippy and Python lint.
lint:
    python3 tests/run.py lint

# Format the Nix definitions with the pinned formatter.
fmt-nix:
    nix fmt

# Format maintained C++ sources with the selected LLVM toolchain.
fmt-cpp:
    python3 scripts/format.py --write
