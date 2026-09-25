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

# Build all three components incrementally.
build: (build-compiler "release") build-lean build-rust

# Configure a compiler profile from CMakePresets.json.
configure profile="release":
    python3 scripts/develop.py configure --profile "$1"

# Build the compiler with a release, dev or sanitize profile.
build-compiler profile="release":
    python3 scripts/develop.py compiler --profile "$1"

# Build the native runtime, tools and examples.
build-rust:
    python3 scripts/develop.py rust

# Build every default target declared by the formal package.
build-lean:
    python3 scripts/develop.py lean

# Run the main suite, including resource-boundary tests; optional suites are separate.
test: test-compiler test-cross test-rust test-lean test-artifact test-install test-evidence test-docs lint demo

# Explicitly remove retained reports when no tests are using them.
clean-reports:
    python3 scripts/develop.py clean-reports

# Build and test the selected compiler profile.
test-compiler profile="release": (build-compiler profile)
    python3 tests/run.py compiler --profile "$1"

# Build and run the native C++ sanitizer tests.
test-sanitize: (test-compiler "sanitize")

# Run cross-language regressions against the built components.
test-cross: build
    python3 tests/run.py cross

# Test command wiring and reporting without compiled project tools.
test-harness:
    python3 tests/run.py harness

# Run Rust tests against the built components.
test-rust: build
    python3 tests/run.py rust

# Run the ordered artifact interoperability drivers.
test-artifact output="": build
    python3 tests/run.py artifact --output "$1"

# Run all discovered formal controls and independent consumers.
test-lean: build-lean
    python3 tests/run.py lean

# Run Groth16 interoperability using an explicitly reproduced fixture.
test-groth16 fixture: build
    python3 tests/run.py groth16 --fixture "$1"

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

# Verify the retained Groth16 evidence.
test-evidence:
    python3 tests/run.py evidence

# Check documentation links, fragments and reachability.
test-docs:
    python3 tests/run.py docs

# Produce and verify a committed argument using explicit development fixtures.
demo: build
    python3 tests/run.py demo

# Measure the maintained direct implementations.
bench output="build/bench":
    python3 scripts/develop.py bench --output "$1"

# Run correctness controls in the separate benchmark workspaces.
test-bench:
    python3 tests/run.py bench

# Check Rust formatting, Clippy and Python lint.
lint:
    python3 tests/run.py lint

# Format the Nix definitions with the pinned formatter.
fmt-nix:
    nix fmt
