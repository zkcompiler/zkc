# Development commands. The Lean toolchain comes from lean/compiler/lean-toolchain through elan.
set shell := ["bash", "--noprofile", "--norc", "-euo", "pipefail", "-c"]
set positional-arguments

# List the recipes.
default:
    @just --list --unsorted

# Build the compiler package, then the formal package.
build:
    cd lean/compiler && lake build
    cd lean/formal && lake build

# Build and test both packages and audit them; with arguments, run the frontend's test driver with them.
test *args:
    #!/usr/bin/env bash
    set -euo pipefail
    if (( $# )); then
        cd lean/compiler
        exec lake test -- "$@"
    fi
    (cd lean/compiler && lake build && lake test)
    (cd lean/formal && lake build && lake test)
    just audit

# Audit both packages: the kernel's replay of the core, the formal library and their tests, no `sorry`, no axiom beyond Lean's three, the import rules.
audit:
    cd lean/compiler && lake exe zkc-audit
    cd lean/formal && lake exe zkc-formal-audit

# Run the checks that need no build: the public tree, the documents and the generated Unicode tables.
check:
    bash .github/scripts/public-tree-guard.sh
    python3 scripts/check_docs.py --all
    python3 lean/compiler/scripts/generate_unicode_tables.py --check
