# Development commands. The Lean toolchain comes from lean/compiler/lean-toolchain through elan.
set shell := ["bash", "--noprofile", "--norc", "-euo", "pipefail", "-c"]
set positional-arguments

# List the recipes.
default:
    @just --list --unsorted

# Build the compiler package: the core and its tests, whose checks run when they are built.
build:
    cd lean/compiler && lake build

# Build and test the compiler package and audit it.
test:
    cd lean/compiler && lake build && lake test
    just audit

# Audit the compiler package: the kernel's replay of the core and its tests, no `sorry`, no axiom beyond Lean's three, the import rules.
audit:
    cd lean/compiler && lake exe zkc-audit

# Run the checks that need no build: the public tree, the documents and the generated Unicode tables.
check:
    bash .github/scripts/public-tree-guard.sh
    python3 scripts/check_docs.py --all
    python3 lean/compiler/scripts/generate_unicode_tables.py --check
