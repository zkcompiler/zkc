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

# Check source verifier certificates and replay the interactive formal library through the kernel.
test-interactive:
    cd lean/formal && lake build Zkc.Formal.Interactive Zkc.Tests.Formal.Interactive Zkc.Tests.Formal.Reuse.Controls Zkc.Tests.Formal.SourceHonestSumcheck
    cd lean/formal && lake lean checks/SourceProtocols.lean
    cd lean/formal && lake env lean --run checks/AuditInteractive.lean

# Export the written knowledge claim and kernel-check the returning fork and source mutations.
test-written-knowledge:
    cd lean/compiler && lake build zkc-knowledge
    cd lean/formal && lake build Zkc.Formal.Written.GroupReplay Zkc.Formal.Written.FiniteModel
    cd lean/formal && lake env python3 checks/written_knowledge.py

# Audit the compiler package: the kernel's replay of the core, the vocabulary and their tests, no `sorry`, no axiom beyond `propext` and `Quot.sound`, the import rules.
audit:
    cd lean/compiler && lake exe zkc-audit

# Run the checks that need no build: the public tree, the documents and the generated Unicode tables.
check:
    bash .github/scripts/public-tree-guard.sh
    python3 scripts/check_docs.py --all
    python3 lean/compiler/scripts/generate_unicode_tables.py --check
