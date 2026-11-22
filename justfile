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
    cd lean/compiler && lake build Zkc.Tools.Audit
    cd lean/formal && lake build ZkcFormal.Interactive ZkcFormalTests.Interactive ZkcFormalTests.Reuse.Controls ZkcFormalTests.SourceHonestSumcheck
    cd lean/formal && lake lean checks/SourceProtocols.lean
    cd lean/formal && lake lean checks/OracleNames.lean
    cd lean/formal && lake lean checks/WorldObservation.lean
    cd lean/formal && lake env lean --run checks/AuditInteractive.lean

# Compile source draw charges, check their VCVio bounds, judge an admitted protocol within its charges, and exercise source and address mutations.
test-written-charge: _charge-checks
    cd lean/formal && lake lean checks/ReplayCharge.lean

# The checks of the written subjects. Each writes the pairs that it accepts into one folder, and the last step judges them all in one run of `lake comparator`.
_charge-checks:
    #!/usr/bin/env bash
    set -euo pipefail
    export ZKC_SUBJECTS=$(mktemp -d "${TMPDIR:-/tmp}/zkc-subjects.XXXXXX")
    trap 'rm -rf "$ZKC_SUBJECTS"' EXIT
    cd lean/formal
    for check in AuditCharge WrittenCharge OccurrenceDepth ProofArguments GoalClause GoalClaim GoalStatement \
        CountCharge FreivaldsCharge GuessCharge EitherCharge TwiceCharge OutsideReading FixedTableSampling Judgment; do
      lake lean "checks/$check.lean"
    done

# Build the public formal package and audit its dependencies and proof controls.
test-formal:
    cd lean/formal && lake build && lake test
    just _charge-checks

# Parse and format the reference corpus and check source contracts and generated view types.
test-frontend:
    cd lean/compiler && lake build Zkc.Tests.Frontend.Reference Zkc.Frontend.Driver.SourcePhases Zkc.Frontend.Written.Selection
    cd lean/compiler && lake env lean --run Zkc/Tests/Frontend/SourceConformance.lean
    cd lean/compiler && lake env lean --run Zkc/Tests/Frontend/ProtocolViews.lean

# Print every admitted example root as a Lean module in which the kernel elaborates the program, compare each with its source, read a fixture back, and refuse four controls.
test-packages:
    cd lean/compiler && lake build Zkc.Frontend.Written.Package Zkc.Kernel Zkc.Tests.Frontend.PrintedPackageSupport Zkc.Tests.Frontend.PrintedFixtureCoverage
    cd lean/compiler && lake env lean --run Zkc/Tests/Frontend/PrintedPackages.lean

# Export the written knowledge claim and kernel-check the returning fork and source mutations.
test-written-knowledge: test-frontend
    cd lean/compiler && lake build zkc-knowledge Zkc.Tools.Audit
    cd lean/formal && lake build ZkcFormal.Written.GroupReplay ZkcFormal.Written.FiniteModel ZkcFormalTools.Policy
    cd lean/formal && lake env python3 checks/written_knowledge.py

# Audit the compiler package: the kernel's replay of the core, the vocabulary and their tests, no `sorry`, no axiom beyond `propext` and `Quot.sound`, the import rules.
audit:
    cd lean/compiler && lake exe zkc-audit

# Run the checks that need no build: the public tree, the documents and the generated Unicode tables.
check:
    bash .github/scripts/public-tree-guard.sh
    python3 scripts/check_docs.py --all
    python3 lean/compiler/scripts/generate_unicode_tables.py --check
