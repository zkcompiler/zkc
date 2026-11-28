# Development commands. The Lean toolchain comes from lean/compiler/lean-toolchain through elan.
set shell := ["bash", "--noprofile", "--norc", "-euo", "pipefail", "-c"]
set positional-arguments

# List the recipes.
default:
    @just --list --unsorted

# Build the compiler package: the core and its tests, whose checks run when they are built. A module that logs fails the build.
build:
    cd lean/compiler && lake build --iofail

# Build and test the compiler package and audit it.
test:
    cd lean/compiler && lake build --iofail && lake test
    just audit

# Build the runtime library and run CFRG draft-04 and end-to-end example runtime verification tests.
test-runtime:
    cd lean/compiler && lake build --iofail ZkcRuntime ZkcRuntimeTests zkc-runtime-tests zkc-check
    cd lean/compiler && lake exe zkc-runtime-tests
    cd lean/compiler && lake exe zkc-check cfrg-vectors

# Check source verifier certificates and replay the interactive formal library through the kernel.
test-interactive:
    cd lean/compiler && lake build --iofail Zkc.Tools.Audit
    cd lean/formal && lake build --iofail ZkcFormal.Interactive ZkcFormalTests.Interactive ZkcFormalTests.Reuse.Controls ZkcFormalTests.SourceHonestSumcheck
    cd lean/formal && lake lean checks/SourceProtocols.lean
    cd lean/formal && lake lean checks/OracleNames.lean
    cd lean/formal && lake lean checks/WorldObservation.lean
    cd lean/formal && lake env lean --run checks/AuditInteractive.lean

# Check source draw charges, the kernel's counts, the direct publications and the charge issuer.
test-written-charge: _charge-checks
    cd lean/formal && lake lean checks/ReplayCharge.lean

# The checks of the written subjects. Each writes the pairs that it accepts into one folder, and the last step judges them all in one run of `lake comparator`.
_charge-checks:
    #!/usr/bin/env bash
    set -euo pipefail
    export ZKC_SUBJECTS=$(mktemp -d "${TMPDIR:-/tmp}/zkc-subjects.XXXXXX")
    trap 'rm -rf "$ZKC_SUBJECTS"' EXIT
    cd lean/formal
    for check in AuditCharge WrittenCharge OccurrenceDepth ProofArguments GoalClause GoalClaim WrittenModel GoalStatement \
        WrittenDecisions WrittenPublish WrittenViews WrittenFees WrittenBoundGuard CountCharge FreivaldsCharge GuessCharge EitherCharge TwiceCharge \
        OutsideReading FixedTableSampling Judgment; do
      lake lean "checks/$check.lean"
    done

# Build the public formal package and audit its dependencies and proof controls.
test-formal:
    cd lean/formal && lake build --iofail && lake test
    just _charge-checks

# Build the frontend libraries and run the source, generated-view and frontend driver suites.
test-frontend:
    cd lean/compiler && lake build --iofail ZkcFrontend ZkcFrontendTools ZkcFrontendTests zkc-syntax zkc-check zkc-frontend-tests
    cd lean/compiler && lake env lean --run Zkc/Tests/Frontend/SourceConformance.lean
    cd lean/compiler && lake env lean --run Zkc/Tests/Frontend/ProtocolViews.lean
    cd lean/compiler && lake exe zkc-frontend-tests
    cd lean/compiler && python3 scripts/test_written_goals.py

# Print every admitted example root as a Lean module in which the kernel elaborates the program, compare each with its source, read a fixture back, and refuse four controls.
test-packages:
    cd lean/compiler && lake build --iofail Zkc.Frontend.Written.Package ZkcKernel Zkc.Tests.Frontend.PrintedPackageSupport Zkc.Tests.Frontend.PrintedFixtureCoverage
    cd lean/compiler && lake env lean --run Zkc/Tests/Frontend/PrintedPackages.lean

# Export the written knowledge claim and kernel-check the returning fork and source mutations.
test-written-knowledge: test-frontend
    cd lean/compiler && lake build --iofail zkc-knowledge Zkc.Tools.Audit
    cd lean/formal && lake build --iofail ZkcFormal.Written.GroupReplay ZkcFormal.Written.FiniteModel ZkcFormalTools.Policy
    cd lean/formal && lake env python3 checks/written_knowledge.py

# Check compiler library coverage and audit the package: the kernel's replay of the core, the vocabulary, the subject library and the tests of the first two, no `sorry`, no axiom beyond `propext` and `Quot.sound`, the import rules.
audit:
    cd lean/compiler && lake exe zkc-audit

# Run the checks that need no build: the public tree, the documents and the generated Unicode tables.
check:
    bash .github/scripts/public-tree-guard.sh
    python3 scripts/check_docs.py --all
    python3 lean/compiler/scripts/generate_unicode_tables.py --check
