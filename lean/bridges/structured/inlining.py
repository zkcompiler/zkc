#!/usr/bin/env python3
"""Regenerate two actual native inlining pairs and check their retained proofs.

Reuses the structured bridge's tool retention, export, execution and evidence
driver. Exact byte comparisons bind the proof data to this run; they are not
an exporter or optimizer correctness theorem.
"""

import argparse
import os
from pathlib import Path
import sys

from check import MODULUS, ROOT, Suite, definition, digest, fixture_table, returned, write_json
from bridges.common.native_entry import native_subject
import snapshot

FIXTURES = Path(__file__).parent / "fixtures"
EXAMPLES = ROOT / "lean/ZkcExamples/Structured"
# Lake may rebuild imported modules before it checks a proof; allow for that.
LAKE_TIMEOUT = 1800
# The retained pairs, from `fixtures.toml`: stem, source module and data name.
SUBJECTS = tuple((stem, spec["module"], spec["data"])
                 for stem, spec in fixture_table().items() if spec["suite"] == "inlining")


def retain(suite, generated, maintained):
    if suite.args.write_fixtures:
        maintained.write_bytes(generated.read_bytes())
    if generated.read_bytes() != maintained.read_bytes():
        raise AssertionError(f"regeneration differs: {maintained}")
    suite.sources.append({"retained": str(maintained.relative_to(ROOT)),
                          "sha256": digest(maintained)})


def retained_subject(suite, stem, module, stage, source, symbol):
    label = f"{stem}-{stage.lower()}"
    subject = suite.export(label, source, symbol)
    native, exported, data = subject
    retain(suite, native, FIXTURES / f"{label}.mlir")
    retain(suite, exported, FIXTURES / f"{label}.json")
    namespace = f"ZkcExamples.Structured.{module}{stage}Data"
    rendered = exported.with_suffix(".lean")
    rendered.write_text(snapshot.render(data, namespace), encoding="utf-8")
    retain(suite, rendered, EXAMPLES / f"{module}{stage}Data.lean")
    return subject


def subject_cases(suite, stem, module, proof):
    source = FIXTURES / f"{stem}.zkc"
    suite.sources.append({"authored": str(source.relative_to(ROOT)), "sha256": digest(source)})
    flags = ["--source-format=zkc", f"--module={module}={source}", f"--subject={fixture_table()[stem]['subject']}"]
    original_text, interface_text, interface = native_subject(
        lambda command: suite.command(f"{stem}:frontend", command), suite.tools["compiler"], flags)
    (suite.directory / f"{stem}-interface.json").write_text(interface_text, encoding="utf-8")
    symbol = interface["protocol"]
    original = retained_subject(suite, stem, proof, "Original", original_text, symbol)
    if not (interface["original"] == digest(original[0])):
        raise AssertionError("frontend interface identifies different bytes")
    prepared = suite.directory / f"{stem}-prepared.mlir"
    suite.command(f"{stem}:prepare", [suite.tools["optimizer"],
        "--zkc-prepare-protocol=simplify=false optimize-finite=false", original[0], "-o", prepared])
    candidate_text = prepared.read_text(encoding="utf-8")
    candidate = retained_subject(suite, stem, proof, "Candidate", candidate_text, symbol)
    # Assert the intended transformation in the exported entry, not by searching
    # the whole module: preparation may retain dormant helper definitions.
    before = definition(original[2], symbol)[9][1]
    after = definition(candidate[2], symbol)[9][1]
    if not (any(instruction[0][0] == "call" for instruction in before)):
        raise AssertionError('bridges/structured/inlining.py:68: any(instruction[0][0] == "call" for instruction in before)')
    if not (all(instruction[0][0] != "call" for instruction in after)):
        raise AssertionError('bridges/structured/inlining.py:69: all(instruction[0][0] != "call" for instruction in after)')
    cases = [(0, 0, 0), (1, 1, 1), (2, 3, 5), (MODULUS - 1, MODULUS - 2, MODULUS - 3)]
    cases += [tuple(suite.rng.randrange(MODULUS) for _ in range(3)) for _ in range(suite.args.cases)]
    for index, values in enumerate(cases):
        a, b, c = values
        value = a + b * c if proof == "SchnorrResponse" else (1 - c) * a + c * b
        expected = returned(str(value % MODULUS))
        for stage, subject in (("original", original), ("candidate", candidate)):
            suite.compare(subject, f"{stem}-{stage}-{index}", list(map(str, values)), expected)
    if proof == "SchnorrResponse":
        # Change just the first addition, in the prepared entry. The helper
        # definition stays untouched. Native formation and Lean admission pass.
        if not (candidate_text.count("algebra.field_add") == 2):
            raise AssertionError('bridges/structured/inlining.py:81: candidate_text.count("algebra.field_add") == 2')
        mutated = retained_subject(suite, stem, proof, "Mutated",
            candidate_text.replace("algebra.field_add", "algebra.field_subtract", 1), symbol)
        suite.compare(mutated, "admitted-arithmetic-mutation", ["2", "3", "5"],
                      returned(str((2 - 3 * 5) % MODULUS)))
    # Refresh imported constructor objects before elaborating the proof source.
    # In particular, --write-fixtures must not prove an older cached subject.
    # Elan selects the toolchain before Lake processes arguments: --dir alone
    # would select the host default and could overwrite this package's objects.
    suite.command(f"{stem}:build-proof", [suite.args.lake,
        "build", f"ZkcExamples.Structured.{proof}"], cwd=ROOT / "lean", timeout=LAKE_TIMEOUT)
    suite.command(f"{stem}:kernel-proof", [suite.args.lake,
        "lean", EXAMPLES / f"{proof}.lean"], cwd=ROOT / "lean", timeout=LAKE_TIMEOUT)
    suite.sources.append({"proof": str((EXAMPLES / f"{proof}.lean").relative_to(ROOT)),
                          "sha256": digest(EXAMPLES / f"{proof}.lean")})


def run_cases(suite):
    args = suite.args
    write_json(suite.directory / "environment.json", {
        "affinity": sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else None,
        "threads": {key: os.environ.get(key) for key in
                    ("LEAN_NUM_THREADS", "OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS")},
        "toolchain": suite.command("lean-version", [args.lake, "env", "lean", "--version"],
                                    cwd=ROOT / "lean").strip(),
    })
    for stem, module, proof in SUBJECTS:
        suite.case(stem, lambda s=stem, m=module, p=proof: subject_cases(suite, s, m, p))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "build/compiler/zkc-compile")
    parser.add_argument("--optimizer", type=Path, default=ROOT / "build/compiler/zkc-opt")
    parser.add_argument("--reference", type=Path, default=ROOT / "build/compiler/test/zkc-structured_reference-test")
    parser.add_argument("--lean", type=Path, default=ROOT / "lean/.lake/build/bin/structured-source")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--cases", type=int, default=16)
    parser.add_argument("--seed", type=int, default=91837)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--write-fixtures", action="store_true",
                        help="replace retained subjects; checked proof sources are never generated")
    args = parser.parse_args()
    args.runtime = None
    suite = Suite(args)
    return suite.run(run_cases)


if __name__ == "__main__":
    sys.exit(main())
