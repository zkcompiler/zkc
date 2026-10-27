#!/usr/bin/env python3
"""Regenerate retained structured fixture bytes without running security proofs.

The differential suites still own their behavioral checks. This command uses
their manifest selections and the same constructor renderer to refresh the
source boundary independently of downstream mathematical consumers.
"""

import argparse
import json
from pathlib import Path
import sys

from check import ROOT, fixture, fixture_stems
from bridges.common.lean_render import Runner, digest
from bridges.common.native_entry import native_subject
import snapshot
import inlining

FIXTURES = Path(__file__).parent / "fixtures"


def retain(path, content, write):
    encoded = content.encode("utf-8")
    if write:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(encoded)
    if not path.is_file() or path.read_bytes() != encoded:
        raise ValueError(f"stale retained fixture: {path.relative_to(ROOT)}")


def authored(runner, compiler, stem):
    selected, modules, (_, module) = fixture(stem)
    flags = ["--source-format=zkc", f"--subject={selected}",
             *[f"--module={name}={path}" for name, path in modules.items()]]
    source, _, interface = native_subject(
        lambda command: runner.run(command).stdout, compiler, flags)
    return source, interface["protocol"], module


def export(runner, compiler, directory, source, symbol):
    directory.mkdir(parents=True, exist_ok=True)
    original = directory / "source.mlir"
    original.write_bytes(source.encode("utf-8"))
    exported = runner.run([compiler, "protocol-structured", original, f"--symbol={symbol}"]).stdout
    data = json.loads(exported)
    runner.check("exact-source-identity", data[:4] ==
                 ["zkc.structured-source/0", "original", "sha256:" + digest(source.encode()), symbol])
    return exported, data


class InliningFixtures:
    """Reuse the inlining suite's exact preparation and mutation generator."""

    def __init__(self, runner, args):
        self.runner, self.args = runner, args
        self.directory, self.sources = args.output, []
        self.tools = dict(compiler=args.compiler.resolve(), optimizer=args.optimizer.resolve())

    def command(self, label, command):
        return self.runner.run(command, name=label).stdout

    def export(self, label, source, symbol):
        directory = self.directory / label
        exported, data = export(self.runner, self.tools["compiler"], directory, source, symbol)
        path = directory / "source.json"
        path.write_text(exported, encoding="utf-8")
        return directory / "source.mlir", path, data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, required=True)
    parser.add_argument("--optimizer", type=Path, help="the matching native optimizer, for inlining fixtures")
    parser.add_argument("--fixture", action="append", help="select a manifest fixture or finite state fixture")
    parser.add_argument("--write-fixtures", action="store_true")
    parser.add_argument("--output", type=Path, required=True, help="command receipts and fresh exports")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    compiler = args.compiler.resolve()
    stems = [stem for suite in ("open_protocol", "primitives", "maps", "tables", "applications", "repeats", "inlining")
             for stem in fixture_stems(suite)] + ["total-state", "unit-state"]
    selected = args.fixture or stems
    if set(selected) - set(stems):
        parser.error("unknown fixture selection")
    if set(selected) & set(fixture_stems("inlining")) and args.optimizer is None:
        parser.error("inlining regeneration requires --optimizer")
    runner = Runner()
    results = []
    try:
        for stem in selected:
            if stem in fixture_stems("inlining"):
                (_, module, proof), = [row for row in inlining.SUBJECTS if row[0] == stem]
                suite = InliningFixtures(runner, args)
                inlining.regenerate_subject(suite, stem, module, proof)
                results.append(dict(fixture=stem, files=suite.sources))
                print(f"{stem}: exact original, prepared and mutation bytes agree", flush=True)
                continue
            if stem in ("total-state", "unit-state"):
                source = (ROOT / f"compiler/test/fixtures/finite/{stem}.mlir").read_text(encoding="utf-8")
                symbol, module = "main", "TotalState" if stem == "total-state" else "UnitState"
            else:
                source, symbol, module = authored(runner, compiler, stem)
            exported, data = export(runner, compiler, args.output / stem, source, symbol)
            targets = [(FIXTURES / f"{stem}.json", exported),
                       (ROOT / f"lean/ZkcExamples/Structured/{module}Data.lean",
                        snapshot.render(data, f"ZkcExamples.Structured.{module}Data"))]
            if stem not in ("total-state", "unit-state"):
                targets.append((FIXTURES / f"{stem}.mlir", source))
            for path, content in targets:
                retain(path, content, args.write_fixtures)
            results.append(dict(fixture=stem, source_sha256=digest(source.encode()),
                                export_sha256=digest(exported.encode()),
                                files={str(path.relative_to(ROOT)): digest(content.encode())
                                       for path, content in targets}))
            print(f"{stem}: exact native export and constructor bytes agree", flush=True)
    finally:
        (args.output / "regeneration.json").write_text(json.dumps(dict(
            commands=runner.commands, checks=runner.checks, fixtures=results), indent=2) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
