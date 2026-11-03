#!/usr/bin/env python3
"""Reproduce the actual plain table and aggregate-message fixtures.

This driver invokes the native compiler and the existing transparent renderers.
It neither evaluates participants nor selects a security claim or baseline.
"""
import argparse
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "lean"))
sys.path.insert(0, str(ROOT / "common/tests"))
from bridges.common import interface as language_interface, source_format  # noqa: E402
from bridges.common.lean_render import Runner, digest, require  # noqa: E402
from bridges.pipeline.source_inventory import Inventory, decode  # noqa: E402
from bridges.construction import pair  # noqa: E402
from bridges.structured import bodies, snapshot  # noqa: E402
from support.project import project_arguments  # noqa: E402

def batch_names(inventory, paired):
    """Presentation names select authored substitutions and actual callees."""
    statics = [["F", ["field", "koala-bear"]]]
    def authored(owner):
        return inventory.authored(owner, statics=statics, scoped=[], domains=[]).symbol
    batch = authored("batch_opening::batch_values")
    step = inventory.single_target(batch, "fold", 2)
    require(step.kind == "generated" and step.declaration["purpose"] == "finite"
            and step.declaration["part"] == "body", "batch step has no finite-body provenance")
    opening = inventory.single_target(step.symbol, "call")
    require(opening.kind == "instance" and opening.declaration["template"]["kind"] == "scoped"
            and opening.declaration["template"]["owner"] == "batch_opening::batch_values",
            "batch callback has another lexical owner")
    realizations = [row[1] for row in inventory.snapshot[7] if row[0] == "realize" and row[4] == batch]
    require(len(realizations) == 1, "batch body has no unique mathematical realization")
    names = {batch: "batchValues", step.symbol: "batchStep", opening.symbol: "checkOpening",
             realizations[0]: "mathematicalAdmission", authored("batch_opening::BatchValues"): "formula",
             authored("batch_opening::check_batch"): "checkBatch", authored("batch_opening::CheckBatch"): "run"}
    if paired:
        names[authored("reusable_aggregate::TwoBatches")] = "pair"
    return names


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--subject", action="append", choices=["table", "batch", "two-batches"],
                        help="regenerate only the selected fixture (default: all)")
    parser.add_argument("--fresh-bodies", action="store_true",
                        help="elaborate typed body printers without Lake replay")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    args.compiler = args.compiler.resolve()
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    os.environ.setdefault("LEAN_NUM_THREADS", "2")
    runner = Runner()
    report = {"status": "running", "compiler_sha256": digest(args.compiler.read_bytes()),
              "subjects": args.subject or ["table", "batch", "two-batches"], "artifacts": {}}

    def generated(path, value):
        if args.write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(value)
        runner.check("exact-generated:" + path.name, path.read_text() == value)

    # A project-backed subject takes its root manifest's source format from the
    # SDK; the explicit module map takes the format of the modules it names.
    table = ROOT / "examples/projects/table/zkc.toml"
    two_batches = ROOT / "lean/fixtures/reusable-aggregate/zkc.toml"
    subjects = [
        ("table", "table_relation::CheckMembership<example::F>",
         project_arguments(table), "TableMembership", table),
        ("batch", "batch_opening::CheckBatch<batch_opening::Scalar>",
         ["--module=batch_opening=lean/bridges/construction/fixtures/batch-opening.zkc",
          *project_arguments(ROOT / "libraries/core/traversal/zkc.toml")], "BatchOpening", None),
        ("two-batches", "reusable_aggregate::TwoBatches<batch_opening::Scalar>",
         project_arguments(two_batches), "ReusableAggregateTwoBatches", two_batches),
    ]
    inventories = {}
    try:
        for name, subject, modules, stem, project in subjects:
            if args.subject and name not in args.subject:
                continue
            directory = args.output / name
            directory.mkdir(exist_ok=True)
            flags = source_format.with_option(["--subject=" + subject, *modules],
                                              None if project is None else source_format.of_project(project))

            def run(mode, *arguments):
                return runner.run([args.compiler, mode, *arguments], name=name + ":" + mode).stdout

            source = run("language-emit", *flags)
            source_path = directory / "source.mlir"
            source_path.write_text(source)
            interface_text = run("language-interface", *flags)
            (directory / "interface.json").write_text(interface_text)
            interface = language_interface.loads(interface_text)
            runner.check(name + ":source-identity", interface["original"] == digest(source.encode()))
            original = run("protocol-structured", source_path, "--symbol=" + interface["protocol"])
            (directory / "original.json").write_text(original)
            if name == "table":
                runner.check("exact-library-source", source ==
                             (ROOT / "lean/bridges/structured/fixtures/table-membership.mlir").read_text())
            checked = run("language-check", *flags, "--source-correspondence")
            (directory / "source-correspondence.json").write_text(checked)
            inventories[name] = Inventory(decode(checked)["source_correspondence"],
                source=source.encode(), interface_text=interface_text, original_text=original)
            original_data = json.loads(original)
            entries = [entry for entry in original_data[7]
                       if entry[0] == "function" and entry[1] == interface["protocol"]]
            runner.check(name + ":one-entry", len(entries) == 1)
            entry = entries[0]
            roster = entry[6]
            runner.check(name + ":paired-roster", roster[0] == "protocol" and len(roster[1]) == 2)
            producer, validator = roster[1]
            publics = [str(index) for index, (type_, scope) in enumerate(zip(entry[4], roster[2]))
                       if validator in scope and type_[0] != "service"]
            policy = ["zkc.native-proof-policy/0", interface["protocol"], producer, validator,
                      "0", "", [], publics, [], "zkc.framed/0", "", []]
            policy_path = directory / "policy.json"
            policy_path.write_text(json.dumps(policy))
            candidate = directory / "candidate.mlir"
            candidate.write_text(run("protocol-construct-proof", source_path, policy_path))
            exported = run("protocol-constructed-pair", source_path, policy_path, candidate)
            (directory / "pair.json").write_text(exported)
            children = json.loads(exported)
            identities = {}
            for role, child in zip(("producer", "validator"), children[1:]):
                text = run("protocol-constructed-participant", source_path, policy_path, candidate,
                           "--role=" + role)
                runner.check(name + ":pair-" + role, json.loads(text) == child)
                (directory / (role + ".json")).write_text(text)
                identities[role] = "sha256:" + digest(text.encode())
            report["artifacts"][name] = dict(identities, source="sha256:" + digest(source.encode()),
                                            original="sha256:" + digest(original.encode()),
                                            pair="sha256:" + digest(exported.encode()))
            namespace = ("Tests." if name == "two-batches" else "ZkcExamples.Construction.") + stem
            generated(ROOT / ("lean/" + namespace.replace(".", "/") + "Artifacts.lean"),
                      pair.render(children, namespace + "Artifacts"))
            data_namespace = "ZkcExamples.Structured.TableMembershipData" if name == "table" else namespace + "Data"
            generated(ROOT / ("lean/" + data_namespace.replace(".", "/") + ".lean"),
                      snapshot.render(json.loads(original), data_namespace))
        for name, namespace in [
            ("batch", "ZkcExamples.Construction.BatchOpening"),
            ("two-batches", "Tests.ReusableAggregateTwoBatches"),
        ]:
            if args.subject and name not in args.subject:
                continue
            runner.run([args.lake, "build", namespace + "Data"],
                       cwd=ROOT / "lean", name=name + ":build-data")
            generated(ROOT / ("lean/" + namespace.replace(".", "/") + "Bodies.lean"),
                      bodies.generate(namespace + "Data", namespace + "Bodies",
                                      names=batch_names(inventories[name], name == "two-batches"),
                                      inventory=inventories[name], runner=runner, lake=args.lake,
                                      fresh=args.fresh_bodies))
        report["status"] = "pass"
    finally:
        if report["status"] == "running":
            report["status"] = "failed"
        report.update(commands=runner.commands, checks=runner.checks)
        (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
