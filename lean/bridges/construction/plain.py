#!/usr/bin/env python3
"""Reproduce the actual plain table and aggregate-message construction fixtures.

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
from bridges.common.lean_render import Runner, digest  # noqa: E402
from bridges.construction import pair  # noqa: E402
from bridges.structured import snapshot  # noqa: E402
from support.project import project_arguments  # noqa: E402

BATCH_NAMES = {
    "zkl_b26f24aff1f462f4c3e9ea4c594fd6eaaac4e0d13a163302bc46f14e913cc892": "checkOpening",
    "finite_zkl_040b90e6fc9f7c074519f3a904772619b0e3c63ed7b7a051cbc3db4b3c514ff3_s3_body": "batchStep",
    "zkl_040b90e6fc9f7c074519f3a904772619b0e3c63ed7b7a051cbc3db4b3c514ff3": "batchValues",
    "zkl_realization_399ea9b40064d603529daacd08256f0188b616e6e22db3af605c971670349b32": "realization",
    "zkf_53219b51c062230506c8b229ef72062dff0e276e6336e241e0b2d30a9a6fe712": "formula",
    "zkl_765e0fbfb20c4afe7930d2c0cbb531d52446ae1c25c74ad1237691d8738b0a85": "checkBatch",
    "zkl_206d594942dc6f123848ad35c8fcdc7017b483db9ccd5c0651d1ad5c850eceab": "run",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    args.compiler = args.compiler.resolve()
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    os.environ["LEAN_NUM_THREADS"] = "2"
    runner = Runner()
    report = {"status": "running", "compiler_sha256": digest(args.compiler.read_bytes())}

    def generated(path, value):
        if args.write:
            path.write_text(value)
        runner.check("exact-generated:" + path.name, path.read_text() == value)

    subjects = [
        ("table", "table_relation::CheckMembership<example::F>",
         project_arguments(ROOT / "examples/projects/table/zkc.toml"), "TableMembership"),
        ("batch", "batch_opening::CheckBatch<batch_opening::Scalar>",
         ["--module=batch_opening=lean/bridges/construction/fixtures/batch-opening.zkc",
          *project_arguments(ROOT / "libraries/core/traversal/zkc.toml")], "BatchOpening"),
    ]
    try:
        for name, subject, modules, stem in subjects:
            directory = args.output / name
            directory.mkdir(exist_ok=True)
            flags = ["--source-format=zkc", "--subject=" + subject, *modules]

            def run(mode, *arguments):
                return runner.run([args.compiler, mode, *arguments], name=name + ":" + mode).stdout

            source = run("language-emit", *flags)
            source_path = directory / "source.mlir"
            source_path.write_text(source)
            interface_text = run("language-interface", *flags)
            (directory / "interface.json").write_text(interface_text)
            interface = json.loads(interface_text)
            runner.check(name + ":source-identity", interface["original"] == digest(source.encode()))
            if name == "table":
                runner.check("exact-library-source", source ==
                             (ROOT / "lean/bridges/structured/fixtures/table-membership.mlir").read_text())
            policy = ["zkc.native-proof-policy/0", interface["protocol"], "role00000000", "role00000001",
                      "0", "", [], ["0", "1"], [], "zkc.framed/0", ""]
            policy_path = directory / "policy.json"
            policy_path.write_text(json.dumps(policy))
            candidate = directory / "candidate.mlir"
            candidate.write_text(run("protocol-construct-proof", source_path, policy_path))
            exported = run("protocol-constructed-pair", source_path, policy_path, candidate)
            (directory / "pair.json").write_text(exported)
            original = run("protocol-structured", source_path, "--symbol=" + interface["protocol"])
            (directory / "original.json").write_text(original)
            namespace = "ZkcExamples.Construction." + stem
            generated(ROOT / ("lean/" + namespace.replace(".", "/") + "Artifacts.lean"),
                      pair.render(json.loads(exported), namespace + "Artifacts"))
            data_namespace = "ZkcExamples.Structured.TableMembershipData" if name == "table" else namespace + "Data"
            generated(ROOT / ("lean/" + data_namespace.replace(".", "/") + ".lean"),
                      snapshot.render(json.loads(original), data_namespace))
        runner.run([args.lake, "build", "ZkcExamples.Construction.BatchOpeningData"],
                   cwd=ROOT / "lean", name="batch:build-data")
        runner.run([sys.executable, ROOT / "lean/bridges/structured/bodies.py", "--data",
                    "ZkcExamples.Construction.BatchOpeningData", "--namespace",
                    "ZkcExamples.Construction.BatchOpeningBodies", "--output",
                    ROOT / "lean/ZkcExamples/Construction/BatchOpeningBodies.lean",
                    *["--name=" + name + "=" + local for name, local in BATCH_NAMES.items()],
                    *([] if args.write else ["--check"])], name="batch:typed-bodies")
        report["status"] = "pass"
    finally:
        if report["status"] == "running":
            report["status"] = "failed"
        report.update(commands=runner.commands, checks=runner.checks)
        (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
