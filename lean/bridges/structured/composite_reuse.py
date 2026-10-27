#!/usr/bin/env python3
"""Check and regenerate the source-bound composite contract fixture.

Uses the maintained native export, constructor renderer, and Lean-owned body
printer. Direct Lean checks read existing dependency outputs; they never ask
Lake to build providers. Build the affected local modules before running this
driver. --write-fixtures refreshes the retained export and its two generated
modules; source equations and mathematical contracts remain authored.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from bridges.common.lean_render import (  # noqa: E402
    ROOT, CheckFailed, Runner, axioms_allowed, printed_axioms, regenerate,
)
from bridges.common.native_entry import native_subject  # noqa: E402
from bridges.structured import bodies, snapshot  # noqa: E402

LEAN = ROOT / "lean"
FIXTURE = Path(__file__).parent / "fixtures/composite-reuse.zkc"
DATA = "Tests.Generated.CompositeReuseData"
BODIES = "Tests.Generated.CompositeReuseBodies"
CONTRACTS = "Tests.CompositeReuseContracts."
CHECKS = "Tests.CompositeReuse."
SYMBOLS = {
    "s9h636f6d706f736974655h5368696674": "shift",
    "s9h636f6d706f736974655h4f75746572": "outer",
    "s9h636f6d706f736974655h5468697264": "third",
}
AUDITED = [
    "Tests.CompositeReuseSource.kernel_admission",
    "Tests.CompositeReuseBodies.outer_invocation", "Tests.CompositeReuseBodies.third_selected_root",
    "Tests.CompositeReuseBodies.outer_binding", "Tests.CompositeReuseBodies.third_binding",
    *(CONTRACTS + name for name in (
        "outer_sound", "third_sound", "outer_honest", "third_honest", "outer_frame", "third_frame")),
    *(CHECKS + name for name in (
        "prefixes", "missing_input_refused", "excluded_role", "changed_signature_refused", "wrong_operand_refused",
        "wrong_route_refused", "changed_frame_refused", "changed_capture_refused",
        "rejecting_is_not_complete", "same_yes_different_no")),
]


def lean(runner, path, *, output=None):
    command = ["lake", "env", "lean", "-DwarningAsError=true"]
    if output is not None:
        if not output.resolve().is_relative_to(LEAN.resolve()) or output.is_symlink():
            raise CheckFailed(f"refuse nonlocal output: {output}")
        output.parent.mkdir(parents=True, exist_ok=True)
        command += ["-o", output]
    return runner.run([*command, path], cwd=LEAN, expect=None)


def export(runner, compiler, directory, source):
    directory.mkdir(parents=True, exist_ok=True)
    flags = ["--source-format=zkc", "--subject=composite::Third", f"--module=composite={source}"]
    original, interface_text, interface = native_subject(
        lambda command: runner.run(command).stdout, compiler, flags)
    original_path = directory / "original.mlir"
    original_path.write_text(original)
    (directory / "interface.json").write_text(interface_text)
    exported = runner.run([
        compiler, "protocol-structured", original_path, f"--symbol={interface['protocol']}",
    ]).stdout
    data = json.loads(exported)
    (directory / "source.json").write_text(exported)
    runner.check("exact-source-identity:" + directory.name, data[:4] == [
        "zkc.structured-source/0", "original", "sha256:" + hashlib.sha256(original.encode()).hexdigest(),
        interface["protocol"],
    ])
    return exported, data


def refusal(runner, compiler, directory, name, source):
    selected = directory / name
    selected.mkdir(parents=True, exist_ok=True)
    source_path = selected / "source.zkc"
    source_path.write_text(source)
    if name == "wrong-role":
        result = runner.run([
            compiler, "language-emit", "--source-format=zkc", "--subject=composite::Third",
            f"--module=composite={source_path}",
        ], expect=None)
        runner.check(name, result.returncode != 0 and "source.roles:" in result.stderr)
        return
    _, data = export(runner, compiler, selected, source_path)
    module = snapshot.render(data, "Mutant").replace(
        "public import Zkc.Source.Structured.Import\n", """public import Zkc.Source.Structured.Import
public import Zkc.Source.Structured.UnitViews
public import Tests.Generated.CompositeReuseBodies
""") + """
open Zkc.Source Zkc.Source.Structured Tests.Generated.CompositeReuseBodies
namespace Mutant
structured_views snapshot helpers [] protocols [shift, outer, third]
end Mutant
"""
    path = selected / "Refusal.lean"
    path.write_text(module)
    result = lean(runner, path)
    diagnostics = result.stdout + result.stderr
    (selected / "lean.log").write_text(diagnostics)
    expected = ("structured_views: no authored protocol body for retained declaration"
                if name == "wrong-callee" else
                "structured_views: the authored bodies do not satisfy the admission phase")
    runner.check(name, result.returncode != 0 and expected in diagnostics and
                 (name == "wrong-callee" or "(kernel) declaration type mismatch" in diagnostics) and
                 not any(message in diagnostics for message in (
                     "timeout", "unknown module", "does not exist", "maximum number of heartbeats")))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--write-fixtures", action="store_true")
    args = parser.parse_args()
    os.environ["LEAN_NUM_THREADS"] = "1"
    directory = args.output.resolve()
    directory.mkdir(parents=True, exist_ok=True)
    runner = Runner()
    try:
        exported, data = export(runner, args.compiler.resolve(), directory, FIXTURE)
        regenerate(runner, FIXTURE.with_suffix(".json"), exported, args.write_fixtures)
        data_path = LEAN / "Tests/Generated/CompositeReuseData.lean"
        regenerate(runner, data_path, snapshot.render(data, DATA), args.write_fixtures)
        compiled = lean(runner, data_path, output=LEAN / ".lake/build/lib/lean/Tests/Generated/CompositeReuseData.olean")
        if compiled.returncode:
            raise CheckFailed(compiled.stdout + compiled.stderr)
        printed = bodies.generate(DATA, BODIES, names=SYMBOLS, runner=runner, fresh=True)
        regenerate(runner, LEAN / "Tests/Generated/CompositeReuseBodies.lean", printed, args.write_fixtures)
        result = lean(runner, LEAN / "Tests/CompositeReuse.lean")
        (directory / "contracts.log").write_text(result.stdout + result.stderr)
        runner.check("source-contract-clients", result.returncode == 0, result.stdout + result.stderr)
        runner.check("opaque-reuse", "COMPOSITE-OPAQUE-REUSE-PASS" in result.stdout)
        for name in AUDITED:
            runner.check("axioms:" + name, axioms_allowed(result.stdout, name))
        audited = lean(runner, LEAN / "Tests/CompositeReuseAudit.lean")
        (directory / "audit.log").write_text(audited.stdout + audited.stderr)
        runner.check("all-owned-declarations", audited.returncode == 0 and
                     "COMPOSITE-REUSE-AUDIT-PASS" in audited.stdout, audited.stdout + audited.stderr)
        source = FIXTURE.read_text()
        for name, changed in (
            ("wrong-operand", source.replace("(ignored, value, first, enabled)", "(value, ignored, first, enabled)", 1)),
            ("wrong-role", source.replace("Shift roles(V,P)(ignored, value, first, enabled)",
                                          "Shift roles(P,V)(ignored, value, first, enabled)", 1)),
            ("wrong-callee", source.replace("Outer", "Other")),
            ("wrong-capture", source.replace("(ignored, shifted, second, enabled)",
                                             "(ignored, shifted, second, true)", 1)),
        ):
            runner.check("mutation-changed:" + name, changed != source)
            refusal(runner, args.compiler.resolve(), directory / "refusals", name, changed)
        (directory / "axioms.json").write_text(json.dumps(printed_axioms(result.stdout), indent=2) + "\n")
        print(f"PASS {len(runner.checks)} source, generation, contract, axiom and refusal checks")
    finally:
        (directory / "checks.json").write_text(json.dumps({
            "commands": runner.commands, "checks": runner.checks,
        }, indent=2) + "\n")


if __name__ == "__main__":
    main()
