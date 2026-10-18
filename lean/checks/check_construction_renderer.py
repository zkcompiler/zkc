#!/usr/bin/env python3
"""Check the constructed-participant renderer's operation classification.

Synthetic exports exercise operation shapes independently of the compiled
examples. Each rendering is elaborated by Lean's parser and kernel, and the
rendered instructions are compared with constructors written independently of
the renderer. Wrongly shaped operations must refuse the whole export with the
renderer's shape diagnostic.
"""

import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import support.evidence  # noqa: E402
import support.lake  # noqa: E402

spec = importlib.util.spec_from_file_location("constructed_participant", HERE / "bridges/construction/render.py")
renderer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(renderer)

TRANSCRIPT = '!local.capability<"transcript:merlin3.bls12-381.fr64be/0">'
FIELD = '!algebra.field<"bls12-381.fr">'


def export(inputs, instructions, returned):
    policy = ["zkc.native-proof-policy/0", "entry", "role00000000", "role00000001", "0",
              "merlin3.bls12-381.fr64be/0", ["9"], [str(index) for index in range(len(inputs) - 1)], [],
              "zkc.framed/0", ""]
    return ["zkc.constructed-participant/0", "sha256:" + "0" * 64, "sha256:" + "1" * 64, policy, "_math_1",
            inputs, ["i1", TRANSCRIPT], instructions, returned]


def check(output, lake):
    output.mkdir(parents=True, exist_ok=True)
    # A validator that conjoins two Boolean checks, as a composed Sigma verifier does.
    conjunction = export(["i1", "i1", TRANSCRIPT], [["arith.andi", [], [], [0, 1], ["i1"], []]], [3, 2])
    source = renderer.render(conjunction, "RenderedConjunction").replace("module\n\n", "", 1)
    source = source.replace("public import Zkc.Construction.Participant\n", "")
    source = source.replace("@[expose] public section\n", "")
    source += '''
open Zkc.Construction in
example : RenderedConjunction.participant.instructions =
    [⟨.calculate .booleanAnd, [0, 1], [.data .boolean], []⟩] := by
  decide +kernel
'''
    path = output / "Rendered.lean"
    path.write_text("import Zkc.Construction.Participant\n" + source, encoding="utf-8")
    run = subprocess.run([lake, "env", "lean", path], cwd=HERE,
                         capture_output=True, encoding="utf-8", timeout=120)
    (output / "lean.log").write_text(run.stdout + run.stderr, encoding="utf-8")
    if run.returncode:
        raise AssertionError(run.stdout + run.stderr)
    # A conjunction must read and produce Booleans; another shape refuses the export.
    inputs = ["i1", "i1", FIELD, TRANSCRIPT]
    malformed = [export(inputs, [["arith.andi", [], [], operands, results, []]], [4, 3])
                 for operands, results in [([2, 2], ["i1"]), ([0, 1], [FIELD]), ([0], ["i1"])]]
    for data in malformed:
        try:
            renderer.render(data, "Rejected")
        except ValueError as error:
            if "boolean conjunction shape" not in str(error):
                raise AssertionError(f"renderer refused a malformed conjunction for another reason: {error}")
            continue
        raise AssertionError("renderer accepted a malformed Boolean conjunction")
    # An attributed conjunction is not the recognized operation; it is retained
    # as unsupported for the Lean rules to refuse.
    attributed = export(["i1", "i1", TRANSCRIPT],
                        [["arith.andi", [["site", ["string", "s"]]], [], [0, 1], ["i1"], []]], [3, 2])
    if '.unsupported "arith.andi"' not in renderer.render(attributed, "Unsupported"):
        raise AssertionError("renderer classified an attributed conjunction")
    report = {"status": "pass", "kernel_cases": 1, "refusal_cases": len(malformed), "unsupported_cases": 1,
              "renderer_sha256": support.lake.sha(Path(renderer.__file__)),
              "subject_sha256": support.lake.sha(path)}
    (output / "result.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=support.evidence.records("construction-renderer"))
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    print(json.dumps(check(args.output.resolve(), support.lake.resolve(args.lake)), indent=2))
