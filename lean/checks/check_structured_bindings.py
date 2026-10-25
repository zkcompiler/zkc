#!/usr/bin/env python3
"""Regenerate actual-source bindings and reject stale structural certificates.

Python only schedules Lean and compares serialized artifacts. Typed source
mutations and every semantic/proof check are performed by Lean.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import types


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


CLIENTS = ("SmallSumcheck", "TwoSums", "GkrRounds")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--overlay", type=Path)
    parser.add_argument("--records", type=Path)
    options = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    directory = (options.records or Path(tempfile.mkdtemp(prefix="zkc-structured-bindings-"))).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, "LEAN_NUM_THREADS": "2"}
    # Poison the legacy Python proof producer in this orchestration process.
    # The Lean route must still produce identical checked artifacts.
    class ForbiddenLegacyProducer:
        def __new__(cls, *args, **kwargs):
            raise AssertionError("legacy Python Evaluator/Step route was used")

    legacy = types.ModuleType("bridges.structured.normal_forms")
    legacy.Evaluator = ForbiddenLegacyProducer
    legacy.Step = ForbiddenLegacyProducer
    sys.modules[legacy.__name__] = legacy
    for producer in (legacy.Evaluator, legacy.Step):
        try:
            producer()
        except AssertionError:
            pass
        else:
            raise AssertionError("legacy route refusal control failed")
    if options.overlay:
        paths = [options.overlay.resolve()]
        paths.extend((root / ".lake/packages").glob("*/.lake/build/lib/lean"))
        paths.append(root / ".lake/build/lib/lean")
        env["LEAN_PATH"] = os.pathsep.join(map(str, paths))

    def run(path: Path, *arguments: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(["lean", *arguments, str(path)], cwd=root, env=env,
                              text=True, capture_output=True, timeout=180)

    regenerated = directory / "regenerated"
    result = subprocess.run(
        ["lean", "--run", "checks/RunGenerators.lean", "bindings", str(regenerated)],
        cwd=root, env=env, text=True, capture_output=True, timeout=180,
    )
    (directory / "regenerate.log").write_text(result.stdout + result.stderr)
    require(result.returncode == 0, "generation failed; see regenerate.log")
    generated = []
    relative = Path("ZkcExamples/Structured/Generated/Bindings")
    for client in CLIENTS:
        for printed, shipped in [
            (".lean", ".lean"), (".inputs.lean", "Inputs.lean"), (".callbacks.lean", "Callbacks.lean"),
            (".template.lean", "Gate.lean" if client == "GkrRounds" else "Sumcheck.lean"),
        ]:
            expected = (regenerated / relative / (client + printed)).read_bytes()
            actual = (root / relative / (client + shipped)).read_bytes()
            require(expected == actual, f"stale generated artifact: {client + shipped}")
            require(b"public import ZkcTools" not in actual, f"proof imports tools: {client + shipped}")
            require(b"ZkcTools.StructuredSource.Presentation" not in actual, f"proof uses tool metadata: {client + shipped}")
            generated.append({"module": client + shipped,
                              "sha256": hashlib.sha256(actual).hexdigest()})
        ledger = json.loads((regenerated / relative / (client + ".obligations.json")).read_text())
        require(ledger["attribution_is_proof_status"] is False, 'attribution must not establish proof status')
        require(all(row["expected_layer"] == "I" and row["route"] == "general-rule"
                   and row["proof_status"] == "external-kernel-receipt-required"
                   for row in ledger["structural"]), 'structural obligations must require external kernel receipts')
        require(all(row["proof_status"] == "open" for row in ledger["mathematical_helpers"]
                   if row["route"] == "unattributed"), 'unattributed mathematics must retain open obligations')
    for printed, shipped in [(".lean", ".lean"), (".inputs.lean", "Inputs.lean"),
                             (".callbacks.lean", "Callbacks.lean")]:
        stem = "Tests/Generated/StructuredBindingsGeneric"
        expected = (regenerated / (stem + printed)).read_bytes()
        actual = (root / (stem + shipped)).read_bytes()
        require(expected == actual, f"stale generic callback fixture: {shipped}")
        generated.append({"module": stem + shipped,
                          "sha256": hashlib.sha256(actual).hexdigest()})
    # Production tools must not import mathematical examples, even transitively
    # through the ledger or default callback printer.
    for source_directory in [root / "ZkcTools/StructuredSource/Bindings",
                      root / "Zkc/Source/Structured/Bindings"]:
        require(all("ZkcExamples" not in path.read_text() for path in source_directory.glob("*.lean")), 'production binding tools must not import examples')

    header = """import Tests.StructuredBindingsSources
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcExamples.Structured.Generated.Bindings
open Tests.StructuredBindingsSources
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
"""
    controls = {
        "same-name-changed-helper": """
example : actualAppend.body.erase = changedAppend.erase := by
  kernel_rfl
""",
        "dropped-actual-guard": """
example : normalize SmallSumcheckCallbacks.protocol0Role1Callback0Signature
    (dropGuards SmallSumcheckCallbacks.protocol0Role1Callback0Body) 1 2
    SmallSumcheckCallbacks.protocol0Role1Callback0Pattern =
      .ok SmallSumcheckCallbacks.protocol0Role1Callback0Form := by
  kernel_rfl
""",
        "changed-actual-private-return": """
example : normalize TwoSums.protocol0Role0Signature (swapPrivate TwoSums.definition0.body) 0 2
    TwoSums.protocol0Role0Pattern = .ok TwoSums.protocol0Role0Form := by
  kernel_rfl
""",
        "same-typed-operand-permutation": """
example : GkrRoundsGate.valueDefinition.body.component
    (Evaluation.meaning (.silent (participantInterface ℚ ℚ))
      (Zkc.Source.Structured.Bindings.helpers GkrRounds.payload).closed)
    (Evaluation.componentOperation (.silent _)
      (Zkc.Source.Structured.Bindings.helpers GkrRounds.payload))
    ((Values.cons (some (1 : ℚ)) (.cons (some 2) (.cons (some 3) (.cons (some 4) .nil))) :
      Values (Component (assignment ℚ ℚ)) GkrRoundsGate.valueDefinition.inputs).get) =
      PIR.Process.done (.cons (some (Zkc.Protocols.AlgebraicRounds.Gate.value (2 : ℚ) 1 3 4)) .nil) := by
  kernel_rfl
""",
    }
    refused = []
    for name, body in controls.items():
        path = directory / f"{name}.lean"
        path.write_text(header + body)
        result = run(path, "-DwarningAsError=true", "-DElab.async=false")
        log = result.stdout + result.stderr
        (directory / f"{name}.log").write_text(log)
        require(result.returncode > 0, f"stale certificate accepted: {name}")
        require("error" in log and any(reason in log for reason in [
            "rfl", "definitionally equal", "declaration type mismatch"]), name)
        require(not any(error in log for error in ["unexpected token", "Unknown identifier",
                                                  "object file", "failed to synthesize"]), log)
        refused.append({"name": name, "status": "kernel-equation-refused"})
        print(f"PASS {name}", flush=True)
    # Compile the actual emitter output for dense and sparse selections. The
    # generated clients check dependent lookup, role remapping and private masks;
    # the emitter also rejects quadratic catalogue duplication on scaled inputs.
    dispatch = directory / "dispatch"
    result = subprocess.run(
        ["lean", "--run", "checks/RunGenerators.lean", "dispatch-controls", str(dispatch)],
        cwd=root, env=env, text=True, capture_output=True, timeout=180,
    )
    (directory / "dispatch-generate.log").write_text(result.stdout + result.stderr)
    require(result.returncode == 0, "dispatch generation failed; see dispatch-generate.log")
    objects = dispatch / "objects"
    objects.mkdir(parents=True, exist_ok=True)
    env["LEAN_PATH"] = str(objects.resolve()) + os.pathsep + env.get("LEAN_PATH", "")
    checked_dispatch = []
    for name in ("DispatchInputs", "DispatchAll", "DispatchProtocols", "DispatchRoles",
                 "DispatchSparse", "DispatchRootOnly", "DispatchEmpty"):
        target = objects / (name + ".olean")
        target.unlink(missing_ok=True)
        result = run(dispatch / (name + ".lean"), "-DwarningAsError=true", "-DElab.async=false",
                     "--root=" + str(dispatch.resolve()), "-o", str(target.resolve()))
        log = result.stdout + result.stderr
        (directory / (name + ".log")).write_text(log)
        require(result.returncode == 0 and "sorryAx" not in log, f"dispatch client failed: {name}")
        checked_dispatch.append(name)
        print(f"PASS {name}", flush=True)
    report = {"format": "zkc.structured-binding-controls/0", "legacy_evaluator_step_disabled": True,
              "generated": generated,
              "dispatch": checked_dispatch,
              "mutations": refused}
    (directory / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS {len(generated)} generated views; {len(refused)} stale certificates refused")


if __name__ == "__main__":
    main()
