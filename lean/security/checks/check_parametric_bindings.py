#!/usr/bin/env python3
"""Compile fresh nominal templates and their deliberate dependent-type failures.

Run from a prepared security package with lake env. Outputs and measurements
stay in --records; this driver never updates packages or repository fixtures.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--records", type=Path)
    args = parser.parse_args()
    package = Path(__file__).resolve().parents[1]
    records = (args.records or Path(tempfile.mkdtemp(prefix="zkc-parametric-"))).resolve()
    records.mkdir(parents=True, exist_ok=True)
    generated = records / "generated"
    generated.mkdir(exist_ok=True)
    environment = dict(os.environ, LEAN_NUM_THREADS="2")
    if not environment.get("LEAN_PATH"):
        environment["LEAN_PATH"] = subprocess.check_output(
            ["lake", "env", "printenv", "LEAN_PATH"], cwd=package, text=True).strip()
    environment["LEAN_PATH"] = str(generated) + os.pathsep + environment["LEAN_PATH"]
    commands = []

    def run(label: str, command: list[str], *, refuses: bool = False) -> str:
        started = time.monotonic()
        metrics = records / (label + ".time")
        result = subprocess.run(["/usr/bin/time", "-f", "%e %U %S %M", "-o", str(metrics), *command],
                                cwd=package, env=environment, text=True, capture_output=True, timeout=240)
        output = result.stdout + result.stderr
        (records / (label + ".log")).write_text(output)
        commands.append({"label": label, "command": command, "returncode": result.returncode,
                         "elapsedSeconds": time.monotonic() - started,
                         "timeUserSystemPeakKiB": metrics.read_text().splitlines()[-1],
                         "expectedRefusal": refuses})
        (records / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        if refuses:
            if not result.returncode or "error:" not in output:
                raise AssertionError(f"{label}: expected a Lean diagnostic")
            if any(word in output for word in ("unknown module", "object file", "maximum recursion",
                                               "maximum number of heartbeats", "Unknown identifier", "sorryAx")):
                raise AssertionError(f"{label}: infrastructure failure is not a refusal")
        elif result.returncode or "sorryAx" in output:
            raise AssertionError(f"{label}: checking failed; see {records / (label + '.log')}")
        print(("REFUSED " if refuses else "PASS ") + label, flush=True)
        return output

    run("generate", ["lean", "-DwarningAsError=true", "--run", "checks/RunParametricBindings.lean", str(generated)])

    def compile_module(name: str, *, refuses: bool = False) -> None:
        source = generated / "ParametricClients" / (name + ".lean")
        run(name, ["lean", "-DwarningAsError=true", "--root=" + str(generated),
                   "-o", str(source.with_suffix(".olean")), str(source)], refuses=refuses)

    for name in ("Mixed", "MixedInstallation", "Gates", "GatesInstallation", "GatesRoot"):
        compile_module(name)
    for name in ("WrongModel", "WrongHelper", "WrongDomain", "WrongRole"):
        compile_module(name, refuses=True)

    # Keep every generated certificate while changing the captured operational
    # prefix. The actual source lookup must refuse the altered equation.
    original = (generated / "ParametricClients/GatesRoot.lean").read_text()
    wrong = original.replace("ParametricClients.GatesRoot", "ParametricClients.WrongCapture")
    assert "protocols.take 1" in wrong
    wrong = wrong.replace("protocols.take 1", "protocols.take 0", 1)
    # Check the exact immutable-prefix evidence first. Comparing entire failed
    # open processes would unfold large unrelated continuations in the control.
    wrong = wrong.split("theorem source_capture", 1)[0] + "end\nend ParametricClients.WrongCapture\n"
    (generated / "ParametricClients/WrongCapture.lean").write_text(wrong)
    compile_module("WrongCapture", refuses=True)

    audit = '''import ParametricClients.MixedInstallation
import ParametricClients.GatesInstallation
import ParametricClients.GatesRoot
import Zkc.Source.Structured.DomainParticipantInterpretation
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings Zkc.Source.Structured.NormalForm
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ParametricClients.Consumers
open MixedInstallation
theorem mixed (a b : model.Field "koala-bear") (service : Nat) :
    Mixed.program.participantOn model 1 (.cons (some a) (.cons (some b) (.cons (some service) .nil))) =
      Mixed.template.view model (Mixed.helperTables model) (Mixed.capture model)
        results processes {} (.cons (some a) (.cons (some b) (.cons (some service) .nil))) := by
  exact (Program.participantOn_eq_plain (model := model) Mixed.program 1 _).trans
    (binding {} (RosterDistinct.root 1 2) _)
#print axioms mixed
#print axioms MixedInstallation.binding
#print axioms GatesInstallation.binding
#print axioms GatesRoot.source_capture
end ParametricClients.Consumers
'''
    (generated / "ParametricClients/Consumers.lean").write_text(audit)
    compile_module("Consumers")

    # These are applications of one list-composition proof, not cloned gate
    # mathematics or independently written root wrappers. Each call is the
    # retained imported Rounds verifier followed by the executable terminal.
    for count in (1, 2, 4):
        source = f'''import TestsSecurity.GkrFiniteGate
import Lean
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Examples.Components
open ZkcSecurity.Families.Sumcheck
noncomputable section
namespace ParametricClients.Calls{count}
open TestsSecurity.GkrFiniteGate
theorem binding : GkrFiniteCalls.verifier (G := ℚ) 83 (inputs {count} false) =
    FiniteCalls.all (GkrFiniteCalls.view 83) (inputs {count} false) :=
  GkrFiniteCalls.binding 83 _ (inputs_valid {count} false)
theorem complete : ∃ events,
    (GkrFiniteCalls.verifier (G := ℚ) 83 (inputs {count} false)).run handler (proof {count}) =
      ⟨.returned true, [], events⟩ := by simpa using honest_composed {count} []
def soundness {{E P : Type}} {{Raw : E → Type}} [∀ e, SampleableType (Raw e)]
    {{absorb : Zkc.Transcript.Interface (participantInterface ℚ ℚ) E P Raw}}
    {{charge : List E → E → ENNReal}}
    (queries : QueryInterface (GkrRoundsBinding.program (F := ℚ) (G := ℚ) 83) absorb)
    (sampling : queries.ConditionalBound (GkrRoundsBinding.representation 83) 2 2 charge)
    (history : List E) := rejected_composed {count} (by decide) queries sampling history
#print axioms binding
#print axioms complete
#print axioms soundness
run_cmd do
  for name in [``binding, ``complete, ``soundness] do
    let info ← Lean.getConstInfo name
    let some value := info.value? true | Lean.throwError "missing checked body"
    Lean.logInfo m!"proof-tree-nodes {{name}} {{value.sizeWithoutSharing}}"
end ParametricClients.Calls{count}
'''
        (generated / "ParametricClients" / f"Calls{count}.lean").write_text(source)
        compile_module(f"Calls{count}")
    manifest = [{"source": str(path), "bytes": path.stat().st_size,
                 "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
                for path in sorted(generated.rglob("*.lean"))]
    (records / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"PASS fresh parametric bindings and five refusal controls: {records}")


if __name__ == "__main__":
    main()
