#!/usr/bin/env python3
"""Compile real ABI/root printer output and independent installation controls.

Run from lean/security under `lake env` after building the focused fixtures and
printers. This driver uses existing dependencies and writes only its output
folder. It never invokes a Lake build or changes the shared test entry point.
After a driver-only correction, --controls-only reuses successful module receipts.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys


LABELS = (
    "Ordered", "Permuted", "Repeated", "Heterogeneous", "WitnessOnly", "NoData",
    "Constrained",
)
PREFIX = "ABIInstallationClients."


def main() -> None:
    if len(sys.argv) not in (2, 3) or (len(sys.argv) == 3 and sys.argv[2] != "--controls-only"):
        raise SystemExit("expected output directory [--controls-only]")
    controls_only = len(sys.argv) == 3
    output = Path(sys.argv[1]).resolve()
    sources = output / "generated"
    objects = output / "objects"
    logs = output / "logs"
    for directory in (sources, objects, logs):
        directory.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    env["LEAN_PATH"] = str(objects) + os.pathsep + env.get("LEAN_PATH", "")
    # A focused rerun reuses the already checked emitted modules and retains
    # their command receipts. Use a full run whenever source/fixtures change.
    receipt = output / "results.json"
    results: list[dict] = (
        [item for item in json.loads(receipt.read_text()) if item["passed"]]
        if controls_only else []
    )

    def run(name: str, command: list[str], *, failure: str | None = None) -> None:
        result = subprocess.run(command, env=env, text=True, capture_output=True, check=False)
        log = result.stdout + result.stderr
        (logs / (name + ".log")).write_text(log)
        passed = result.returncode > 0 if failure else result.returncode == 0
        if failure:
            passed = passed and failure in log
        # Lean may recover with an admitted placeholder to continue diagnostics;
        # such an elaboration is never accepted as a positive fixture.
        if failure is None:
            passed = passed and "declaration uses 'sorry'" not in log and "sorryAx" not in log
        results[:] = [item for item in results if item["name"] != name]
        results.append({"name": name, "command": command, "exit_code": result.returncode,
                        "expected_error": failure, "passed": passed})
        (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(f"{'PASS' if passed else 'FAIL'} {name}", flush=True)
        if not passed:
            raise SystemExit(log)

    def compile_module(name: str, *, failure: str | None = None, reuse_checked: bool = False) -> None:
        relative = Path(*name.split("."))
        source = sources / relative.with_suffix(".lean")
        target = objects / relative.with_suffix(".olean")
        object_matches = not target.exists() if failure else target.is_file()
        if (controls_only and reuse_checked and object_matches
                and any(item["name"] == name for item in results)):
            print(f"REUSE {name}", flush=True)
            return
        target.parent.mkdir(parents=True, exist_ok=True)
        target.unlink(missing_ok=True)
        run(name, ["lean", "-DwarningAsError=true", "--root=" + str(sources), "-o", str(target), str(source)],
            failure=failure)
        if failure and target.exists():
            raise SystemExit(f"rejected module left an object: {target}")

    if not controls_only:
        run("generate", ["lean", "--run", "checks/RunABIInstallations.lean", str(sources)])

        for label in LABELS:
            for suffix in ("ABI", "Producer", "Validator"):
                compile_module(PREFIX + label + suffix)
            compile_module(PREFIX + label + "Completeness")
        for label in ("SchnorrRandomized", "SmallSumcheck"):
            compile_module(PREFIX + "Existing" + label + "ABI")
        compile_module(PREFIX + "ConstrainedInterpretedABI")
        compile_module(PREFIX + "ConstrainedInterpretedCompleteness")
    for suffix, diagnostic in (
        ("MissingNonvacuity", "Tactic `assumption` failed"),
        ("WrongNonvacuity", "Type mismatch"),
        ("WrongClauseABI", "Type mismatch"),
        ("CrossedNonvacuity", "Type mismatch"),
        ("MissingClauseABI", "Unknown identifier"),
    ):
        compile_module(PREFIX + "Constrained" + suffix, failure=diagnostic, reuse_checked=True)

    def write_client(name: str, text: str, *, failure: str | None = None) -> None:
        path = sources / (name + ".lean")
        unchanged = path.is_file() and path.read_text() == text
        path.write_text(text)
        compile_module(name, failure=failure, reuse_checked=unchanged)

    imports = "\n".join("import " + PREFIX + label + "Completeness" for label in LABELS)
    client = imports + "\nimport " + PREFIX + "ConstrainedInterpretedABI\n" + r'''
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Claims.HonestPair
namespace Controls
open ABIInstallationClients
open TestsSecurity.ABIInstallations
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section

example : OrderedABI.arguments 3 7 = .cons (3 : ZMod 5) (.cons (7 : ZMod 5) .nil) := rfl
example : PermutedABI.arguments 3 7 = .cons (7 : ZMod 5) (.cons (3 : ZMod 5) .nil) := rfl
example : RepeatedABI.arguments 3 = .cons (3 : ZMod 5) (.cons (3 : ZMod 5) .nil) := rfl
example : HeterogeneousABI.arguments 7 true = .cons true (.cons (7 : Nat) (.cons true .nil)) := rfl
example : WitnessOnlyABI.arguments 3 = .cons (3 : ZMod 5) (.cons (3 : ZMod 5) .nil) := rfl
example (witness : WitnessOnly.validatorSubject.Witness) :
    WitnessOnly.validatorSubject.target.application.read {}
      (WitnessOnly.validatorSubject.boundary WitnessOnlyABI.statement)
      (WitnessOnly.validatorSubject.assignments WitnessOnlyABI.statement witness) =
        WitnessOnlyABI.validatorArguments witness := WitnessOnlyABI.validator_application_read witness

example (values : WitnessOnly.validatorArtifacts.Statement Fixtures.model) :
    values = WitnessOnlyABI.statement := WitnessOnlyABI.statement_surjective values
example (values : NoData.validatorArtifacts.Statement Fixtures.model) :
    values = NoDataABI.statement := NoDataABI.statement_surjective values
example : NoDataABI.StatementData = Unit := rfl
-- The public-binding event survives even when its public row is empty.
example : WitnessOnlyABI.initialHistory =
    [Zkc.Construction.Domain.Event.publicBinding ⟨WitnessOnly.subject.originalExport, []⟩] := rfl
example : NoDataABI.initialHistory =
    [Zkc.Construction.Domain.Event.publicBinding ⟨NoData.subject.originalExport, []⟩] := rfl

example (n : Nat) (service : Option Nat) :
    Constrained.subject.HonestInput (ConstrainedABI.inputs n service) ↔
      n < indexLimit ∧ ConstrainedABI.inputCondition (ConstrainedABI.inputs n service) :=
  ConstrainedABI.honestInput_iff n service
theorem interpreted_condition (n : Nat) (service : Option Nat) :
    ConstrainedInterpretedABI.inputCondition (ConstrainedInterpretedABI.inputs n service) ↔ n = 1 := by
  change (some n : Option Nat) = some 1 ↔ n = 1
  simp only [Option.some.injEq]
example (n : Nat) (service : Option Nat) :
    Constrained.subject.HonestInput (ConstrainedInterpretedABI.inputs n service) ↔
      n < indexLimit ∧ n = 1 := by
  exact (ConstrainedInterpretedABI.honestInput_iff n service).trans
    (and_congr Iff.rfl (interpreted_condition n service))
example : ¬ Constrained.subject.HonestInput (ConstrainedInterpretedABI.inputs 0 none) := by
  rw [ConstrainedInterpretedABI.honestInput_iff, interpreted_condition]
  simp
example : Constrained.subject.HonestInput (ConstrainedInterpretedABI.inputs 1 none) := by
  rw [ConstrainedInterpretedABI.honestInput_iff]
  exact ⟨by decide +kernel, rfl⟩

#print axioms PermutedABI.application_read
#print axioms RepeatedABI.application_read
#print axioms HeterogeneousABI.application_read
#print axioms WitnessOnlyABI.statement_surjective
#print axioms NoDataCompleteness.compiled_ideal_complete
#print axioms ConstrainedInterpretedABI.honestInput_iff
#print axioms ConstrainedCompleteness.compiled_ideal_complete
end
end Controls
'''
    write_client("InstallationControls", client)
    write_client("WrongSelectorClient", r'''
import ABIInstallationClients.PermutedABI
open Zkc.Source
open ABIInstallationClients.PermutedABI
example : arguments 3 7 = .cons (3 : ZMod 5) (.cons (7 : ZMod 5) .nil) := by rfl
''', failure="Tactic `rfl` failed")
    write_client("WrongSourceClauseClient", r'''
import ABIInstallationClients.ConstrainedInterpretedABI
open ABIInstallationClients.ConstrainedInterpretedABI
example : TestsSecurity.ABIInstallations.Constrained.subject.HonestInput (inputs 3 none) := by
  rw [honestInput_iff]
  change (3 : Nat) < Zkc.Source.Structured.indexLimit ∧ some (3 : Nat) = some 1
  exact ⟨by decide +kernel, by decide +kernel⟩
''', failure="Tactic `decide` proved")

    # Pair admission requires a service input, so zero-source rows cannot
    # instantiate Subject today. Compile the actual emitted structural row
    # declarations and root elimination in a typed, empty-row client instead.
    template = (sources / "EmptySourceTemplate.lean").read_text()
    rows = template[template.index("def sourceInputs"):template.index("abbrev StatementData")]
    root = (sources / "EmptyRootTemplate.lean").read_text()
    elimination = next(line for line in root.splitlines() if " := data_surjective values" in line)
    zero = r'''
module
public import ZkcSecurity.Tools.SubjectABI
public import TestsSecurity.ABIInstallations.Fixtures
@[expose] public section
noncomputable section
namespace EmptyRows
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.Tools.SubjectABI
abbrev model := TestsSecurity.ABIInstallations.Fixtures.model
namespace subject
abbrev Inputs := Values (Component model.Value) []
end subject
abbrev Data := Values (TypedABI.Slot Zkc.Construction.Domain.dataType model.Value) []
namespace validatorArtifacts
abbrev Statement (model : DomainModel) := Values model.Value []
end validatorArtifacts
'''
    zero += rows
    zero += "def subject.HonestInput (_values : subject.Inputs) : Prop := True\n"
    zero += "namespace abi\n"
    zero += "theorem honest_exists (values : subject.Inputs) (_honest : subject.HonestInput values) :\n"
    zero += "    ∃ data : Data, values = TypedABI.optional Zkc.Construction.Domain.dataType data := by\n"
    zero += "  cases values; exact ⟨.nil, rfl⟩\nend abi\n"
    zero += template[template.index("theorem honestInput_exists"):template.index("def arguments")]
    zero += "theorem root_elimination (values : Data) : values = data := by\n" + elimination + "\n  rfl\n"
    zero += "#print axioms sourceInputs_surjective\n#print axioms data_surjective\n"
    zero += "#print axioms honestInput_exists\n#print axioms statement_surjective\n#print axioms root_elimination\nend EmptyRows\n"
    write_client("EmptySourceRows", zero)
    print(f"All {len(results)} ABI installation controls passed; results: {output / 'results.json'}")


if __name__ == "__main__":
    main()
