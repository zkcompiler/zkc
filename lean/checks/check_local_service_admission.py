#!/usr/bin/env python3
"""Check exact local-service exports and admission of the actual Schnorr producer.

Uses existing native/Lean dependencies, never a Lake build. --lean-path selects
an isolated compiled-module tree when the maintained package is built concurrently.
All fresh exports, generated kernel controls, commands and results are retained.
"""
import argparse
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean"
sys.path.insert(0, str(LEAN))
from bridges.common import lean_render  # noqa: E402
from bridges.construction import pair  # noqa: E402
from bridges.structured import snapshot  # noqa: E402


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def instructions(block):
    for instruction in block:
        yield instruction
        for region in instruction[5]:
            yield from instructions(region[1])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "build/compiler/zkc-compile")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-path", type=Path)
    parser.add_argument("--native-only", action="store_true")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    (output / "result.json").write_text(json.dumps({"status": "running"}) + "\n")
    compiler = args.compiler.resolve()
    commands = []

    def run(command, cwd=ROOT):
        command = [str(value) for value in command]
        started = time.monotonic()
        result = subprocess.run(command, cwd=cwd, capture_output=True, text=True, timeout=180)
        log = output / f"command-{len(commands):03}.log"
        log.write_text(result.stdout + result.stderr)
        commands.append({"command": command, "cwd": str(cwd), "returncode": result.returncode,
                         "seconds": time.monotonic() - started, "log": str(log)})
        (output / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
        return result.stdout

    definitions = []
    data_by_name = {}
    for name, entry, module, path in [
        ("Schnorr", "example::Proof", "example", "examples/projects/schnorr/main.zkc"),
        ("Aliases", "service_control::AliasProof", "service_control",
         "compiler/test/fixtures/constructed-services/borrowed.zkc"),
        ("Repeated", "service_control::RepeatProof", "service_control",
         "compiler/test/fixtures/constructed-services/borrowed.zkc"),
        ("LocalRepeated", "service_control::LocalRepeatProof", "service_control",
         "compiler/test/fixtures/constructed-services/borrowed.zkc"),
    ]:
        flags = ["--source-format=zkc", "--entry=" + entry, f"--module={module}={ROOT / path}",
                 "--module=schnorr=" + str(ROOT / "libraries/protocols/sigma/schnorr/lib.zkc")]
        source = output / (name + ".mlir")
        source.write_text(run([compiler, "language-emit", *flags]))
        deployment = json.loads(run([compiler, "language-bundle", *flags]))
        policy = output / (name + "-policy.json")
        policy.write_text(json.dumps(deployment[2][1]))
        candidate = output / (name + "-candidate.mlir")
        candidate.write_text(run([compiler, "protocol-construct-proof", source, policy]))
        data = json.loads(run([compiler, "protocol-constructed-pair", source, policy, candidate]))
        pair.decode(data, expected=deepcopy(data))
        (output / (name + "-pair.json")).write_text(json.dumps(data, indent=2) + "\n")
        original = json.loads(run([compiler, "protocol-structured", source,
                                   "--symbol=" + data[1][3][1]]))
        (output / (name + "-source.json")).write_text(json.dumps(original, indent=2) + "\n")
        queries = [op for op in instructions(data[1][7]) if op[0] == "protocol.service_query"]
        require(queries and all(len(op) == 7 and op[3] == [] for op in queries), 'service query envelope or argument list changed')
        require(len(data[2][9]) == (1 if name == "Aliases" else 0), 'validator service-port inventory changed')
        require(len(data[1][5]) == 4, 'producer source inputs must exclude nonce witnesses')
        if name == "Aliases":
            require(len(data[1][9]) == 3, 'producer service ports must include unused spare ports')
            require(len(queries) == 5, 'producer must retain unused replies and borrowed aliases')
            events = [lean_render.template(op[6][0])[-1] for op in queries]
            require({event[3] for event in events} >= {"input_0", "input_1"}, 'borrowed aliases lost their distinct input origins')
            require(len({dict(op[1])["port"][1] for op in queries}) == 2, 'borrowed aliases lost their distinct ports')
        if name == "Repeated":
            require(len(queries) == 2 and all(len(op[6][1]) == 1 for op in queries), 'repeated services must retain one dynamic coordinate')
        if name == "LocalRepeated":
            require([len(op[6][1]) for op in queries] == [1, 0], 'local repeated service coordinates changed')
        definitions.append(lean_render.strip_header(snapshot.render(original, name + ".Source")))
        definitions.append(lean_render.strip_header(pair.render(data, name)))
        data_by_name[name] = data

    # A malformed/old envelope cannot silently erase the new interface.
    refusal_count = 0
    for change in [lambda d: d[1].pop(), lambda d: d[1].append([]),
                   lambda d: d[1][9].append(deepcopy(d[1][9][0])),
                   lambda d: d[1][9][0].__setitem__(2, "03"),
                   lambda d: d[1][9][0].append("ignored"),
                   lambda d: d[1][7][0].pop(),
                   lambda d: d[1][7][0].append("ignored"),
                   lambda d: d[1][7][0][1][0].__setitem__(1, ["string", "index"]),
                   lambda d: d[1][7][0][3].append(2),
                   lambda d: d[1][7][0][4].__setitem__(0, '!algebra.field<"other">'),
                   lambda d: d[1][7][0][6][1].append(True),
                   lambda d: d[1][7][0][1][2].__setitem__(1, ["string", "other-site"])]:
        changed = deepcopy(data_by_name["Schnorr"])
        change(changed)
        try:
            pair.decode(changed)
        except ValueError:
            refusal_count += 1
        else:
            raise AssertionError("malformed service export was accepted")

    controls = '''
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.AuthoredPair

def importChecked (source : Snapshot) (accepted : (Structured.check source).isOk = true) :
    Imported source := by
  cases found : Structured.check source with
  | error error => simp_all [Except.isOk, Except.toBool]
  | ok program => exact ⟨program, found⟩
'''
    for name in data_by_name:
        controls += f'''
namespace {name}
def imported : Imported Source.snapshot := importChecked Source.snapshot (by decide +kernel)
def selected : Selection Source.snapshot :=
  ⟨artifacts, Validator.participant.policy, Producer.participant.symbol, Validator.participant.symbol,
    (inputContract Source.snapshot).getD ⟨[], []⟩,
    (Source.snapshot.contracts[0]'(by decide)).clauses[0]'(by decide)⟩
def context : Context := (exportContext Source.snapshot Validator.participant).getD
  ⟨"", [], 0, 1, 0, "", none, "", []⟩
example : select Source.snapshot artifacts "knowledge" = .ok selected := by decide +kernel
example : Zkc.Construction.AuthoredPair.check imported selected artifacts = .ok () := by decide +kernel
example : SourceOccurrences.check Source.snapshot context Producer.participant = .ok () := by decide +kernel
example : checkProducer imported.program context Producer.participant = .ok () := by decide +kernel
end {name}
'''
    controls += '''
namespace Schnorr
private def port := Producer.participant.servicePorts[0]'(by decide)
private def localInstruction := Producer.participant.instructions[0]'(by decide)
private def template : Template := match localInstruction.operation with
  | .localService _ _ template _ => template
  | _ => ⟨"", [], []⟩
private def request := Request.draw "bls12-381.fr"
example : SourceOccurrences.localValid Source.snapshot context port request template = true := by decide +kernel
example : SourceOccurrences.localValid Source.snapshot context { port with owner := "role00000001" }
    request template = false := by decide +kernel
example : SourceOccurrences.localValid Source.snapshot context { port with root := 4 }
    request template = false := by decide +kernel
example : SourceOccurrences.localValid Source.snapshot context { port with contract := "random.other/0" }
    request template = false := by decide +kernel
example : SourceOccurrences.localValid Source.snapshot context port (Request.draw "other")
    template = false := by decide +kernel
example : SourceOccurrences.localValid Source.snapshot context port request
    { template with event := template.event.set 2 "another-site" } = false := by decide +kernel
example : SourceOccurrences.localValid Source.snapshot context port request
    { template with entry := "another-entry" } = false := by decide +kernel
example : SourceOccurrences.localValid Source.snapshot context port request
    { template with event := template.event.set 6 "role00000001" } = false := by decide +kernel
example : SourceOccurrences.localValid Source.snapshot context port { request with method := "index" }
    template = false := by decide +kernel
-- Keep the old validator rule coin-free even when given an otherwise valid local request.
example : (Zkc.Construction.check context { Validator.participant with
    instructions := [localInstruction] }).isOk = false := by decide +kernel
-- Port identity is checked against source even for a newly self-consistent selection.
example : selectionValid (original := Source.snapshot) { selected with artifacts :=
    { artifacts with producer := { Producer.participant with servicePorts := [] } } } = false := by decide +kernel
end Schnorr
'''
    # Wrong dynamic coordinates remain readable but fail the producer checker.
    changed = deepcopy(data_by_name["Repeated"])
    for op in instructions(changed[1][7]):
        if op[0] == "protocol.service_query":
            op[6][1] = []
    definitions.append(lean_render.strip_header(pair.render(changed, "WrongCoordinates")))
    changed_root = deepcopy(data_by_name["Aliases"])
    # Change the first unused draw to another same-owner, same-domain root.
    for attr in changed_root[1][7][0][1]:
        if attr[0] == "port":
            attr[1][1] = "service_3"
    definitions.append(lean_render.strip_header(pair.render(changed_root, "WrongRoot")))
    changed_loop = deepcopy(data_by_name["Repeated"])
    for op in changed_loop[1][7]:
        if op[0] == "protocol.loop":
            for attr in op[1]:
                if attr[0] == "site":
                    attr[1][1] = "another-repeat"
            break
    definitions.append(lean_render.strip_header(pair.render(changed_loop, "WrongLoopSite")))
    controls += '''
example : (checkProducer Repeated.imported.program Repeated.context
    WrongCoordinates.Producer.participant).isOk = false := by decide +kernel
example : checkProducer Aliases.imported.program Aliases.context
    WrongRoot.Producer.participant = .ok () := by decide +kernel
example : (SourceOccurrences.check Aliases.Source.snapshot Aliases.context
    WrongRoot.Producer.participant).isOk = false := by decide +kernel
example : (Zkc.Construction.AuthoredPair.check Aliases.imported
    ({ Aliases.selected with artifacts := WrongRoot.artifacts } : Selection Aliases.Source.snapshot)
    WrongRoot.artifacts).isOk = false := by decide +kernel
example : checkProducer Repeated.imported.program Repeated.context
    WrongLoopSite.Producer.participant = .ok () := by decide +kernel
example : (SourceOccurrences.check Repeated.Source.snapshot Repeated.context
    WrongLoopSite.Producer.participant).isOk = false := by decide +kernel
#print axioms Zkc.Construction.AuthoredPair.admitted_selection
#print axioms Zkc.Construction.AuthoredPair.admitted_occurrences
#print axioms Zkc.Construction.AuthoredPair.admitted_servicePorts
'''
    path = output / "LocalServices.lean"
    path.write_text("module\n\npublic import Zkc.Construction.AuthoredPair\n\n@[expose] public section\n\n"
                    "set_option maxRecDepth 10000\nset_option maxHeartbeats 8000000\n\n"
                    + "\n".join(definitions) + controls)
    if not args.native_only:
        command = ["lake", "env"]
        if args.lean_path:
            base = run(["lake", "env", "printenv", "LEAN_PATH"], cwd=LEAN).strip()
            command += ["env", "LEAN_PATH=" + str(args.lean_path.resolve()) + ":" + base]
        log = run([*command, "lean", path], cwd=LEAN)
        (output / "lean.log").write_text(log)
    result = {"status": "pass", "compiled_pairs": list(data_by_name),
              "strict_reader_refusals": refusal_count, "lean_checked": not args.native_only}
    (output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
