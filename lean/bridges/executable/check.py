#!/usr/bin/env python3
"""Check the executable Schnorr proof validator against Lean and the runtime.

The driver compiles `example::Proof` and retains its original source, native
deployment, Entry package, constructed validator export and the `zkc.program/0`
validator the runtime admits. It then

1. requires the committed executable and construction data to be the exact
   renderings of the fresh program and exports, and runs the Lean lowering rule
   on the fresh rendering and on mutated programs, each refused for its named
   reason; the constructed export's policy must be the deployment's, and the
   role map the runtime uses must select the Lean statement's acceptance
   position and public inputs;
2. runs the runtime verifier on an honest proof at every instruction budget
   and on mutated proofs, and requires its outcome, stop site, helper,
   charged instructions, transcript transitions and read messages to equal
   those the Lean executable meaning predicts for the same bytes; the runtime
   must accept exactly the sufficient-budget honest runs and reject the wrong
   response, which the value-free prediction cannot tell apart;
3. checks the axiom closure of every theorem from the lowering rule to the
   byte-level knowledge-soundness theorem in the ArkLib integration, and that
   the byte-level theorem's proof reaches the general composed rules and not
   the Entry's equation about the compiled program's meaning (`spec_equation`);
4. writes a verification receipt naming every artifact digest, the checked
   rules, the theorems and the remaining assumptions, and checks on the
   runtime that it executes exactly the program the receipt names: the pinned
   package runs, a package with another program but the same pin is refused,
   a program changed without its inner digest is refused, and a re-pinned
   package with a mutated program runs but fails the receipt check.

This is bounded evidence for the trusted links: the runtime's execution of the
admitted program, its codecs and kernels, and the renderer.
"""

import argparse
import copy
import datetime
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
LEAN = ROOT / "lean"
MODULES = ["example=examples/projects/schnorr/main.zkc", "schnorr=libraries/schnorr/lib.zkc"]
ENTRY = "example::Proof"
PUBLIC = ROOT / "examples/projects/schnorr/inputs/example.Proof/public.json"
WITNESS = ROOT / "examples/projects/schnorr/inputs/example.Proof/witness.json"
DATA = LEAN / "ZkcExamples/Executable/SchnorrProofProgramData.lean"
NAMESPACE = "ZkcExamples.Executable.SchnorrProofProgramData"
HEADER = 40


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


executable = load("executable_render", Path(__file__).resolve().parent / "render.py")
constructed = load("construction_render", ROOT / "lean/bridges/construction/render.py")
# The structured renderer imports its siblings; it is appended after this directory, so no
# module of this bridge is shadowed by a structured-bridge module of the same name.
sys.path.append(str(ROOT / "lean/bridges/structured"))
import snapshot as structured  # noqa: E402

CONSTRUCTION_DATA = {
    LEAN / "ZkcExamples/Construction/SchnorrProofData.lean": "ZkcExamples.Construction.SchnorrProofData",
    LEAN / "ZkcExamples/Construction/SchnorrProofParticipant.lean":
        "ZkcExamples.Construction.SchnorrProofParticipant",
}
THEOREM = "ZkcSecurity.Examples.ExecutableSchnorrFiatShamir.knowledge_soundness"
# The theorem chain the receipt names, checked in the security package.
CHAIN = [
    THEOREM,
    "ZkcSecurity.Examples.ExecutableSchnorrFiatShamir.acceptance_le",
    "ZkcSecurity.Examples.CompiledSchnorrFiatShamir.knowledge_soundness",
    "ZkcExamples.Executable.SchnorrProof.accepted",
    "ZkcExamples.Executable.SchnorrProof.executable_validate",
    "ZkcExamples.Executable.SchnorrProof.executable_rejects",
    "ZkcExamples.Construction.SchnorrProof.compiled",
    "ZkcExamples.Construction.SchnorrProof.compiled_transform",
    "Zkc.Executable.execute_metered",
    "Zkc.Executable.validate_ideal",
    "Zkc.Executable.validate_rejects",
    "Zkc.Construction.compiled_transform",
    "Zkc.Construction.check_sound",
    "Zkc.Construction.project_sound",
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Declarations the byte-level theorem's proof must reach: the general rules and
# their checks on this Entry.
USED = [
    "Zkc.Construction.compiled_transform",
    "Zkc.Construction.check_sound",
    "Zkc.Construction.project_sound",
    "ZkcExamples.Construction.SchnorrProof.compiled",
    "Zkc.Executable.validate_ideal",
    "Zkc.Executable.validate_rejects",
    "ZkcExamples.Executable.SchnorrProof.accepted",
]
# Entry-specific equations about the compiled program's meaning, which the proof must not use.
UNUSED = [
    "ZkcExamples.Construction.SchnorrProof.spec_equation",
]
# Per-protocol equations about the original program, recorded in the receipt: they
# tie the admitted original to the protocol experiment the security library uses.
ORIGINAL = [
    "ZkcExamples.Construction.SchnorrProof.process_equation",
]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def capacity(instructions):
    return ["zkc.native-capacity/0", "65536", "4096", "16777216", "67108864",
            [str(instructions), "100000", "4294967296"], ["67108864", "268435456"]]


def lean_bytes(data):
    return "[" + ", ".join(str(byte) for byte in data) + "]"


def body(text):
    """Drop the module header so several renderings share one Lean file."""
    return "\n".join(line for line in text.splitlines()
                     if line not in ("module", "@[expose] public section")
                     and not line.startswith("public import "))


class Driver:
    def __init__(self, args):
        self.args = args
        self.output = args.output
        self.commands = []
        self.checks = []

    def run(self, arguments, *, cwd=ROOT, expect=0, name=None):
        started = now()
        result = subprocess.run([str(a) for a in arguments], cwd=cwd, capture_output=True, text=True,
                                check=False)
        self.commands.append(dict(name=name, arguments=[str(a) for a in arguments], cwd=str(cwd),
                                  exit=result.returncode, started=started, finished=now(),
                                  stdout_sha256=digest(result.stdout.encode()), stderr=result.stderr[-4000:]))
        if expect is not None and result.returncode != expect:
            raise RuntimeError(f"{name or arguments[0]} exited {result.returncode}: {result.stderr[-2000:]}")
        return result

    def check(self, name, passed, detail=""):
        self.checks.append(dict(name=name, passed=bool(passed), detail="" if passed else detail))
        if not passed:
            raise RuntimeError(f"check failed: {name} {detail}")

    # Compilation and retained artifacts.

    def compile(self):
        common = ["--source-format=zkc", f"--entry={ENTRY}", *[f"--module={m}" for m in MODULES]]
        compiler = self.args.compiler
        source = self.run([compiler, "language-emit", *common], name="emit").stdout.encode()
        (self.output / "source.mlir").write_bytes(source)
        deployment_text = self.run([compiler, "language-bundle", *common], name="bundle").stdout.rstrip("\n")
        (self.output / "deployment.json").write_text(deployment_text)
        package_text = self.run([compiler, "language-package", *common], name="package").stdout
        package_bytes = package_text.encode()
        (self.output / "package.zkpkg").write_bytes(package_bytes)
        package = json.loads(package_text)
        deployment = json.loads(deployment_text)
        program = deployment[4].encode()
        (self.output / "program.json").write_bytes(program)
        self.check("package-artifact", package["artifact"] == deployment_text)
        self.check("package-original", package["original"].encode() == source)
        self.check("deployment-source", deployment[1] == digest(source))
        self.check("deployment-program", deployment[5] == digest(program))
        policy = deployment[2][1]
        (self.output / "policy.json").write_text(json.dumps(policy))
        candidate = self.run([compiler, "protocol-construct-proof", self.output / "source.mlir",
                              self.output / "policy.json"], name="construct").stdout
        (self.output / "candidate.mlir").write_text(candidate)
        export_text = self.run([compiler, "protocol-constructed-participant", self.output / "source.mlir",
                                self.output / "policy.json", self.output / "candidate.mlir"],
                               name="participant").stdout
        (self.output / "participant.json").write_text(export_text)
        exported = json.loads(export_text)
        original_text = self.run([compiler, "protocol-structured", self.output / "source.mlir",
                                  f"--symbol={policy[1]}"], name="original").stdout
        (self.output / "original.json").write_text(original_text)
        self.check("participant-source", exported[1] == "sha256:" + digest(source))
        self.check("participant-policy", exported[3] == policy, json.dumps([exported[3], policy]))
        return dict(source=source, deployment=deployment, deployment_text=deployment_text,
                    package=package, package_bytes=package_bytes, program=program,
                    exported=exported, export_text=export_text, original_text=original_text)

    def regenerate(self, artifacts):
        files = {DATA: executable.render(artifacts["deployment"], NAMESPACE)}
        renderers = [lambda namespace: structured.render(json.loads(artifacts["original_text"]), namespace),
                     lambda namespace: constructed.render(artifacts["exported"], namespace)]
        for (path, namespace), render in zip(CONSTRUCTION_DATA.items(), renderers):
            files[path] = render(namespace)
        for path, text in files.items():
            if self.args.write and path == DATA:
                path.write_text(text, encoding="utf-8")
            current = path.read_text(encoding="utf-8") if path.exists() else None
            self.check(f"regenerated:{path.relative_to(ROOT)}", current == text,
                       "committed data differs from the fresh export")

    def axioms(self):
        """The axiom closure of every theorem in the receipt's chain, and the declarations
        the byte-level theorem's proof reaches."""
        path = self.output / "ReceiptAxioms.lean"
        queried = USED + UNUSED + ORIGINAL
        path.write_text(
            "import ZkcSecurity.Examples.ExecutableSchnorrFiatShamir\n\n"
            + "".join(f"#print axioms {name}\n" for name in CHAIN)
            + "\nopen Lean in\n"
            "/-- Whether `target` occurs in the transitive constant dependencies of `root`. -/\n"
            "def reaches (root target : Name) : CoreM Bool := do\n"
            "  let env ← getEnv\n"
            "  let mut visited : NameSet := {}\n"
            "  let mut pending : List Name := [root]\n"
            "  repeat\n"
            "    match pending with\n"
            "    | [] => break\n"
            "    | name :: rest =>\n"
            "      pending := rest\n"
            "      if name == target then return true\n"
            "      unless visited.contains name do\n"
            "        visited := visited.insert name\n"
            "        if let some info := env.find? name then\n"
            "          for used in info.getUsedConstantsAsSet do\n"
            "            unless visited.contains used do pending := used :: pending\n"
            "  return false\n\n"
            + "".join(f"#eval do IO.println s!\"reaches {name}: {{← reaches `{THEOREM} `{name}}}\"\n"
                      for name in queried),
            encoding="utf-8")
        result = self.run([self.args.lake, "env", "lean", path], cwd=LEAN / "integrations/arklib",
                          name="receipt-axioms")
        found = {}
        for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout):
            found[name] = sorted(a.strip() for a in axioms.split(",") if a.strip())
        for name in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout):
            found[name] = []
        for name in CHAIN:
            self.check(f"axioms:{name}", name in found and set(found[name]) <= ALLOWED_AXIOMS,
                       json.dumps(found.get(name)))
        reached = dict(re.findall(r"^reaches (\S+): (true|false)$", result.stdout, re.M))
        for name in USED:
            self.check(f"proof-uses:{name}", reached.get(name) == "true", json.dumps(reached.get(name)))
        for name in UNUSED:
            self.check(f"proof-avoids:{name}", reached.get(name) == "false", json.dumps(reached.get(name)))
        self.dependencies = dict(uses=USED, avoids=UNUSED,
                                 original_stage_equations={name: reached.get(name) == "true"
                                                           for name in ORIGINAL})
        return found

    # The Lean lowering rule on the fresh program and on mutations.

    def mutated_deployment(self, deployment, change):
        value = copy.deepcopy(deployment)
        program = json.loads(value[4])
        change(program)
        value[4] = json.dumps(program, separators=(",", ":"))
        value[5] = digest(value[4].encode())
        return value

    def program_mutations(self, deployment):
        def function(program, symbol):
            return next(item for item in program[2] if item[1] == symbol)

        def validator(program):
            return next(item for item in program[3] if item[3] == deployment[2][1][3])

        def step(program, symbol, site):
            return next(item for item in function(program, symbol)[4] if item[:2] == ["op", site])

        def addition_swapped(program):
            operation = step(program, "_calculation_2", "value_2")
            operation[4] = list(reversed(operation[4]))

        def comparison_trivial(program):
            operation = step(program, "_calculation_2", "value_3")
            operation[4] = [operation[4][0], operation[4][0]]

        def results_swapped(program):
            body = validator(program)[6]
            body[-1][1] = list(reversed(body[-1][1]))

        def base_observed(program):
            call = next(item for item in validator(program)[6] if item[:2] == ["local", "_transcript_12"])
            call[3] = [call[3][0], validator(program)[4][0][0]]

        def stale_transcript(program):
            participant = validator(program)[6]
            first = next(item for item in participant if item[:2] == ["local", "_transcript_12"])
            third = next(item for item in participant if item[:2] == ["local", "_transcript_14"])
            third[3] = [first[4][0], third[3][1]]

        def uninstalled(program):
            binding = next(item for item in program[1] if item[0] == "_calculation_6")
            binding[3] = "fast/curve.add"

        def unchecked_representation(program):
            receive = next(item for item in validator(program)[6] if item[0] == "receive")
            receive[5] = receive[5].replace("@arkworks.g1/0", "@unchecked.g1/0")

        def formal_retyped(program):
            function(program, "_calculation_2")[2][0][1] = "bool@native.bool/0"

        def function_duplicated(program):
            program[2].append(copy.deepcopy(function(program, "_calculation_2")))

        return {
            "addition-swapped": (addition_swapped, ".instruction 12"),
            "comparison-trivial": (comparison_trivial, ".instruction 13"),
            "results-swapped": (results_swapped, ".different \"returned\""),
            "base-observed": (base_observed, ".instruction 2"),
            "stale-transcript": (stale_transcript, ".operation \"transition\""),
            "uninstalled-implementation": (uninstalled, ".binding \"_calculation_6\""),
            "unchecked-representation": (unchecked_representation, ".representation"),
            "formal-retyped": (formal_retyped, ".operation \"calculation_0\""),
            "function-duplicated": (function_duplicated, ".duplicate \"function\""),
        }

    def lean_rule(self, artifacts):
        deployment = artifacts["deployment"]
        exported = artifacts["exported"]
        parts = ["import Zkc.Executable.Installed", "import Zkc.Executable.Lowering",
                 "import Zkc.Construction.Participant", "import ZkcExamples.Construction.SchnorrProof",
                 "set_option maxRecDepth 20000",
                 body(constructed.render(exported, "Fresh.Constructed")),
                 body(executable.render(deployment, "Fresh.Actual")),
                 "open Zkc.Executable",
                 "def refusal : Except Refusal Lowered → Option Refusal\n"
                 "  | .error refusal => some refusal\n  | .ok _ => none"]
        selected = self.selected = self.role_map(deployment)
        proofs = ["theorem actual_accepted : refusal (checkLowering installed Fresh.Constructed.participant "
                  "Fresh.Actual.validator) = none := by decide +kernel",
                  "theorem actual_total : (checkLowering installed Fresh.Constructed.participant "
                  "Fresh.Actual.validator).toOption.map (·.total) = some 25 := by decide +kernel",
                  # The runtime decides acceptance at its role map's index; the theorems read the
                  # committed acceptance position and bind data inputs in policy order.
                  "theorem acceptance_position : ZkcExamples.Construction.SchnorrProof.acceptancePosition = "
                  f"{int(selected['acceptance'])} := by decide +kernel",
                  "theorem public_inputs : ZkcExamples.Construction.SchnorrProof.participant.policy.publicInputs = "
                  f"[{', '.join(str(int(port)) for port in selected['data_inputs'])}] := by decide +kernel"]
        mutations = self.program_mutations(deployment)
        for index, (name, (change, reason)) in enumerate(mutations.items()):
            namespace = f"Fresh.Mutation{index}"
            parts.append(body(executable.render(self.mutated_deployment(deployment, change), namespace)))
            proofs.append(f"/-- {name} -/\ntheorem mutation{index}_refused : refusal (checkLowering installed "
                          f"Fresh.Constructed.participant {namespace}.validator) = some ({reason}) := "
                          f"by decide +kernel")
        proofs.append("#print axioms actual_accepted")
        source = "\n\n".join(parts + proofs) + "\n"
        path = self.output / "FreshLowering.lean"
        path.write_text(source, encoding="utf-8")
        result = self.run([self.args.lake, "env", "lean", path], cwd=LEAN, name="lean-rule")
        marker = "'actual_accepted' depends on axioms: ["
        axioms = result.stdout.split(marker, 1)[1].split("]", 1)[0] if marker in result.stdout else None
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        self.check("lean-rule", axioms is not None
                   and {name.strip() for name in axioms.split(",") if name.strip()} <= allowed,
                   result.stdout[-400:])
        return {name: reason for name, (_, reason) in mutations.items()}

    @staticmethod
    def role_selection(deployment):
        """The validator's role-map row, which the runtime uses for inputs and acceptance, and
        whether it takes the policy's public inputs in order and selects its acceptance output."""
        policy = deployment[2][1]
        rows = [row for row in deployment[6] if row[0] == policy[3]]
        if len(rows) != 1:
            return None
        _, symbol, inputs, outputs, _, acceptance = rows[0]
        data_inputs = [port for port, _ in inputs]
        selects = (acceptance.isdigit() and int(acceptance) < len(outputs)
                   and outputs[int(acceptance)][0] == policy[4])
        return dict(symbol=symbol, data_inputs=data_inputs, acceptance=acceptance,
                    inputs_match=data_inputs == policy[7], acceptance_match=selects)

    def role_map(self, deployment):
        selection = self.role_selection(deployment)
        self.check("role-map-validator", selection is not None)
        self.check("role-map-public-inputs", selection["inputs_match"], json.dumps(selection))
        self.check("role-map-acceptance", selection["acceptance_match"], json.dumps(selection))
        # Controls: a policy selecting another output, or public inputs in another order, fails.
        other = copy.deepcopy(deployment)
        other[2][1][4] = str(int(other[2][1][4]) + 1)
        reordered = copy.deepcopy(deployment)
        reordered[2][1][7] = list(reversed(reordered[2][1][7]))
        self.check("role-map-refuses-other-acceptance", not self.role_selection(other)["acceptance_match"])
        self.check("role-map-refuses-reordered-inputs", not self.role_selection(reordered)["inputs_match"])
        return dict(symbol=selection["symbol"], data_inputs=selection["data_inputs"],
                    acceptance=selection["acceptance"])

    # The runtime and the Lean predictions.

    def verify(self, package, pin, proof, name, *, instructions=None):
        path = self.output / f"proof-{name}.bin"
        path.write_bytes(proof)
        arguments = [self.args.native, "--json", "verify", f"--package={package}", f"--sha256={pin}",
                     f"--public={PUBLIC}", f"--proof={path}"]
        if instructions is not None:
            limits = self.output / f"capacity-{instructions}.json"
            limits.write_text(json.dumps(capacity(instructions)))
            arguments.append(f"--capacity={limits}")
        result = self.run(arguments, expect=None, name=f"verify:{name}")
        report = json.loads(result.stdout) if result.stdout.strip() else {}
        (self.output / f"verify-{name}.json").write_text(result.stdout)
        return result.returncode, report

    @staticmethod
    def observed(exit_code, report):
        """The runtime's observation in the vocabulary of the Lean prediction."""
        execution = report.get("execution") or {}
        stop = execution.get("stop") or {}
        code = report.get("code")
        transcript = [r for r in execution.get("resources") or [] if r.get("stage") == "transcript"]
        if code == "proof-header":
            outcome = "header"
        elif exit_code == 0:
            outcome = "accepted"
        elif code in ("artifact-rejected", "proof-trailing"):
            outcome = "returned"
        elif code == "proof-truncated":
            outcome = "truncated"
        elif stop.get("kind") == "Limit":
            outcome = "limit"
        elif str(stop.get("kind", "")).startswith("Decode"):
            outcome = "decode"
        else:
            outcome = f"other:{code}:{stop.get('kind')}"
        local = stop.get("local")
        return dict(outcome=outcome,
                    site=stop.get("site") if outcome not in ("header", "truncated") else None,
                    call=[local["site"], local["function"]] if local else None,
                    used=execution.get("instructions"),
                    transitions=transcript[0]["transitions"] if transcript else None,
                    messages=execution.get("messages"),
                    complete=code != "proof-trailing" if outcome in ("accepted", "returned") else None)

    def scenarios(self, proof):
        """Proof mutations and the payloads the runtime codec refuses in each."""
        assert proof[:8] == b"ZKCPRF00" and len(proof) == 148

        def replace(data, offset, value):
            return data[:offset] + value + data[offset + len(value):]

        first, second = proof[48:102], proof[110:148]
        return {
            "honest": (proof, []),
            "commitment-not-on-curve": (replace(proof, 60, bytes([proof[60] ^ 0x01])),
                                        [replace(first, 12, bytes([first[12] ^ 0x01]))]),
            "commitment-wrong-tag": (replace(proof, 53, b"\x07"), [replace(first, 5, b"\x07")]),
            "response-out-of-range": (replace(proof, 116, b"\xff" * 32),
                                      [replace(second, 6, b"\xff" * 32)]),
            "response-wrong-value": (replace(proof, 116, b"\x00" * 31 + b"\x01"), []),
            "response-missing": (proof[:102], []),
            "response-truncated": (proof[:120], []),
            "trailing-byte": (proof + b"\x00", []),
            "header-binding": (replace(proof, 8, bytes([proof[8] ^ 0x01])), []),
        }

    def predictions(self, artifacts, cases, binding):
        """Evaluate the Lean executable meaning on every case."""
        lines = ["import Zkc.Executable.Installed", "import Mathlib.Algebra.Field.ZMod",
                 # The occurrence context is the committed one, which `regenerate` ties to the
                 # fresh original and constructed exports.
                 "import ZkcExamples.Construction.SchnorrProof",
                 body(executable.render(artifacts["deployment"], "Fresh.Actual")),
                 "open Zkc.Construction Zkc.Executable",
                 "local instance : Fact (Nat.Prime 5) := ⟨by decide⟩",
                 "abbrev Scalar := ZMod 5",
                 "def challengeZero : History Scalar Scalar → Id Scalar := fun _ => 0",
                 "def decodeExcept (invalid : List (List UInt8)) : PhysicalType → List UInt8 → "
                 "Option (Payload Scalar Scalar)\n"
                 "  | ⟨.data (.group domain), _⟩, payload => if invalid.contains payload then none "
                 "else some (.group domain 0)\n"
                 "  | ⟨.data (.field domain), _⟩, payload => if invalid.contains payload then none "
                 "else some (.field domain 0)\n"
                 "  | _, _ => none",
                 "def text : Option String → String\n  | some value => \"\\\"\" ++ value ++ \"\\\"\"\n"
                 "  | none => \"null\"",
                 "def predict (budget : Nat) (binding bytes : List UInt8) (invalid : List (List UInt8)) : "
                 "String :=\n"
                 "  if bytes.take 40 = magic ++ binding then\n"
                 "    let run := Id.run (execute installed Fresh.Actual.validator\n"
                 "      ZkcExamples.Construction.SchnorrProof.context challengeZero\n"
                 "      (decodeExcept invalid) budget [.group \"bls12-381.g1\" 0, .group \"bls12-381.g1\" 0] []\n"
                 "      (bytes.drop 40))\n"
                 "    let (outcome, site, call) := match run.result with\n"
                 "      | .returned _ => (\"returned\", none, none)\n"
                 "      | .stopped cause site call => (match cause with\n"
                 "          | .limit => \"limit\" | .decode => \"decode\" | .truncated => \"truncated\"\n"
                 "          | .contract => \"contract\", site, call)\n"
                 "    \"{\\\"outcome\\\": \\\"\" ++ outcome ++ \"\\\", \\\"site\\\": \" ++ text site ++\n"
                 "      \", \\\"call\\\": \" ++ (match call with\n"
                 "        | some (site, function) => \"[\\\"\" ++ site ++ \"\\\", \\\"\" ++ function ++ \"\\\"]\"\n"
                 "        | none => \"null\") ++\n"
                 "      \", \\\"used\\\": \" ++ toString run.used ++ \", \\\"transitions\\\": \" ++\n"
                 "      toString run.transitions ++ \", \\\"messages\\\": \" ++ toString run.messages ++\n"
                 "      \", \\\"complete\\\": \" ++ toString run.unread.isEmpty ++ \"}\"\n"
                 "  else \"{\\\"outcome\\\": \\\"header\\\"}\""]
        for budget, bytes_, invalid in cases:
            lines.append(f"#eval IO.println (predict {budget} {lean_bytes(binding)} {lean_bytes(bytes_)} "
                         f"[{', '.join(lean_bytes(item) for item in invalid)}])")
        path = self.output / "Predictions.lean"
        path.write_text("\n\n".join(lines) + "\n", encoding="utf-8")
        result = self.run([self.args.lake, "env", "lean", path], cwd=LEAN, name="lean-predictions")
        values = [json.loads(line) for line in result.stdout.splitlines() if line.startswith("{")]
        self.check("lean-predictions", len(values) == len(cases), result.stdout[-400:])
        return values

    def runtime(self, artifacts):
        package = self.output / "package.zkpkg"
        pin = digest(artifacts["package_bytes"])
        result = self.run([self.args.native, "--json", "prove", f"--package={package}", f"--sha256={pin}",
                           f"--public={PUBLIC}", f"--witness={WITNESS}",
                           f"--output={self.output / 'proof.bin'}"], name="prove")
        producer = json.loads(result.stdout)
        proof = (self.output / "proof.bin").read_bytes()
        binding = proof[8:HEADER]
        self.check("proof-binding", binding.hex() == producer["execution"]["binding_sha256"])
        cases, observed, codes = [], [], {}
        for budget in range(0, 27):
            exit_code, report = self.verify(package, pin, proof, f"budget-{budget}", instructions=budget)
            cases.append((budget, proof, []))
            observed.append((f"budget-{budget}", self.observed(exit_code, report)))
        for name, (bytes_, invalid) in self.scenarios(proof).items():
            exit_code, report = self.verify(package, pin, bytes_, name)
            cases.append((1000000, bytes_, invalid))
            observed.append((name, self.observed(exit_code, report)))
            codes[name] = (exit_code, report.get("code"))
        # The Lean prediction maps every value to zero, so it cannot tell a wrong response from
        # the right one; the runtime must reject the wrong response itself.
        self.check("runtime-rejects-wrong-response", codes["response-wrong-value"][0] != 0
                   and codes["response-wrong-value"][1] == "artifact-rejected",
                   json.dumps(codes["response-wrong-value"]))
        predicted = self.predictions(artifacts, cases, binding)
        comparisons = []
        for (name, actual), expected in zip(observed, predicted):
            if expected["outcome"] == "returned" and actual["outcome"] == "accepted":
                expected = dict(expected, outcome="accepted")
            keys = ["outcome"] if expected["outcome"] == "header" else \
                ["outcome", "site", "call", "used", "transitions", "messages"]
            if expected["outcome"] in ("accepted", "returned"):
                keys.append("complete")
            same = all(actual.get(key) == expected.get(key) for key in keys)
            comparisons.append(dict(case=name, runtime=actual, lean=expected, compared=keys, same=same))
            self.check(f"runtime-agrees:{name}", same, json.dumps(dict(runtime=actual, lean=expected)))
        threshold = [c["case"] for c in comparisons if c["runtime"]["outcome"] == "accepted"]
        self.check("runtime-threshold", threshold[:2] == ["budget-25", "budget-26"])
        self.check("runtime-accepted-cases", threshold == ["budget-25", "budget-26", "honest"],
                   json.dumps(threshold))
        return dict(pin=pin, proof_sha256=digest(proof), binding=binding.hex(), comparisons=comparisons)

    # The receipt and its binding to the runtime.

    def receipt(self, artifacts, runtime, axioms):
        deployment = artifacts["deployment"]
        files = ["lean/ZkcExamples/Construction/SchnorrProofData.lean",
                 "lean/ZkcExamples/Construction/SchnorrProofParticipant.lean",
                 "lean/ZkcExamples/Executable/SchnorrProofProgramData.lean"]
        return {
            "format": "zkc.verification-receipt/0",
            "entry": ENTRY,
            "tools": {"compiler": digest(self.args.compiler.read_bytes()),
                      "native": digest(self.args.native.read_bytes()),
                      "lean_toolchain": (LEAN / "lean-toolchain").read_text().strip(),
                      "lake_manifests": {path: digest((ROOT / path).read_bytes()) for path in
                                         ["lean/lake-manifest.json",
                                          "lean/integrations/arklib/lake-manifest.json"]}},
            "artifacts": {
                "source_modules": {m.split("=")[0]: digest((ROOT / m.split("=")[1]).read_bytes()) for m in MODULES},
                "original": digest(artifacts["source"]),
                "original_export": digest(artifacts["original_text"].encode()),
                "constructed_export": digest(artifacts["export_text"].encode()),
                "constructed_candidate": artifacts["exported"][2],
                "program": digest(artifacts["program"]),
                "deployment": digest(artifacts["deployment_text"].encode()),
                "descriptor": deployment[3],
                "package": runtime["pin"],
            },
            "lean_data": {path: digest((ROOT / path).read_bytes()) for path in files},
            "runtime_selection": self.selected,
            "rules": [
                {"name": "transcript construction and participant projection",
                 "check": "Zkc.Construction.checkCompiled",
                 "accepts": ["original_export", "constructed_export"],
                 "certificate": "ZkcExamples.Construction.SchnorrProof.compiled",
                 "soundness": ["Zkc.Construction.compiled_transform", "Zkc.Construction.check_sound",
                               "Zkc.Construction.project_sound"],
                 "instance": "ZkcExamples.Construction.SchnorrProof.compiled_transform"},
                {"name": "executable lowering", "check": "Zkc.Executable.checkLowering",
                 "vocabulary": "Zkc.Executable.installed",
                 "accepts": ["constructed_export", "program"],
                 "certificate": "ZkcExamples.Executable.SchnorrProof.accepted",
                 "soundness": ["Zkc.Executable.execute_metered", "Zkc.Executable.validate_ideal",
                               "Zkc.Executable.validate_rejects"]},
            ],
            "theorem": THEOREM,
            "axioms": axioms,
            "proof_dependencies": self.dependencies,
            "assumptions": [
                "Lean kernel and the installed Lean toolchain",
                "the protocol-structured exporter and its renderer denote the original MLIR",
                "the zkc.program/0 renderer denotes the admitted program bytes",
                "the runtime accepts proof bytes for the admitted validator only when "
                "Zkc.Executable.validate accepts them under the Entry's checked occurrence context "
                "ZkcExamples.Construction.SchnorrProof.context",
                "installed kernels implement the meanings of Zkc.Executable.installed",
                "the native codec is a function of a message's bytes and type",
                "the bytes the native kernels absorb are an injective encoding of the model events: the "
                "suite's framing, labels and payload codecs encode typed histories injectively, and each "
                "occurrence template's model occurrence under ZkcExamples.Construction.SchnorrProof.context "
                "determines its native bytes (the occurrence-template encoding is proved injective by "
                "Zkc.Construction.occurrence_inj)",
                "the Merlin suite behaves as a random oracle on its absorbed byte histories",
                "reduced 64-byte challenges are treated as exactly uniform scalars",
                "the host binds the authorized public context and the policy's public inputs",
                "fixed statement: the statement is chosen before the prover runs",
            ],
        }

    def repackage(self, artifacts, change, *, keep_inner_digest=False):
        package = copy.deepcopy(artifacts["package"])
        deployment = copy.deepcopy(artifacts["deployment"])
        program = json.loads(deployment[4])
        change(program)
        deployment[4] = json.dumps(program, separators=(",", ":"))
        if not keep_inner_digest:
            deployment[5] = digest(deployment[4].encode())
        package["artifact"] = json.dumps(deployment, separators=(",", ":"))
        data = json.dumps(package, separators=(",", ":")).encode()
        return data, deployment

    def binding(self, artifacts, runtime, receipt):
        package = self.output / "package.zkpkg"
        named = json.loads(json.loads(package.read_bytes())["artifact"])[4].encode()
        self.check("receipt-program", digest(named) == receipt["artifacts"]["program"])
        self.check("receipt-package", digest(package.read_bytes()) == receipt["artifacts"]["package"])
        honest = (self.output / "proof.bin").read_bytes()
        wrong = self.scenarios(honest)["response-wrong-value"][0]
        exit_code, report = self.verify(package, receipt["artifacts"]["package"], honest, "receipt-honest")
        self.check("runtime-runs-receipt-package", exit_code == 0 and report.get("status") == "accepted"
                   and report.get("package_sha256") == receipt["artifacts"]["package"], json.dumps(report)[-400:])
        exit_code, report = self.verify(package, receipt["artifacts"]["package"], wrong, "receipt-wrong")
        self.check("receipt-package-rejects-wrong-response",
                   exit_code != 0 and report.get("code") == "artifact-rejected", json.dumps(report)[-400:])
        results = {}

        def trivial(program):
            function = next(item for item in program[2] if item[1] == "_calculation_2")
            operation = next(item for item in function[4] if item[:2] == ["op", "value_3"])
            operation[4] = [operation[4][0], operation[4][0]]

        mutated, deployment = self.repackage(artifacts, trivial)
        path = self.output / "package-mutated.zkpkg"
        path.write_bytes(mutated)
        exit_code, report = self.verify(path, receipt["artifacts"]["package"], wrong, "mutated-same-pin")
        results["same-pin"] = report.get("code")
        self.check("runtime-refuses-other-package", exit_code != 0 and report.get("code") == "entry-package-identity",
                   json.dumps(report)[-400:])
        exit_code, report = self.verify(path, digest(mutated), wrong, "mutated-repinned")
        results["repinned-wrong-proof"] = report.get("status")
        self.check("mutated-program-changes-acceptance", exit_code == 0 and report.get("status") == "accepted",
                   json.dumps(report)[-400:])
        mutated_program = deployment[4].encode()
        self.check("receipt-refuses-mutated-program", digest(mutated_program) != receipt["artifacts"]["program"])
        stale, _ = self.repackage(artifacts, trivial, keep_inner_digest=True)
        path = self.output / "package-stale-digest.zkpkg"
        path.write_bytes(stale)
        exit_code, report = self.verify(path, digest(stale), honest, "stale-inner-digest")
        results["stale-inner-digest"] = report.get("code")
        self.check("runtime-refuses-stale-program-digest",
                   exit_code != 0 and report.get("code") == "native-proof-candidate-binding",
                   json.dumps(report)[-400:])
        return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "build/compiler/zkc-compile")
    parser.add_argument("--native", type=Path, default=ROOT / "target/release/zkc",
                        help="the runtime CLI")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--output", type=Path, required=True, help="new or empty evidence directory")
    parser.add_argument("--write", action="store_true",
                        help="rewrite the committed Lean data from the fresh program")
    args = parser.parse_args()
    args.output = args.output.resolve()
    args.compiler = args.compiler.resolve()
    args.native = args.native.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    if any(args.output.iterdir()):
        parser.error("--output must be a new or empty directory")
    driver = Driver(args)
    report = dict(format="zkc.executable-check/0", entry=ENTRY, started=now(), status="failed")
    try:
        artifacts = driver.compile()
        driver.regenerate(artifacts)
        report["refused_mutations"] = driver.lean_rule(artifacts)
        runtime = driver.runtime(artifacts)
        receipt = driver.receipt(artifacts, runtime, driver.axioms())
        (args.output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        report["binding"] = driver.binding(artifacts, runtime, receipt)
        report["runtime"] = runtime
        report["receipt"] = receipt
        report["status"] = "pass"
    except (RuntimeError, ValueError, KeyError, IndexError, StopIteration) as error:
        report["error"] = str(error)
    report.update(finished=now(), commands=driver.commands, checks=driver.checks)
    (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(dict(status=report["status"], checks=len(driver.checks), error=report.get("error"))))
    sys.exit(0 if report["status"] == "pass" else 1)


if __name__ == "__main__":
    main()
