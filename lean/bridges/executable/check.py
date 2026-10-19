#!/usr/bin/env python3
"""Check the executable proof validators against Lean and the runtime.

For each subject, the compiled `example::Proof` Entries of the Schnorr and
Sumcheck examples, the driver compiles the Entry and retains its original
source, native deployment, Entry package, constructed validator export and the
`zkc.program/0` validator the runtime admits. It then

1. requires the committed executable and construction data to be the exact
   renderings of the fresh program and exports, and runs the Lean lowering rule
   on the fresh rendering and on mutated programs, each refused for its named
   reason or, for a changed helper body, accepted; the constructed export's
   policy must be the deployment's, and the role map the runtime uses must
   select the Lean statement's acceptance position and public inputs;
2. runs the runtime verifier on an honest proof at every instruction budget up
   to one past its acceptance threshold and on mutated proofs, and requires its
   outcome, stop site, local call, charged instructions, transcript transitions
   and read messages to equal those the Lean executable meaning predicts for
   the same bytes, with a decoder that refuses the payloads a mutation
   corrupted and reads the payloads it changed as another value; the runtime
   must accept exactly the honest runs at sufficient budgets;
3. checks the axiom closure of every theorem from the lowering rule to the
   byte-level security theorems in the ArkLib integration, and that their
   proofs reach the general composed rules and no Entry-specific equation
   about the compiled program's meaning;
4. writes a verification receipt per subject naming every artifact digest, the
   checked rules, the theorems and the remaining assumptions, and checks on the
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

sys.path.append(str(ROOT / "common/tests/support"))
from project import project_inputs  # noqa: E402

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Example-namespace theorems are Entry-specific. Among those a proof reaches, the
# walk lists every equation between processes (`PIR.Proc`), whether the kernel
# checks it by evaluation (`rfl`), and whether its statement names a meaning of a
# compiled program; the receipt records the original-side ones, and none may name
# a compiled meaning.
ENTRY_PREFIXES = ["ZkcExamples", "ZkcSecurity.Examples"]
COMPILED_MEANINGS = [
    "Zkc.Construction.spec",
    "Zkc.Construction.specK",
    "Zkc.Construction.ideal",
    "Zkc.Construction.idealK",
    "Zkc.Executable.execute",
    "Zkc.Executable.validate",
    "Zkc.Executable.metered",
]
# A root whose closure contains an Entry-specific equation about the compiled
# program: the classification must find it.
CLASSIFIER_CONTROL = "ZkcExamples.Construction.SchnorrProof.spec_equation"
# The terminal check helper of the Sumcheck example.
CHECK_HELPER = "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc"


def project_modules(manifest):
    modules, assets = project_inputs(ROOT / manifest)
    if assets:
        raise ValueError(f"{manifest} has assets")
    return [f"{name}={Path(source).resolve().relative_to(ROOT)}" for name, source in sorted(modules.items())]


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


def replace(data, offset, value):
    return data[:offset] + value + data[offset + len(value):]


def program_function(program, symbol):
    return next(item for item in program[2] if item[1] == symbol)


def program_validator(program, deployment):
    return next(item for item in program[3] if item[3] == deployment[2][1][3])


def function_operation(program, symbol, contract):
    """Select one top-level operation by its declared contract, retaining its names.

    Generated sites and binding symbols can change during Kernel lowering. A
    missing or ambiguous target is an error, never a skipped mutation.
    """
    bindings = {binding[0]: binding[1] for binding in program[1]}
    matches = [item for item in program_function(program, symbol)[4]
               if item[0] == "op" and bindings[item[2]] == contract]
    if len(matches) != 1:
        raise ValueError(f"expected one {contract!r} operation in {symbol!r}, found {len(matches)}")
    return matches[0]


class Schnorr:
    """The compiled Schnorr `example::Proof` Entry."""

    name = "schnorr"
    entry = "example::Proof"
    modules = ["example=examples/projects/schnorr/main.zkc", "schnorr=libraries/schnorr/lib.zkc"]
    public = ROOT / "examples/projects/schnorr/inputs/example.Proof/public.json"
    witness = ROOT / "examples/projects/schnorr/inputs/example.Proof/witness.json"
    data = LEAN / "ZkcExamples/Executable/SchnorrProofProgramData.lean"
    namespace = "ZkcExamples.Executable.SchnorrProofProgramData"
    construction = "ZkcExamples.Construction.SchnorrProof"
    # The executable takes the data inputs base then statement; values are mapped to zero.
    prediction_data = '[.data (.group "bls12-381.g1" 0), .data (.group "bls12-381.g1" 0)]'
    threshold = 25
    theorem = "ZkcSecurity.Examples.ExecutableSchnorrFiatShamir.knowledge_soundness"
    security_module = "ZkcSecurity.Examples.ExecutableSchnorrFiatShamir"
    chain = [
        theorem,
        "ZkcSecurity.Examples.ExecutableSchnorrFiatShamir.acceptance_le",
        "ZkcSecurity.Examples.CompiledSchnorrFiatShamir.knowledge_soundness",
        "ZkcExamples.Executable.SchnorrProof.accepted",
        "ZkcExamples.Executable.SchnorrProof.executable_validate",
        "ZkcExamples.Executable.SchnorrProof.executable_rejects",
        "ZkcExamples.Construction.SchnorrProof.kernel_admission",
        "ZkcExamples.Construction.SchnorrProof.compiled",
        "ZkcExamples.Construction.SchnorrProof.compiled_transform",
        "Zkc.Executable.execute_metered",
        "Zkc.Executable.validate_ideal",
        "Zkc.Executable.validate_rejects",
        "Zkc.Executable.execute_cleaned",
        "Zkc.Construction.compiled_transform",
        "Zkc.Construction.check_sound",
        "Zkc.Construction.project_sound",
    ]
    # Declarations the byte-level theorem's proof must reach: the general rules, the
    # admitted original they are applied to, and their checks on this Entry.
    used = [
        "Zkc.Construction.compiled_transform",
        "Zkc.Construction.check_sound",
        "Zkc.Construction.project_sound",
        "ZkcExamples.Construction.SchnorrProof.imported",
        "ZkcExamples.Construction.SchnorrProof.compiled",
        "Zkc.Executable.validate_ideal",
        "Zkc.Executable.validate_rejects",
        "ZkcExamples.Executable.SchnorrProof.accepted",
    ]
    # Entry-specific equations about the compiled program's meaning, which the proof must not use.
    unused = ["ZkcExamples.Construction.SchnorrProof.spec_equation"]
    lean_files = ["lean/ZkcExamples/Construction/SchnorrProofData.lean",
                  "lean/ZkcExamples/Construction/SchnorrProofParticipant.lean",
                  "lean/ZkcExamples/Executable/SchnorrProofProgramData.lean"]
    assumptions = [
        "Lean kernel and the installed Lean toolchain",
        "the protocol-structured exporter and its renderer denote the original MLIR",
        "the zkc.program/0 renderer reads the admitted program bytes as the runtime's program loader does",
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
    ]
    wrong_case = "response-wrong-value"

    def construction_data(self, artifacts):
        """Committed construction data: path, namespace, rendering, and whether this
        driver owns the file."""
        return [
            (LEAN / "ZkcExamples/Construction/SchnorrProofData.lean", "ZkcExamples.Construction.SchnorrProofData",
             lambda namespace: structured.render(json.loads(artifacts["original_text"]), namespace), True),
            (LEAN / "ZkcExamples/Construction/SchnorrProofParticipant.lean",
             "ZkcExamples.Construction.SchnorrProofParticipant",
             lambda namespace: constructed.render(artifacts["exported"], namespace), True),
        ]

    def rule_theorems(self):
        return ["theorem actual_total : (checkLowering installed Fresh.Constructed.participant "
                "Fresh.Actual.validator).toOption.map (·.total?) = some (some 25) := by decide +kernel"]

    def mutations(self, deployment):
        addition_binding = function_operation(json.loads(deployment[4]), "_calculation_2", "curve.add")[2]

        def addition_swapped(program):
            operation = function_operation(program, "_calculation_2", "curve.add")
            operation[4] = list(reversed(operation[4]))

        def comparison_trivial(program):
            operation = function_operation(program, "_calculation_2", "curve.equal")
            operation[4] = [operation[4][0], operation[4][0]]

        def results_swapped(program):
            body = program_validator(program, deployment)[6]
            body[-1][1] = list(reversed(body[-1][1]))

        def base_observed(program):
            participant = program_validator(program, deployment)
            call = next(item for item in participant[6] if item[:2] == ["local", "_transcript_12"])
            call[3] = [call[3][0], participant[4][0][0]]

        def stale_transcript(program):
            participant = program_validator(program, deployment)[6]
            first = next(item for item in participant if item[:2] == ["local", "_transcript_12"])
            third = next(item for item in participant if item[:2] == ["local", "_transcript_14"])
            third[3] = [first[4][0], third[3][1]]

        def uninstalled(program):
            binding = next(item for item in program[1] if item[0] == addition_binding)
            binding[3] = "fast/curve.add"

        def unchecked_representation(program):
            receive = next(item for item in program_validator(program, deployment)[6] if item[0] == "receive")
            receive[5] = receive[5].replace("@arkworks.g1/0", "@unchecked.g1/0")

        def formal_retyped(program):
            program_function(program, "_calculation_2")[2][0][1] = "bool@native.bool/0"

        def function_duplicated(program):
            program[2].append(copy.deepcopy(program_function(program, "_calculation_2")))

        return {
            "addition-swapped": (addition_swapped, "some (.instruction 12)"),
            "comparison-trivial": (comparison_trivial, "some (.instruction 13)"),
            "results-swapped": (results_swapped, "some (.different \"returned\")"),
            "base-observed": (base_observed, "some (.instruction 2)"),
            "stale-transcript": (stale_transcript, "some (.operation \"transition\")"),
            "uninstalled-implementation": (uninstalled, f"some (.binding {json.dumps(addition_binding)})"),
            "unchecked-representation": (unchecked_representation, "some .representation"),
            "formal-retyped": (formal_retyped, "some (.operation \"calculation_0\")"),
            "function-duplicated": (function_duplicated, "some (.duplicate \"function\")"),
        }

    def scenarios(self, proof):
        """Proof mutations, the payloads the runtime codec refuses in each, and the
        payloads it reads as another value."""
        assert proof[:8] == b"ZKCPRF00" and len(proof) == 148
        first, second = proof[48:102], proof[110:148]
        return {
            "honest": (proof, [], []),
            "commitment-not-on-curve": (replace(proof, 60, bytes([proof[60] ^ 0x01])),
                                        [replace(first, 12, bytes([first[12] ^ 0x01]))], []),
            "commitment-wrong-tag": (replace(proof, 53, b"\x07"), [replace(first, 5, b"\x07")], []),
            "response-out-of-range": (replace(proof, 116, b"\xff" * 32),
                                      [replace(second, 6, b"\xff" * 32)], []),
            "response-wrong-value": (replace(proof, 116, b"\x00" * 31 + b"\x01"), [], []),
            "response-missing": (proof[:102], [], []),
            "response-truncated": (proof[:120], [], []),
            "trailing-byte": (proof + b"\x00", [], []),
            "header-binding": (replace(proof, 8, bytes([proof[8] ^ 0x01])), [], []),
        }

    def runtime_only(self, driver, codes):
        # With every value mapped to zero the prediction cannot tell a wrong response from
        # the right one; the runtime must reject the wrong response itself.
        driver.check("schnorr:runtime-rejects-wrong-response", codes["response-wrong-value"][0] != 0
                     and codes["response-wrong-value"][1] == "artifact-rejected",
                     json.dumps(codes["response-wrong-value"]))

    @staticmethod
    def receipt_mutation(program):
        operation = function_operation(program, "_calculation_2", "curve.equal")
        operation[4] = [operation[4][0], operation[4][0]]

    def rules_entry(self):
        return [
            {"name": "transcript construction and participant projection",
             "check": "Zkc.Construction.checkCompiled",
             "accepts": ["original_export", "constructed_export"],
             "subject": "ZkcExamples.Construction.SchnorrProof.imported",
             "admission": "ZkcExamples.Construction.SchnorrProof.kernel_admission",
             "certificate": "ZkcExamples.Construction.SchnorrProof.compiled",
             "soundness": ["Zkc.Construction.compiled_transform", "Zkc.Construction.check_sound",
                           "Zkc.Construction.project_sound"],
             "instance": "ZkcExamples.Construction.SchnorrProof.compiled_transform"},
            {"name": "executable lowering", "check": "Zkc.Executable.checkLowering",
             "vocabulary": "Zkc.Executable.installed",
             "accepts": ["constructed_export", "program"],
             "certificate": "ZkcExamples.Executable.SchnorrProof.accepted",
             "soundness": ["Zkc.Executable.execute_metered", "Zkc.Executable.validate_ideal",
                           "Zkc.Executable.validate_rejects", "Zkc.Executable.execute_cleaned"]},
        ]


class Sumcheck:
    """The compiled Sumcheck `example::Proof` Entry."""

    name = "sumcheck"
    entry = "example::Proof"
    public = ROOT / "examples/projects/sumcheck/inputs/example.Proof/public.json"
    # Every input of the producer is public.
    witness = None
    data = LEAN / "ZkcExamples/Executable/SumcheckProofProgramData.lean"
    namespace = "ZkcExamples.Executable.SumcheckProofProgramData"
    construction = "ZkcExamples.Construction.SumcheckProof"
    # The executable takes the table values, the claim and the round count; the
    # prediction keeps the shapes of the public inputs (four values, two rounds) and
    # maps every value to zero, so that every honest check holds.
    prediction_data = '[.vector "bls12-381.fr" [0, 0, 0, 0], .data (.field "bls12-381.fr" 0), .index 2]'
    threshold = 190
    theorem = "ZkcSecurity.Examples.ExecutableSumcheckFiatShamir.adaptive_soundness"
    security_module = "ZkcSecurity.Examples.ExecutableSumcheckFiatShamir"
    chain = [
        theorem,
        "ZkcSecurity.Examples.ExecutableSumcheckFiatShamir.reduced_soundness",
        "ZkcSecurity.Examples.ExecutableSumcheckFiatShamir.soundness",
        "ZkcSecurity.Examples.ExecutableSumcheckFiatShamir.acceptance_le",
        "ZkcSecurity.Examples.ExecutableSumcheckFiatShamir.verifyBytes_prunes",
        "ZkcSecurity.Examples.ExecutableSumcheckFiatShamir.initial_determined",
        "ZkcSecurity.VCVio.Pruning.Prunes.prEvent_le",
        "ZkcSecurity.Examples.CompiledSumcheckFiatShamir.adaptive_soundness",
        "ZkcSecurity.Examples.CompiledSumcheckFiatShamir.soundness",
        "ZkcExamples.Executable.SumcheckProof.accepted",
        "ZkcExamples.Executable.SumcheckProof.executable_metered",
        "ZkcExamples.Executable.SumcheckProof.executable_prunes",
        "ZkcExamples.Executable.SumcheckProof.executable_transform_prunes",
        "ZkcExamples.Executable.SumcheckHelpers.prepared",
        "ZkcExamples.Executable.SumcheckHelpers.check_prepared",
        "ZkcExamples.Construction.SumcheckProof.compiled",
        "ZkcExamples.Construction.SumcheckProof.compiled_transform",
        "Zkc.Executable.execute_metered",
        "Zkc.Executable.validate_metered",
        "Zkc.Executable.metered_prunes",
        "Zkc.Executable.validate_prunes",
        "Zkc.Executable.execute_cleaned",
        "Zkc.Construction.compiled_transform",
        "Zkc.Construction.check_sound",
        "Zkc.Construction.project_sound",
    ]
    used = [
        "Zkc.Construction.compiled_transform",
        "Zkc.Construction.check_sound",
        "Zkc.Construction.project_sound",
        "ZkcExamples.Structured.SumcheckSourceViews.imported",
        "ZkcExamples.Construction.SumcheckProof.compiled",
        "Zkc.Executable.validate_prunes",
        "ZkcExamples.Executable.SumcheckProof.accepted",
        "ZkcExamples.Executable.SumcheckHelpers.check_prepared",
        "ZkcSecurity.VCVio.Pruning.Prunes.prEvent_le",
        "ZkcSecurity.Examples.ExecutableSumcheckFiatShamir.initial_determined",
    ]
    unused = []
    lean_files = ["lean/ZkcExamples/Structured/SumcheckSourceData.lean",
                  "lean/ZkcExamples/Construction/SumcheckProofParticipant.lean",
                  "lean/ZkcExamples/Executable/SumcheckProofProgramData.lean"]
    assumptions = [
        "Lean kernel and the installed Lean toolchain",
        "the protocol-structured exporter and its renderer denote the original MLIR",
        "the zkc.program/0 renderer reads the admitted program bytes as the runtime's program loader does",
        "the runtime accepts proof bytes for the admitted validator only when "
        "Zkc.Executable.validate accepts them under the Entry's checked occurrence context "
        "ZkcExamples.Construction.SumcheckProof.context",
        "installed kernels implement the meanings of Zkc.Executable.installed",
        "the native codec is a function of a message's bytes and type",
        "the bytes the native kernels absorb are an injective encoding of the model events, and each "
        "occurrence template's model occurrence under ZkcExamples.Construction.SumcheckProof.context "
        "determines its native bytes",
        "the Merlin suite behaves as a random oracle on its absorbed byte histories",
        "the suite's challenge derivation is the decoding of the adaptive theorem, with its stated loss",
        "the managed transcript absorbs the invocation's public values injectively, as "
        "ZkcSecurity.Examples.ExecutableSumcheckFiatShamir.initial encodes them",
    ]
    wrong_case = "first-round-check"

    def __init__(self):
        self.modules = project_modules("examples/projects/sumcheck/zkc.toml")

    def construction_data(self, artifacts):
        """Committed construction data: path, namespace, rendering, and whether this
        driver owns the file. The structured bridge owns the admitted source's
        rendering; this driver compares it."""
        return [
            (LEAN / "ZkcExamples/Structured/SumcheckSourceData.lean", "ZkcExamples.Structured.SumcheckSourceData",
             lambda namespace: structured.render(json.loads(artifacts["original_text"]), namespace), False),
            (LEAN / "ZkcExamples/Construction/SumcheckProofParticipant.lean",
             "ZkcExamples.Construction.SumcheckProofParticipant",
             lambda namespace: constructed.render(artifacts["exported"], namespace), True),
        ]

    def rule_theorems(self):
        return ["theorem actual_helpers : Instruction.helperList Fresh.Constructed.participant.instructions = "
                "[\"zkl_411728361dd91cce996681067ff835983db4b50a2c76153019bcfb3dff123b46\", "
                "\"zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58\", "
                f"\"{CHECK_HELPER}\"] := by decide +kernel"]

    def mutations(self, deployment):
        def participant(program):
            return program_validator(program, deployment)[6]

        def loop(program):
            return next(item for item in participant(program) if item[0] == "loop")

        def maximum_raised(program):
            loop(program)[2][2] = "3"

        def count_retargeted(program):
            loop(program)[2][1] = program_validator(program, deployment)[4][1][0]

        def carried_swapped(program):
            carried = loop(program)[3]
            carried[0][1], carried[1][1] = carried[1][1], carried[0][1]

        def round_check_trivial(program):
            operation = function_operation(program, "_calculation_3", "field.equal")
            operation[4] = [operation[4][1], operation[4][1]]

        def stale_transcript(program):
            body = loop(program)[5]
            first = next(item for item in body if item[:2] == ["local", "_transcript_12"])
            second = next(item for item in body if item[:2] == ["local", "_transcript_13"])
            second[3] = [first[3][0]] + second[3][1:]

        def helper_retargeted(program):
            call = next(item for item in participant(program) if item[0] == "local")
            call[2] = "_calculation_4"

        def results_swapped(program):
            body = participant(program)
            body[-1][1] = list(reversed(body[-1][1]))

        def uninstalled(program):
            binding = next(item for item in program[1] if item[0] == "_transcript_0")
            binding[3] = "fast/transcript.native.indexed.observe.data"

        def check_body_changed(program):
            terminal = program_function(program, CHECK_HELPER)
            constant = next(item for item in terminal[4] if item[:3] == ["op", "lc_2_s2", "zkl_binding_0"])
            constant[3] = ["2"]

        return {
            "loop-maximum-raised": (maximum_raised, "some (.instruction 1)"),
            "loop-count-retargeted": (count_retargeted, "some (.loop \"apply_18_label_726564756365_s15\")"),
            "loop-carried-swapped": (carried_swapped, "some (.operation \"apply_18_label_726564756365_s24\")"),
            "round-check-trivial": (round_check_trivial, "some (.instruction 1)"),
            "stale-transcript": (stale_transcript, "some (.operation \"transition\")"),
            "helper-retargeted": (helper_retargeted, "some (.operation \"apply_18_label_726564756365_s12\")"),
            "results-swapped": (results_swapped, "some (.different \"returned\")"),
            "uninstalled-implementation": (uninstalled, "some (.binding \"_transcript_0\")"),
            # The rule reads a helper body only for its sorts and its freedom from transcript
            # operations; what the body computes is the obligation
            # `ZkcExamples.Executable.SumcheckHelpers.check_prepared` discharges for the
            # committed program, which regeneration ties to the fresh one.
            "check-body-changed": (check_body_changed, "none"),
        }

    def scenarios(self, proof):
        """Proof mutations, the payloads the runtime codec refuses in each, and the
        payloads it reads as another value."""
        assert proof[:8] == b"ZKCPRF00" and len(proof) == 224
        frames = [proof[48 + 46 * index:86 + 46 * index] for index in range(4)]
        assert all(proof[40 + 46 * index:48 + 46 * index] == bytes([38, 0, 0, 0, 0, 0, 0, 0])
                   for index in range(4))

        def value_changed(index):
            offset = 48 + 46 * index + 6
            changed = replace(proof, offset, bytes([proof[offset] ^ 0x01]))
            return changed, [], [changed[48 + 46 * index:86 + 46 * index]]

        return {
            "honest": (proof, [], []),
            "round-value-out-of-range": (replace(proof, 54, b"\xff" * 32), [replace(frames[0], 6, b"\xff" * 32)],
                                         []),
            "round-value-wrong-tag": (replace(proof, 53, b"\x07"), [replace(frames[0], 5, b"\x07")], []),
            "first-round-check": value_changed(0),
            "second-round-check": value_changed(2),
            "last-message-missing": (proof[:178], [], []),
            "last-message-truncated": (proof[:200], [], []),
            "trailing-byte": (proof + b"\x00", [], []),
            "header-binding": (replace(proof, 8, bytes([proof[8] ^ 0x01])), [], []),
        }

    def runtime_only(self, driver, codes):
        for name in ("first-round-check", "second-round-check"):
            driver.check(f"sumcheck:runtime-rejects-{name}", codes[name][0] != 0, json.dumps(codes[name]))

    @staticmethod
    def receipt_mutation(program):
        # The round check and the terminal comparison compare a value with itself, so a
        # wrong round message is accepted.
        round_check = function_operation(program, "_calculation_3", "field.equal")
        round_check[4] = [round_check[4][1], round_check[4][1]]
        terminal = program_function(program, CHECK_HELPER)
        branch = next(item for item in terminal[4] if item[:3] == ["if", "lc_2_s6", "v149"])
        final = next(item for item in branch[4]
                     if item[:2] == ["op", "lc_2_s7_44_s8h73756d636865636b11h636865636b5f7461626c65_3_s11"])
        final[4] = [final[4][1], final[4][1]]

    def rules_entry(self):
        return [
            {"name": "transcript construction and participant projection",
             "check": "Zkc.Construction.checkCompiled",
             "accepts": ["original_export", "constructed_export"],
             "subject": "ZkcExamples.Structured.SumcheckSourceViews.imported",
             "certificate": "ZkcExamples.Construction.SumcheckProof.compiled",
             "soundness": ["Zkc.Construction.compiled_transform", "Zkc.Construction.check_sound",
                           "Zkc.Construction.project_sound"],
             "instance": "ZkcExamples.Construction.SumcheckProof.compiled_transform"},
            {"name": "executable lowering", "check": "Zkc.Executable.checkLowering",
             "vocabulary": "Zkc.Executable.installed",
             "accepts": ["constructed_export", "program"],
             "certificate": "ZkcExamples.Executable.SumcheckProof.accepted",
             "helper_preparation": "ZkcExamples.Executable.SumcheckHelpers.prepared",
             "soundness": ["Zkc.Executable.execute_metered", "Zkc.Executable.validate_metered",
                           "Zkc.Executable.metered_prunes", "Zkc.Executable.validate_prunes",
                           "Zkc.Executable.execute_cleaned"]},
        ]


SUBJECTS = {subject.name: subject for subject in (Schnorr(), Sumcheck())}


class Driver:
    def __init__(self, args):
        self.args = args
        self.output = args.output
        self.commands = []
        self.checks = []
        self.dependencies = {}
        self.selected = {}

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

    def directory(self, subject):
        path = self.output / subject.name
        path.mkdir(parents=True, exist_ok=True)
        return path

    # Compilation and retained artifacts.

    def compile(self, subject):
        output = self.directory(subject)
        prefix = subject.name
        common = ["--source-format=zkc", f"--entry={subject.entry}", *[f"--module={m}" for m in subject.modules]]
        compiler = self.args.compiler
        source = self.run([compiler, "language-emit", *common], name=f"{prefix}:emit").stdout.encode()
        (output / "source.mlir").write_bytes(source)
        deployment_text = self.run([compiler, "language-bundle", *common],
                                   name=f"{prefix}:bundle").stdout.rstrip("\n")
        (output / "deployment.json").write_text(deployment_text)
        package_text = self.run([compiler, "language-package", *common], name=f"{prefix}:package").stdout
        package_bytes = package_text.encode()
        (output / "package.zkpkg").write_bytes(package_bytes)
        package = json.loads(package_text)
        deployment = json.loads(deployment_text)
        program = deployment[4].encode()
        (output / "program.json").write_bytes(program)
        self.check(f"{prefix}:package-artifact", package["artifact"] == deployment_text)
        self.check(f"{prefix}:package-original", package["original"].encode() == source)
        self.check(f"{prefix}:deployment-source", deployment[1] == digest(source))
        self.check(f"{prefix}:deployment-program", deployment[5] == digest(program))
        policy = deployment[2][1]
        (output / "policy.json").write_text(json.dumps(policy))
        candidate = self.run([compiler, "protocol-construct-proof", output / "source.mlir",
                              output / "policy.json"], name=f"{prefix}:construct").stdout
        (output / "candidate.mlir").write_text(candidate)
        export_text = self.run([compiler, "protocol-constructed-participant", output / "source.mlir",
                                output / "policy.json", output / "candidate.mlir"],
                               name=f"{prefix}:participant").stdout
        (output / "participant.json").write_text(export_text)
        exported = json.loads(export_text)
        original_text = self.run([compiler, "protocol-structured", output / "source.mlir",
                                  f"--symbol={policy[1]}"], name=f"{prefix}:original").stdout
        (output / "original.json").write_text(original_text)
        self.check(f"{prefix}:participant-source", exported[1] == "sha256:" + digest(source))
        self.check(f"{prefix}:participant-policy", exported[3] == policy, json.dumps([exported[3], policy]))
        return dict(source=source, deployment=deployment, deployment_text=deployment_text,
                    package=package, package_bytes=package_bytes, program=program,
                    exported=exported, export_text=export_text, original_text=original_text)

    def regenerate(self, subject, artifacts):
        files = {subject.data: (executable.render(artifacts["deployment"], subject.namespace), True)}
        for path, namespace, render, owned in subject.construction_data(artifacts):
            files[path] = (render(namespace), owned)
        for path, (text, owned) in files.items():
            if self.args.write and owned and path == subject.data:
                path.write_text(text, encoding="utf-8")
            current = path.read_text(encoding="utf-8") if path.exists() else None
            self.check(f"regenerated:{path.relative_to(ROOT)}", current == text,
                       "committed data differs from the fresh export")

    def axioms(self, subjects):
        """The axiom closure of every theorem in the receipts' chains, and the declarations
        each byte-level theorem's proof reaches."""
        path = self.output / "ReceiptAxioms.lean"
        prefixes = ", ".join(f"`{name}" for name in ENTRY_PREFIXES)
        meanings = ", ".join(f"`{name}" for name in COMPILED_MEANINGS)
        imports = sorted({subject.security_module for subject in subjects}
                         | {"ZkcSecurity.Examples.ExecutableSchnorrFiatShamir"})
        chain = []
        for subject in subjects:
            chain += [name for name in subject.chain if name not in chain]
        reaches = [(subject.theorem, name) for subject in subjects for name in subject.used + subject.unused]
        path.write_text(
            "".join(f"import {name}\n" for name in imports) + "import Zkc.Executable.Cleanup\n\n"
            + "".join(f"#print axioms {name}\n" for name in chain)
            + "\nopen Lean in\n"
            "/-- The transitive constant dependencies of `root`, `root` included. -/\n"
            "def dependencyClosure (root : Name) : CoreM (Array Name) := do\n"
            "  let env ← getEnv\n"
            "  let mut visited : NameSet := {}\n"
            "  let mut order : Array Name := #[]\n"
            "  let mut pending : List Name := [root]\n"
            "  repeat\n"
            "    match pending with\n"
            "    | [] => break\n"
            "    | name :: rest =>\n"
            "      pending := rest\n"
            "      unless visited.contains name do\n"
            "        visited := visited.insert name\n"
            "        order := order.push name\n"
            "        if let some info := env.find? name then\n"
            "          for used in info.getUsedConstantsAsSet do\n"
            "            unless visited.contains used do pending := used :: pending\n"
            "  return order\n\n"
            "open Lean in\n"
            "/-- Whether `target` occurs in the transitive constant dependencies of `root`. -/\n"
            "def reaches (root target : Name) : CoreM Bool :=\n"
            "  return (← dependencyClosure root).contains target\n\n"
            "open Lean Meta in\n"
            "/-- Entry-specific theorems in the closure of `root` whose statement is an\n"
            "equation between processes: whether the kernel checks each by evaluation\n"
            "(its proof is `rfl`) and whether its statement names a compiled meaning.\n"
            "Equation lemmas generated for definitions are unfoldings and are skipped. -/\n"
            "def processEquations (root : Name) : MetaM (Array (Name × Bool × Bool)) := do\n"
            "  let env ← getEnv\n"
            f"  let meanings : List Name := [{meanings}]\n"
            "  for meaning in meanings do\n"
            "    unless env.contains meaning do throwError \"unknown compiled meaning {meaning}\"\n"
            "  let mut found := #[]\n"
            "  for name in (← dependencyClosure root).qsort Name.lt do\n"
            f"    unless [{prefixes}].any (·.isPrefixOf name) do continue\n"
            "    if let .str _ last := name then\n"
            "      if last.startsWith \"eq_\" then continue\n"
            "    let some (.thmInfo info) := env.find? name | continue\n"
            "    let isProcess ← forallTelescope info.type fun _ body => do\n"
            "      let body ← whnfR body\n"
            "      if body.isAppOfArity ``Eq 3 then\n"
            "        return (← whnfR (body.getArg! 0)).isAppOf ``PIR.Proc\n"
            "      return false\n"
            "    unless isProcess do continue\n"
            "    let evaluated ← lambdaTelescope info.value fun _ proof =>\n"
            "      return proof.isAppOf ``Eq.refl || proof.isAppOf ``rfl\n"
            "    let compiled := info.type.getUsedConstants.any meanings.contains\n"
            "    found := found.push (name, evaluated, compiled)\n"
            "  return found\n\n"
            + "".join(f"#eval do IO.println s!\"reaches {root} {name}: {{← reaches `{root} `{name}}}\"\n"
                      for root, name in reaches)
            + "\nopen Lean Meta in\n"
            "#eval show MetaM Unit from do\n"
            + "".join(f"  for (name, evaluated, compiled) in ← processEquations `{subject.theorem} do\n"
                      f"    IO.println s!\"process-equation {subject.theorem} {{name}} evaluated={{evaluated}} "
                      "compiled={compiled}\"\n" for subject in subjects)
            + f"  for (name, evaluated, compiled) in ← processEquations `{CLASSIFIER_CONTROL} do\n"
            "    IO.println s!\"control-equation {name} evaluated={evaluated} compiled={compiled}\"\n",
            encoding="utf-8")
        result = self.run([self.args.lake, "env", "lean", path], cwd=LEAN / "integrations/arklib",
                          name="receipt-axioms")
        found = {}
        for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout):
            found[name] = sorted(a.strip() for a in axioms.split(",") if a.strip())
        for name in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout):
            found[name] = []
        for name in chain:
            self.check(f"axioms:{name}", name in found and set(found[name]) <= ALLOWED_AXIOMS,
                       json.dumps(found.get(name)))
        reached = {(root, name): value for root, name, value in
                   re.findall(r"^reaches (\S+) (\S+): (true|false)$", result.stdout, re.M)}
        controls = re.findall(r"^control-equation (\S+) evaluated=(true|false) compiled=(true|false)$",
                              result.stdout, re.M)
        self.check("process-equation-classifier", (CLASSIFIER_CONTROL, "false", "true") in controls,
                   json.dumps(controls))
        for subject in subjects:
            for name in subject.used:
                value = reached.get((subject.theorem, name))
                self.check(f"{subject.name}:proof-uses:{name}", value == "true", json.dumps(value))
            for name in subject.unused:
                value = reached.get((subject.theorem, name))
                self.check(f"{subject.name}:proof-avoids:{name}", value == "false", json.dumps(value))
            equations = re.findall(rf"^process-equation {re.escape(subject.theorem)} (\S+) "
                                   r"evaluated=(true|false) compiled=(true|false)$", result.stdout, re.M)
            compiled = [name for name, _, flag in equations if flag == "true"]
            self.check(f"{subject.name}:proof-avoids-compiled-equations", not compiled, json.dumps(compiled))
            self.dependencies[subject.name] = dict(
                uses=subject.used, avoids=subject.unused,
                original_stage_equations=dict(
                    evaluated=[name for name, flag, _ in equations if flag == "true"],
                    derived=[name for name, flag, _ in equations if flag == "false"]))
        return {name: found.get(name) for name in chain}

    # The Lean lowering rule on the fresh program and on mutations.

    def mutated_deployment(self, deployment, change):
        value = copy.deepcopy(deployment)
        program = json.loads(value[4])
        change(program)
        value[4] = json.dumps(program, separators=(",", ":"))
        value[5] = digest(value[4].encode())
        return value

    def lean_rule(self, subject, artifacts):
        deployment = artifacts["deployment"]
        exported = artifacts["exported"]
        parts = ["import Zkc.Executable.Installed", "import Zkc.Executable.Lowering",
                 "import Zkc.Construction.Participant", f"import {subject.construction}",
                 "set_option maxRecDepth 20000",
                 body(constructed.render(exported, "Fresh.Constructed")),
                 body(executable.render(deployment, "Fresh.Actual")),
                 "open Zkc.Construction Zkc.Executable",
                 "def refusal : Except Refusal Lowered → Option Refusal\n"
                 "  | .error refusal => some refusal\n  | .ok _ => none"]
        selected = self.selected[subject.name] = self.role_map(subject, deployment)
        proofs = ["theorem actual_accepted : refusal (checkLowering installed Fresh.Constructed.participant "
                  "Fresh.Actual.validator) = none := by decide +kernel",
                  *subject.rule_theorems(),
                  # The runtime decides acceptance at its role map's index; the theorems read the
                  # committed acceptance position and bind data inputs in policy order.
                  f"theorem acceptance_position : {subject.construction}.acceptancePosition = "
                  f"{int(selected['acceptance'])} := by decide +kernel",
                  f"theorem public_inputs : {subject.construction}.participant.policy.publicInputs = "
                  f"[{', '.join(str(int(port)) for port in selected['data_inputs'])}] := by decide +kernel"]
        mutations = subject.mutations(deployment)
        for index, (name, (change, reason)) in enumerate(mutations.items()):
            namespace = f"Fresh.Mutation{index}"
            parts.append(body(executable.render(self.mutated_deployment(deployment, change), namespace)))
            proofs.append(f"/-- {name} -/\ntheorem mutation{index}_refused : refusal (checkLowering installed "
                          f"Fresh.Constructed.participant {namespace}.validator) = {reason} := "
                          f"by decide +kernel")
        proofs.append("#print axioms actual_accepted")
        source = "\n\n".join(parts + proofs) + "\n"
        path = self.directory(subject) / "FreshLowering.lean"
        path.write_text(source, encoding="utf-8")
        result = self.run([self.args.lake, "env", "lean", path], cwd=LEAN, name=f"{subject.name}:lean-rule")
        marker = "'actual_accepted' depends on axioms: ["
        axioms = result.stdout.split(marker, 1)[1].split("]", 1)[0] if marker in result.stdout else None
        self.check(f"{subject.name}:lean-rule", axioms is not None
                   and {name.strip() for name in axioms.split(",") if name.strip()} <= ALLOWED_AXIOMS,
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

    def role_map(self, subject, deployment):
        prefix = subject.name
        selection = self.role_selection(deployment)
        self.check(f"{prefix}:role-map-validator", selection is not None)
        self.check(f"{prefix}:role-map-public-inputs", selection["inputs_match"], json.dumps(selection))
        self.check(f"{prefix}:role-map-acceptance", selection["acceptance_match"], json.dumps(selection))
        # Controls: a policy selecting another output, or public inputs in another order, fails.
        other = copy.deepcopy(deployment)
        other[2][1][4] = str(int(other[2][1][4]) + 1)
        reordered = copy.deepcopy(deployment)
        reordered[2][1][7] = list(reversed(reordered[2][1][7]))
        self.check(f"{prefix}:role-map-refuses-other-acceptance",
                   not self.role_selection(other)["acceptance_match"])
        self.check(f"{prefix}:role-map-refuses-reordered-inputs",
                   not self.role_selection(reordered)["inputs_match"])
        return dict(symbol=selection["symbol"], data_inputs=selection["data_inputs"],
                    acceptance=selection["acceptance"])

    # The runtime and the Lean predictions.

    def verify(self, subject, package, pin, proof, name, *, instructions=None):
        output = self.directory(subject)
        path = output / f"proof-{name}.bin"
        path.write_bytes(proof)
        arguments = [self.args.native, "--json", "verify", f"--package={package}", f"--sha256={pin}",
                     f"--public={subject.public}", f"--proof={path}"]
        if instructions is not None:
            limits = output / f"capacity-{instructions}.json"
            limits.write_text(json.dumps(capacity(instructions)))
            arguments.append(f"--capacity={limits}")
        result = self.run(arguments, expect=None, name=f"{subject.name}:verify:{name}")
        report = json.loads(result.stdout) if result.stdout.strip() else {}
        (output / f"verify-{name}.json").write_text(result.stdout)
        return result.returncode, report

    @staticmethod
    def observed(exit_code, report):
        """The runtime's observation in the vocabulary of the Lean prediction."""
        execution = report.get("execution") or {}
        stop = execution.get("stop") or {}
        code = report.get("code")
        kind = str(stop.get("kind", ""))
        transcript = [r for r in execution.get("resources") or [] if r.get("stage") == "transcript"]
        if code == "proof-header":
            outcome = "header"
        elif exit_code == 0:
            outcome = "accepted"
        elif code in ("artifact-rejected", "proof-trailing"):
            outcome = "returned"
        elif code == "proof-truncated":
            outcome = "truncated"
        elif kind == "Limit":
            outcome = "limit"
        elif kind.startswith("Decode"):
            outcome = "decode"
        elif kind.startswith("Explicit(") and kind.endswith(")"):
            outcome = "explicit:" + kind[len("Explicit("):-1].strip('"')
        else:
            outcome = f"other:{code}:{kind}"
        local = stop.get("local")
        return dict(outcome=outcome,
                    site=stop.get("site") if outcome not in ("header", "truncated") else None,
                    call=[local["site"], local["function"]] if local else None,
                    used=execution.get("instructions"),
                    transitions=transcript[0]["transitions"] if transcript else None,
                    messages=execution.get("messages"),
                    complete=code != "proof-trailing" if outcome in ("accepted", "returned") else None)

    def predictions(self, subject, artifacts, cases, binding):
        """Evaluate the Lean executable meaning on every case."""
        lines = ["import Zkc.Executable.Installed", "import Mathlib.Algebra.Field.ZMod",
                 # The occurrence context is the committed one, which `regenerate` ties to the
                 # fresh original and constructed exports.
                 f"import {subject.construction}",
                 body(executable.render(artifacts["deployment"], "Fresh.Actual")),
                 "open Zkc.Construction Zkc.Executable",
                 "local instance : Fact (Nat.Prime 5) := ⟨by decide⟩",
                 "abbrev Scalar := ZMod 5",
                 "def challengeZero : History Scalar Scalar → Id Scalar := fun _ => 0",
                 "def decodeWith (invalid ones : List (List UInt8)) : PhysicalType → List UInt8 → "
                 "Option (Payload Scalar Scalar)\n"
                 "  | ⟨.data (.group domain), _⟩, payload => if invalid.contains payload then none\n"
                 "      else some (.group domain (if ones.contains payload then 1 else 0))\n"
                 "  | ⟨.data (.field domain), _⟩, payload => if invalid.contains payload then none\n"
                 "      else some (.field domain (if ones.contains payload then 1 else 0))\n"
                 "  | _, _ => none",
                 "def text : Option String → String\n  | some value => \"\\\"\" ++ value ++ \"\\\"\"\n"
                 "  | none => \"null\"",
                 "def cause : Cause → String\n"
                 "  | .limit => \"limit\" | .decode => \"decode\" | .truncated => \"truncated\"\n"
                 "  | .contract => \"contract\" | .kernel reason => \"kernel:\" ++ toString (repr reason)\n"
                 "  | .explicit .reject => \"explicit:reject\"\n"
                 "  | .explicit reason => \"explicit:\" ++ toString (repr reason)",
                 "def predict (budget : Nat) (binding bytes : List UInt8) (invalid ones : List (List UInt8)) : "
                 "String :=\n"
                 "  if bytes.take 40 = magic ++ binding then\n"
                 "    let run := Id.run (execute installed Fresh.Actual.validator\n"
                 f"      {subject.construction}.context challengeZero\n"
                 f"      (decodeWith invalid ones) budget {subject.prediction_data} []\n"
                 "      (bytes.drop 40))\n"
                 "    let (outcome, site, call) := match run.result with\n"
                 "      | .returned _ => (\"returned\", none, none)\n"
                 "      | .stopped stop site call => (cause stop, site, call)\n"
                 "    \"{\\\"outcome\\\": \\\"\" ++ outcome ++ \"\\\", \\\"site\\\": \" ++ text site ++\n"
                 "      \", \\\"call\\\": \" ++ (match call with\n"
                 "        | some (site, function) => \"[\\\"\" ++ site ++ \"\\\", \\\"\" ++ function ++ \"\\\"]\"\n"
                 "        | none => \"null\") ++\n"
                 "      \", \\\"used\\\": \" ++ toString run.used ++ \", \\\"transitions\\\": \" ++\n"
                 "      toString run.transitions ++ \", \\\"messages\\\": \" ++ toString run.messages ++\n"
                 "      \", \\\"complete\\\": \" ++ toString run.unread.isEmpty ++ \"}\"\n"
                 "  else \"{\\\"outcome\\\": \\\"header\\\"}\""]
        for budget, bytes_, invalid, ones in cases:
            lines.append(f"#eval IO.println (predict {budget} {lean_bytes(binding)} {lean_bytes(bytes_)} "
                         f"[{', '.join(lean_bytes(item) for item in invalid)}] "
                         f"[{', '.join(lean_bytes(item) for item in ones)}])")
        path = self.directory(subject) / "Predictions.lean"
        path.write_text("\n\n".join(lines) + "\n", encoding="utf-8")
        result = self.run([self.args.lake, "env", "lean", path], cwd=LEAN,
                          name=f"{subject.name}:lean-predictions")
        values = [json.loads(line) for line in result.stdout.splitlines() if line.startswith("{")]
        self.check(f"{subject.name}:lean-predictions", len(values) == len(cases), result.stdout[-400:])
        return values

    def runtime(self, subject, artifacts):
        output = self.directory(subject)
        package = output / "package.zkpkg"
        pin = digest(artifacts["package_bytes"])
        arguments = [self.args.native, "--json", "prove", f"--package={package}", f"--sha256={pin}",
                     f"--public={subject.public}", f"--output={output / 'proof.bin'}"]
        if subject.witness is not None:
            arguments.append(f"--witness={subject.witness}")
        result = self.run(arguments, name=f"{subject.name}:prove")
        producer = json.loads(result.stdout)
        proof = (output / "proof.bin").read_bytes()
        binding = proof[8:HEADER]
        self.check(f"{subject.name}:proof-binding", binding.hex() == producer["execution"]["binding_sha256"])
        cases, observed, codes = [], [], {}
        for budget in range(0, subject.threshold + 2):
            exit_code, report = self.verify(subject, package, pin, proof, f"budget-{budget}", instructions=budget)
            cases.append((budget, proof, [], []))
            observed.append((f"budget-{budget}", self.observed(exit_code, report)))
        for name, (bytes_, invalid, ones) in subject.scenarios(proof).items():
            exit_code, report = self.verify(subject, package, pin, bytes_, name)
            cases.append((1000000, bytes_, invalid, ones))
            observed.append((name, self.observed(exit_code, report)))
            codes[name] = (exit_code, report.get("code"))
        subject.runtime_only(self, codes)
        predicted = self.predictions(subject, artifacts, cases, binding)
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
            self.check(f"{subject.name}:runtime-agrees:{name}", same,
                       json.dumps(dict(runtime=actual, lean=expected)))
        accepted = [c["case"] for c in comparisons if c["runtime"]["outcome"] == "accepted"]
        expected = [f"budget-{subject.threshold}", f"budget-{subject.threshold + 1}", "honest"]
        self.check(f"{subject.name}:runtime-accepted-cases", accepted == expected, json.dumps(accepted))
        return dict(pin=pin, proof_sha256=digest(proof), binding=binding.hex(), comparisons=comparisons)

    # The receipt and its binding to the runtime.

    def receipt(self, subject, artifacts, runtime, axioms):
        deployment = artifacts["deployment"]
        return {
            "format": "zkc.verification-receipt/0",
            "entry": subject.entry,
            "subject": subject.name,
            "tools": {"compiler": digest(self.args.compiler.read_bytes()),
                      "native": digest(self.args.native.read_bytes()),
                      "lean_toolchain": (LEAN / "lean-toolchain").read_text().strip(),
                      "lake_manifests": {path: digest((ROOT / path).read_bytes()) for path in
                                         ["lean/lake-manifest.json",
                                          "lean/integrations/arklib/lake-manifest.json"]}},
            "artifacts": {
                "source_modules": {m.split("=")[0]: digest((ROOT / m.split("=")[1]).read_bytes())
                                   for m in subject.modules},
                "original": digest(artifacts["source"]),
                "original_export": digest(artifacts["original_text"].encode()),
                "constructed_export": digest(artifacts["export_text"].encode()),
                "constructed_candidate": artifacts["exported"][2],
                "program": digest(artifacts["program"]),
                "deployment": digest(artifacts["deployment_text"].encode()),
                "descriptor": deployment[3],
                "package": runtime["pin"],
            },
            "lean_data": {path: digest((ROOT / path).read_bytes()) for path in subject.lean_files},
            "runtime_selection": self.selected[subject.name],
            "rules": subject.rules_entry(),
            "theorem": subject.theorem,
            "axioms": {name: axioms[name] for name in subject.chain},
            "proof_dependencies": self.dependencies[subject.name],
            "assumptions": subject.assumptions,
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

    def binding(self, subject, artifacts, receipt):
        prefix = subject.name
        output = self.directory(subject)
        package = output / "package.zkpkg"
        named = json.loads(json.loads(package.read_bytes())["artifact"])[4].encode()
        self.check(f"{prefix}:receipt-program", digest(named) == receipt["artifacts"]["program"])
        self.check(f"{prefix}:receipt-package", digest(package.read_bytes()) == receipt["artifacts"]["package"])
        honest = (output / "proof.bin").read_bytes()
        wrong = subject.scenarios(honest)[subject.wrong_case][0]
        exit_code, report = self.verify(subject, package, receipt["artifacts"]["package"], honest, "receipt-honest")
        self.check(f"{prefix}:runtime-runs-receipt-package", exit_code == 0 and report.get("status") == "accepted"
                   and report.get("package_sha256") == receipt["artifacts"]["package"], json.dumps(report)[-400:])
        exit_code, report = self.verify(subject, package, receipt["artifacts"]["package"], wrong, "receipt-wrong")
        self.check(f"{prefix}:receipt-package-rejects-wrong-proof", exit_code != 0, json.dumps(report)[-400:])
        results = {}
        mutated, deployment = self.repackage(artifacts, subject.receipt_mutation)
        path = output / "package-mutated.zkpkg"
        path.write_bytes(mutated)
        exit_code, report = self.verify(subject, path, receipt["artifacts"]["package"], wrong, "mutated-same-pin")
        results["same-pin"] = report.get("code")
        self.check(f"{prefix}:runtime-refuses-other-package",
                   exit_code != 0 and report.get("code") == "entry-package-identity", json.dumps(report)[-400:])
        exit_code, report = self.verify(subject, path, digest(mutated), wrong, "mutated-repinned")
        results["repinned-wrong-proof"] = report.get("status")
        self.check(f"{prefix}:mutated-program-changes-acceptance",
                   exit_code == 0 and report.get("status") == "accepted", json.dumps(report)[-400:])
        mutated_program = deployment[4].encode()
        self.check(f"{prefix}:receipt-refuses-mutated-program",
                   digest(mutated_program) != receipt["artifacts"]["program"])
        stale, _ = self.repackage(artifacts, subject.receipt_mutation, keep_inner_digest=True)
        path = output / "package-stale-digest.zkpkg"
        path.write_bytes(stale)
        exit_code, report = self.verify(subject, path, digest(stale), honest, "stale-inner-digest")
        results["stale-inner-digest"] = report.get("code")
        self.check(f"{prefix}:runtime-refuses-stale-program-digest",
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
    parser.add_argument("--subject", action="append", choices=sorted(SUBJECTS),
                        help="check only the named subjects (default: all)")
    parser.add_argument("--write", action="store_true",
                        help="rewrite the committed program data from the fresh programs")
    args = parser.parse_args()
    args.output = args.output.resolve()
    args.compiler = args.compiler.resolve()
    args.native = args.native.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    if any(args.output.iterdir()):
        parser.error("--output must be a new or empty directory")
    subjects = [SUBJECTS[name] for name in (args.subject or SUBJECTS)]
    driver = Driver(args)
    report = dict(format="zkc.executable-check/0", started=now(), status="failed", subjects={})
    try:
        retained = {}
        for subject in subjects:
            artifacts = driver.compile(subject)
            driver.regenerate(subject, artifacts)
            refused = driver.lean_rule(subject, artifacts)
            runtime = driver.runtime(subject, artifacts)
            retained[subject.name] = (artifacts, runtime)
            report["subjects"][subject.name] = dict(entry=subject.entry, refused_mutations=refused,
                                                    runtime=runtime)
        axioms = driver.axioms(subjects)
        for subject in subjects:
            artifacts, runtime = retained[subject.name]
            receipt = driver.receipt(subject, artifacts, runtime, axioms)
            (driver.directory(subject) / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
            entry = report["subjects"][subject.name]
            entry["binding"] = driver.binding(subject, artifacts, receipt)
            entry["receipt"] = receipt
        report["status"] = "pass"
    except (RuntimeError, ValueError, KeyError, IndexError, StopIteration) as error:
        report["error"] = str(error)
    report.update(finished=now(), commands=driver.commands, checks=driver.checks)
    (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(dict(status=report["status"], checks=len(driver.checks), error=report.get("error"))))
    sys.exit(0 if report["status"] == "pass" else 1)


if __name__ == "__main__":
    main()
