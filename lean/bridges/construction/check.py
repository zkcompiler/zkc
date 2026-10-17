#!/usr/bin/env python3
"""Check compiled proof Entries' transcript construction and projection in Lean.

For each subject, the compiled Schnorr and Sumcheck `example::Proof` Entries,
the driver compiles the Entry, retains its original export, native policy,
constructed candidate and exported validator participant, and requires the
committed Lean data to be their exact rendering. It then runs the composed Lean
check (transcript construction and participant projection) on the fresh export,
together with mutated exports that it must refuse, and for Schnorr confirms that
the native checker refuses mutated candidates before export. This is bounded
agreement evidence: native exporter correctness and the primitive meanings
remain stated boundaries.
"""

import argparse
import copy
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
import render as constructed  # noqa: E402

# The structured renderer is appended after this directory, so no module of this
# bridge can be shadowed by a structured-bridge module of the same name.
sys.path.append(str(ROOT / "lean/bridges/structured"))
import snapshot as structured  # noqa: E402

sys.path.append(str(ROOT / "common/tests/support"))
from project import project_inputs  # noqa: E402

DATA = ROOT / "lean/ZkcExamples/Construction"


class Subject:
    """One compiled proof Entry and the Lean data and proofs that consume it.

    `original_owned` is false when another bridge owns the original's rendering;
    this driver then only compares it.
    """

    def __init__(self, name, modules, original, participant, module, program, original_owned):
        self.name = name
        self.entry = "example::Proof"
        self.modules = modules
        self.original = original
        self.participant = participant
        self.module = module
        self.program = program
        self.original_owned = original_owned


def project_modules(manifest):
    modules, assets = project_inputs(ROOT / manifest)
    if assets:
        raise ValueError(f"{manifest} has assets")
    return [f"{name}={source}" for name, source in sorted(modules.items())]


SUBJECTS = [
    Subject("schnorr", ["example=examples/projects/schnorr/main.zkc", "schnorr=libraries/schnorr/lib.zkc"],
            (DATA / "SchnorrProofData.lean", "ZkcExamples.Construction.SchnorrProofData"),
            (DATA / "SchnorrProofParticipant.lean", "ZkcExamples.Construction.SchnorrProofParticipant"),
            "ZkcExamples.Construction.SchnorrProof", "ZkcExamples.Construction.SchnorrProof.program", True),
    Subject("sumcheck", project_modules("examples/projects/sumcheck/zkc.toml"),
            (ROOT / "lean/ZkcExamples/Structured/SumcheckSourceData.lean",
             "ZkcExamples.Structured.SumcheckSourceData"),
            (DATA / "SumcheckProofParticipant.lean", "ZkcExamples.Construction.SumcheckProofParticipant"),
            "ZkcExamples.Construction.SumcheckProof", "ZkcExamples.Structured.SumcheckSourceViews.program",
            False),
]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


class Driver:
    def __init__(self, args):
        self.args = args
        self.output = args.output
        self.commands = []
        self.checks = []

    def run(self, arguments, *, cwd=ROOT, expect=0, name=None):
        started = now()
        result = subprocess.run([str(a) for a in arguments], cwd=cwd, capture_output=True,
                                text=True, check=False)
        self.commands.append(dict(name=name, arguments=[str(a) for a in arguments], cwd=str(cwd),
                                  exit=result.returncode, started=started, finished=now(),
                                  stdout_sha256=digest(result.stdout.encode()),
                                  stderr=result.stderr[-4000:]))
        if expect is not None and result.returncode != expect:
            raise RuntimeError(f"{name or arguments[0]} exited {result.returncode}: {result.stderr[-2000:]}")
        return result

    def compile(self, *arguments, name):
        return self.run([self.args.compiler, *arguments], name=name).stdout

    def check(self, name, passed, detail=""):
        self.checks.append(dict(name=name, passed=bool(passed), detail="" if passed else detail))
        if not passed:
            raise RuntimeError(f"check failed: {name} {detail}")

    def export(self, subject):
        directory = self.output / subject.name
        directory.mkdir()
        modules = [f"--module={module}" for module in subject.modules]
        common = ["--source-format=zkc", f"--entry={subject.entry}", *modules]
        source = self.compile("language-emit", *common, name=f"{subject.name}:emit").encode()
        (directory / "source.mlir").write_bytes(source)
        deployment = json.loads(self.compile("language-bundle", *common, name=f"{subject.name}:bundle"))
        self.check(f"{subject.name}:deployment-source", deployment[1] == digest(source))
        policy = deployment[2][1]
        (directory / "policy.json").write_text(json.dumps(policy))
        entry = policy[1]
        candidate = self.compile("protocol-construct-proof", directory / "source.mlir",
                                 directory / "policy.json", name=f"{subject.name}:construct")
        (directory / "candidate.mlir").write_text(candidate)
        exported = json.loads(self.compile(
            "protocol-constructed-participant", directory / "source.mlir",
            directory / "policy.json", directory / "candidate.mlir", name=f"{subject.name}:participant"))
        original = json.loads(self.compile("protocol-structured", directory / "source.mlir",
                                           f"--symbol={entry}", name=f"{subject.name}:original"))
        self.check(f"{subject.name}:participant-source", exported[1] == "sha256:" + digest(source))
        self.check(f"{subject.name}:participant-policy", exported[3] == policy)
        self.check(f"{subject.name}:original-source", original[2] == "sha256:" + digest(source))
        (directory / "participant.json").write_text(json.dumps(exported))
        (directory / "original.json").write_text(json.dumps(original))
        return source, policy, candidate, exported, original

    def compare(self, subject, original, exported):
        files = {
            subject.original[0]: (structured.render(original, subject.original[1]), subject.original_owned),
            subject.participant[0]: (constructed.render(exported, subject.participant[1]), True),
        }
        for path, (text, owned) in files.items():
            if self.args.write and owned:
                path.write_text(text, encoding="utf-8")
            current = path.read_text(encoding="utf-8") if path.exists() else None
            self.check(f"regenerated:{path.relative_to(ROOT)}", current == text,
                       "committed data differs from the fresh export")

    def lean_rule(self, subject, original, exported):
        """Run the composed Lean check on the fresh export and on mutated exports."""
        mutations = {}

        def mutate(name, change):
            value = copy.deepcopy(exported)
            change(value[7])
            mutations[name] = value

        def nested(instructions):
            for item in instructions:
                yield item
                for region in item[5]:
                    yield from nested(region[1])

        def instruction(instructions, operation, occurrence=0):
            matches = [item for item in nested(instructions) if item[0] == operation]
            return matches[occurrence]

        def first_observation_reads_base(instructions):
            instruction(instructions, "crypto.exec.indexed_transcript_observe_data")[3][1] = 0

        def challenge_reads_host_transcript(instructions):
            observed = instruction(instructions, "crypto.exec.indexed_transcript_challenge")
            observed[3][0] = len(exported[5]) - 1

        def challenge_names_delivery(instructions):
            challenge = instruction(instructions, "crypto.exec.indexed_transcript_challenge")
            parameters = dict(challenge[1])["parameters"][1]
            tree, _ = constructed.decode_tree(bytes.fromhex(parameters[0]))
            tree[4][2] = exported[3][8][0][1]
            parameters[0] = constructed.encode_tree(tree).hex()

        def decision_compares_base_with_itself(instructions):
            instruction(instructions, "algebra.group_equal")[3][:] = [0, 0]

        def loop_body(instructions):
            return instruction(instructions, "protocol.loop")[5][0][1]

        def round_check_dropped(instructions):
            body = loop_body(instructions)
            body.remove(instruction(body, "local.guard"))

        def claim_update_mutated(instructions):
            body = loop_body(instructions)
            update = [item for item in body if item[0] == "algebra.field_add"][-1]
            update[3][:] = [update[3][0], update[3][0]]

        def stale_claim_yielded(instructions):
            # The body's references start after the loop's environment: the
            # inputs and the results of the top-level instructions before it,
            # then the induction index and the carried values.
            loop = instruction(instructions, "protocol.loop")
            position = next(index for index, item in enumerate(instructions) if item is loop)
            base = len(exported[5]) + sum(len(item[4]) for item in instructions[:position])
            loop[5][0][2][1] = base + 2

        # Each mutation is refused for the obligation it violates. Those that keep
        # the transcript wiring are accepted by the construction rule alone.
        if subject.name == "schnorr":
            mutate("commitment-omitted", first_observation_reads_base)
            mutate("challenge-before-commitment", challenge_reads_host_transcript)
            mutate("wrong-domain-separator", challenge_names_delivery)
            mutate("decision-compares-base-with-itself", decision_compares_base_with_itself)
            codes = {"commitment-omitted": "construction-observe",
                     "challenge-before-commitment": "construction-challenge",
                     "wrong-domain-separator": "construction-challenge-site",
                     "decision-compares-base-with-itself": "projection-unexplained"}
            construction_accepts = {"decision-compares-base-with-itself"}
        else:
            mutate("wrong-domain-separator", challenge_names_delivery)
            mutate("round-check-dropped", round_check_dropped)
            mutate("claim-update-mutated", claim_update_mutated)
            mutate("stale-claim-yielded", stale_claim_yielded)
            codes = {"wrong-domain-separator": "construction-challenge-site",
                     "round-check-dropped": "projection-guard",
                     "claim-update-mutated": "projection-unexplained",
                     "stale-claim-yielded": "projection-repeat-yield"}
            construction_accepts = {"round-check-dropped", "claim-update-mutated", "stale-claim-yielded"}

        def body(text):
            """Drop the module header so several renderings share one check file."""
            return "\n".join(line for line in text.splitlines()
                             if line not in ("module", "@[expose] public section")
                             and not line.startswith("public import "))

        parts = [f"import {subject.module}", "set_option maxRecDepth 20000",
                 body(structured.render(original, "Fresh.Original")),
                 body(constructed.render(exported, "Fresh.Actual"))]
        # The admitted original program was checked from the retained snapshot,
        # which must be the fresh one.
        program = subject.program
        proofs = ["theorem original_retained : Fresh.Original.snapshot = "
                  f"{subject.original[1]}.snapshot := rfl",
                  "theorem actual_accepted : Zkc.Construction.checkCompiled Fresh.Original.snapshot "
                  f"{program} Fresh.Actual.participant = .ok () := by decide +kernel"]
        for index, (name, value) in enumerate(mutations.items()):
            namespace = f"Fresh.Mutation{index}"
            parts.append(body(constructed.render(value, namespace)))
            if name in construction_accepts:
                proofs.append(f"/-- {name} -/\ntheorem mutation{index}_construction_accepted : "
                              f"Zkc.Construction.checkExport Fresh.Original.snapshot {namespace}.participant "
                              "= .ok () := by decide +kernel")
            proofs.append(f"/-- {name} -/\ntheorem mutation{index}_refused : Zkc.Construction.checkCompiled "
                          f"Fresh.Original.snapshot {program} {namespace}.participant = "
                          f".error \"{codes[name]}\" := by decide +kernel")
        proofs.append("#print axioms actual_accepted")
        source = "\n\n".join(parts + proofs) + "\n"
        path = self.output / subject.name / "FreshExport.lean"
        path.write_text(source, encoding="utf-8")
        result = self.run([self.args.lake, "env", "lean", path], cwd=ROOT / "lean",
                          name=f"{subject.name}:lean-rule")
        marker = "'actual_accepted' depends on axioms: ["
        axioms = result.stdout.split(marker, 1)[1].split("]", 1)[0] if marker in result.stdout else None
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        self.check(f"{subject.name}:lean-rule", axioms is not None
                   and {name.strip() for name in axioms.split(",") if name.strip()} <= allowed,
                   result.stdout[-400:])
        return list(mutations)

    def native_refusal(self, subject, candidate, exported):
        """The native checker refuses mutated Schnorr candidates before any export."""
        directory = self.output / subject.name
        lines = candidate.splitlines()
        calls = [i for i, line in enumerate(lines) if "local.call @_transcript_4(" in line]
        self.check("native-mutation-site", len(calls) == 2)
        # The second participant is the validator; its challenge reads its host transcript.
        prefix, rest = lines[calls[1]].split("local.call @_transcript_4(", 1)
        lines[calls[1]] = prefix + "local.call @_transcript_4(%arg2" + rest[rest.index(")"):]
        # Each mutation names the native refusal and diagnostic it must produce.
        refusals = {"challenge-before-commitment": ("\n".join(lines) + "\n", "native-proof-candidate",
                                                    "affine participant value reused")}

        challenge = next(item for item in exported[7]
                         if item[0] == "crypto.exec.indexed_transcript_challenge")
        hex_text = dict(challenge[1])["parameters"][1][0]
        tree, _ = constructed.decode_tree(bytes.fromhex(hex_text))
        tree[4][2] = exported[3][8][0][1]
        self.check("native-origin-present", candidate.count(hex_text) == 1)
        refusals["wrong-domain-separator"] = (candidate.replace(
            hex_text, constructed.encode_tree(tree).hex()), "native-proof-correspondence", "")

        reasons = {}
        for name, (text, code, detail) in refusals.items():
            path = directory / f"candidate-{name}.mlir"
            path.write_text(text)
            result = self.run([self.args.compiler, "protocol-constructed-participant",
                               directory / "source.mlir", directory / "policy.json", path],
                              expect=None, name=f"native-refusal:{name}")
            reason = result.stderr.strip().splitlines()[-1] if result.stderr.strip() else ""
            self.check(f"native-refusal:{name}", result.returncode != 0 and reason == code
                       and detail in result.stderr, result.stderr[-400:])
            reasons[name] = reason
        return reasons


    def native_helper_refusal(self, subject, candidate, exported):
        """The Lean rules read a helper call with the original's checked helper; the
        native checker must refuse a candidate whose prepared helper body differs."""
        directory = self.output / subject.name
        callee = dict(exported[7][-1][1])["callee"][1]
        start = candidate.index(f"local.func @{callee}(")
        end = candidate.index("local.func", start + 1)
        body = candidate[start:end]
        constant = 'parameters = ["1"]'
        self.check(f"{subject.name}:native-helper-constant", body.count(constant) >= 1)
        mutated = candidate[:start] + body.replace(constant, 'parameters = ["2"]', 1) + candidate[end:]
        path = directory / "candidate-terminal-helper-mutated.mlir"
        path.write_text(mutated)
        result = self.run([self.args.compiler, "protocol-constructed-participant",
                           directory / "source.mlir", directory / "policy.json", path],
                          expect=None, name=f"{subject.name}:native-refusal:terminal-helper-mutated")
        reason = result.stderr.strip().splitlines()[-1] if result.stderr.strip() else ""
        self.check(f"{subject.name}:native-refusal:terminal-helper-mutated",
                   result.returncode != 0 and reason == "native-proof-correspondence", result.stderr[-400:])
        return {"terminal-helper-mutated": reason}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "build/compiler/zkc-compile")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--output", type=Path, required=True, help="new or empty evidence directory")
    parser.add_argument("--write", action="store_true",
                        help="rewrite the committed Lean data from the fresh export")
    args = parser.parse_args()
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    if any(args.output.iterdir()):
        parser.error("--output must be a new or empty directory")
    driver = Driver(args)
    report = dict(format="zkc.construction-check/0", started=now(), status="failed", subjects={})
    try:
        for subject in SUBJECTS:
            source, policy, candidate, exported, original = driver.export(subject)
            result = dict(entry=subject.entry, source_sha256=digest(source), policy=policy,
                          candidate_sha256=digest(candidate.encode()),
                          participant_sha256=digest(json.dumps(exported).encode()))
            report["subjects"][subject.name] = result
            driver.compare(subject, original, exported)
            result["refused_mutations"] = driver.lean_rule(subject, original, exported)
            if subject.name == "schnorr":
                result["native_refusals"] = driver.native_refusal(subject, candidate, exported)
            else:
                result["native_refusals"] = driver.native_helper_refusal(subject, candidate, exported)
        report["status"] = "pass"
    except (RuntimeError, ValueError, KeyError, IndexError) as error:
        report["error"] = str(error)
    report.update(finished=now(), commands=driver.commands, checks=driver.checks)
    (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(dict(status=report["status"], checks=len(driver.checks),
                          error=report.get("error"))))
    sys.exit(0 if report["status"] == "pass" else 1)


if __name__ == "__main__":
    main()
