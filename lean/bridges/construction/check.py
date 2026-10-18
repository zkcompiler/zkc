#!/usr/bin/env python3
"""Check compiled proof Entries' transcript construction and projection in Lean.

For each subject, the compiled `example::Proof` Entries of the Schnorr, Sumcheck,
composed Sumcheck and GKR examples and the compiled `example::AndProof` and
`example::EqualityProof` Entries of the Sigma example, the driver compiles the
Entry, retains its
original export, native policy, constructed candidate and exported validator
participant, and requires the committed Lean data to be their exact rendering.
It then runs the composed Lean check (transcript construction and participant
projection) on the fresh export, together with mutated exports that it must
refuse, checks that the Lean model of the occurrence encoding reproduces every
exported template's native bytes, and confirms that the native checker refuses
mutated candidates before export. This is bounded agreement evidence: native
exporter correctness and the primitive meanings remain stated boundaries.
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

    def __init__(self, name, modules, original, participant, module, imported, original_owned,
                 entry="example::Proof"):
        self.name = name
        self.entry = entry
        self.modules = modules
        self.original = original
        self.participant = participant
        self.module = module
        self.imported = imported
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
            "ZkcExamples.Construction.SchnorrProof", "ZkcExamples.Construction.SchnorrProof.imported", True),
    Subject("sumcheck", project_modules("examples/projects/sumcheck/zkc.toml"),
            (ROOT / "lean/ZkcExamples/Structured/SumcheckSourceData.lean",
             "ZkcExamples.Structured.SumcheckSourceData"),
            (DATA / "SumcheckProofParticipant.lean", "ZkcExamples.Construction.SumcheckProofParticipant"),
            "ZkcExamples.Construction.SumcheckProof", "ZkcExamples.Structured.SumcheckSourceViews.imported",
            False),
    Subject("composed-sumcheck", project_modules("examples/projects/sumcheck/composed/zkc.toml"),
            (DATA / "ComposedSumcheckProofData.lean", "ZkcExamples.Construction.ComposedSumcheckProofData"),
            (DATA / "ComposedSumcheckProofParticipant.lean",
             "ZkcExamples.Construction.ComposedSumcheckProofParticipant"),
            "ZkcExamples.Construction.ComposedSumcheckProof",
            "ZkcExamples.Construction.ComposedSumcheckProof.imported", True),
    Subject("schnorr-and", project_modules("examples/projects/sigma/zkc.toml"),
            (DATA / "SchnorrAndProofData.lean", "ZkcExamples.Construction.SchnorrAndProofData"),
            (DATA / "SchnorrAndProofParticipant.lean", "ZkcExamples.Construction.SchnorrAndProofParticipant"),
            "ZkcExamples.Construction.SchnorrAndProof", "ZkcExamples.Construction.SchnorrAndProof.imported", True,
            entry="example::AndProof"),
    Subject("chaum-pedersen", project_modules("examples/projects/sigma/zkc.toml"),
            (DATA / "ChaumPedersenProofData.lean", "ZkcExamples.Construction.ChaumPedersenProofData"),
            (DATA / "ChaumPedersenProofParticipant.lean",
             "ZkcExamples.Construction.ChaumPedersenProofParticipant"),
            "ZkcExamples.Construction.ChaumPedersenProof", "ZkcExamples.Construction.ChaumPedersenProof.imported",
            True, entry="example::EqualityProof"),
    Subject("gkr", project_modules("examples/projects/gkr/zkc.toml"),
            (ROOT / "lean/ZkcExamples/Structured/GkrSourceData.lean", "ZkcExamples.Structured.GkrSourceData"),
            (DATA / "GkrProofParticipant.lean", "ZkcExamples.Construction.GkrProofParticipant"),
            "ZkcExamples.Construction.GkrProof", "ZkcExamples.Structured.GkrSourceViews.imported", True),
]
SIGMA = {"schnorr-and", "chaum-pedersen"}


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

        def template_tree(item):
            return constructed.decode_tree(bytes.fromhex(dict(item[1])["parameters"][1][0]))[0]

        def challenge_names_delivery(instructions):
            # The delivery's local site, in the challenge's own protocol: its
            # application path then qualifies it to the selected delivery site.
            delivery = next(item for item in nested(instructions)
                            if item[0] == "crypto.exec.indexed_transcript_observe_data"
                            and template_tree(item)[4][4] == exported[3][3])
            challenge = instruction(instructions, "crypto.exec.indexed_transcript_challenge")
            parameters = dict(challenge[1])["parameters"][1]
            tree, _ = constructed.decode_tree(bytes.fromhex(parameters[0]))
            tree[4][2] = template_tree(delivery)[4][2]
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

        def conjunction_reads_left_twice(instructions):
            conjunction = instruction(instructions, "arith.andi")
            conjunction[3][:] = [conjunction[3][0], conjunction[3][0]]

        def right_check_reads_left_reduction(instructions):
            checks = [item for item in instructions if item[0] == "local.call" and len(item[3]) == 3]
            checks[1][3][1:] = checks[0][3][1:]

        def regions(instructions):
            """Each instruction list: the top level, then every region body in program order."""
            yield instructions
            for item in instructions:
                for region in item[5]:
                    yield from regions(region[1])

        def layer_loop(instructions):
            return [item for item in instructions if item[0] == "protocol.loop"][1]

        def first_round_check_dropped(instructions):
            # The first guard in program order is the first layer's first round check.
            body = next(region for region in regions(instructions)
                        if any(item[0] == "local.guard" for item in region))
            body.remove(next(item for item in body if item[0] == "local.guard"))

        def wiring_check_dropped(instructions):
            body = layer_loop(instructions)[5][0][1]
            body.remove(next(item for item in body if item[0] == "local.guard"))

        def round_claim_update_mutated(instructions):
            rounds = instruction(layer_loop(instructions)[5][0][1], "protocol.loop")[5][0][1]
            update = [item for item in rounds if item[0] == "algebra.field_add"][-1]
            update[3][:] = [update[3][0], update[3][0]]

        def stale_layer_claim_yielded(instructions):
            # As for Sumcheck: the layer loop's body starts after its environment,
            # then the layer index, the point and the claim.
            loop = layer_loop(instructions)
            position = next(index for index, item in enumerate(instructions) if item is loop)
            base = len(exported[5]) + sum(len(item[4]) for item in instructions[:position])
            loop[5][0][2][1] = base + 2

        def second_commitment_omitted(instructions):
            # The second observation absorbs the first commitment again.
            first = instruction(instructions, "crypto.exec.indexed_transcript_observe_data")
            second = instruction(instructions, "crypto.exec.indexed_transcript_observe_data", 1)
            second[3][1] = first[3][1]

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
        elif subject.name == "sumcheck":
            mutate("wrong-domain-separator", challenge_names_delivery)
            mutate("round-check-dropped", round_check_dropped)
            mutate("claim-update-mutated", claim_update_mutated)
            mutate("stale-claim-yielded", stale_claim_yielded)
            codes = {"wrong-domain-separator": "construction-challenge-site",
                     "round-check-dropped": "projection-guard",
                     "claim-update-mutated": "projection-unexplained",
                     "stale-claim-yielded": "projection-repeat-yield"}
            construction_accepts = {"round-check-dropped", "claim-update-mutated", "stale-claim-yielded"}
        elif subject.name == "gkr":
            mutate("wrong-domain-separator", challenge_names_delivery)
            mutate("round-check-dropped", first_round_check_dropped)
            mutate("wiring-check-dropped", wiring_check_dropped)
            mutate("claim-update-mutated", round_claim_update_mutated)
            mutate("stale-claim-yielded", stale_layer_claim_yielded)
            codes = {"wrong-domain-separator": "construction-challenge-site",
                     "round-check-dropped": "projection-guard",
                     "wiring-check-dropped": "projection-guard",
                     "claim-update-mutated": "projection-unexplained",
                     "stale-claim-yielded": "projection-repeat-yield"}
            construction_accepts = {"round-check-dropped", "wiring-check-dropped", "claim-update-mutated",
                                    "stale-claim-yielded"}
        elif subject.name in SIGMA:
            mutate("second-commitment-omitted", second_commitment_omitted)
            mutate("decision-compares-base-with-itself", decision_compares_base_with_itself)
            mutate("conjunction-reads-left-twice", conjunction_reads_left_twice)
            codes = {"second-commitment-omitted": "construction-observe",
                     "decision-compares-base-with-itself": "projection-unexplained",
                     "conjunction-reads-left-twice": "projection-unexplained"}
            construction_accepts = {"decision-compares-base-with-itself", "conjunction-reads-left-twice"}
        else:
            mutate("conjunction-reads-left-twice", conjunction_reads_left_twice)
            mutate("right-check-reads-left-reduction", right_check_reads_left_reduction)
            codes = {"conjunction-reads-left-twice": "projection-unexplained",
                     "right-check-reads-left-reduction": "projection-call"}
            construction_accepts = set(codes)

        # The Lean model of the canonical occurrence encoding must reproduce the
        # native bytes of every exported template, in program order.
        def templates(instructions):
            for item in nested(instructions):
                if item[0] in ("crypto.exec.indexed_transcript_observe_data",
                               "crypto.exec.indexed_transcript_challenge"):
                    yield list(bytes.fromhex(dict(item[1])["parameters"][1][0]))

        def body(text):
            """Drop the module header so several renderings share one check file."""
            return "\n".join(line for line in text.splitlines()
                             if line not in ("module", "@[expose] public section")
                             and not line.startswith("public import "))

        parts = [f"import {subject.module}", "import Zkc.Construction.Encoding", "set_option maxRecDepth 20000",
                 body(structured.render(original, "Fresh.Original")),
                 body(constructed.render(exported, "Fresh.Actual"))]
        # The original was admitted from the retained snapshot, which must be the
        # fresh one; its admission is then the fresh original's admission, and the
        # composed check runs on that admitted subject.
        imported = subject.imported
        encoded = json.dumps(list(templates(exported[7])))
        proofs = ["theorem original_retained : Fresh.Original.snapshot = "
                  f"{subject.original[1]}.snapshot := rfl",
                  "/-- The retained original's admission, for the fresh original. -/\n"
                  "def freshImported : Zkc.Source.Structured.Imported Fresh.Original.snapshot :=\n"
                  f"  ⟨{imported}.program, by rw [original_retained]; exact {imported}.admitted⟩",
                  "theorem templates_encoded : (Zkc.Construction.Instruction.templatesList "
                  "Fresh.Actual.participant.instructions).map (fun template => "
                  f"(Zkc.Construction.templateTree template).encode) = {encoded} := by decide +kernel",
                  "theorem actual_accepted : Zkc.Construction.checkCompiled freshImported "
                  "Fresh.Actual.participant = .ok () := by decide +kernel"]
        for index, (name, value) in enumerate(mutations.items()):
            namespace = f"Fresh.Mutation{index}"
            parts.append(body(constructed.render(value, namespace)))
            if name in construction_accepts:
                proofs.append(f"/-- {name} -/\ntheorem mutation{index}_construction_accepted : "
                              f"Zkc.Construction.checkExport Fresh.Original.snapshot {namespace}.participant "
                              "= .ok () := by decide +kernel")
            proofs.append(f"/-- {name} -/\ntheorem mutation{index}_refused : Zkc.Construction.checkCompiled "
                          f"freshImported {namespace}.participant = "
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

    def domain_separator_refusal(self, candidate, exported, prefix=""):
        """A candidate whose challenge template names the delivery site instead of
        the selected query site is refused natively; the mutation is generic."""
        challenge = next(item for item in exported[7]
                         if item[0] == "crypto.exec.indexed_transcript_challenge")
        hex_text = dict(challenge[1])["parameters"][1][0]
        tree, _ = constructed.decode_tree(bytes.fromhex(hex_text))
        tree[4][2] = exported[3][8][0][1]
        self.check(f"{prefix}native-origin-present", candidate.count(hex_text) == 1)
        return {"wrong-domain-separator": (candidate.replace(
            hex_text, constructed.encode_tree(tree).hex()), "native-proof-correspondence", "")}

    def native_refusals(self, subject, refusals, prefix=""):
        """Run the native checker on each mutated candidate; each must be refused
        with its named reason and diagnostic."""
        directory = self.output / subject.name
        reasons = {}
        for name, (text, code, detail) in refusals.items():
            path = directory / f"candidate-{name}.mlir"
            path.write_text(text)
            result = self.run([self.args.compiler, "protocol-constructed-participant",
                               directory / "source.mlir", directory / "policy.json", path],
                              expect=None, name=f"{prefix}native-refusal:{name}")
            reason = result.stderr.strip().splitlines()[-1] if result.stderr.strip() else ""
            self.check(f"{prefix}native-refusal:{name}", result.returncode != 0 and reason == code
                       and detail in result.stderr, result.stderr[-400:])
            reasons[name] = reason
        return reasons

    def native_refusal(self, subject, candidate, exported):
        """The native checker refuses mutated Schnorr candidates before any export."""
        lines = candidate.splitlines()
        calls = [i for i, line in enumerate(lines) if "local.call @_transcript_4(" in line]
        self.check("native-mutation-site", len(calls) == 2)
        # The second participant is the validator; its challenge reads its host transcript.
        prefix, rest = lines[calls[1]].split("local.call @_transcript_4(", 1)
        lines[calls[1]] = prefix + "local.call @_transcript_4(%arg2" + rest[rest.index(")"):]
        # Each mutation names the native refusal and diagnostic it must produce.
        refusals = {"challenge-before-commitment": ("\n".join(lines) + "\n", "native-proof-candidate",
                                                    "affine participant value reused")}
        refusals.update(self.domain_separator_refusal(candidate, exported))
        return self.native_refusals(subject, refusals)


    def native_helper_refusal(self, subject, candidate, exported):
        """The Lean rules read a helper call with the original's checked helper; the
        native checker must refuse a candidate whose prepared helper body differs."""
        directory = self.output / subject.name
        calls = [item for item in exported[7] if item[0] == "local.call"]
        callee = dict(calls[-1][1])["callee"][1]
        # The helper ends at the closing brace at its own indentation.
        lines = candidate.splitlines(keepends=True)
        first = next(index for index, line in enumerate(lines) if f"local.func @{callee}(" in line)
        indentation = lines[first][:len(lines[first]) - len(lines[first].lstrip())]
        last = next(index for index in range(first + 1, len(lines)) if lines[index].rstrip() == indentation + "}")
        body = "".join(lines[first:last + 1])
        constant = 'parameters = ["1"]'
        self.check(f"{subject.name}:native-helper-constant", body.count(constant) >= 1)
        mutated = ("".join(lines[:first]) + body.replace(constant, 'parameters = ["2"]', 1)
                   + "".join(lines[last + 1:]))
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
            elif subject.name in SIGMA:
                prefix = f"{subject.name}:"
                result["native_refusals"] = driver.native_refusals(
                    subject, driver.domain_separator_refusal(candidate, exported, prefix), prefix)
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
