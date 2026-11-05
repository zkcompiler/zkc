"""Validate the ordinary library-backed BLS G1 Schnorr proof consumer.

Only the native fixture driver produces proofs. Independent Python affine and
hash-chain references check the original equation, every reached hash and the
complete physical ModExp/ADD/MSM sequence, including failed admission calls. The
unmodified compiler/solc artifact is deployed once per case and called twice.
SDK/CLI capture is a separate gate.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "common/tests/support"))

from abi import encode_verify  # noqa: E402
from curve_controls import G, P, R, compressed, frame, scalar_frame, scale  # noqa: E402
from curve_physical import check_physical_execution, group_add, modexp, msm, mutation_controls  # noqa: E402
from foundation_controls import Subjects, check_native_outcome, invocation_root, static_trace  # noqa: E402
from hash_chain_reference import BLS_SUITE, Chain, fr64be  # noqa: E402
from logical_tree import decode_tree, encode_tree  # noqa: E402
from mutant import omit_final_observation  # noqa: E402
from oracle import chain_trace, check_trace  # noqa: E402
from probe import check_solc, compile_request, execute  # noqa: E402
from project import project_inputs  # noqa: E402
from source_modules import library_modules  # noqa: E402
from validate import check_return, check_revert, removed_final_hash_control  # noqa: E402
import target  # noqa: E402

PROJECT = ROOT / "examples/projects/schnorr-bls-keccak"


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def sha(data):
    return hashlib.sha256(data).hexdigest()


class Stop(Exception):
    def __init__(self, native, code, frontier):
        self.native, self.revert, self.frontier = native, ("decode", code), frontier


def decode(wire, kind, physical=None, hash_frontier=0):
    """Independent exact native leaf admission, including subgroup membership."""
    width, tag = (54, 9) if kind == "group" else (38, 1)
    if len(wire) != width:
        raise Stop("artifact-stopped:Decode(Length)", 2, "wire-length")
    if wire[:6] != b"ZKCV\x00" + bytes([tag]):
        raise Stop("artifact-stopped:Decode(Header)", 3, "wire-header")
    if kind == "scalar":
        value = int.from_bytes(wire[6:], "little")
        if value >= R:
            raise Stop("artifact-stopped:Decode(Scalar)", 4, "scalar-canonicality")
        return value
    payload = wire[6:]
    flags = payload[0] & 0xe0
    x = int.from_bytes(bytes([payload[0] & 0x1f]) + payload[1:], "big")
    bad = Stop("artifact-stopped:Decode(Group)", 4, "group-admission")
    if not flags & 0x80 or x >= P:
        raise bad
    if flags & 0x40:
        if flags != 0xc0 or x:
            raise bad
        return None
    rhs = (modexp(physical, x, 3, hash_frontier) + 4) % P
    y = modexp(physical, rhs, (P + 1) // 4, hash_frontier)
    if modexp(physical, y, 2, hash_frontier) != rhs:
        raise bad
    if bool(flags & 0x20) != (y > (-y) % P):
        y = (-y) % P
    point = (x, y)
    if compressed(point) != payload:
        raise bad
    subgroup_valid = scale(point, R) is None
    msm(physical, point, 1, hash_frontier, subgroup_valid=subgroup_valid)
    if not subgroup_valid:
        raise bad
    return point


def replay(fixture):
    """Original Schnorr equation, proof consumption, and exact stop/hash frontier.

    Inputs are the checked source descriptor, public frames and native proof;
    neither emitted Yul nor observed EVM outcomes supply expected behavior.
    """
    descriptor = fixture["descriptor"]
    events = descriptor[3]
    if descriptor[1][5] != BLS_SUITE or [r[0] for r in events] != [
            "message", "query", "message", "message"]:
        raise AssertionError("expected the library's static managed Schnorr schedule")
    producer, verifier = descriptor[1][2:4]
    templates = [decode_tree(bytes.fromhex(r[1])) for r in events]
    directions = [[producer, verifier], [verifier, producer], [producer, verifier]]
    for row, direction in zip((templates[0], templates[2], templates[3]), directions, strict=True):
        if row[4][4:] != direction:
            raise AssertionError("source communication direction changed")
    if templates[1][4][4:] != ["random.bls12-381.fr/0", "draw", verifier]:
        raise AssertionError("unexpected source challenge")
    if any(t[0] != "zkc.native-origin-template/0" or t[3] for t in templates):
        raise AssertionError("expected static source occurrences")
    if len(fixture["public"]) != 2:
        raise AssertionError("expected the library's public base and point")
    root = invocation_root(fixture)
    digest = hashlib.sha256(root).digest()
    proof = bytes.fromhex(fixture["proof"])
    cursor, transitions = 40, 0
    trace, frames, physical, chain = [], [], [], None
    challenge, commitment, response, left, right = None, None, None, None, None
    decision, stop, frontier = None, None, "proof-header"

    def origin(index):
        t = templates[index]
        return encode_tree(["zkc.native-origin/0", t[1], t[2], [], t[4]])

    def observe(index, wire):
        nonlocal transitions
        chain.absorb(b"origin", origin(index))
        chain.absorb(b"value", wire)
        transitions += 1

    def receive(name, kind):
        nonlocal cursor, frontier
        frontier = name
        start = cursor
        if cursor + 8 > len(proof):
            raise Stop("proof-truncated", 5, "frame-length")
        length = int.from_bytes(proof[cursor:cursor + 8], "little")
        cursor += 8
        if length > len(proof) - cursor:
            raise Stop("proof-truncated", 5, "frame-payload")
        wire = proof[cursor:cursor + length]
        cursor += length
        frames.append({"name": name, "start": start, "end": cursor, "wire": wire.hex()})
        return wire, decode(wire, kind, physical, len(trace) + len(chain.calls))

    try:
        # The endpoint fully decodes public values in declaration order before
        # checking the proof header or hashing its invocation binding.
        for index, wire in enumerate(fixture["public"]):
            frontier = f"public-{index}"
            value = decode(bytes.fromhex(wire), "group", physical, 0)
            if index == 0:
                base = value
            else:
                point = value
        frontier = "proof-header"
        if len(proof) < 40:
            raise Stop("proof-truncated", 11, "proof-header-length")
        if proof[:8] != b"ZKCPRF00":
            raise Stop("proof-header", 11, "proof-header-magic")
        trace.append({"kind": "sha256", "input": root.hex(), "output": digest.hex(), "status": "return"})
        if proof[8:40] != digest:
            raise Stop("proof-header", 12, "proof-binding")
        chain = Chain(BLS_SUITE, root)
        wire, commitment = receive("commitment", "group")
        observe(0, wire)
        chain.absorb(b"origin", origin(1))
        challenge = fr64be(chain.request(b"challenge", 64))
        transitions += 1
        observe(2, scalar_frame(challenge))
        wire, response = receive("response", "scalar")
        observe(3, wire)
        frontier = "complete-equation/proof-end"
        hash_frontier = len(trace) + len(chain.calls)
        left = msm(physical, base, response, hash_frontier)
        product = msm(physical, point, challenge, hash_frontier)
        right = group_add(physical, commitment, product, hash_frontier)
        decision = left == right
        if cursor != len(proof):
            raise Stop("proof-trailing", 13, "complete-equation/proof-end")
    except Stop as error:
        stop, decision = error, None
        frontier = (frontier + "/" + error.frontier
                    if frontier in ("public-0", "public-1", "commitment", "response") else error.frontier)
    if chain is not None:
        trace += chain_trace(chain)
    if stop is None:
        check_trace(trace, static_trace(fixture))
    return {"trace": trace, "precompile_trace": physical, "decision": decision,
            "native_error": stop.native if stop else None, "revert": stop.revert if stop else None,
            "frontier": frontier, "transitions": transitions, "frames": frames,
            "challenge": challenge, "response": response,
            "commitment": frame(commitment).hex() if chain is not None and transitions else None,
            "equation_left": frame(left).hex() if response is not None else None,
            "equation_right": frame(right).hex() if response is not None else None,
            "binding_sha256": digest.hex(), "proof_sha256": sha(proof), "proof_bytes": len(proof)}


class Controls(Subjects):
    def compile(self, fork):
        flags = library_modules("protocols/sigma/schnorr")
        subject = super().compile(fork, (PROJECT / "main.zkc").read_text(), "example", flags,
                                  evm_flags=(f"--evm-version={fork}",))
        path, envelope, compiled, artifact = subject
        if compiled["limits"] != target.LIMITS:
            raise AssertionError("consumer must retain all declared default limits")
        if envelope[1] != compiled["original"] or envelope[2] != compiled["descriptor"]:
            raise AssertionError("native/target original source or descriptor differs")
        save(path / "solc.json", artifact)
        (path / "verifier.yul").write_text(compiled["yul"])
        for kind in ("creation", "runtime"):
            (path / f"{kind}.bin").write_bytes(bytes.fromhex(artifact[kind]))
        save(path / "identities.json", {
            "original": compiled["original"], "descriptor_sha256": sha(encode_tree(compiled["descriptor"])),
            "native_package_sha256": sha((path / "native.json").read_bytes()),
            "declaration": compiled["declaration"], "installation": compiled["installation"],
            "compiler": compiled["compiler"], "capture": compiled["capture"],
            "fork": fork, "limits": compiled["limits"],
            **{f"{kind}_sha256": sha(bytes.fromhex(artifact[kind])) for kind in ("creation", "runtime")},
            "runtime_bytes": len(artifact["runtime"]) // 2, "creation_bytes": len(artifact["creation"]) // 2})
        return subject

    def native(self, subject, name, base, point, secret, *, proof=None, context=b"curve-consumer"):
        path, envelope, compiled, _ = subject
        descriptor, policy = envelope[2], envelope[2][1]
        wires = {0: frame(base), 1: frame(point), 2: scalar_frame(secret)}

        def request(role):
            mapping = next(row for row in envelope[6] if row[0] == role)
            return ["zkc.native-proof-inputs/0",
                    [[*row[:2], wires[int(row[1])].hex()] for row in descriptor[4]],
                    [[row[0], ["wire", wires[int(row[0])].hex()]] for row in mapping[2]],
                    context.hex(), [[row[0], "64"] for row in mapping[4]], "64"]

        requests = path / f"{name}.inputs.json"
        save(requests, {"prover": request(policy[2]), "verifier": request(policy[3])})
        command = [str(self.args.native_driver), str(path / "native.json"), str(requests)]
        if proof is None and self.args.retained_native is not None:
            retained_path = self.args.retained_native / f"{name}.native.json"
            retained_inputs = self.args.retained_native / f"{name}.inputs.json"
            retained = json.loads(retained_path.read_text())
            if (retained["producer"] is None
                    or json.loads(retained_inputs.read_text()) != json.loads(requests.read_text())
                    or retained["source"] != compiled["original"] or retained["descriptor"] != descriptor
                    or retained["public"] != [wires[int(r[1])].hex() for r in descriptor[4]]
                    or retained["context"] != context.hex()
                    or retained["package_sha256"] != sha((path / "native.json").read_bytes())):
                raise AssertionError(f"{name}: retained producer subject or inputs differ")
            proof = bytes.fromhex(retained["proof"])
            save(path / f"{name}.retained-native.json", {
                "fixture": str(retained_path), "fixture_sha256": sha(retained_path.read_bytes()),
                "inputs": str(retained_inputs), "inputs_sha256": sha(retained_inputs.read_bytes()),
                "proof_sha256": sha(proof),
                "scope": "retained native producer proof; native verification rerun with supplied bytes"})
        if proof is not None:
            supplied = path / f"{name}.supplied.proof"
            supplied.write_bytes(proof)
            command.append(str(supplied))
        process = subprocess.run(command, text=True, capture_output=True, timeout=90)
        (path / f"{name}.native.stderr").write_text(process.stderr)
        if process.returncode:
            raise AssertionError(f"{name} native driver: {process.stderr}")
        fixture = json.loads(process.stdout)
        save(path / f"{name}.native.json", fixture)
        (path / f"{name}.proof").write_bytes(bytes.fromhex(fixture["proof"]))
        if (fixture["source"] != compiled["original"] or fixture["descriptor"] != descriptor
                or fixture["public"] != [wires[int(r[1])].hex() for r in descriptor[4]]
                or fixture["context"] != context.hex()
                or fixture["package_sha256"] != sha((path / "native.json").read_bytes())):
            raise AssertionError("native fixture changed its captured subject or invocation")
        if proof is not None and fixture["proof"] != proof.hex():
            raise AssertionError("native verifier changed supplied proof bytes")
        return fixture

    def check(self, subject, name, fixture, decision, native_error=None, revert=None):
        path, envelope, compiled, artifact = subject
        if fixture["source"] != compiled["original"] or fixture["descriptor"] != envelope[2]:
            raise AssertionError("fixture does not belong to the selected target source")
        expected = replay(fixture)
        save(path / f"{name}.expected.json", expected)
        if (expected["decision"] is not decision or expected["native_error"] != native_error
                or expected["revert"] != revert):
            raise AssertionError(f"{name}: independent original outcome differs from explicit case expectation")
        check_native_outcome(fixture, decision, native_error)
        published = {"0": "5a4b4356000501"} if decision is True else {}
        if fixture["outputs"] != published:
            raise AssertionError("native output publication differs from its decision")
        resources = [r for r in fixture["native"]["resources"] if r.get("stage") == "transcript"]
        if (len(resources) != 1 or resources[0]["transitions"] != expected["transitions"]
                or resources[0]["generation"] != expected["transitions"]
                or resources[0]["budget"] != 64 - expected["transitions"]
                or fixture["native"]["messages"] != len(expected["frames"])
                or fixture["native"]["binding_sha256"] != expected["binding_sha256"]):
            raise AssertionError("native transcript transition frontier differs")
        if native_error and native_error.startswith("artifact-stopped:"):
            failed_frame = expected["frontier"].split("/")[0]
            event = 0 if failed_frame == "commitment" else 3
            template = decode_tree(bytes.fromhex(envelope[2][3][event][1]))
            native_stop = fixture["native"]["stop"]
            if (native_stop["kind"] != native_error.split(":", 1)[1]
                    or native_stop["role"] != envelope[2][1][3]
                    or native_stop["site"] != template[4][2]):
                raise AssertionError(f"native stop moved from source event {event}")
        calldata = encode_verify(list(map(bytes.fromhex, fixture["public"])),
                                 bytes.fromhex(fixture["context"]), bytes.fromhex(fixture["proof"]))
        (path / f"{name}.calldata").write_bytes(calldata)
        execution = execute(self.args.runner, artifact, calldata, repeat_count=2)
        save(path / f"{name}.evm.json", execution)
        if (execution["fork"] != compiled["fork"]
                or execution["runtime_bytecode"].removeprefix("0x") != artifact["runtime"]
                or execution["code_size"] != len(artifact["runtime"]) // 2
                or len(execution["calls"]) != 2):
            raise AssertionError("deployed code, fork or invocation count differs")
        check_physical_execution(execution, expected["precompile_trace"])
        for nonce, call in enumerate(execution["calls"], 1):
            if call["nonce"] != nonce or call["address"] != execution["address"]:
                raise AssertionError("expected consecutive calls to the same installed contract")
            if (call["memory_high_water"] > compiled["limits"]["memory_bytes"]
                    or call["gas_used"] > target.transaction_gas(compiled["fork"])):
                raise AssertionError("execution exceeded its declared resource limits")
            result = execution | call
            if revert:
                check_revert(result, *revert, expected["trace"])
            else:
                check_return(result, int(decision).to_bytes(32, "big").hex(), expected["trace"])
        self.cases.append({"case": name, "fork": compiled["fork"], "decision": decision,
                           "native_error": fixture["native_error"], "revert": revert,
                           "frontier": expected["frontier"], "hashes": len(expected["trace"]),
                           "physical_precompiles": len(expected["precompile_trace"]),
                           "transitions": expected["transitions"], "proof_sha256": expected["proof_sha256"],
                           "creation_sha256": sha(bytes.fromhex(artifact["creation"])),
                           "runtime_sha256": sha(bytes.fromhex(artifact["runtime"])),
                           "runtime_bytes": execution["code_size"], "deployment_gas": execution["deployment_gas"],
                           "gas": [c["gas_used"] for c in execution["calls"]],
                           "memory_high_water": [c["memory_high_water"] for c in execution["calls"]]})
        return expected, execution


def replace_frame(proof, span, wire):
    return proof[:span["start"]] + len(wire).to_bytes(8, "little") + wire + proof[span["end"]:]


def malformed(proof, expected):
    spans = {s["name"]: s for s in expected["frames"]}
    yield "trailing", proof + b"\x00", "proof-trailing", ("decode", 13)
    for name, span in spans.items():
        for suffix, cut in (("length", span["start"] + 7), ("payload", span["end"] - 1)):
            yield f"truncated-{name}-{suffix}", proof[:cut], "proof-truncated", ("decode", 5)
        wire = bytes.fromhex(span["wire"])
        for label, changed, error, code in (
                ("short", wire[:-1], "Length", 2), ("extra", wire + b"\x00", "Length", 2),
                ("tag", wire[:5] + b"\xff" + wire[6:], "Header", 3)):
            yield f"{name}-{label}", replace_frame(proof, span, changed), f"artifact-stopped:Decode({error})", ("decode", code)
    group = spans["commitment"]
    payload = bytes.fromhex(group["wire"])[6:]
    nonsquare = next(x for x in range(1, 100) if pow((x**3 + 4) % P, (P - 1) // 2, P) == P - 1)
    for name, value in {
            "uncompressed": bytes([payload[0] & 0x7f]) + payload[1:],
            "infinity-sign": b"\xe0" + bytes(47),
            "infinity-payload": b"\xc0" + bytes(46) + b"\x01",
            "x-modulus": bytes([0x80 | (P >> 376)]) + P.to_bytes(48, "big")[1:],
            "x-all-bits": b"\x9f" + b"\xff" * 47,
            "nonsquare": bytes([0x80 | (nonsquare >> 376)]) + nonsquare.to_bytes(48, "big")[1:],
            "outside-subgroup": b"\x80" + bytes(47),
    }.items():
        changed = replace_frame(proof, group, b"ZKCV\x00\x09" + value)
        yield f"commitment-{name}", changed, "artifact-stopped:Decode(Group)", ("decode", 4)
        if name == "outside-subgroup":
            # An invalid response beyond this earlier point cannot mask it.
            bad = spans["response"]
            yield "group-before-bad-response", replace_frame(changed, bad, scalar_frame(R)), \
                "artifact-stopped:Decode(Group)", ("decode", 4)
    for scalar in (R, 2**256 - 1):
        yield f"response-noncanonical-{scalar}", replace_frame(proof, spans["response"], scalar_frame(scalar)), \
            "artifact-stopped:Decode(Scalar)", ("decode", 4)
    yield "short-proof-header", proof[:39], "proof-truncated", ("decode", 11)
    yield "bad-proof-magic", b"X" + proof[1:], "proof-header", ("decode", 11)
    yield "bad-proof-binding", proof[:8] + bytes([proof[8] ^ 1]) + proof[9:], "proof-header", ("decode", 12)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("compiler", "native-driver", "solc", "runner", "output"):
        parser.add_argument(f"--{name}", required=True, type=Path)
    parser.add_argument("--retained-native", type=Path,
                        help="reuse producer proofs from a prior fork directory; rerun native verification")
    args = parser.parse_args()
    for name in ("compiler", "native_driver", "solc", "runner", "output"):
        setattr(args, name, getattr(args, name).resolve())
    if args.retained_native is not None:
        args.retained_native = args.retained_native.resolve()
    # A result directory is immutable evidence; never overwrite an earlier run.
    args.output.mkdir(parents=True, exist_ok=False)
    save(args.output / "run.json", {"status": "running", "command": sys.argv})
    version = check_solc(args.solc)
    modules, assets = project_inputs(PROJECT / "zkc.toml")
    if assets:
        raise AssertionError("unexpected application assets")
    tools = {
        "command": sys.argv, "solc_version": version, "target_declaration": target.IDENTITY,
        "retained_native": str(args.retained_native) if args.retained_native else None,
        "tools": {name: {"path": str(getattr(args, name)), "sha256": sha(getattr(args, name).read_bytes())}
                  for name in ("compiler", "native_driver", "solc", "runner")},
        "modules": {name: {"path": str(p), "sha256": sha(p.read_bytes())} for name, p in modules.items()}}
    save(args.output / "tools.json", tools)
    public = json.loads((PROJECT / "inputs/example.Proof/public.json").read_text())
    witness = json.loads((PROJECT / "inputs/example.Proof/witness.json").read_text())
    if (public != {"base": {"bytes": compressed(G).hex()}, "point": {"bytes": compressed(scale(G, 3)).hex()}}
            or witness != {"scalar": "3"}):
        raise AssertionError("maintained example inputs changed; review the baseline case")
    controls = Controls(args)
    subjects = [controls.compile(fork) for fork in ("prague", "osaka")]
    if subjects[0][1][1:3] != subjects[1][1][1:3]:
        raise AssertionError("fork selection changed original source/descriptor")
    subject = subjects[0]
    baseline, reference = None, None
    signs = set()

    def check(name, fixture, decision, error=None, revert=None):
        results = [controls.check(s, name, fixture, decision, error, revert) for s in subjects]
        save(args.output / "summary.json", controls.cases)
        return results[0][0]

    cases = [("generator-secret-3", G, scale(G, 3), 3, True),
             ("base-2-secret-7", scale(G, 2), scale(G, 14), 7, True),
             ("base-17-secret-19", scale(G, 17), scale(G, 323), 19, True),
             ("negative-base", scale(G, R - 1), scale(G, R - 5), 5, True),
             ("negative-secret", G, scale(G, R - 1), R - 1, True),
             ("zero-secret", G, None, 0, True),
             ("identity-base", None, None, 23, True),
             ("identity-base-false", None, G, 23, False),
             ("false-equation", scale(G, 2), scale(G, 15), 7, False)]
    for name, base, point, secret, decision in cases:
        fixture = controls.native(subject, name, base, point, secret)
        expected = check(name, fixture, decision)
        if fixture["producer"] is None and args.retained_native is None:
            raise AssertionError("ordinary cases must contain actual native producer evidence")
        commitment = bytes.fromhex(expected["commitment"])
        if commitment != frame(None):
            signs.add(bool(commitment[6] & 0x20))
        if baseline is None:
            baseline, reference = fixture, expected
    save(args.output / "commitment-signs.json", sorted(signs))
    proof = bytes.fromhex(baseline["proof"])
    spans = {s["name"]: s for s in reference["frames"]}
    mutations = [("changed-response", replace_frame(proof, spans["response"],
                  scalar_frame((reference["response"] + 1) % R)), False, None, None)]
    commitment = decode(bytes.fromhex(spans["commitment"]["wire"]), "group")
    for name, value in (("identity-commitment", None), ("negated-commitment", scale(commitment, R - 1))):
        mutations.append((name, replace_frame(proof, spans["commitment"], frame(value)), False, None, None))
    changed_response = mutations[0][1]
    mutations.append(("false-equation-trailing", changed_response + b"\x00", None, "proof-trailing", ("decode", 13)))
    mutations.extend((name, changed, None, error, revert) for name, changed, error, revert in malformed(proof, reference))
    for name, changed, decision, error, revert in mutations:
        fixture = controls.native(subject, name, G, scale(G, 3), 3, proof=changed)
        check(name, fixture, decision, error, revert)
    physical_mutants = 0
    for s in subjects:
        path = s[0]
        original = json.loads((path / "generator-secret-3.evm.json").read_text())
        rejected = mutation_controls(original, reference)
        save(path / "physical-mutations.json", rejected)
        physical_mutants += len(rejected)
    # A deliberately invalid copy must still return true but fail full hashing.
    for s in subjects:
        path, _, _, artifact = s
        calldata = encode_verify(list(map(bytes.fromhex, baseline["public"])),
                                 bytes.fromhex(baseline["context"]), proof)
        original = json.loads((path / "generator-secret-3.evm.json").read_text())
        mutant = compile_request(args.solc, omit_final_observation(artifact["request"], reference["transitions"]))
        save(path / "omitted-final-hash.solc.json", mutant)
        result = removed_final_hash_control(args.runner, artifact, calldata, original,
                                           reference["trace"], None, mutant)
        save(path / "omitted-final-hash.json", result)
    command = [str(args.compiler), "language-evm", "--source-format=zkc", "--entry=example::Proof",
               f"--module=example={PROJECT / 'main.zkc'}", *library_modules("protocols/sigma/schnorr"),
               "--evm-version=cancun"]
    refused = subprocess.run(command, capture_output=True, text=True, timeout=90)
    save(args.output / "cancun-refusal.json", {"command": command, "returncode": refused.returncode,
                                             "stdout": refused.stdout, "stderr": refused.stderr})
    if refused.returncode == 0 or "evm.group-fork" not in refused.stderr:
        raise AssertionError("ordinary curve consumer did not refuse Cancun precisely")
    for group in ("tools", "modules"):
        for name, identity in tools[group].items():
            if sha(Path(identity["path"]).read_bytes()) != identity["sha256"]:
                raise AssertionError(f"{name} changed during validation")
    save(args.output / "run.json", {
        "status": "passed", "command": sys.argv, "cases": len(controls.cases),
        "calls_per_case": 2, "final_hash_mutants_rejected": 2, "cancun_refused": True,
        "physical_trace_mutants_rejected": physical_mutants,
        "retained_producer_proofs": 9 if args.retained_native else 0,
        "scope": "native proof, source affine equation, exact deployed bytes, outcomes, managed hashes "
                 "and complete source-derived physical ModExp/ADD/MSM traces",
        "separate_gates": ["ordinary SDK/CLI capture", "formal correspondence", "cryptographic security",
                           "universal call ABI trace", "gas theorem"]})
    print(f"{len(controls.cases)} real Schnorr consumer cases passed, two calls each; "
          f"{physical_mutants} physical trace mutations and two final-hash mutants rejected; Cancun refused")


if __name__ == "__main__":
    main()
