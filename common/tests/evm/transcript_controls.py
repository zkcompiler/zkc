"""Deployed managed Keccak controls using source compilation and real native proofs.

The byte oracle follows construction.md and native-index-block.md, using the
independent Python Keccak reference. Neither target Yul nor engine traces supply
expected samples, preimages, stops or outcomes. Only evm_fixture produces proofs;
supplied proofs are explicit negative controls. Exact artifacts, native reports,
expected traces and revm reports remain beside each source.

All tools are explicit; invocation/builds belong to the caller. The optional
evm_wire consumer preserves production requests before forcing answer bytes.
Its helper-only receipts are separate from compiled/deployed native proofs.
"""

import argparse
import copy
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "common/tests/support"))

from abi import encode_verify  # noqa: E402
from foundation_controls import (  # noqa: E402
    Subjects, check_native_outcome, field_wire, index_wire, invocation_root,
)
from hash_chain_reference import (  # noqa: E402
    Chain, KOALA_BEAR_P, OCTIC_SUITE, QUARTIC_SUITE, rejection31le, uniform_index,
)
from logical_tree import decode_tree, encode_tree  # noqa: E402
from oracle import chain_trace  # noqa: E402
from probe import SOLC_SHA256, check_solc, compile_request, execute  # noqa: E402
from validate import check_return, check_revert  # noqa: E402
from wire_controls import indices, settings  # noqa: E402
import target  # noqa: E402

@dataclass(frozen=True)
class Model:
    kind: str = "challenge"
    bound: int = 8
    count: int = 5
    bits: int | None = None
    repeated: bool = False
    guarded: bool = False
    degree: int = 4

    @property
    def field(self):
        return f"koala-bear.ext{self.degree}-binomial3"

    @property
    def suite(self):
        return QUARTIC_SUITE if self.degree == 4 else OCTIC_SUITE


class Stop(Exception):
    def __init__(self, native, kind, code):
        self.native, self.revert = native, (kind, code)


def source(model):
    """Small echo clients keep sampling, delivery and verifier checks observable."""
    value_type = {"challenge": "F", "index": "index", "block": "Indices"}[model.kind]
    query = {"challenge": "coins.draw()", "index": f"coins.index<{model.bound}>()",
             "block": f"coins.indices({model.bound},{model.count})"}[model.kind]
    # A deliberately checked numerical operation gives the source stop a
    # stable backend cause, independent of generated source guard/site names.
    helper = '''fn enforce(ok:bool)->bool {
      let one:index=1;
      let divisor:index=if ok {1} else {0};
      let checked=kernel("index.div",one,divisor);
      return checked==one;
    }'''
    if model.kind == "block":
        helper += '''fn same(a:Indices,b:Indices)->bool {
      let n=kernel("indices.length",a);
      let mut matched=kernel("indices.length",b)==n;
      if matched {
        for i in 0..n {
          matched=matched && kernel("indices.at",a,i)==kernel("indices.at",b,i);
        }
      }
      return enforce(matched);
    }'''
    comparison = "same(sample,echo)" if model.kind == "block" else "sample==echo"
    body = f'''let commitment=send P->V(seed);
      #[site(sample)] let sample={query};
      let delivered=send V->P(sample);
      let echo=send P->V(delivered);
      let checked@V={comparison};'''
    if (model.guarded or model.repeated) and model.kind != "block":
        body += "let enforced@V=enforce(checked);"
    body += "let tail=send P->V(seed);"
    rounds = ",rounds:index@(P,V)" if model.repeated else ""
    outputs = ("accepted:bool@V" if model.repeated else
               f"sampled:{value_type}@V,echoed:{value_type}@V,accepted:bool@V")
    decision = "enforced" if model.guarded and model.kind != "block" else "checked"
    returns = ("accepted=accepted" if model.repeated else
               f"sampled=sample,echoed=echo,accepted={decision} && flag")
    if model.repeated:
        checked = "checked" if model.kind == "block" else "enforced"
        body += f"accepted=accepted && {checked};"
        body = f"let mut accepted@V=flag;for i in 0..rounds roles(P,V) max 3 {{{body}}}"
    gate = "" if model.bits is None else f"gate sample bits {model.bits};"
    return f'''module transcript;
    domain F=field("{model.field}");type Indices=builtin("indices");{helper}
    protocol Echo roles(P,V)(seed:index@P,flag:bool@V,coins:Random<F>@V{rounds})
      ->({outputs}){{{body}return({returns});}}
    proof Proof=Echo{{prover P;verifier V;public{{flag{',rounds' if model.repeated else ''}}};
      accept accepted;construction fiat_shamir("{model.suite}",coins);{gate}}}
    '''


def occurrence(row, coordinates):
    template = decode_tree(bytes.fromhex(row[1]))
    if template[0] != "zkc.native-origin-template/0" or template[3]:
        raise AssertionError("expected a canonical static origin template")
    if sum(step[0] == "repeat" for step in template[2]) != len(coordinates):
        raise AssertionError("dynamic coordinates do not match the source repeats")
    return encode_tree(["zkc.native-origin/0", template[1], template[2],
                        list(map(str, coordinates)), template[4]])


def block(chain, origin, model, witness, *, forced_answer=None):
    """Full request, including successor hashing before testing the gate."""
    chain.absorb(b"origin", origin)
    chain.absorb(b"bound", model.bound.to_bytes(8, "little"))
    chain.absorb(b"count", model.count.to_bytes(8, "little"))
    if model.bits:
        chain.absorb(b"difficulty", model.bits.to_bytes(8, "little"))
        chain.absorb(b"gate-witness", index_wire(witness))
        answer = chain.request(b"gated-indices", 8 + 8 * model.count)
        if forced_answer is not None:
            if len(forced_answer) != len(answer):
                raise ValueError("forced gated answer has the wrong length")
            answer = forced_answer
        # Python integers make the b=64 whole-word case explicit and defined.
        passes = int.from_bytes(answer[:8], "little") & ((1 << model.bits) - 1) == 0
        answer = answer[8:]
    else:
        answer = chain.request(b"indices", 8 * model.count)
        if forced_answer is not None:
            if len(forced_answer) != len(answer):
                raise ValueError("forced ungated answer has the wrong length")
            answer = forced_answer
        passes = True
    values = [int.from_bytes(answer[i:i + 8], "little") & (model.bound - 1)
              for i in range(0, len(answer), 8)]
    return values, passes


def decode(wire, kind, degree=4):
    """Reached canonical leaf checks, independently of target wire helpers."""
    width = {"challenge": 6 + 4 * degree, "index": 14}.get(kind)
    if (width is not None and len(wire) != width) or (width is None and len(wire) < 10):
        raise Stop("artifact-stopped:Decode(Length)", "decode", 2)
    tag = {"challenge": 21 if degree == 4 else 26, "index": 31, "block": 68}[kind]
    if wire[:6] != b"ZKCV\x00" + bytes([tag]):
        raise Stop("artifact-stopped:Decode(Header)", "decode", 3)
    if kind == "challenge":
        values = [int.from_bytes(wire[i:i + 4], "little") for i in range(6, 6 + 4 * degree, 4)]
        if any(value >= KOALA_BEAR_P for value in values):
            raise Stop("artifact-stopped:Decode(Scalar)", "decode", 4)
    elif kind == "block":
        count = int.from_bytes(wire[6:10], "little")
        if len(wire) != 10 + 8 * count:
            raise Stop("artifact-stopped:Decode(Length)", "decode", 2)
        values = [int.from_bytes(wire[i:i + 8], "little") for i in range(10, len(wire), 8)]
    else:
        values = int.from_bytes(wire[6:], "little")
    return values


def replay(fixture, model, *, rounds=1, flag=True, gate_witness_code, gate_rejection_code):
    """Execute this source client's reached semantics; retain exact hash frontier."""
    descriptor = fixture["descriptor"]
    if descriptor[1][5] != model.suite:
        raise AssertionError("unexpected transcript suite")
    query_kind = ("gated-indices" if model.bits is not None else "indices") \
        if model.kind == "block" else {"challenge": "query", "index": "index"}[model.kind]
    events = descriptor[3]
    if [row[0] for row in events] != ["message", query_kind, "message", "message", "message"]:
        raise AssertionError(f"unexpected source communication: {events}")
    query = events[1]
    expected_parameters = ([] if model.kind == "challenge" else [str(model.bound)])
    if model.kind == "block":
        expected_parameters += [str(model.count)]
        if model.bits is not None:
            expected_parameters += [str(model.bits)]
    if query[2:] != expected_parameters:
        raise AssertionError("descriptor request does not match authored source")
    selected = descriptor[1][11]
    if model.bits is not None and (len(selected) != 1 or selected[0][1] != str(model.bits)):
        raise AssertionError("source-selected gate differs from its policy")
    slots = [[query[1], "gate." + selected[0][0], "index", "native.index/0"]] if model.bits is not None else []
    if descriptor[7] != slots:
        raise AssertionError("construction witness slots differ from the source selection")
    root = invocation_root(fixture)
    digest = hashlib.sha256(root).digest()
    trace = [{"kind": "sha256", "input": root.hex(), "output": digest.hex(), "status": "return"}]
    proof, cursor, chain = bytes.fromhex(fixture["proof"]), 40, None
    frames, samples, decisions, requests, gate_inputs = [], [], [], [], []
    stop, decision, outputs = None, None, None

    def receive(name, kind):
        nonlocal cursor
        start = cursor
        if cursor + 8 > len(proof):
            raise Stop("proof-truncated", "decode", 5)
        size = int.from_bytes(proof[cursor:cursor + 8], "little")
        cursor += 8
        if cursor + size > len(proof):
            raise Stop("proof-truncated", "decode", 5)
        wire = proof[cursor:cursor + size]
        cursor += size
        frames.append({"name": name, "start": start, "end": cursor, "wire": wire.hex()})
        return wire, decode(wire, kind, model.degree)

    def observe(row, coordinates, wire):
        chain.absorb(b"origin", occurrence(row, coordinates))
        chain.absorb(b"value", wire)

    try:
        if len(proof) < 40:
            raise Stop("proof-truncated", "decode", 11)
        if proof[:8] != b"ZKCPRF00":
            raise Stop("proof-header", "decode", 11)
        if proof[8:40] != digest:
            raise Stop("proof-header", "decode", 12)
        chain = Chain(model.suite, root)
        if model.repeated and rounds > 3:
            raise Stop("exhausted:local-bound-limit", "source", 6)
        for iteration in range(rounds if model.repeated else 1):
            coordinates = [iteration] if model.repeated else []
            commitment, _ = receive("commitment", "index")
            observe(events[0], coordinates, commitment)
            origin = occurrence(query, coordinates)
            witness = None
            if model.bits is not None:
                _, witness = receive("witness", "index")
                if model.bits == 0 and witness != 0:
                    raise Stop("refused:gate-witness", "source", gate_witness_code)
                gate_inputs.append({"state": chain.state.hex(), "origin": origin.hex()})
            if model.kind == "block":
                value, passes = block(chain, origin, model, witness)
                if not passes:
                    raise Stop("rejected:require", "source", gate_rejection_code)
                wire = indices(value)
            else:
                chain.absorb(b"origin", origin)
                if model.kind == "challenge":
                    answers = []

                    def answer():
                        raw = chain.request(b"challenge", 64)
                        answers.append(raw.hex())
                        return raw

                    value = rejection31le(answer, degree=model.degree)
                    requests.append(answers)
                    wire = field_wire(model.field, value)
                else:
                    chain.absorb(b"bound", model.bound.to_bytes(8, "little"))
                    value = uniform_index(chain.request(b"index", 64), model.bound)
                    wire = index_wire(value)
            samples.append(wire.hex())
            observe(events[2], coordinates, wire)
            echo, echoed = receive("echo", model.kind)
            observe(events[3], coordinates, echo)
            checked = echoed == value
            if (model.kind == "block" or model.guarded or model.repeated) and not checked:
                raise Stop("refused:index-zero-divisor", "source", 2)
            tail, _ = receive("tail", "index")
            observe(events[4], coordinates, tail)
            decisions.append(checked)
            outputs = {"0": wire.hex(), "1": echo.hex(),
                       "2": (b"ZKCV\x00\x05" + bytes([checked and flag])).hex()}
        decision = flag if model.repeated else decisions[-1] and flag
        if model.repeated:
            outputs = {"0": (b"ZKCV\x00\x05" + bytes([decision])).hex()}
        if cursor != len(proof):
            raise Stop("proof-trailing", "decode", 13)
    except Stop as error:
        stop, decision, outputs = error, None, None
    if chain is not None:
        trace += chain_trace(chain)
    return {"trace": trace, "decision": decision, "native_error": stop.native if stop else None,
            "revert": stop.revert if stop else None, "outputs": outputs,
            "frames": frames, "samples": samples, "challenge_answers": requests,
            "gate_inputs": gate_inputs, "final_state": chain.state.hex() if chain else None}


class Controls(Subjects):
    def native(self, subject, name, *, rounds=1, flag=True, context=b"transcript", proof=None):
        path, envelope, compiled, _ = subject
        descriptor, policy = envelope[2], envelope[2][1]
        wires = {0: index_wire(37), 1: b"ZKCV\x00\x05" + bytes([flag]), 2: index_wire(rounds)}

        def request(role):
            mapping = next(row for row in envelope[6] if row[0] == role)
            return ["zkc.native-proof-inputs/0",
                    [[*row[:2], wires[int(row[1])].hex()] for row in descriptor[4]],
                    [[row[0], ["wire", wires[int(row[0])].hex()]] for row in mapping[2]],
                    context.hex(), [[row[0], "64"] for row in mapping[4]], "64"]

        requests = path / f"{name}.inputs.json"
        requests.write_text(json.dumps({"prover": request(policy[2]), "verifier": request(policy[3])}))
        command = [str(self.args.native_driver), str(path / "native.json"), str(requests)]
        if proof is not None:
            supplied = path / f"{name}.proof"
            supplied.write_bytes(proof)
            command.append(str(supplied))
        process = subprocess.run(command, text=True, capture_output=True, timeout=90)
        if process.returncode:
            raise AssertionError(f"{path.name}/{name} native: {process.stderr}")
        fixture = json.loads(process.stdout)
        (path / f"{name}.native.json").write_text(json.dumps(fixture, indent=2) + "\n")
        if (fixture["source"] != compiled["original"] or fixture["descriptor"] != compiled["descriptor"]
                or fixture["descriptor"] != descriptor):
            raise AssertionError("native/EVM checked subjects differ")
        expected_public = [wires[int(row[1])].hex() for row in descriptor[4]]
        if fixture["public"] != expected_public or fixture["context"] != context.hex():
            raise AssertionError("native fixture changed the invocation inputs")
        if proof is not None and fixture["proof"] != proof.hex():
            raise AssertionError("native fixture changed the supplied proof")
        return fixture

    def check(self, subject, model, name, *, fixture=None, **inputs):
        path, _, _, artifact = subject
        if fixture is None:
            fixture = self.native(subject, name, **inputs)
        expected = replay(fixture, model, rounds=inputs.get("rounds", 1),
                          flag=inputs.get("flag", True), gate_witness_code=self.args.gate_witness_code,
                          gate_rejection_code=self.args.gate_rejection_code)
        check_native_outcome(fixture, expected["decision"], expected["native_error"])
        # The proof API withholds participant outputs on a rejected decision.
        # Keep the independent execution's outputs as evidence, but compare the
        # API publication contract as well as the underlying acceptance result.
        published = expected["outputs"] if expected["decision"] else {}
        if fixture["outputs"] != published:
            raise AssertionError(f"{path.name}/{name}: native outputs differ from independent samples")
        (path / f"{name}.expected.json").write_text(json.dumps(expected, indent=2) + "\n")
        calldata = encode_verify(list(map(bytes.fromhex, fixture["public"])),
                                 bytes.fromhex(fixture["context"]), bytes.fromhex(fixture["proof"]))
        execution = execute(self.args.runner, artifact, calldata, repeat_count=2)
        (path / f"{name}.evm.json").write_text(json.dumps(execution, indent=2) + "\n")
        if len(execution["calls"]) != 2:
            raise AssertionError("expected two calls on the same deployment")
        for call in execution["calls"]:
            result = execution | call
            try:
                if expected["revert"]:
                    check_revert(result, *expected["revert"], expected["trace"])
                else:
                    check_return(result, int(expected["decision"]).to_bytes(32, "big").hex(), expected["trace"])
            except AssertionError as error:
                raise AssertionError(f"{path.name}/{name}: {error}; see {path / (name + '.evm.json')}") from error
        self.cases.append({"subject": path.name, "case": name,
                           "decision": expected["decision"], "native_error": expected["native_error"],
                           "revert": expected["revert"], "hashes": len(expected["trace"]),
                           "runtime_bytes": len(artifact["runtime"]) // 2,
                           "gas": [call["gas_used"] for call in execution["calls"]]})
        return fixture, expected

    def compile(self, name, model, flags=()):
        subject = super().compile(name, source(model), "transcript", flags)
        path, _, _, artifact = subject
        (path / "solc.json").write_text(json.dumps(artifact, indent=2) + "\n")
        return subject


def replace_frame(proof, span, wire):
    return proof[:span["start"]] + len(wire).to_bytes(8, "little") + wire + proof[span["end"]:]


def stopped(controls, subject, model, name, proof, native_error, revert):
    fixture, expected = controls.check(subject, model, name, proof=proof)
    if expected["native_error"] != native_error or expected["revert"] != revert:
        raise AssertionError(f"{name}: the intended reached stop was masked")
    return fixture, expected


def mutations(controls, subject, model, fixture, expected):
    proof = bytes.fromhex(fixture["proof"])
    frames = {frame["name"]: frame for frame in expected["frames"]}
    # Exhaustion of framing at each reached slot must stop before its observation.
    for name, span in frames.items():
        for suffix, cut in (("length", span["start"] + 7), ("payload", span["end"] - 1)):
            stopped(controls, subject, model, f"truncated-{name}-{suffix}", proof[:cut],
                    "proof-truncated", ("decode", 5))
    stopped(controls, subject, model, "trailing", proof + b"\x00", "proof-trailing", ("decode", 13))
    echo = frames["echo"]
    wrong_tag = bytearray.fromhex(echo["wire"])
    wrong_tag[5] = 5
    stopped(controls, subject, model, "echo-wrong-tag", replace_frame(proof, echo, wrong_tag),
            "artifact-stopped:Decode(Header)", ("decode", 3))
    for name, changed in (("short-wire", bytes.fromhex(echo["wire"])[:-1]),
                          ("extra-wire", bytes.fromhex(echo["wire"]) + b"\x00")):
        stopped(controls, subject, model, "echo-" + name, replace_frame(proof, echo, changed),
                "artifact-stopped:Decode(Length)", ("decode", 2))
    if model.kind == "challenge":
        noncanonical = bytearray.fromhex(echo["wire"])
        noncanonical[6:10] = KOALA_BEAR_P.to_bytes(4, "little")
        stopped(controls, subject, model, "noncanonical-coordinate", replace_frame(proof, echo, noncanonical),
                "artifact-stopped:Decode(Scalar)", ("decode", 4))
        coordinates = decode(bytes.fromhex(echo["wire"]), "challenge", model.degree)
        coordinates[0] = (coordinates[0] + 1) % KOALA_BEAR_P
        wrong = field_wire(model.field, coordinates)
    elif model.kind == "index":
        wrong = index_wire(decode(bytes.fromhex(echo["wire"]), "index") ^ 1)
    else:
        values = decode(bytes.fromhex(echo["wire"]), "block")
        for name, changed in (("short-count", values[:-1]), ("long-count", values + [0]),
                              ("out-of-bound", [model.bound, *values[1:]])):
            stopped(controls, subject, model, name, replace_frame(proof, echo, indices(changed)),
                    "refused:index-zero-divisor", ("source", 2))
        different = next((i for i, value in enumerate(values) if value != values[0]), None)
        if different is not None:
            reordered = values[:]
            reordered[0], reordered[different] = reordered[different], reordered[0]
            stopped(controls, subject, model, "reordered-indices", replace_frame(proof, echo, indices(reordered)),
                    "refused:index-zero-divisor", ("source", 2))
        if len(set(values)) != len(values):
            stopped(controls, subject, model, "deduplicated-indices",
                    replace_frame(proof, echo, indices(list(dict.fromkeys(values)))),
                    "refused:index-zero-divisor", ("source", 2))
        wrong = indices([values[0] ^ 1, *values[1:]])
    changed = replace_frame(proof, echo, wrong)
    _, stopped_expected = controls.check(subject, model, "wrong-echo", proof=changed)
    intended = "refused:index-zero-divisor" if model.kind == "block" or model.guarded else None
    if stopped_expected["native_error"] != intended or stopped_expected["decision"] is not (None if intended else False):
        raise AssertionError("wrong echo did not reach its intended source check")
    if intended:
        tail = frames["tail"]
        changed = changed[:tail["start"]] + b"\xff" * 8
        _, later = controls.check(subject, model, "require-before-malformed-tail", proof=changed)
        if later["trace"] != stopped_expected["trace"] or later["revert"] != ("source", 2):
            raise AssertionError("an unreached malformed tail changed the numerical stop frontier")


def gate_mutations(controls, subject, model, fixture, expected):
    proof = bytes.fromhex(fixture["proof"])
    witness = next(frame for frame in expected["frames"] if frame["name"] == "witness")
    malformed = bytearray.fromhex(witness["wire"])
    malformed[5] = 5
    stopped(controls, subject, model, "witness-wrong-tag", replace_frame(proof, witness, malformed),
            "artifact-stopped:Decode(Header)", ("decode", 3))
    stopped(controls, subject, model, "witness-short-wire",
            replace_frame(proof, witness, bytes.fromhex(witness["wire"])[:-1]),
            "artifact-stopped:Decode(Length)", ("decode", 2))
    if model.bits == 0:
        rejected = 1
        error, revert = "refused:gate-witness", ("source", controls.args.gate_witness_code)
    else:
        initial = expected["gate_inputs"][0]
        for rejected in range(1024):
            chain = Chain(QUARTIC_SUITE, b"")
            chain.calls.clear()
            chain.state = bytes.fromhex(initial["state"])
            _, passes = block(chain, bytes.fromhex(initial["origin"]), model, rejected)
            if not passes:
                break
        else:
            raise AssertionError("no independently rejecting witness in the control interval")
        error, revert = "rejected:require", ("source", controls.args.gate_rejection_code)
    changed = replace_frame(proof, witness, index_wire(rejected))
    _, failed = stopped(controls, subject, model, "invalid-witness", changed, error, revert)
    # A failed positive gate has already hashed the complete answer and successor;
    # b=0's noncanonical nonce stops before the request consumes any chain state.
    tail = next(frame for frame in expected["frames"] if frame["name"] == "echo")
    changed = changed[:tail["start"]] + b"\xff" * 8
    _, later = stopped(controls, subject, model, "gate-before-malformed-echo", changed, error, revert)
    if later["trace"] != failed["trace"]:
        raise AssertionError("a frame after the gate stop changed its primitive frontier")


def compiled_matrix(controls, suite):
    if suite == "challenge":
        models = [("challenge", Model()), ("challenge-guarded", Model(guarded=True))]
    elif suite == "octic":
        models = [("octic-challenge", Model(degree=8)),
                  ("octic-guarded", Model(guarded=True, degree=8))]
    elif suite == "index":
        models = [(f"index-{bound}", Model("index", bound=bound)) for bound in (1, 256, 1 << 63)]
    elif suite == "block":
        models = [(f"block-{bound}-{count}", Model("block", bound, count))
                  for bound, count in ((1, 9), (8, 1), (8, 3), (8, 4), (8, 5), (1 << 63, 9),
                                       (256, 128), (256, 129))]
    elif suite == "gate":
        models = [(f"gate-{bits}-{count}", Model("block", 8, count, bits))
                  for bits, count in ((0, 5), (6, 1), (6, 3), (6, 4), (6, 5), (6, 9))]
    else:
        models = [("repeat-challenge", Model(repeated=True)),
                  ("repeat-gate", Model("block", bits=6, repeated=True))]
    for name, model in models:
        subject = controls.compile(name, model)
        if model.repeated:
            for rounds in (0, 1, 3):
                repeated_fixture, _ = controls.check(subject, model, f"rounds-{rounds}", rounds=rounds)
            _, last = controls.check(subject, model, "last-iteration-truncated", rounds=3,
                                     proof=bytes.fromhex(repeated_fixture["proof"])[:-1])
            if last["native_error"] != "proof-truncated" or last["revert"] != ("decode", 5):
                raise AssertionError("repeated truncation did not reach its intended final slot")
            continue
        fixture, expected = controls.check(subject, model, "valid")
        if model.kind == "block" and model.count >= 128:
            values = decode(bytes.fromhex(expected["samples"][0]), "block")
            if len(values) != model.count or len(set(values)) < 2:
                raise AssertionError("overlap control requires Q varied, ordered samples")
        controls.check(subject, model, "completed-false", flag=False)
        mutations(controls, subject, model, fixture, expected)
        if model.bits is not None:
            gate_mutations(controls, subject, model, fixture, expected)
        if model.kind == "block" and model.bound == 1:
            if decode(bytes.fromhex(expected["samples"][0]), "block") != [0] * model.count:
                raise AssertionError("bound-one samples lost their exact duplicate count")
        if model.kind == "block" and model.count > model.bound:
            values = decode(bytes.fromhex(expected["samples"][0]), "block")
            if len(values) != model.count or len(set(values)) == model.count:
                raise AssertionError("the duplicate control did not preserve Q ordered samples")
        if model.kind == "challenge" and not model.guarded:
            # Masking and rejecting consumed candidates are reachable by varying
            # only context. Require both features in the actual decoder prefix.
            # Find it with the independent oracle, then require a real native
            # proof and the complete deployed trace for that exact invocation.
            for counter in range(4096):
                context = f"rejection-{counter}".encode()
                candidate = copy.deepcopy(fixture)
                candidate["context"] = context.hex()
                candidate["proof"] = (b"ZKCPRF00" + hashlib.sha256(invocation_root(candidate)).digest()
                                      + bytes.fromhex(fixture["proof"])[40:]).hex()
                trial = replay(candidate, model, gate_witness_code=controls.args.gate_witness_code,
                               gate_rejection_code=controls.args.gate_rejection_code)
                if consumed_sampler_edges(trial["challenge_answers"][0][0]) == {"masked", "rejected"}:
                    controls.check(subject, model, "masked-and-rejected-word", context=context)
                    break
            else:
                raise AssertionError("no consumed masking/rejection edges in the bounded context search")
        print(name, "passed", flush=True)
    if suite == "gate":
        # Rebind a real proof as a negative control for the b=64 verifier.
        # There is deliberately no attempt to produce an honest 64-bit witness.
        full_word_gate(controls, fixture)


def full_word_gate(controls, native_fixture):
    model = Model("block", 8, 9, 64)
    subject = controls.compile("gate-64-negative", model)
    candidate = copy.deepcopy(native_fixture)
    candidate["source"], candidate["descriptor"] = subject[1][1:3]
    body = bytes.fromhex(native_fixture["proof"])[40:]
    header = b"ZKCPRF00" + hashlib.sha256(invocation_root(candidate)).digest()
    candidate["proof"] = (header + body).hex()
    expected = replay(candidate, model, gate_witness_code=controls.args.gate_witness_code,
                      gate_rejection_code=controls.args.gate_rejection_code)
    if expected["native_error"] != "rejected:require":
        raise AssertionError("the b=64 negative witness unexpectedly passed the independent predicate")
    stopped(controls, subject, model, "full-word-gate-fails", bytes.fromhex(candidate["proof"]),
            "rejected:require", ("source", controls.args.gate_rejection_code))


def consumed_sampler_edges(encoded):
    accepted, edges = 0, set()
    raw = bytes.fromhex(encoded)
    for at in range(0, 64, 4):
        word = int.from_bytes(raw[at:at + 4], "little")
        value = word & 0x7fffffff
        if value >= KOALA_BEAR_P:
            edges.add("rejected")
            continue
        if word != value:
            edges.add("masked")
        accepted += 1
        if accepted == 4:
            break
    return edges


def reference_edges():
    """Synthetic oracle probes only; these never count as deployed compiler cases."""
    results = []
    for name, blocks, expected, calls in (
        ("masked-and-rejected", [[KOALA_BEAR_P, 0x80000001, 0x04030201, KOALA_BEAR_P - 1, 5]],
         [1, 0x04030201, KOALA_BEAR_P - 1, 5], 1),
        ("partial-across-answers", [[1], [2], [3], [4]], [1, 2, 3, 4], 4),
        ("retry-empty-first-answer", [[], [1, 2, 3, 4]], [1, 2, 3, 4], 2),
        ("last-allowed-answer", [[]] * 15 + [[1, 2, 3, 4]], [1, 2, 3, 4], 16),
        ("exhaustion", [[]] * 16, None, 16),
        ("partial-exhaustion", [[1, 2, 3]] + [[]] * 15, None, 16),
    ):
        consumed = 0

        def answer():
            nonlocal consumed
            words = blocks[consumed]
            consumed += 1
            return b"".join(word.to_bytes(4, "little") for word in words) + b"\xff" * (64 - 4 * len(words))

        try:
            value = rejection31le(answer, degree=4)
        except ValueError as error:
            if str(error) != "challenge-rejection-limit":
                raise
            value = None
        if value != expected or consumed != calls:
            raise AssertionError(f"reference probe {name}: {value}, calls={consumed}")
        results.append({"case": name, "coordinates": value, "answers": consumed,
                        "blocks": [(b"".join(word.to_bytes(4, "little") for word in words)
                                    + b"\xff" * (64 - 4 * len(words))).hex() for words in blocks],
                        "scope": "reference-only; no compiled or deployed target evidence"})
    return results


def compile_helpers(args, name, option):
    path = args.output / name
    path.mkdir(exist_ok=True)
    process = subprocess.run([str(args.sampler_consumer), option],
                             text=True, capture_output=True, timeout=30)
    if process.returncode:
        raise AssertionError(f"{name} consumer: {process.stderr}")
    (path / "probe.yul").write_text(process.stdout)
    artifact = compile_request(args.solc, {"language": "Yul",
        "sources": {"probe.yul": {"content": process.stdout}}, "settings": settings()})
    (path / "solc.json").write_text(json.dumps(artifact, indent=2) + "\n")
    return path, artifact


def helper_chain(state):
    """Explicit helper state, with no artificial native binding event."""
    chain = Chain(QUARTIC_SUITE, b"")
    chain.calls.clear()
    chain.state = state
    return chain


def helper_calldata(blocks, *parameters):
    """Eight u256 header words, then caller-supplied equal-length answers."""
    length = len(blocks[0]) if blocks else 0
    if any(len(raw) != length for raw in blocks) or len(parameters) > 6:
        raise ValueError("invalid helper calldata")
    header = [len(blocks), length, *parameters]
    return b"".join(word.to_bytes(32, "big") for word in header).ljust(256, b"\x00") + b"".join(blocks)


def helper_output(calls, state, values):
    # Request retries are internal: generation/draws advance once and consume
    # exactly one transition. The final chain digest is independently checked.
    words = [calls, 1, 1, 0, int.from_bytes(state, "big"), *values]
    return b"".join(word.to_bytes(32, "big") for word in words).hex()


def sampler_helpers(args, probes):
    """Force decoder bytes after real requests, never substitute a compiler proof."""
    path, artifact = compile_helpers(args, "sampler-helpers", "--emit-transcript-sampler")
    receipts = []
    for probe in probes:
        blocks = list(map(bytes.fromhex, probe["blocks"]))
        chain = helper_chain(bytes(32))
        chain.absorb(b"origin", b"sampler-origin")
        states = []

        def answer():
            chain.request(b"challenge", 64)
            raw = blocks[len(states)]
            states.append(chain.state.hex())
            return raw

        try:
            coordinates = rejection31le(answer, degree=4)
        except ValueError as error:
            if str(error) != "challenge-rejection-limit":
                raise
            coordinates = None
        if coordinates != probe["coordinates"] or len(states) != probe["answers"]:
            raise AssertionError("sampler helper expectation differs from the authored edge case")
        trace = chain_trace(chain)
        expected = {"case": probe["case"], "answers": len(states),
                    "scope": "helper-only: production decoder and requests, synthetic answers; no compiled proof",
                    "coordinates": coordinates, "trace": trace,
                    "request_states": states, "final_state": chain.state.hex()}
        (path / (probe["case"] + ".expected.json")).write_text(json.dumps(expected, indent=2) + "\n")
        calldata = helper_calldata(blocks)
        result = execute(args.runner, artifact, calldata, repeat_count=2)
        (path / (probe["case"] + ".evm.json")).write_text(json.dumps(result, indent=2) + "\n")
        if len(result["calls"]) != 2:
            raise AssertionError("expected two helper calls on the same deployment")
        for call in result["calls"]:
            execution = result | call
            if probe["coordinates"] is None:
                check_revert(execution, "resource", args.sampler_exhaustion_code, trace)
            else:
                check_return(execution, helper_output(len(states), chain.state, coordinates), trace)
        receipts.append(expected)
    return receipts


def block_helpers(args):
    """Target ceilings and exact gate equations from a shared explicit state/origin."""
    path, artifact = compile_helpers(args, "block-helpers", "--emit-transcript-block")
    ceiling = target.LIMITS["public_elements"]
    words = [0x0102030405060708, (1 << 64) - 1, (1 << 63) + 1, 0, 255]
    suffix = b"".join(word.to_bytes(8, "little") for word in words)
    cases = [
        ("maximum-count", Model("block", 256, ceiling), 0, None, None),
        ("one-over-count", Model("block", 256, ceiling + 1), 0, None, ("resource", 2)),
        ("ungated", Model("block", 256, 5), 0, None, None),
        ("gate-zero-equation", Model("block", 256, 5, 0), 0, None, None),
        ("gate-64-zero-passes", Model("block", 256, 5, 64), 19, bytes(8) + suffix, None),
        ("gate-64-high-bit-fails", Model("block", 256, 5, 64), 19,
         (1 << 63).to_bytes(8, "little") + suffix, ("source", args.gate_rejection_code)),
    ]
    receipts, ungated = [], None
    for name, model, witness, forced, revert in cases:
        chain = helper_chain((7).to_bytes(32, "big"))
        values, passes = None, None
        if model.count <= ceiling:
            values, passes = block(chain, b"block-origin", model, witness, forced_answer=forced)
            if passes != (revert is None):
                raise AssertionError(f"{name}: authored gate outcome differs from independent predicate")
            if len(values) != model.count or len(set(values)) < 2:
                raise AssertionError(f"{name}: requires varied ordered indices")
        trace = chain_trace(chain)
        expected = {"case": name, "scope": "helper-only; no source compilation or native proof",
                    "count": model.count, "bits": model.bits, "witness": witness,
                    "forced_answer": forced.hex() if forced is not None else None,
                    "values": values, "revert": revert, "trace": trace,
                    "final_state": chain.state.hex()}
        if name == "ungated":
            ungated = (values, trace, chain.state)
        elif name == "gate-zero-equation" and (values, trace, chain.state) != ungated:
            raise AssertionError("b=0 differs from ungated at the same state and origin")
        (path / (name + ".expected.json")).write_text(json.dumps(expected, indent=2) + "\n")
        calldata = helper_calldata([] if forced is None else [forced],
                                   model.count, model.bits or 0, witness)
        result = execute(args.runner, artifact, calldata, repeat_count=2)
        (path / (name + ".evm.json")).write_text(json.dumps(result, indent=2) + "\n")
        if len(result["calls"]) != 2:
            raise AssertionError("expected two block-helper calls on the same deployment")
        for call in result["calls"]:
            execution = result | call
            if revert:
                check_revert(execution, *revert, trace)
            else:
                check_return(execution, helper_output(1, chain.state, values), trace)
        receipts.append(expected)
    return receipts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("compiler", "native-driver", "solc", "runner", "output"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    parser.add_argument("--gate-witness-code", type=int, required=True,
                        help="agreed EVM source code for refused:gate-witness; never read from Yul/trace")
    parser.add_argument("--gate-rejection-code", type=int, required=True,
                        help="agreed EVM source code for a failed positive gate (rejected:require)")
    parser.add_argument("--sampler-consumer", type=Path,
                        help="zkc-evm_wire-test; enables separate sampler and block helper probes")
    parser.add_argument("--sampler-exhaustion-code", type=int,
                        help="agreed EVM resource code for challenge-rejection-limit; required with consumer")
    suites = ("challenge", "octic", "index", "block", "gate", "repeated")
    parser.add_argument("--suite", action="append", choices=(*suites, "helpers"))
    args = parser.parse_args()
    for name in ("compiler", "native_driver", "solc", "runner", "output"):
        setattr(args, name, getattr(args, name).resolve())
    if any(not 0 <= code < 1 << 256 for code in (args.gate_witness_code, args.gate_rejection_code)):
        parser.error("gate source codes must be u256 values")
    if (args.sampler_consumer is None) != (args.sampler_exhaustion_code is None):
        parser.error("sampler consumer and exhaustion code must be supplied together")
    if args.suite and "helpers" in args.suite and args.sampler_consumer is None:
        parser.error("the helpers suite requires --sampler-consumer")
    if args.sampler_consumer is not None:
        args.sampler_consumer = args.sampler_consumer.resolve()
        if not 0 <= args.sampler_exhaustion_code < 1 << 256:
            parser.error("sampler exhaustion code must be a u256")
    version = check_solc(args.solc)
    controls = Controls(args)
    receipt = {"scope": "bounded source/native/deployed agreement; not an SDK artifact authentication test",
               "solc_version": version, "solc_sha256": SOLC_SHA256,
               "tools": {name: {"path": str(getattr(args, name)),
                                "sha256": hashlib.sha256(getattr(args, name).read_bytes()).hexdigest()}
                         for name in ("compiler", "native_driver", "runner")},
               "gate_witness_code": args.gate_witness_code,
               "gate_rejection_code": args.gate_rejection_code,
               "sampler_exhaustion_code": args.sampler_exhaustion_code,
               "selected_suites": args.suite or list(suites),
               "compiled_cases": controls.cases, "reference_only": reference_edges(),
               "sampler_helpers": [], "block_helpers": [],
               "missing_coverage": ["compiled native proof with passing b=64 witness: honest search is infeasible",
                                    "compiled proof-path partial/retry/exhaustion: infeasible context search",
                                    "block refusal precedence and internal preflight atomicity"]}
    if args.sampler_consumer is not None:
        receipt["tools"]["sampler_consumer"] = {
            "path": str(args.sampler_consumer),
            "sha256": hashlib.sha256(args.sampler_consumer.read_bytes()).hexdigest()}
        receipt["sampler_helpers"] = sampler_helpers(args, receipt["reference_only"])
        receipt["block_helpers"] = block_helpers(args)
    else:
        receipt["missing_coverage"].append("transcript helper probes: --sampler-consumer was not supplied")
    (args.output / "summary.json").write_text(json.dumps(receipt, indent=2) + "\n")
    for suite in args.suite or suites:
        if suite != "helpers":
            compiled_matrix(controls, suite)
        (args.output / "summary.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"compiled_cases": len(controls.cases), "calls_per_case": 2,
                      "reference_only": len(receipt["reference_only"]),
                      "sampler_helpers": len(receipt["sampler_helpers"]),
                      "block_helpers": len(receipt["block_helpers"])}))


if __name__ == "__main__":
    main()
