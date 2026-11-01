"""Compare checked EVM arithmetic and structured transport with native proofs.

Uses the existing solc/revm adapter and integer binomial reference. The native
producer supplies every proof; this harness builds inputs and independent
expectations, without implementing a proof producer or target runtime.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from abi import encode_verify
from binomial_reference import Binomial, PLONKY3_FIELDS
from hash_chain_reference import BLS12_381_R, BLS_SUITE, Chain, fr64be
from logical_tree import decode_tree, encode_tree
from oracle import chain_trace
from probe import PROFILES, check_solc, compile_request, execute
from validate import check_return, check_revert

ROOT = Path(__file__).resolve().parents[3]
FIELDS = PLONKY3_FIELDS | {
    "bls12-381.fr": Binomial(1, modulus=BLS12_381_R, coordinate_bytes=32),
    "bn254.fr": Binomial(1, modulus=21888242871839275222246405745257275088548364400416034343698204186575808495617,
                         coordinate_bytes=32),
    "ristretto255.scalar": Binomial(1, modulus=2**252 + 27742317777372353535851937790883648493,
                                coordinate_bytes=32),
}
TAGS = {"bls12-381.fr": (1, 66), "bn254.fr": (40, 41),
        "ristretto255.scalar": (13, 14), "koala-bear": (19, 20),
        "koala-bear.ext4-binomial3": (21, 22), "koala-bear.ext8-binomial3": (26, 27),
        "baby-bear": (90, 91), "baby-bear.ext4-binomial11": (93, 94),
        "goldilocks": (96, 97), "goldilocks.ext2-binomial7": (99, 100)}


def frame(tag, body):
    return b"ZKCV\x00" + bytes([tag]) + body


def field_wire(field, value):
    return frame(TAGS[field][0], FIELDS[field].coordinates(value))


def vector_wire(field, values):
    return frame(TAGS[field][1], len(values).to_bytes(4, "little") + b"".join(
        FIELDS[field].coordinates(value) for value in values))


def index_wire(value):
    return frame(31, value.to_bytes(8, "little"))


def sequence(children):
    return frame(69, len(children).to_bytes(4, "little") + b"".join(
        len(child).to_bytes(4, "little") + child for child in children))


def variant(tag, *children):
    return frame(65, tag.to_bytes(4, "little") + b"".join(
        len(child).to_bytes(4, "little") + child for child in children))


def raw_bytes(value):
    return frame(70, len(value).to_bytes(4, "little") + value)


def invocation_root(fixture):
    descriptor = fixture["descriptor"]
    policy = descriptor[1]
    public = [[*port[:3], wire] for port, wire in
              zip(descriptor[4], fixture["public"], strict=True)]
    return encode_tree(["zkc.native-proof-binding/0", "sha256", descriptor[2],
                        fixture["source"], *policy[1:4], descriptor, public, fixture["context"]])


def static_trace(fixture):
    """Exact hash oracle for subjects with static (non-repeated) communication."""
    root = invocation_root(fixture)
    digest = hashlib.sha256(root).digest()
    proof = bytes.fromhex(fixture["proof"])
    if proof[:40] != b"ZKCPRF00" + digest:
        raise AssertionError("native proof does not bind the independently encoded root")
    trace = [{"kind": "sha256", "input": root.hex(), "output": digest.hex(),
              "status": "return"}]
    descriptor, cursor = fixture["descriptor"], 40
    if not descriptor[1][5]:
        return trace
    if descriptor[1][5] != BLS_SUITE:
        raise AssertionError("unimplemented reference suite")
    chain = Chain(BLS_SUITE, root)
    challenge = None
    for kind, encoded in descriptor[3]:
        template = decode_tree(bytes.fromhex(encoded))
        if template[3]:
            raise AssertionError("static trace requires no repeated coordinates")
        origin = encode_tree(["zkc.native-origin/0", template[1], template[2], [], template[4]])
        chain.absorb(b"origin", origin)
        if kind == "query":
            challenge = field_wire("bls12-381.fr", [fr64be(chain.request(b"challenge", 64))])
        elif template[4][4] == descriptor[1][2]:
            size = int.from_bytes(proof[cursor:cursor + 8], "little")
            cursor += 8
            payload = proof[cursor:cursor + size]
            if len(payload) != size:
                raise AssertionError("truncated native frame")
            cursor += size
            chain.absorb(b"value", payload)
        else:
            if challenge is None:
                raise AssertionError("reference delivery precedes the challenge")
            chain.absorb(b"value", challenge)
    if cursor != len(proof):
        raise AssertionError("reference did not consume native proof")
    return trace + chain_trace(chain)


def check_native_outcome(fixture, expected, error):
    """A stopped native execution must have the specified cause, not just None."""
    if (expected is None) != (error is not None):
        raise ValueError("stopped native controls require an exact error")
    # The SDK reports a completed Boolean false as artifact-rejected; it is
    # distinct from a stopped execution whose decision is None.
    if expected is False:
        error = "artifact-rejected"
    if (type(fixture["decision"]) is not type(expected) or fixture["decision"] != expected
            or fixture["native_error"] != error):
        raise AssertionError(f"native outcome {(fixture['decision'], fixture['native_error'])} "
                             f"differs from {(expected, error)}")


class Subjects:
    def __init__(self, args):
        self.args, self.cases = args, []
        args.output.mkdir(parents=True, exist_ok=True)

    def compile(self, name, text, module="calculation", flags=()):
        path = self.args.output / name
        path.mkdir(exist_ok=True)
        source = path / "subject.zkc"
        source.write_text(text)
        command = [str(self.args.compiler), "--source-format=zkc", f"--entry={module}::Proof",
                   f"--module={module}={source}", *flags]
        products = []
        for mode in ("language-package", "language-evm"):
            process = subprocess.run([command[0], mode, *command[1:]], text=True,
                                     capture_output=True, timeout=90)
            if process.returncode:
                raise AssertionError(f"{name} {mode}: {process.stderr}")
            products.append(json.loads(process.stdout))
        package, compiled = products
        (path / "native.json").write_text(package["artifact"])
        (path / "source.json").write_text(json.dumps(compiled, indent=2) + "\n")
        artifact = compile_request(self.args.solc, {
            "language": "Yul", "sources": {"verifier.yul": {"content": compiled["yul"]}},
            "settings": {"evmVersion": compiled["manifest"]["fork"],
                         "optimizer": PROFILES["colon"],
                         "outputSelection": {"*": {"*": ["evm.bytecode.object",
                                                             "evm.deployedBytecode.object"]}}}})
        if len(artifact["runtime"]) // 2 > 24576 or len(artifact["creation"]) // 2 > 49152:
            raise AssertionError(f"{name}: deployment size exceeds frozen ceilings")
        return path, json.loads(package["artifact"]), compiled, artifact

    def run(self, subject, name, wires, *, expected=True, proof=None, native_error=None,
            evm_revert=None):
        if expected is None and evm_revert is None:
            raise ValueError("stopped controls require an exact EVM refusal")
        path, envelope, compiled, artifact = subject
        descriptor, policy = envelope[2], envelope[2][1]

        def request(role):
            mapping = next(m for m in envelope[6] if m[0] == role)
            return ["zkc.native-proof-inputs/0",
                    [[r[0], r[1], wires[int(r[1])].hex()] for r in descriptor[4]],
                    [[r[0], ["wire", wires[int(r[0])].hex()]] for r in mapping[2]],
                    "666f756e646174696f6e", [[r[0], "64"] for r in mapping[4]],
                    "64" if policy[5] else "0"]

        requests = path / f"{name}.inputs.json"
        requests.write_text(json.dumps({"prover": request(policy[2]), "verifier": request(policy[3])}))
        command = [str(self.args.native_driver), str(path / "native.json"), str(requests)]
        if proof is not None:
            proof_path = path / f"{name}.proof"
            proof_path.write_bytes(proof)
            command.append(str(proof_path))
        process = subprocess.run(command, text=True, capture_output=True, timeout=90)
        if process.returncode:
            raise AssertionError(f"{path.name}/{name} native: {process.stderr}")
        fixture = json.loads(process.stdout)
        (path / f"{name}.native.json").write_text(json.dumps(fixture, indent=2) + "\n")
        try:
            check_native_outcome(fixture, expected, native_error)
        except AssertionError as error:
            raise AssertionError(f"{path.name}/{name}: {error}") from error
        if fixture["source"] != compiled["source_sha256"] or descriptor != compiled["descriptor"]:
            raise AssertionError("native and EVM checked subjects differ")
        public = list(map(bytes.fromhex, fixture["public"]))
        calldata = encode_verify(public, bytes.fromhex(fixture["context"]), bytes.fromhex(fixture["proof"]))
        execution = execute(self.args.runner, artifact, calldata, gas=20_000_000)
        result_path = path / f"{name}.evm.json"
        result_path.write_text(json.dumps(execution, indent=2) + "\n")
        outcome = {key: execution[key] for key in ("status", "reason", "output", "runtime_gas")}
        failure = f"{path.name}/{name}: {outcome}; full execution: {result_path}"
        if evm_revert is not None:
            # These stopping subjects use authored, unobserved framed messages;
            # the header hash is the complete executed primitive frontier.
            root = invocation_root(fixture)
            trace = [{"kind": "sha256", "input": root.hex(),
                      "output": hashlib.sha256(root).hexdigest(), "status": "return"}]
            try:
                check_revert(execution, *evm_revert, trace)
            except AssertionError as error:
                raise AssertionError(f"{failure}: {error}") from error
        else:
            trace = static_trace(fixture)
            try:
                check_return(execution, int(expected).to_bytes(32, "big").hex(), trace)
            except AssertionError as error:
                raise AssertionError(f"{failure}: {error}") from error
        self.cases.append({"subject": path.name, "case": name, "decision": expected,
                           "runtime_bytes": len(artifact["runtime"]) // 2,
                           "gas": execution["runtime_gas"], "hashes": len(trace),
                           "native_error": native_error, "evm_revert": evm_revert})
        return fixture, execution


def arithmetic_source(field, expression):
    return f'''module calculation; domain F=field("{field}");
fn work(a:F,b:F)->F{{return {expression};}}
protocol Check roles(P,V)(a:F@P,b:F@P,expected:F@V)->(extra:F@V,accepted:bool@V){{
 let left=send P->V(a); let right=send P->V(b);
 let actual@V=work(left,right);
 return(extra=actual,accepted=actual==expected);
}}
proof Proof=Check{{prover P;verifier V;public{{expected}};accept accepted;construction authored;}}
'''


def arithmetic(subjects):
    for name, field in FIELDS.items():
        a = [field.modulus - 2 - i for i in range(field.degree)]
        b = [i + 3 for i in range(field.degree)]
        for operation, expression, result in (
            ("multiply", "a*b", field.mul(a, b)),
            ("subtract", "a-b", [(x - y) % field.modulus for x, y in zip(a, b, strict=True)]),
            ("divide", 'a*kernel<F>("field.inverse",b)',
             field.mul(a, field.power(b, field.modulus**field.degree - 2))),
            ("inverse", 'kernel<F>("field.inverse",a)', field.power(a, field.modulus**field.degree - 2)),
        ):
            subject = subjects.compile(f"{name}-{operation}", arithmetic_source(name, expression))
            inputs = {0: field_wire(name, a), 1: field_wire(name, b), 2: field_wire(name, result)}
            fixture, _ = subjects.run(subject, "valid", inputs)
            wrong = field.add(result, field.ONE)
            subjects.run(subject, "wrong-result", inputs | {2: field_wire(name, wrong)}, expected=False)
            if operation == "inverse":
                subjects.run(subject, "zero", inputs | {0: field_wire(name, field.ZERO)},
                             expected=None, native_error="refused:zero-inverse",
                             evm_revert=("source", 2))
            # EOF is checked even when the chosen non-first acceptance is false.
            if name == "koala-bear.ext4-binomial3" and operation == "multiply":
                subjects.run(subject, "trailing-proof", inputs,
                             proof=bytes.fromhex(fixture["proof"]) + b"\x00", expected=None,
                             native_error="proof-trailing", evm_revert=("decode", 13))


def structured(subjects):
    field = "koala-bear.ext4-binomial3"
    f = FIELDS[field]
    a, b = [1, 2, 3, 4], [5, 6, 7, 8]
    source = (Path(__file__).parent / "fixtures/structured.zkc").read_text()
    for managed in (False, True):
        text = source
        if managed:
            text = text.replace("expected:F@V)", "expected:F@V, challenges:Random<Fr>@V)")
            text = text.replace('domain F =', 'domain Fr = field("bls12-381.fr");\ndomain F =', 1)
            text = text.replace("  let received =", "  let c=challenges.draw(); let delivered=send V->P(c);\n  let received =", 1)
            text = text.replace("construction authored;", f'construction fiat_shamir("{BLS_SUITE}",challenges);')
        subject = subjects.compile("structured-managed" if managed else "structured-authored", text, "values")
        for name, children, expected in (
            ("empty", [], f.ZERO),
            ("mixed", [variant(0), variant(1, field_wire(field, a), field_wire(field, b)),
                       variant(2, raw_bytes(b"nested payload")), variant(0)], f.mul(a, b)),
            ("large-bytes", [variant(2, raw_bytes(bytes(9000)))], f.ZERO),
        ):
            wires = {0: sequence(children),
                     1: frame(68, (3).to_bytes(4, "little") + b"".join(
                         i.to_bytes(8, "little") for i in (0, 3, 2**64 - 1))),
                     2: raw_bytes(b"opaque\x00bytes"), 3: field_wire(field, expected)}
            fixture, _ = subjects.run(subject, name, wires)
            for port in (0, 1, 2):
                if fixture["outputs"][str(port)] != wires[port].hex():
                    raise AssertionError("native structured round trip differs from canonical input")


def envelopes(subjects):
    source = (Path(__file__).parent / "fixtures/envelopes.zkc").read_text()
    subject = subjects.compile("keccak-envelopes", source, "envelopes")
    for count in (0, 1, 24):
        root = frame(79, bytes(range(32)))
        path = frame(80, count.to_bytes(4, "little") + bytes(range(32)) * count)
        fixture, _ = subjects.run(subject, f"path-{count}", {0: root, 1: path})
        if fixture["outputs"] != {"0": root.hex(), "1": path.hex(),
                                  "2": frame(5, b"\x01").hex()}:
            raise AssertionError("opaque root/path transport changed canonical bytes")


def vectors(subjects):
    source = (Path(__file__).parent / "fixtures/vector.zkc").read_text()
    for name, field in FIELDS.items():
        subject = subjects.compile("vector-" + name,
                                   source.replace("koala-bear.ext4-binomial3", name), "vectors")
        for count in (0, 2, 4):
            values = [[(field.modulus - 1 - i - j) % field.modulus
                       for j in range(field.degree)] for i in range(count)]
            total = field.ZERO
            for value in values:
                total = field.add(total, value)
            expected = field.add(field.add(total, total), values[1]) if values else total
            subjects.run(subject, f"length-{count}", {
                0: vector_wire(name, values), 1: field_wire(name, expected),
                2: frame(5, bytes([count == 2])), 3: index_wire(count // 2)},
                expected=True if count else None,
                native_error=None if count else "refused:split-length",
                evm_revert=None if count else ("source", 5))


def finite(subjects):
    field, f = "koala-bear.ext4-binomial3", FIELDS["koala-bear.ext4-binomial3"]
    source = (Path(__file__).parent / "fixtures/finite.zkc").read_text()
    for flags in ((), ("--no-simplify", "--no-finite-bulk")):
        subject = subjects.compile("finite-ordered" if flags else "finite-default",
                                   source, "traversals", flags)
        for count, lower, upper in ((0, 1, 3), (1, 1, 3), (3, 1, 3), (3, 3, 1)):
            seed = [7, 3, 1, 5]
            a = [[2 + i, 1, 2, 3] for i in range(count)]
            b = [[5 + i, 3, 2, 1] for i in range(count)]
            paired, mapped, triangular, cartesian = (seed[:] for _ in range(4))
            ten = [10, 0, 0, 0]
            for x, y in zip(a, b, strict=True):
                paired = f.add(f.mul(paired, ten), f.mul(x, y))
                mapped = f.add(mapped, f.add(f.mul(x, x), seed))
            for i in range(count):
                for x in a[:i]:
                    triangular = f.add(triangular, x)
            for _ in range(lower, upper):
                for y in b:
                    cartesian = f.add(cartesian, y)
            wires = {0: vector_wire(field, a), 1: vector_wire(field, b),
                     2: field_wire(field, seed), 3: index_wire(lower), 4: index_wire(upper)}
            wires.update({i: field_wire(field, value) for i, value in
                          enumerate((paired, mapped, triangular, cartesian), 5)})
            subjects.run(subject, f"length-{count}-range-{lower}-{upper}", wires)
            if count == 0:
                # Admission is eager even when the first zipped input is empty.
                subjects.run(subject, "empty-zip-mismatch", wires | {
                    1: vector_wire(field, [f.ONE])}, expected=None,
                    native_error="rejected:require", evm_revert=("source", 5))
            if count == 3 and lower == 1:
                subjects.run(subject, "range-one-over", wires | {
                    4: index_wire(1048577)}, expected=None,
                    native_error="exhausted:local-bound-limit", evm_revert=("resource", 13))


def participant_loops(subjects):
    source = (Path(__file__).parent / "fixtures/loops.zkc").read_text()
    for flags in ((), ("--no-simplify", "--no-calculation-batching")):
        subject = subjects.compile("loop-captures-ordered" if flags else "loop-captures-default",
                                   source, "capture_bindings", flags)

        def aliases(node):
            if not isinstance(node, list):
                return False
            if len(node) == 7 and node[0] == "loop":
                captures = node[4]
                parents = [parent for _, parent in captures]
                if len(set(parents)) < len(parents):
                    return True
            return any(aliases(child) for child in node)

        # The source must actually exercise distinct formals bound to one
        # parent, rather than merely repeating a value inside one callback.
        if not aliases(json.loads(subject[1][4])):
            raise AssertionError("participant loop fixture lost its aliased capture bindings")
        for count in (0, 1, 3):
            wires = {0: field_wire("bls12-381.fr", [7]), 1: index_wire(count)}
            fixture, _ = subjects.run(subject, f"rounds-{count}", wires)
            if count:
                proof = bytearray.fromhex(fixture["proof"])
                second = 48 + int.from_bytes(proof[40:48], "little")
                size = int.from_bytes(proof[second:second + 8], "little")
                changed = field_wire("bls12-381.fr", [8])
                if size != len(changed):
                    raise AssertionError("second loop message has an unexpected wire type")
                proof[second + 8:second + 8 + size] = changed
                subjects.run(subject, f"rounds-{count}-changed-capture", wires,
                             proof=proof, expected=False)


def filtered(subjects):
    field, f = "koala-bear.ext4-binomial3", FIELDS["koala-bear.ext4-binomial3"]
    source = (Path(__file__).parent / "fixtures/filtered.zkc").read_text()
    for collection_only in (False, True):
        # Exercise each conditional body independently: a fold stop must not
        # mask a collect stop. Tuple state also spans several physical lanes.
        text = source.replace('state+kernel<F>("field.inverse",x)', 'state+x') if collection_only else source
        for flags in ((), ("--no-simplify", "--no-finite-bulk")):
            name = "filtered-collect" if collection_only else "filtered-fold"
            subject = subjects.compile(name + ("-ordered" if flags else "-default"),
                                       text, "filtered", flags)
            for case, values, enabled in (
                ("empty", [], True),
                ("skipped-zero", [f.ZERO], False),
                ("kept", [[2, 1, 0, 1], [3, 2, 1, 0]], True),
                ("stopping-zero", [f.ZERO], True),
            ):
                seed = [7, 3, 1, 5]
                first, second, third = f.add(seed, seed), seed[:], seed[:]
                if enabled and case != "stopping-zero":
                    for value in values:
                        inverse = f.power(value, f.modulus**f.degree - 2)
                        first = f.add(first, f.add(value if collection_only else inverse, inverse))
                        second, third = f.add(second, value), f.mul(third, value)
                wires = {0: vector_wire(field, values), 1: field_wire(field, f.ONE),
                         2: frame(5, bytes([enabled])), 3: field_wire(field, seed),
                         4: field_wire(field, first), 5: field_wire(field, second),
                         6: field_wire(field, third)}
                stopping = case == "stopping-zero"
                fixture, _ = subjects.run(subject, case, wires, expected=None if stopping else True,
                                          native_error="refused:zero-inverse" if stopping else None,
                                          evm_revert=("source", 2) if stopping else None)
                if case in ("skipped-zero", "stopping-zero"):
                    proof = bytearray.fromhex(fixture["proof"])
                    # Damage the second reached-or-unreached canonical frame.
                    offset = 48 + int.from_bytes(proof[40:48], "little") + 8
                    proof[offset] ^= 0xff
                    subjects.run(subject, case + "-malformed-later", wires, proof=bytes(proof),
                                 expected=None, native_error="refused:zero-inverse" if stopping
                                 else "artifact-stopped:Decode(Header)",
                                 evm_revert=("source", 2) if stopping else ("decode", 3))


def capacity(subjects):
    source = (Path(__file__).parent / "fixtures/filtered_capacity.zkc").read_text()
    field, f = "koala-bear.ext4-binomial3", FIELDS["koala-bear.ext4-binomial3"]
    for flags in ((), ("--no-simplify", "--no-finite-bulk")):
        subject = subjects.compile("selected-capacity" + ("-ordered" if flags else "-default"),
                                   source, "capacity", flags)
        for name, selected, body_stop, predicate_stop in (
            ("none", 0, 2**64 - 1, 2**64 - 1),
            ("one", 1, 2**64 - 1, 2**64 - 1),
            ("at-cap", 1024, 2**64 - 1, 2**64 - 1),
            ("over-cap", 1025, 2**64 - 1, 2**64 - 1),
            ("stopping-predicate", 0, 2**64 - 1, 0),
            ("stopping-body-at-cap", 1025, 1024, 2**64 - 1),
        ):
            stopping = name.startswith("stopping-")
            wires = {0: field_wire(field, f.ONE), 1: index_wire(selected),
                     2: index_wire(body_stop), 3: index_wire(predicate_stop),
                     4: field_wire(field, [selected, 0, 0, 0])}
            subjects.run(subject, name, wires, expected=None if stopping else True,
                         native_error="refused:zero-inverse" if stopping else None,
                         evm_revert=("source", 2) if stopping else
                         ("resource", 2) if name == "over-cap" else None)


def bytes_access(subjects):
    source = (Path(__file__).parent / "fixtures/bytes.zkc").read_text()
    subject = subjects.compile("bytes-access", source, "byte_access")
    for name, data, position, expected in (
        ("first", bytes(range(256)), 0, 0),
        ("last", bytes(range(256)), 255, 255),
        ("empty", b"", 0, None),
        ("one-past-end", b"abc", 3, None),
    ):
        subjects.run(subject, name, {0: raw_bytes(data), 1: index_wire(position),
                                    2: index_wire(expected or 0)},
                     expected=True if expected is not None else None,
                     native_error="refused:bytes-bounds" if expected is None else None,
                     evm_revert=("source", 3) if expected is None else None)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("compiler", "native-driver", "solc", "runner", "output"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    suites = {"arithmetic": arithmetic, "structured": structured, "envelopes": envelopes,
              "vectors": vectors, "finite": finite, "filtered": filtered,
              "loops": participant_loops, "capacity": capacity, "bytes": bytes_access}
    parser.add_argument("--suite", action="append", choices=suites)
    args = parser.parse_args()
    for name in ("compiler", "native_driver", "solc", "runner", "output"):
        setattr(args, name, getattr(args, name).resolve())
    check_solc(args.solc)
    subjects = Subjects(args)
    for name in args.suite or suites:
        suites[name](subjects)
    (args.output / "summary.json").write_text(json.dumps(subjects.cases, indent=2) + "\n")
    print(json.dumps(subjects.cases, indent=2))


if __name__ == "__main__":
    main()
