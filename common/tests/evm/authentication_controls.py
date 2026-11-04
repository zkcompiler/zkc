"""Native/deployed row authentication and polynomial controls for parent execution.

Uses the existing fixture driver, solc adapter and independent integer Keccak.
The native driver produces framed source proofs. This module constructs only
their mathematical inputs and expected primitive hashes; it is not a prover.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from abi import encode_verify, keccak256
from coset_reference import CosetReference
from foundation_controls import (
    Subjects, check_native_outcome, field_wire, frame, index_wire, invocation_root,
    vector_wire,
)
from message_frames import children, replace_child
from oracle_deployment import table_realization
from probe import check_solc, execute
from validate import check_return, check_revert


FIELDS = {
    "koala-bear": (1, 33, 34, "koala-bear.canonical-u32le/0"),
    "koala-bear.ext4-binomial3": (4, 79, 80, "koala-bear.ext4-binomial3.ascending-u32le/0"),
    "koala-bear.ext8-binomial3": (8, 35, 36, "koala-bear.ext8-binomial3.ascending-u32le/0"),
}
FIXTURES = Path(__file__).parent / "fixtures"


def boolean(value):
    return frame(5, bytes([value]))


def hash_step(message):
    digest = keccak256(message)
    return digest, {"kind": "keccak256", "input": message.hex(),
                    "output": digest.hex(), "status": "return"}


def leaf_message(field, width, height, row):
    degree, _, _, codec = FIELDS[field]
    words = b"".join(int(coefficient).to_bytes(4, "little")
                     for element in row for coefficient in element)
    if len(words) != len(row) * degree * 4:
        raise ValueError("incorrect row coordinate width")
    return (b"zkc.oracle.keccak256.leaf/0\x00" + len(codec).to_bytes(8, "little")
            + codec.encode() + width.to_bytes(8, "little") + height.to_bytes(8, "little")
            + words)


def opening(field, width, height, position):
    """Independent cap-zero binary tree, including zero-digest leaf padding."""
    degree, _, _, _ = FIELDS[field]
    rows = [[tuple(1 + 100 * r + 10 * c + j for j in range(degree))
             for c in range(width)] for r in range(height)]
    return opening_rows(field, rows, position)


def opening_rows(field, rows, position):
    width, height = len(rows[0]), len(rows)
    layer = [keccak256(leaf_message(field, width, height, row)) for row in rows]
    layer += [bytes(32)] * ((1 << (height - 1).bit_length()) - height)
    path, coordinate = [], position
    while len(layer) > 1:
        path.append(layer[coordinate ^ 1])
        layer = [keccak256(b"zkc.oracle.keccak256.node/0\x00" + a + b)
                 for a, b in zip(layer[::2], layer[1::2], strict=True)]
        coordinate >>= 1
    return layer[0], rows[position], path


def authenticate(field, root, width, height, position, row, path):
    """Returns raw bool plus the exact ordered crypto prefix after admission."""
    if not width or not height or height > 1 << 24:
        raise ValueError("oracle-shape")
    if width * height > 1 << 20:
        raise ValueError("oracle-element-limit")
    if position >= height:
        raise ValueError("oracle-coordinate")
    if len(row) != width or len(path) != (height - 1).bit_length():
        return False, []
    digest, step = hash_step(leaf_message(field, width, height, row))
    trace = [step]
    for level, sibling in enumerate(path):
        left, right = (sibling, digest) if position >> level & 1 else (digest, sibling)
        digest, step = hash_step(b"zkc.oracle.keccak256.node/0\x00" + left + right)
        trace.append(step)
    return digest == root, trace


def messages(proof):
    result, at = [], 40
    while at < len(proof):
        if at + 8 > len(proof):
            raise ValueError("truncated proof frame length")
        size = int.from_bytes(proof[at:at + 8], "little")
        start, end = at + 8, at + 8 + size
        if end > len(proof):
            raise ValueError("truncated proof frame")
        result.append((at, start, end, proof[start:end]))
        at = end
    return result


class Controls(Subjects):
    def native(self, subject, name, wires, *, proof=None, context=b"authentication", budget=64):
        path, envelope, compiled, _ = subject
        descriptor, policy = envelope[2], envelope[2][1]

        def request(role):
            mapping = next(row for row in envelope[6] if row[0] == role)
            return ["zkc.native-proof-inputs/0",
                    [[*row[:2], wires[int(row[1])].hex()] for row in descriptor[4]],
                    [[row[0], ["wire", wires[int(row[0])].hex()]] for row in mapping[2]],
                    context.hex(), [[row[0], str(budget)] for row in mapping[4]],
                    str(budget) if policy[5] else "0"]

        inputs = path / f"{name}.inputs.json"
        inputs.write_text(json.dumps({"prover": request(policy[2]), "verifier": request(policy[3])}))
        command = [str(self.args.native_driver), str(path / "native.json"), str(inputs)]
        if proof is not None:
            supplied = path / f"{name}.proof"
            supplied.write_bytes(proof)
            command.append(str(supplied))
        process = subprocess.run(command, text=True, capture_output=True, timeout=180)
        if process.returncode:
            raise AssertionError(f"{name}: native fixture generation: {process.stderr}")
        fixture = json.loads(process.stdout)
        (path / f"{name}.native.json").write_text(json.dumps(fixture, indent=2) + "\n")
        if fixture["source"] != compiled["original"] or fixture["descriptor"] != compiled["descriptor"]:
            raise AssertionError("native and EVM checked subjects differ")
        if fixture["public"] != [wires[int(row[1])].hex() for row in descriptor[4]]:
            raise AssertionError("native invocation changed public inputs")
        if fixture["context"] != context.hex() or (proof is not None and fixture["proof"] != proof.hex()):
            raise AssertionError("native invocation changed context or supplied proof")
        return fixture

    def check(self, subject, name, wires, *, expected=True, trace=(), native_error=None,
              revert=None, proof=None, fixture=None, complete_trace=None):
        if fixture is None:
            fixture = self.native(subject, name, wires, proof=proof)
        check_native_outcome(fixture, expected, native_error)
        root = invocation_root(fixture)
        binding = hashlib.sha256(root).digest()
        if bytes.fromhex(fixture["proof"])[:40] != b"ZKCPRF00" + binding:
            raise AssertionError("proof header did not bind independent invocation bytes")
        complete = [{"kind": "sha256", "input": root.hex(), "output": binding.hex(),
                     "status": "return"}, *trace]
        if complete_trace is not None:
            if not complete_trace or complete_trace[0] != complete[0]:
                raise AssertionError("independent trace does not start at this invocation binding")
            complete = complete_trace
        path, _, _, artifact = subject
        calldata = encode_verify(list(map(bytes.fromhex, fixture["public"])),
                                 bytes.fromhex(fixture["context"]), bytes.fromhex(fixture["proof"]))
        execution = execute(self.args.runner, artifact, calldata, repeat_count=2)
        (path / f"{name}.expected.json").write_text(json.dumps(complete, indent=2) + "\n")
        (path / f"{name}.evm.json").write_text(json.dumps(execution, indent=2) + "\n")
        if len(execution["calls"]) != 2:
            raise AssertionError("expected two calls on the same deployment")
        for call in execution["calls"]:
            if revert:
                check_revert(execution | call, *revert, complete)
            else:
                check_return(execution | call, int(expected).to_bytes(32, "big").hex(), complete)
        self.cases.append({"subject": path.name, "case": name, "decision": expected,
                           "native_error": native_error, "revert": revert,
                           "hashes": len(complete), "runtime_bytes": len(artifact["runtime"]) // 2,
                           "gas": [call["gas_used"] for call in execution["calls"]]})
        return fixture


def authentication(controls):
    source = (FIXTURES / "authentication.zkc").read_text()
    for field, (_, root_tag, path_tag, _) in FIELDS.items():
        text = source.replace("koala-bear.ext4-binomial3", field)
        subject = controls.compile("row-" + field, text, "authentication")
        for width, height, position in ((1, 1, 0), (2, 8, 0), (2, 8, 7), (3, 5, 4)):
            root, row, path = opening(field, width, height, position)

            def run(label, *, r=root, values=row, siblings=path, w=width, h=height,
                    at=position, guard=False, error=None, revert=None):
                if error:
                    valid, trace = None, []
                else:
                    valid, trace = authenticate(field, r, w, h, at, values, siblings)
                    trace *= 2
                return controls.check(subject, f"{width}-{height}-{position}-{label}", {
                    0: frame(root_tag, r), 1: vector_wire(field, values),
                    2: frame(path_tag, len(siblings).to_bytes(4, "little") + b"".join(siblings)),
                    3: index_wire(w), 4: index_wire(h), 5: index_wire(at), 6: boolean(guard),
                }, expected=valid, trace=trace, native_error=error, revert=revert)

            honest = run("honest")
            run("honest-guarded", guard=True)
            run("wrong-root", r=bytes([root[0] ^ 1]) + root[1:])
            changed = list(row)
            changed[0] = ((row[0][0] + 1) % 2130706433, *row[0][1:])
            run("wrong-row", values=changed)
            run("short-row", values=row[:-1])
            run("extra-row", values=row + row[:1])
            run("extra-path", siblings=path + [bytes(32)])
            if path:
                run("short-path", siblings=path[:-1])
                run("wrong-sibling", siblings=[bytes([path[0][0] ^ 1]) + path[0][1:], *path[1:]])
            run("shape-before-coordinate", w=0, at=2**64 - 1,
                error="refused:oracle-shape", revert=("source", 10))
            run("height-before-element-limit", w=2**64 - 1, h=(1 << 24) + 1,
                error="refused:oracle-shape", revert=("source", 10))
            run("element-before-coordinate", w=2**64 - 1, at=2**64 - 1,
                error="exhausted:oracle-element-limit", revert=("resource", 16))
            run("coordinate-before-width", values=[], at=height,
                error="refused:oracle-coordinate", revert=("source", 11))
            if (width, height, position) == (2, 8, 0):
                encoded = bytes.fromhex(honest["proof"])
                spans = messages(encoded)
                if len(spans) != 1 or len(children(spans[0][3])) != 3:
                    raise AssertionError("raw source did not send one root/row/path tuple")
                start, _, end, packet = spans[0]
                inputs = {0: frame(root_tag, root), 1: vector_wire(field, row),
                          2: frame(path_tag, len(path).to_bytes(4, "little") + b"".join(path)),
                          3: index_wire(width), 4: index_wire(height),
                          5: index_wire(position), 6: boolean(False)}
                root_frame, row_frame, path_frame = children(packet)
                noncanonical = bytearray(row_frame)
                noncanonical[10:14] = (2130706433).to_bytes(4, "little")
                for label, child, replacement, native, code in (
                    ("noncanonical-row", 1, bytes(noncanonical), "Scalar", 4),
                    ("short-root", 0, root_frame[:-1], "Length", 2),
                    ("short-path-payload", 2, path_frame[:-1], "Length", 2),
                    ("wrong-path-domain", 2, path_frame[:5] + bytes([root_tag]) + path_frame[6:], "Header", 3),
                ):
                    changed = replace_child(packet, [child], replacement)
                    supplied = encoded[:start] + len(changed).to_bytes(8, "little") + changed + encoded[end:]
                    controls.check(subject, label, inputs, proof=supplied, expected=None,
                                   native_error=f"artifact-stopped:Decode({native})", revert=("decode", code))
        # A tiny opening of a large shape must not be charged as a materialized
        # table against public_elements. No million-row tree is needed here.
        row = [tuple(range(1, FIELDS[field][0] + 1))]
        path = [bytes([i]) * 32 for i in range(20)]
        _, trace = authenticate(field, bytes(32), 1, 1 << 20, (1 << 20) - 1, row, path)
        root = bytes.fromhex(trace[-1]["output"])
        controls.check(subject, "large-committed-shape-small-opening", {
            0: frame(root_tag, root), 1: vector_wire(field, row),
            2: frame(path_tag, len(path).to_bytes(4, "little") + b"".join(path)),
            3: index_wire(1), 4: index_wire(1 << 20), 5: index_wire((1 << 20) - 1),
            6: boolean(False)}, trace=trace * 2)


def polynomial(controls):
    source = (FIXTURES / "polynomial.zkc").read_text()
    for field in FIELDS:
        subject = controls.compile("polynomial-" + field,
                                   source.replace("koala-bear.ext4-binomial3", field), "polynomial")
        ref = CosetReference(field)
        shift = tuple([3, *range(1, ref.degree)])
        coefficients = [ref.embed(2), tuple(range(1, ref.degree + 1)), ref.embed(7)]
        for label, values, size, at, flag in (
            ("empty", [], 1, 0, True), ("zero", [ref.zero] * 4, 8, 7, True),
            ("nonbase", coefficients, 32, 19, True),
            ("trailing-zero", coefficients + [ref.zero] * 5, 32, 31, True),
            ("selected-zero", coefficients, 32, 2**64 - 1, False),
        ):
            selected = at if flag else 0
            expected = ref.horner(values, ref.domain(shift, size)[selected])
            generator = ref.domain(ref.one, size)[1 % size]
            controls.check(subject, label, {0: vector_wire(field, values),
                1: field_wire(field, shift), 2: index_wire(size), 3: index_wire(at),
                4: boolean(flag), 5: field_wire(field, generator), 6: field_wire(field, expected)})
        # The first root call precedes point admission. Native output preflight,
        # mathematical domain admission, size refusal, shift, coordinate order
        # must all remain visible even when the final Boolean is unreached.
        for label, size, shift_value, at, error, revert in (
            ("zero-size", 0, ref.zero, 2**64 - 1, "refused:coset-size", ("source", 12)),
            ("nonpower-before-shift", 3, ref.zero, 3, "refused:coset-size", ("source", 12)),
            ("root-before-shift", 1 << 25, ref.zero, 0, "refused:coset-size", ("source", 12)),
            ("element-before-shift", 1 << 21, ref.zero, 0, "refused:coset-element-limit", ("source", 15)),
            ("shift-before-coordinate", 8, ref.zero, 8, "refused:coset-zero-shift", ("source", 13)),
            ("coordinate", 8, shift, 8, "refused:coset-coordinate", ("source", 14)),
        ):
            controls.check(subject, label, {0: vector_wire(field, []),
                1: field_wire(field, shift_value), 2: index_wire(size), 3: index_wire(at),
                4: boolean(True), 5: field_wire(field, ref.one), 6: field_wire(field, ref.zero)},
                expected=None, native_error=error, revert=revert)


def logical(controls):
    """Real common query controllers, repeated reads and physical selections."""
    field = "koala-bear.ext4-binomial3"
    word = [tuple(1 + 10 * i + j for j in range(4)) for i in range(16)]
    for grouping, order, authentication_policy in (
        ("individual", "natural", "per-query"),
        ("antipodal-pairs", "bit-reversed", "atomic-blocks"),
    ):
        paired = grouping == "antipodal-pairs"
        height = len(word) // (2 if paired else 1)
        rows = [[word[i], word[i + height]] if paired else [word[i]] for i in range(height)]
        if order == "bit-reversed":
            bits = (height - 1).bit_length()
            rows = [rows[int(f"{i:0{bits}b}"[::-1], 2)] for i in range(height)]
        selected = table_realization(f"rows.merkle-keccak256.{field}/0", grouping=grouping,
                                     table_order=order, authentication=authentication_policy)
        subject = controls.compile("logical-" + grouping, (FIXTURES / "authenticated_read.zkc").read_text(),
                                   "authenticated_read", (selected,))
        for position in (0, 7, 15):
            leaf = position % height
            if order == "bit-reversed":
                leaf = int(f"{leaf:0{bits}b}"[::-1], 2)
            root, row, path = opening_rows(field, rows, leaf)
            valid, trace = authenticate(field, root, len(row), height, leaf, row, path)
            if not valid:
                raise AssertionError("independent logical opening failed")
            inputs = {0: vector_wire(field, word), 1: index_wire(len(word)),
                      2: index_wire(position), 3: field_wire(field, word[position])}
            controls.check(subject, f"repeat-{position}", inputs, trace=trace * 2)
            inputs[3] = field_wire(field, (word[position][0] + 1, *word[position][1:]))
            controls.check(subject, f"value-false-{position}", inputs, expected=False, trace=trace * 2)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("compiler", "native-driver", "solc", "runner", "output"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    suites = {"authentication": authentication, "polynomial": polynomial, "logical": logical}
    parser.add_argument("--suite", action="append", choices=suites)
    args = parser.parse_args()
    for name in ("compiler", "native_driver", "solc", "runner", "output"):
        setattr(args, name, getattr(args, name).resolve())
    check_solc(args.solc)
    controls = Controls(args)
    for suite in args.suite or suites:
        suites[suite](controls)
    (args.output / "summary.json").write_text(json.dumps(controls.cases, indent=2) + "\n")
    print(json.dumps(controls.cases, indent=2))


if __name__ == "__main__":
    main()
