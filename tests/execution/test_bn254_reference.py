#!/usr/bin/env python3
"""BN254 native/Lean differential checks; all generated files stay in output.

The independently materialized Lean ZMod interpreter supplies the arithmetic
comparison, bounded to cosets <=128. Pairing tests check formation and execution
using an explicitly selected trusted public primitive service; they do not
independently verify curve or pairing equations. Matrix payloads are encoded in
Lean, with SHA256 supplied through the explicit hash boundary.
"""
import copy
import hashlib
import json
from pathlib import Path
import random
import shutil
from types import SimpleNamespace

from journal import Journal
from toolchain import Toolchain, records

F = "bn254.fr"
MODULUS = 21888242871839275222246405745257275088548364400416034343698204186575808495617
ROOT = Path(__file__).resolve().parents[2]

# The Lean reference these results are compared against.
CHECKER = "interactive-protocol"


def main(groth16=None, r1cs=None):
    """The differential. `groth16` and `r1cs` name an authored Groth16 source and
    the compiled relation its circuit depends on, which come from the Circom and
    snarkjs generation under `tests/groth16` rather than from any build here."""
    tools = Toolchain()
    journal = Journal(records())
    args = SimpleNamespace(compiler=tools.compiler, runtime=tools.runtime,
                           lean=tools.checker(CHECKER), primitive=tools.primitive,
                           output=journal.directory, groth16=groth16, r1cs=r1cs)
    checks = 0
    cases = []

    def run(command, refusal=None):
        nonlocal checks
        checks += 1
        return journal.json(command, refuses=refusal)

    def save(name, value):
        return journal.write(name + ".json", value)

    def ty(kind):
        return kind if kind in ("index", "indices", "bool") else kind + ":" + F

    def wire(kind, value):
        header = b"ZKCV\x01" + bytes([{"field": 40, "vector": 41, "polynomial": 42,
            "round": 43, "matrix": 45, "index": 31, "indices": 32, "bool": 5}[kind]])
        def le(n, width=32):
            return int(n).to_bytes(width, "little")
        if kind == "matrix":
            rows, cols, entries = value
            return header + le(rows, 4) + le(cols, 4) + le(len(entries), 4) + b"".join(
                le(r, 4) + le(c, 4) + le(v) for r, c, v in entries)
        if kind == "bool":
            return header + bytes([value == "true"])
        if kind in ("index", "field"):
            return header + le(value, 8 if kind == "index" else 32)
        prefix = b"" if kind == "round" else le(len(value), 4)
        return header + prefix + b"".join(le(x, 8 if kind == "indices" else 32) for x in value)

    def strings(value):
        return list(map(strings, value)) if isinstance(value, list) else str(value)

    def source(contract, kinds, outputs, attrs):
        ins = [["x" + str(i), ty(k)] for i, k in enumerate(kinds)]
        outs = ["y" + str(i) for i in range(len(outputs))]
        return ["zkc.protocol/1", [["kernel", contract, [F], ""]],
                [["function", "Work", ins, list(map(ty, outputs)),
                  [["op", "work", "kernel", attrs, [x[0] for x in ins], outs],
                   ["return", outs]], ["Work", []]]],
                [["protocol", "Main", ["P"], [], [[n, "P", t] for n, t in ins],
                  [["P", ty(k)] for k in outputs], [],
                  [["local", "work", "P", "Work", [x[0] for x in ins], outs], ["return", outs]]]],
                [["instance", "root", "Main", [], [], [["P", "P"]]]], [["entry", "main", "root"]]]

    def exercise(label, contract, inputs, outputs, attrs=None, error=None):
        kinds = [k for k, _ in inputs]
        sp = save(label + "-source", source(contract, kinds, outputs, attrs or []))
        plan = run([args.compiler, "protocol-compile", sp])
        pp = save(label + "-physical", plan)
        run([args.lean, "--check-generic", sp, pp])
        native_inputs = [["x" + str(i), ["wire", wire(k, v).hex()]] for i, (k, v) in enumerate(inputs)]
        logical_inputs = [["x" + str(i), [ty(k), strings(v)]] for i, (k, v) in enumerate(inputs)]
        np = save(label + "-native-inputs", ["zkc.run/2", "main", "bn254-test", [],
                    [["P", [], native_inputs, []]], []])
        rp = save(label + "-reference-inputs", ["zkc.reference-inputs/1", "main", "bn254-test",
                    [["P", logical_inputs]], [], [], []])
        ref = run([args.lean, "--generic-reference", sp, rp])
        if contract == "matrix.identity_check":
            assert ref[3][0] == "pending-primitive", ref
            request = ref[4][-1][1]
            assert request[:2] == ["zkc.hash/1", "sha256"], request
            payload = bytes.fromhex(request[2])
            expected_payload = json.dumps(["zkc.matrix/1", F, strings(inputs[0][1])], separators=(",", ":")).encode()
            assert payload == expected_payload, (payload, expected_payload)
            fixture = json.loads(rp.read_text())
            fixture[5].append([request, ["ok", hashlib.sha256(payload).hexdigest()]])
            rp = save(label + "-reference-inputs", fixture)
            ref = run([args.lean, "--generic-reference", sp, rp])
        actual = run([args.runtime, "run-protocol", sp, pp, np, args.lean])
        save(label + "-lean", ref)
        save(label + "-native", actual)
        if error:
            assert ref[3][:2] == ["refused", error], (label, ref[3])
            assert actual["outcome"][0] == "stopped", (label, actual)
        else:
            assert ref[3][0] == "returned", (label, ref[3])
            expected = []
            for spelling, value in ref[3][1]:
                kind = spelling.split(":")[0]
                if kind == "bool":
                    expected.append(["bool", value == "true"])
                elif kind == "index":
                    expected.append(["index", int(value)])
                else:
                    expected.append(["wire", kind, wire(kind, value).hex()])
            assert actual["outcome"] == ["returned", {"P": expected}], (label, actual["outcome"], expected)
        cases.append(label)
        return ref[3]

    rnd = random.Random(254)
    for operation in ("add", "sub", "mul"):
        exercise(operation, "field." + operation, [("field", MODULUS-1), ("field", 13)], ["field"])
    exercise("inverse", "field.inverse", [("field", 7)], ["field"])
    exercise("inverse-zero", "field.inverse", [("field", 0)], ["field"], error="inverse-zero")
    exercise("dot", "vector.dot", [("vector", [MODULUS-1, 3, 5]), ("vector", [2, 4, 6])], ["field"])
    exercise("dot-shape", "vector.dot", [("vector", [1]), ("vector", [])], ["field"], error="vector-shape")
    matrix = [2, 3, [[0, 1, 3], [1, 0, 4], [1, 2, MODULUS-1]]]
    exercise("matrix", "matrix.mul_vector", [("matrix", matrix), ("vector", [2, 5, 7])], ["vector"])
    exercise("transpose", "matrix.transpose_mul_vector", [("matrix", matrix), ("vector", [2, 3])], ["vector"])
    exercise("bilinear", "matrix.bilinear", [("matrix", matrix), ("vector", [2, 3]), ("vector", [2, 5, 7])], ["field"])
    exercise("matrix-shape", "matrix.mul_vector", [("matrix", matrix), ("vector", [2])], ["vector"], error="matrix-shape")
    digest = hashlib.sha256(json.dumps(["zkc.matrix/1", F, strings(matrix)], separators=(",", ":")).encode()).hexdigest()
    exercise("matrix-identity", "matrix.identity_check", [("matrix", matrix)], ["bool"], [digest])
    exercise("matrix-identity-wrong", "matrix.identity_check", [("matrix", matrix)], ["bool"], ["0" * 64])
    exercise("slice", "vector.slice", [("vector", [1,2,3]), ("index", 1), ("index", 2)], ["vector"])
    exercise("slice-empty", "vector.slice", [("vector", [1,2,3]), ("index", 3), ("index", 0)], ["vector"])
    exercise("slice-bounds", "vector.slice", [("vector", [1,2,3]), ("index", 2**64-1), ("index", 2)], ["vector"], error="vector-slice-bounds")
    exercise("horner", "poly.univariate_evaluate", [("polynomial", [2, 3, 4]), ("field", 5)], ["field"])
    exercise("divide", "poly.divide_opening", [("polynomial", [2, 3, 4]), ("field", 5), ("field", 117)], ["polynomial"])
    exercise("false-opening", "poly.divide_opening", [("polynomial", [2, 3, 4]), ("field", 5), ("field", 116)], ["polynomial"], error="polynomial-opening-value")
    for n in (2, 8, 32, 128):
        cs = [rnd.randrange(MODULUS) for _ in range(min(n, 7))]
        result = exercise(f"fft{n}", "poly.coset_evaluate", [("polynomial", cs), ("field", 7), ("index", n)], ["vector"])
        xs = list(map(int, result[1][0][1]))
        back = exercise(f"ifft{n}", "poly.coset_interpolate", [("vector", xs), ("field", 7)], ["polynomial"])
        assert list(map(int, back[1][0][1])) == cs
        exercise(f"fold{n}", "poly.even_odd_fold", [("vector", xs), ("field", 7), ("field", 11)], ["vector"])
        exercise(f"quotient{n}", "poly.opening_quotient", [("vector", xs), ("field", 7), ("field", 0), ("field", cs[0])], ["vector"])
    exercise("domain-root", "poly.domain_root", [("index", 65536)], ["field"])
    exercise("nonpower", "poly.domain_root", [("index", 3)], ["field"], error="coset-size")
    exercise("zero-shift", "poly.domain_points", [("field", 0), ("index", 4)], ["vector"], error="coset-zero-shift")

    # Generic associated groups must survive specialization and participant formation.
    pir = '''module {
      fn Pair<F: domain Field>(left: Vector<F::PairingG1::Element>, right: Vector<F::PairingG2::Element>)
          -> bool requires (PairingField(F)) { let ok = pairing::check::<F>(left,right); return ok; }
      configure Concrete = Pair(F=bn254.fr);
      protocol Main { roles(V); inputs(V left: Vector<bn254.g1::Element>, V right: Vector<bn254.g2::Element>);
        outputs(V bool); local V: let ok = Concrete(left,right); return ok; }
      instance root: Main {roles(V=V);} entry main=root;
    }'''
    path = args.output / "pairing.pir"
    path.write_text(pir)
    sp = save("pairing-source", run([args.compiler, "protocol-source", path]))
    plan = run([args.compiler, "protocol-compile", path])
    pp = save("pairing-physical", plan)
    run([args.lean, "--check-generic", sp, pp])
    for old, new, refusal in [("bn254.g1", "bn254.g2", "binding-type"),
                              ("bn254.g2", "bn254.g1", "binding-type"),
                              ("bn254.fr", "bls12-381.fr", "binding-static-arguments")]:
        mutant = json.loads(json.dumps(plan).replace(old, new))
        run([args.lean, "--check-generic", sp, save("swapped-" + old, mutant)], refusal)
    authored = json.loads(sp.read_text())
    wrong_operands = copy.deepcopy(authored)
    wrong_operands[1][0][6][0][5].reverse()
    run([args.lean, "--check-generic", save("source-operands-swapped", wrong_operands), pp],
        "generic-requirement-not-provided")
    no_capability = copy.deepcopy(authored)
    no_capability[1][0][3] = [["Field", ["F"]]]
    run([args.lean, "--check-generic", save("source-missing-pairing-field", no_capability), pp],
        "generic-requirement-not-provided")
    # Both substituted physical types are valid in isolation. Refusal must
    # preserve the source's G1/G2 distinction, not merely reject bad spelling.
    same_groups = json.loads(json.dumps(plan).replace(
        "groups:bn254.g2@arkworks.bn254-g2-vector/1",
        "groups:bn254.g1@arkworks.bn254-g1-vector/1"))
    run([args.lean, "--check-generic", sp, save("valid-type-wrong-group", same_groups)],
        "binding-operation-signature")

    # The public service supplies actual points/pairings. This checks source
    # orchestration and native agreement; these kernels share upstream trust.
    def primitive(name, arguments, inputs):
        request = ["zkc.public-primitive/1", [], name, arguments, [], inputs]
        reply = run([args.primitive, save("primitive-request", request)])
        assert reply[0] == "ok", reply
        return reply[1:]

    g1 = primitive("curve.generator", ["bn254.g1"], [])[0]
    g2 = primitive("curve.generator", ["bn254.g2"], [])[0]
    neg = primitive("curve.neg", ["bn254.g1"], [g1])[0]
    def groups(domain, points):
        header = b"ZKCV\x01" + bytes([47 if domain == "bn254.g1" else 49])
        return ["groups:" + domain, (header + len(points).to_bytes(4, "little") +
            b"".join(bytes.fromhex(p[1])[6:] for p in points)).hex()]

    for label, left, right, expected in [
        ("pair-true", [g1, neg], [g2, g2], True),
        ("pair-false", [g1], [g2], False),
        ("pair-empty", [], [], True),
        ("pair-length", [g1], [], None),
    ]:
        values = [["left", groups("bn254.g1", left)], ["right", groups("bn254.g2", right)]]
        ref_inputs = ["zkc.reference-inputs/1", "main", "bn254-pair", [["V", values]], [], [], []]
        for _ in range(12):
            ref = run([args.lean, "--generic-reference", sp, save(label + "-reference-inputs", ref_inputs)])
            if ref[3][0] != "pending-primitive":
                break
            request = ref[4][-1][1]
            assert request[2] in ("validate", "pairing.check"), request
            answer = primitive(request[2], [] if request[2] == "validate" else request[3], request[5])
            decoded = []
            for kind, raw in answer:
                assert kind == "bool"
                b = bytes.fromhex(raw)
                assert b[:6] == b"ZKCV\x01\x05" and b[6:] in (b"\x00", b"\x01")
                decoded.append([kind, "true" if b[6] else "false"])
            ref_inputs[5].append([request, ["ok", decoded]])
        native = ["zkc.run/2", "main", "bn254-pair", [], [["V", [],
            [[name, ["wire", value[1]]] for name, value in values], []]], []]
        actual = run([args.runtime, "run-protocol", sp, pp, save(label + "-native-inputs", native), args.lean])
        save(label + "-lean", ref)
        save(label + "-native", actual)
        if expected is None:
            assert ref[3][:2] == ["refused", "pairing-length"], ref[3]
            assert actual["outcome"][0] == "stopped", actual
        else:
            assert ref[3] == ["returned", [["bool", str(expected).lower()]]], ref[3]
            assert actual["outcome"] == ["returned", {"V": [["bool", expected]]}], actual

    source_json = json.loads(sp.read_text())
    envelope = ["zkc.relations/1", [[], []], source_json]
    run([args.lean, "--check-generic", save("relation-envelope", envelope), pp], "generic-library")
    if args.groth16:
        if not args.r1cs:
            raise ValueError("a Groth16 source needs the compiled relation its circuit resolves")
        staged = args.output / "groth16"
        staged.mkdir(exist_ok=True)
        shutil.copyfile(args.groth16, staged / "protocol.pir")
        shutil.copyfile(args.r1cs, staged / "circuit.r1cs")
        snapshot = save("groth16-snapshot", run([args.compiler, "protocol-resolve", staged / "protocol.pir"]))
        gs = save("groth16-source", run([args.compiler, "protocol-materialize", snapshot]))
        gp = save("groth16-physical", run([args.compiler, "protocol-compile", gs]))
        run([args.lean, "--check-generic", gs, gp])
    print(json.dumps({"status": "pass", "checks": checks, "arithmetic_cases": len(cases),
        "max_transform_size": 128, "pairing_scope": "structural and executed with trusted shared public primitive service",
        "groth16_checked": bool(args.groth16), "slice_checked": True}))


def test_bn254_reference():
    main()


if __name__ == "__main__":
    main()
