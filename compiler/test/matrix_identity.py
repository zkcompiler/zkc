"""Generic identity binding, malformed attributes and normalized relation data.

Backend same-shape coefficient rejection lives in Rust matrix_identity tests.
"""

import copy
import hashlib
import json
from pathlib import Path
import re
import struct
from cases import case
from commands import Commands
from tools import compiler, optimizer, records

fields = {
    "bls12-381.fr": 52435875175126190479447740508185965837690552500527637822603658699938581184513,
    "ristretto255.scalar": 7237005577332262213973186563042994240857116359379907606001950938285454250989,
    "koala-bear": 2130706433,
    "bn254.fr": 21888242871839275222246405745257275088548364400416034343698204186575808495617,
}


commands = Commands(records())


def run(tool, *args, text=None, refuses=None):
    return commands.run([tool, *args], stdin=text, refuses=refuses)


def digest(field, matrix):
    return hashlib.sha256(
        json.dumps(["zkc.matrix/1", field, matrix], separators=(",", ":")).encode()
    ).hexdigest()


def source(field, attrs, requirements="requires (Field(F))"):
    return f'''module {{
      fn Check<F: domain Field>(m:Matrix<F::Element>) -> (bool) {requirements} {{
        [check] let ok = matrix::identity_check::<F>(m) attributes ({attrs});
        return (ok);
      }}
      configure Concrete = Check(F="{field}");
      protocol Main {{ roles (P); inputs (P m:Matrix<"{field}"::Element>);
        outputs (P bool); local [call] P: let ok = Concrete(m); return (ok);
      }}
      instance concrete: Main {{roles (P=P);}} entry main = concrete;
    }}'''


for field in [*fields, "koala-bear.ext8-binomial3"]:
    expected = digest(field, ["4", "8", [["0", "1", "7"], ["1", "3", "11"]]])
    text = source(field, json.dumps(expected))
    logical = run(compiler, "protocol-import", "-", text=text)
    assert "algebra.matrix_identity_check" in logical and expected in logical
    assert "algebra.matrix_identity_check" in run(
        optimizer, "--verify-each", "--canonicalize", "--cse", text=logical
    )
    physical = run(compiler, "protocol-physical-ir", "-", text=text)
    run(optimizer, "--verify-each", text=physical)
    plan = json.loads(run(compiler, "protocol-compile", "-", text=text))
    assert json.loads(run(compiler, "protocol-export", "-", text=physical)) == plan
    run(
        compiler,
        "protocol-import",
        "-",
        text=source(field, json.dumps(expected), ""),
        refuses="generic-public-requirement",
    )
    for bad in [
        [],
        [""],
        ["0" * 63],
        ["0" * 65],
        ["A" * 64],
        ["g" * 64],
        ["é" * 32],
        ["0" * 63 + " "],
        [expected, expected],
    ]:
        attrs = ",".join(json.dumps(a) for a in bad)
        run(
            compiler,
            "protocol-import",
            "-",
            text=source(field, attrs),
            refuses="interactive-kernel-parameters",
        )
        # Actual IR independently refuses the modified digest, not just source.
        if len(bad) == 1:
            changed = logical.replace(expected, bad[0])
            run(
                optimizer,
                "--verify-each",
                text=changed,
                refuses="interactive-kernel-parameters",
            )


def binary(prime, rows, width=32):
    # Independent external R1CS author: five columns, three constraints, two
    # public values. Dimensions therefore pad to 4 x 8 in the generated view.
    header = struct.pack("<I", width) + prime.to_bytes(width, "little")
    header += struct.pack("<IIIIQI", 5, 1, 1, 2, 5, len(rows))
    terms = bytearray()
    for row in rows:
        for form in row:
            terms.extend(struct.pack("<I", len(form)))
            for column, coefficient in form:
                terms.extend(struct.pack("<I", column))
                terms.extend(coefficient.to_bytes(width, "little"))
    labels = b"".join(struct.pack("<Q", n) for n in range(5))
    result = b"r1cs" + struct.pack("<II", 1, 3)
    for kind, data in enumerate([header, terms, labels], 1):
        result += struct.pack("<IQ", kind, len(data)) + data
    return result


def hashes(ir):
    return set(re.findall(r'parameters = \["([0-9a-f]{64})"\]', ir))


directory = records()
path = Path(directory) / "relation.r1cs"
source_path = Path(directory) / "source.pir"
snapshot_path = Path(directory) / "snapshot.json"
views = [(field, "rank_one") for field in fields]
views.append(("bls12-381.fr", "multilinear"))
for field, view in views:
    with case(f"{field} {view} matrix identity"):
        prime = fields[field]
        dimensions = ["4", "8"] if view == "multilinear" else ["3", "5"]
        source_path.write_text(f"""module {{
          relation Circuit = r1cs("relation.r1cs");
          derive Rows = {view}(Circuit, public_matrices);
        }}""")
        rows = [
            [[(1, 7)], [(3, 11)], [(2, 13)]],
            [[(0, 2)], [(4, 5)], [(2, 17)]],
            [[(1, 19)], [], [(0, 23)]],
        ]
        path.write_bytes(binary(prime, rows))
        canonical = run(compiler, "protocol-resolve", source_path)
        # The source origin separately carries relation identity, while only
        # parameters on actual identity ops carry these matrix digests.
        ir = run(compiler, "protocol-import", "-", text=canonical)
        actual = hashes(ir)
        matrices = [
            [
                *dimensions,
                [
                    [str(r), str(c), str(a)]
                    for r, row in enumerate(rows)
                    for c, a in row[k]
                ],
            ]
            for k in range(3)
        ]
        expected = {digest(field, matrix) for matrix in matrices}
        assert actual == expected, (field, actual, expected)
        snapshot_path.write_text(canonical)
        data = json.loads(
            run(compiler, "protocol-relation-data", snapshot_path, "Rows")
        )
        assert data[4] == matrices
        # Reorder, duplicate, cancel and insert explicit zero terms before the
        # importer normalizes. Raw byte identity changes; all matrix pins stay.
        raw = copy.deepcopy(rows)
        raw[0][0] = [(4, 11), (1, 9), (3, 0), (1, prime - 2), (4, prime - 11)]
        path.write_bytes(binary(prime, raw, width=(prime.bit_length() + 7) // 8))
        normalized = run(compiler, "protocol-resolve", source_path)
        assert normalized == canonical
        # Coefficient-only mutation must change the generated pin at same shape.
        different = copy.deepcopy(rows)
        different[0][0][0] = (1, 8)
        path.write_bytes(binary(prime, different))
        altered = run(compiler, "protocol-resolve", source_path)
        altered_ir = run(compiler, "protocol-import", "-", text=altered)
        assert altered != canonical and hashes(altered_ir) != actual

print(f"matrix identity: {commands.save()} compiler/IR/normalization checks passed")
