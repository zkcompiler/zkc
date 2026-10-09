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
from tools import compiler, records

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


def source(field, parameters):
    return f'''!M = tensor<?x?x!algebra.field<"{field}">>
module {{ "protocol.module"() ({{
 "local.binding"() {{sym_name="check",contract="matrix.identity_check",arguments=["{field}"],implementation=""}} : ()->()
 local.func @Check(%m:!M)->i1 attributes {{logical_origin=["Check",[]]}} {{
   %ok = "algebra.exec.matrix_identity_check"(%m) {{binding=@check,parameters={json.dumps(parameters, ensure_ascii=False)},site="check"}} : (!M)->i1
   local.return %ok : i1
 }}
 "protocol.func"() ({{^entry(%m:!M):
   %ok = "protocol.local_call"(%m) {{callee=@Check,role="P",site="work"}} : (!M)->i1
   "protocol.return"(%ok) : (i1)->()
 }}) {{sym_name="main",function_type=(!M)->i1,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]}} : ()->()
}}) {{profile=#protocol.profile<protocol>}} : ()->() }}'''

for field in [*fields, "koala-bear.ext8-binomial3"]:
    expected = digest(field, ["4", "8", [["0", "1", "7"], ["1", "3", "11"]]])
    logical = commands.verified(source(field, [expected]))
    physical = commands.verified(logical, None, "--zkc-project-protocol", "--zkc-lower-math", "--zkc-select-physical")
    assert expected in commands.source("protocol-export", physical)
    for bad in [[], [""], ["0" * 63], ["0" * 65], ["A" * 64], ["g" * 64],
                ["é" * 32], ["0" * 63 + " "], [expected, expected]]:
        commands.verified(source(field, bad), "interactive-kernel-parameters")


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
for field, prime in fields.items():
    with case(f"{field} normalized matrix identity"):
        rows = [
            [[(1, 7)], [(3, 11)], [(2, 13)]],
            [[(0, 2)], [(4, 5)], [(2, 17)]],
            [[(1, 19)], [], [(0, 23)]],
        ]
        path.write_bytes(binary(prime, rows))
        canonical = run(compiler, "relation-read", path)
        actual = json.loads(run(compiler, "relation-matrices", path))
        matrices = [["4", "8", [[str(r), str(c), str(a)] for r,row in enumerate(rows)
                                    for c,a in row[k]]] for k in range(3)]
        assert actual == matrices
        ir = run(compiler, "relation-import", path)
        assert json.loads(run(compiler, "relation-export", "-", text=ir)) == json.loads(canonical)
        raw = copy.deepcopy(rows)
        raw[0][0] = [(4, 11), (1, 9), (3, 0), (1, prime - 2), (4, prime - 11)]
        path.write_bytes(binary(prime, raw, width=(prime.bit_length() + 7) // 8))
        assert run(compiler, "relation-read", path) == canonical
        assert json.loads(run(compiler, "relation-matrices", path)) == matrices
        different = copy.deepcopy(rows)
        different[0][0][0] = (1, 8)
        path.write_bytes(binary(prime, different))
        altered = json.loads(run(compiler, "relation-matrices", path))
        assert {digest(field, m) for m in altered} != {digest(field, m) for m in matrices}
print(f"matrix identity: {commands.save()} compiler/IR/normalization checks passed")
