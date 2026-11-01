"""Generic identity binding, malformed attributes and normalized relation data.

Backend same-shape coefficient rejection lives in Rust matrix_identity tests.
"""

import copy
import hashlib
import json
from pathlib import Path
import struct
from cases import case
from commands import Commands
from scoped_sources import invocation, scoped_function
from tools import canonical_program, compiler, records

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
        json.dumps(["zkc.matrix/0", field, matrix], separators=(",", ":")).encode()
    ).hexdigest()


def source(field, parameters):
    call = invocation('exec.apply', ['!M'], ['i1'],
                      f'binding=@check,parameters=[{", ".join(parameters)}],site="check"')
    check = scoped_function('Check', ['!M'], ['i1'], call, ['%r'])
    return f'''!M = !data.field_matrix<"{field}">
module {{ "protocol.module"() ({{
 "runtime.binding"() {{sym_name="check",contract="matrix.identity_check",arguments=["{field}"],implementation="",function_type=(!runtime.scope,!M)->!exec.outcome<(i1)>}} : ()->()
 {check}
 "protocol.func"() ({{^entry(%m:!M):
   %ok = "protocol.local_call"(%m) {{callee=@Check,role="P",site="work"}} : (!M)->i1
   "protocol.return"(%ok) : (i1)->()
 }}) {{sym_name="main",function_type=(!M)->i1,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]}} : ()->()
}}) {{profile=#protocol.profile<protocol>}} : ()->() }}'''


def asset(digest):
    values = ", ".join(str(value if value < 128 else value - 256)
                       for value in bytes.fromhex(digest))
    return f'#runtime.asset<"zkc.matrix/0", [{values}]>'


for field in [*fields, "koala-bear.ext8-binomial3"]:
    expected = digest(field, ["4", "8", [["0", "1", "7"], ["1", "3", "11"]]])
    with case(f"{field} identity binding survives physical selection"):
        logical = commands.verified(source(field, [asset(expected)]))
        physical = commands.verified(logical, None, "--zkc-project-protocol", "--zkc-lower-math", "--zkc-select-physical")
        program = json.loads(commands.source("protocol-export", physical))
        canonical_program(commands, json.dumps(program))
        operations = [step for function in program[2] for step in function[4]
                      if step[0] == 'op']
        assert len(operations) == 1
        assert operations[0][3] == [expected]
    for index, bad in enumerate([[], [""], ["0" * 63], ["0" * 65], ["A" * 64], ["g" * 64],
                                 ["é" * 32], ["0" * 63 + " "], [expected, expected]]):
        with case(f"{field} rejects malformed identity parameter {index}"):
            # Digest spelling belongs to the byte reader; native attributes
            # carry the digest bytes and cannot express hex case or padding.
            malformed = copy.deepcopy(program)
            operation = next(step for function in malformed[2]
                             for step in function[4] if step[0] == 'op')
            operation[3] = bad
            canonical_program(commands, json.dumps(malformed),
                              refuses='interactive-kernel-parameters')
            commands.verified(source(field, [json.dumps(p, ensure_ascii=False) for p in bad]),
                              "interactive-kernel-parameters")

    for label, parameters, code in [
        ('missing', [], 'interactive-kernel-parameters'),
        ('duplicate', [asset(expected), asset(expected)], 'interactive-kernel-parameters'),
        ('wrong-format', [asset(expected).replace('zkc.matrix/0', 'zkc.other/0')],
         'interactive-kernel-parameters'),
        ('short-digest', [asset('00' * 31)], 'asset-reference'),
        ('long-digest', [asset('00' * 33)], 'asset-reference'),
    ]:
        with case(f"{field} rejects native identity {label}"):
            commands.verified(source(field, parameters), code)


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
