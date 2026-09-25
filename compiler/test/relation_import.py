"""External container, canonical subject, structured IR and staging controls."""

import copy
import json
import struct
from cases import case
from commands import Commands
from tools import compiler, optimizer, records

FIELDS = {
    "bn254.fr": 21888242871839275222246405745257275088548364400416034343698204186575808495617,
    "bls12-381.fr": 52435875175126190479447740508185965837690552500527637822603658699938581184513,
    "ristretto255.scalar": 7237005577332262213973186563042994240857116359379907606001950938285454250989,
    "koala-bear": 2130706433,
}


commands = Commands(records())


def invoke(command, *args, refuses=None, data=None):
    """These tools answer in bytes, and reading them is the caller's business."""
    result = commands.attempt([command, *args], stdin=data, text=False)
    said = result.stderr.decode(errors="replace")
    if refuses:
        assert result.returncode > 0 and refuses in said, (args, refuses, said)
    else:
        assert result.returncode == 0, (args, said)
    return result.stdout


def container(
    prime,
    rows,
    *,
    width=None,
    columns=4,
    outputs=1,
    inputs=1,
    private=1,
    labels=None,
    version=1,
    kinds=(1, 2, 3),
):
    """Independent R1CS-v1 fixture author; no production serializer reused."""
    width = width or (prime.bit_length() + 7) // 8
    labels = list(range(columns)) if labels is None else labels
    header = struct.pack("<I", width) + prime.to_bytes(width, "little")
    header += struct.pack(
        "<IIIIQI", columns, outputs, inputs, private, columns, len(rows)
    )
    constraints = bytearray()
    for row in rows:
        for form in row:
            constraints += struct.pack("<I", len(form))
            for column, coefficient in form:
                constraints += struct.pack("<I", column) + coefficient.to_bytes(
                    width, "little"
                )
    sections = (header, constraints, b"".join(struct.pack("<Q", x) for x in labels))
    result = b"r1cs" + struct.pack("<II", version, len(kinds))
    for kind, section in zip(kinds, sections, strict=True):
        result += struct.pack("<IQ", kind, len(section)) + section
    return result


def canonical(field, rows=None, columns=4, outputs=1, inputs=1):
    if rows is None:
        rows = [[[["2", "1"]], [["3", "1"]], [["1", "1"]]]]
    return ["zkc.relation.r1cs/1", field, str(columns), str(outputs), str(inputs), rows]


directory = records()
source = directory / "relation.json"
binary = directory / "relation.r1cs"
irfile = directory / "relation.mlir"

def run(mode, model, *args, refuses=None):
    source.write_text(json.dumps(model))
    return invoke(compiler, mode, source, *args, refuses=refuses)

for field, prime in FIELDS.items():
    model = canonical(field)
    baseline = json.loads(run("relation-inspect", model))
    assert baseline["columns"] == 4 and baseline["nonzeros"] == 3
    raw_rows = [[[(2, 2), (0, 0), (2, prime - 1)], [(3, 1)], [(1, 1)]]]
    binary.write_bytes(container(prime, raw_rows))
    assert json.loads(invoke(compiler, "relation-read", binary)) == model
    assert (
        json.loads(invoke(compiler, "relation-inspect", binary))["subject"]
        == baseline["subject"]
    )
    # Word-rounded external encoding has the same exact field and relation.
    width = ((prime.bit_length() + 63) // 64) * 8
    binary.write_bytes(container(prime, raw_rows, width=width))
    assert json.loads(invoke(compiler, "relation-read", binary)) == model
    ir = run("relation-import", model, "Circuit")
    assert b"relation.r1cs @Circuit" in ir
    invoke(optimizer, "--verify-each", data=ir)
    irfile.write_bytes(ir)
    assert json.loads(invoke(compiler, "relation-export", irfile)) == model
    # JSON is canonical; only the external binary boundary normalizes terms.
    for form in ([["2", "0"]], [["2", "1"], ["2", "1"]], [["3", "1"], ["2", "1"]]):
        bad = copy.deepcopy(model)
        bad[5][0][0] = form
        run("relation-read", bad, refuses="relation-noncanonical")
    for literal in ("01", "-1", str(prime), " 1", "1.0"):
        bad = copy.deepcopy(model)
        bad[5][0][0][0][1] = literal
        run("relation-read", bad, refuses="relation-coefficient")
    for index in ("4", "65536"):
        bad = copy.deepcopy(model)
        bad[5][0][0][0][0] = index
        run("relation-read", bad, refuses="relation-column")
    for dimension in ("0", "65537", "01", "-1", "999999999999999999999"):
        bad = copy.deepcopy(model)
        bad[2] = dimension
        run("relation-read", bad, refuses="relation-dimension")
    duplicate = copy.deepcopy(model)
    duplicate[5] *= 2
    duplicated_ir = run("relation-import", duplicate, "Circuit")
    optimized = invoke(optimizer, "--zkc-deduplicate-relations", data=duplicated_ir)
    irfile.write_bytes(optimized)
    assert json.loads(invoke(compiler, "relation-export", irfile)) == model
    assert (
        baseline["subject"]
        != json.loads(run("relation-inspect", duplicate))["subject"]
    )
    changed = copy.deepcopy(model)
    changed[3:5] = ["0", "2"]
    assert (
        baseline["subject"]
        != json.loads(run("relation-inspect", changed))["subject"]
    )
    # Local libraries currently need a field with table/point/PCS support.
    if field == "bls12-381.fr":
        code = run("relation-compile", model, "Circuit")
        assert b"vector::scatter_sum" in code and b"vector::constant" in code
        invoke(compiler, "protocol-import", "-", data=code)
        staged = run("relation-compile-data", model, "Circuit")
        assert b"matrix::mul_vector" in staged and b"matrix::bilinear" in staged
        assert b"vector::scatter_sum" not in staged
        invoke(compiler, "protocol-import", "-", data=staged)
        changed[3:5] = model[3:5]
        changed[5][0][0][0][1] = "2"
        assert run("relation-compile-data", changed, "Circuit") != staged
        assert b"matrix::identity_check" in staged
        assert run("relation-compile", changed, "Circuit") != code
        matrices = json.loads(run("relation-matrices", model))
        assert matrices == [["2", "4", [["0", str(c), "1"]]] for c in (2, 3, 1)]

prime = FIELDS["koala-bear"]
rows = [[[(2, 1)], [(3, 1)], [(1, 1)]]]
raw = container(prime, rows)
for prefix in range(len(raw)):
    binary.write_bytes(raw[:prefix])
    result = commands.attempt([compiler, "relation-read", binary], text=False)
    assert result.returncode > 0, ("accepted truncated binary", prefix)
for data, code in (
    (raw + b"extra", "relation-trailing-data"),
    (container(prime, rows, version=2), "relation-version"),
    (container(prime, rows, kinds=(1, 2, 4)), "relation-sections"),
    (container(prime, rows, kinds=(1, 2, 2)), "relation-sections"),
    (container(101, rows), "relation-field"),
    (container(prime, rows, labels=[1, 1, 2, 3]), "relation-wire-map"),
    (container(prime, rows, labels=[0, 1, 2, 4]), "relation-wire-map"),
    (
        container(prime, [[[(2, prime)], [(3, 1)], [(1, 1)]]]),
        "relation-coefficient",
    ),
    (container(prime, [[[(4, 1)], [(3, 1)], [(1, 1)]]]), "relation-column"),
):
    with case(f"malformed container refused as {code}"):
        binary.write_bytes(data)
        invoke(compiler, "relation-read", binary, refuses=code)
for raw_json, code in (
    (b"[" * 20, "relation-depth-limit"),
    (b'["' + b"a" * 1025, "relation-string-limit"),
    (b'{"unexpected":1}', "relation-json"),
    (b'["\\q"]', "relation-json"),
):
    invoke(compiler, "relation-read", "-", data=raw_json, refuses=code)
invoke(
    compiler,
    "relation-import",
    "-",
    "bad-name",
    data=json.dumps(canonical("koala-bear")).encode(),
    refuses="relation-symbol",
)

# Consumer limits are distinct from relation formation. Large sparse data
# must remain usable even when embedding its indices into code is refused.
large = canonical("bls12-381.fr", rows=[[[["0", "1"]], [], []]] * 16384)
run("relation-compile", large, refuses="relation-specialization-attributes")
assert b"matrix::mul_vector" in run("relation-compile-data", large)
public = canonical("bls12-381.fr", rows=[], columns=130, outputs=0, inputs=129)
run("relation-compile-data", public, refuses="relation-public-opening-limit")
long_coefficients = canonical(
    "bls12-381.fr",
    rows=[[[["0", str(FIELDS["bls12-381.fr"] - 1)]], [], []]] * 15000,
)
run("relation-compile", long_coefficients, refuses="source-limit")
for rows, code in (
    ([[[], []]], "relation-row"),
    ([[[["0"]], [], []]], "relation-term"),
):
    run("relation-read", canonical("koala-bear", rows=rows), refuses=code)
irfile.write_text("module {}")
invoke(compiler, "relation-export", irfile, refuses="relation-module")
irfile.write_text("not valid MLIR")
invoke(compiler, "relation-export", irfile, refuses="relation-ir")
invoke(compiler, "relation-unknown", "-", refuses="relation-command")
for opening, closing, value in (("[", "]", "0 : i64"), ("<tuple", ">", "i1")):
    # Array attributes and recursively nested types exercise the pre-parser
    # boundary, including input far smaller than the byte limit.
    irfile.write_text(
        "module attributes {test.deep = "
        + opening * 16384
        + value
        + closing * 16384
        + "} {}"
    )
    invoke(compiler, "relation-export", irfile, refuses="relation-depth-limit")
    invoke(compiler, "relation-air-export", irfile, refuses="air-ir-depth-limit")

print(f"{commands.save()} relation import/IR/staging checks passed")
