"""Structured AIR survives MLIR transport and drives native analysis,
scheduling and trace evaluation, including residual localization."""

import json
from pathlib import Path
from commands import Commands
from tools import compiler, corpus, optimizer, records

repository = Path(__file__).resolve().parents[2]


commands = Commands(records())


def run(tool, *args, data=None, error=None):
    """These tools answer in bytes, and reading them is the caller's business."""
    result = commands.attempt([tool, *args], stdin=data, text=False)
    if error:
        assert result.returncode > 0 and error.encode() in result.stderr, result.stderr
    else:
        assert not result.returncode, result.stderr
    return result.stdout


directory = records()
cases = corpus / "air"
relation = directory / "relation.json"
trace = directory / "trace.json"
statement = directory / "statement.json"
# Every field the corpus states the same quadratic case over. Naming the fields
# the glob must find keeps an empty match a failure here rather than three
# unbound names further down.
fields = sorted(cases.glob("quadratic-*.json"))
assert [path.stem for path in fields] == [
    "quadratic-bls12-381.fr",
    "quadratic-koala-bear",
    "quadratic-ristretto255.scalar",
], fields
for path in fields:
    case = json.loads(path.read_text())
    relation.write_text(json.dumps(case["air"]))
    trace.write_text(json.dumps(case["trace"]))
    statement.write_text(json.dumps(case["statement"]))
    analysis = json.loads(run(compiler, "relation-air-inspect", relation))
    ir = run(compiler, "relation-air-import", relation, "Trace")
    assert b"relation.air @Trace" in ir and b"lookahead" in ir
    canonical = run(optimizer, "--verify-each", data=ir)
    module = directory / "trace.mlir"
    module.write_bytes(canonical)
    encoded = run(compiler, "relation-air-export", module)
    assert json.loads(encoded) == json.loads(
        run(compiler, "relation-air-read", relation)
    )
    relation.write_bytes(encoded)
    assert json.loads(run(compiler, "relation-air-inspect", relation)) == analysis
    plan = json.loads(run(compiler, "relation-air-plan", relation, "4"))
    assert plan["scheduled_reads"] == 4 and plan["dense_trace_cells"] == 32
    polynomial = json.loads(
        run(compiler, "relation-air-polynomial", relation, "4", "4", "3")
    )
    assert polynomial["quotient_chunks"] == 1
    assert [c["quotient_degree"] for c in polynomial["constraints"]] == [3, 2, 2]
    for args, code in (
        (("01", "4", "3"), "air-polynomial-parameter"),
        (("-1", "4", "3"), "air-polynomial-parameter"),
        (("4294967296", "4", "3"), "air-polynomial-parameter"),
        (("0", "4", "3"), "air-polynomial-height"),
        (("4", "3", "3"), "air-polynomial-domain-size"),
        (("4", "4", "2"), "air-polynomial-trace-degree"),
    ):
        run(compiler, "relation-air-polynomial", relation, *args, error=code)
    result = json.loads(
        run(compiler, "relation-air-evaluate", relation, trace, statement)
    )
    assert result["satisfied"] and result["scheduled_reads"] == 4
    case["statement"][1] = "257"
    statement.write_text(json.dumps(case["statement"]))
    assert not json.loads(
        run(compiler, "relation-air-evaluate", relation, trace, statement)
    )["satisfied"]
    for height in ("0", "01", "-1", "65537", "99999999999999999999"):
        run(compiler, "relation-air-plan", relation, height, error="air-height")
    run(
        optimizer,
        data=ir.replace(b"columns = 8 : i64", b"columns = -1 : i64"),
        error="air-ir-attribute",
    )
    run(
        optimizer,
        data=ir.replace(b"columns = 8 : i64", b"extra = true, columns = 8 : i64"),
        error="air-ir-attribute",
    )
    run(
        optimizer,
        data=ir.replace(b'field = "', b'field = "\\FF', 1),
        error="air-ir-attribute",
    )
    run(
        compiler, "relation-air-import", relation, "bad-name", error="air-ir-symbol"
    )
# Written to be refused, each by the command that can see the reason: an
# unsupported operation and an understated degree at admission, a window and a
# height against the trace, a field mismatch only once the trace is supplied.
for name, command, diagnostic in (
    ("lookup", "relation-air-read", "air-unsupported-operation"),
    ("understated-degree", "relation-air-read", "air-degree-declaration"),
    ("last-window", "relation-air-plan", "air-window-out-of-range"),
    ("zero-height", "relation-air-plan", "air-height"),
    ("wrong-field", "relation-air-evaluate", "air-trace-field"),
):
    case = json.loads((cases / f"{name}.json").read_text())
    relation.write_text(json.dumps(case["air"]))
    trace.write_text(json.dumps(case["trace"]))
    statement.write_text(json.dumps(case["statement"]))
    options = {
        "relation-air-plan": [str(case["trace"]["height"])],
        "relation-air-evaluate": [str(trace), str(statement)],
    }.get(command, [])
    run(compiler, command, relation, *options, error=diagnostic)

# A declared degree of four is admitted and inspected as four, so the degree
# check refuses an understatement rather than anything above a fixed ceiling.
case = json.loads((cases / "degree-four.json").read_text())
relation.write_text(json.dumps(case["air"]))
analysis = json.loads(run(compiler, "relation-air-inspect", relation))
assert analysis["constraints"][0]["expression_degree"] == 4, analysis

# A violation is found and located wherever it sits, including at either end of
# the trace: the residual that is not zero is the one the case was built around.
for name, constraint, row in (
    ("first-violation-koala-bear", 1, 0),
    ("last-violation-koala-bear", 2, 3),
):
    case = json.loads((cases / f"{name}.json").read_text())
    relation.write_text(json.dumps(case["air"]))
    trace.write_text(json.dumps(case["trace"]))
    statement.write_text(json.dumps(case["statement"]))
    result = json.loads(
        run(compiler, "relation-air-evaluate", relation, trace, statement)
    )
    assert not result["satisfied"], name
    violated = [
        (one["constraint"], one["row"])
        for one in result["residuals"]
        if one["value"] != "0"
    ]
    assert violated == [(constraint, row)], (name, violated)

print(f"{commands.save()} AIR IR/consumer checks passed")
