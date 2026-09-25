"""Maintained compiled-relation loading, ownership and generated AIR execution."""

import copy
import hashlib
import json
from pathlib import Path
from commands import Commands
from tools import compiler, records

FIELD = "bls12-381.fr"
PRIME = 52435875175126190479447740508185965837690552500527637822603658699938581184513


commands = Commands(records())


def run(mode, path, refuses=None, extra=()):
    return commands.run([compiler, mode, path, *extra], refuses=refuses)


def evaluate(function, bindings, arguments):
    """Independent finite integer execution of generated ordinary PIR ops."""
    env = {
        parameter[0]: value
        for parameter, value in zip(function[2], arguments, strict=True)
    }
    for instruction in function[4]:
        if instruction[0] == "return":
            return [env[name] for name in instruction[1]]
        tag, _site, binding, attrs, inputs, outputs = instruction
        assert tag == "op"
        contract = bindings[binding]
        args = [env[name] for name in inputs]
        if contract == "vector.length_check":
            value = len(args[0]) == int(attrs[0])
        elif contract == "control.require":
            assert args[0], "failed generated input guard"
            continue
        elif contract == "vector.at":
            value = args[0][int(attrs[0])]
        elif contract == "field.constant":
            value = int(attrs[0])
        elif contract == "field.add":
            value = (args[0] + args[1]) % PRIME
        elif contract == "field.mul":
            value = (args[0] * args[1]) % PRIME
        elif contract == "field.neg":
            value = -args[0] % PRIME
        elif contract == "vector.empty":
            value = []
        elif contract == "vector.append":
            value = args[0] + [args[1]]
        else:
            raise AssertionError(contract)
        assert len(outputs) == 1
        env[outputs[0]] = value
    raise AssertionError("missing generated return")


directory = records()
source = directory / "source.pir"
asset = directory / "multiply.json"
relation = [
    "zkc.relation.r1cs/1",
    FIELD,
    "4",
    "1",
    "1",
    [[[["2", "1"]], [["3", "1"]], [["1", "1"]]]],
]
asset.write_text(json.dumps(relation))
spelling = f'''module {{
      relation Circuit = r1cs("multiply.json");
      derive Rows = multilinear(Circuit, specialized);
      fn Assemble(s: Vector<"{FIELD}"::Element>, w: Vector<"{FIELD}"::Element>) -> (Vector<"{FIELD}"::Element>) {{
        let a = Rows_Assemble(s, w); return (a);
      }}
    }}'''
source.write_text(spelling)
formatted = run("protocol-format", source)
source.write_text(formatted)
assert run("protocol-format", source) == formatted
inspection = json.loads(run("protocol-parse", source))
assert "Circuit" in json.dumps(inspection) and "Rows" in json.dumps(inspection)
# File-based admission now captures and decodes declared assets, just like
# project compilation. The frozen snapshot remains independently admissible.
run("protocol-admit", source)
snapshot = directory / "snapshot.json"
frozen = run("protocol-resolve", source)
snapshot.write_text(frozen)
assert json.loads(frozen)[0] == "zkc.relations/1"
run("protocol-admit", snapshot)
asset.unlink()
run("protocol-admit", snapshot)
run("protocol-resolve", source, "relation-asset-missing")
mlir = directory / "source.mlir"
original = run("protocol-import", snapshot)
mlir.write_text(original)
assert "relation.r1cs @Circuit" in original and "relation = @Circuit" in original
assert 'relation_views = [["Rows", @Circuit' in original
exported = json.loads(run("protocol-export", mlir))
assert exported[1] == json.loads(frozen)[1]
mlir.write_text(original.replace("relation = @Circuit", "relation = @Unknown", 1))
run("protocol-export", mlir, "relation-function-association")
mlir.write_text(
    original.replace(', relation = @Circuit, relation_view = "Rows"', "", 1)
)
run("protocol-export", mlir, "relation-function-association")
mlir.write_text(
    original.replace('constraints = [[[[2, "1"]]', 'constraints = [[[[2, "2"]]', 1)
)
run("protocol-export", mlir, "relation-generated-function")
for old, new, refusal in [
    ('"multiply.json"', '"../escape.json"', "relation-asset-path"),
    ('"multiply.json"', '"/directory/escape.json"', "relation-asset-path"),
    ("r1cs(", "unknown(", "relation-import-family"),
    ("Circuit, specialized", "Missing, specialized", "source-name-unresolved"),
    # Arithmetic views do not declare an Assemble helper. The call is refused
    # by resolution before the incompatible relation/view pair is elaborated.
    ("multilinear(", "arithmetic(", "source-name-kind"),
]:
    asset.write_text(json.dumps(relation))
    source.write_text(spelling.replace(old, new))
    run("protocol-resolve", source, refusal)
# Without that invalid helper reference, retain the family-specific refusal.
source.write_text('module { relation Circuit = r1cs("multiply.json"); '
                  'derive Rows = arithmetic(Circuit, specialized); }')
run("protocol-resolve", source, "relation-view-family")
source.write_text(
    spelling.replace(
        "derive Rows", 'relation Circuit = r1cs("multiply.json"); derive Rows'
    )
)
run("protocol-resolve", source, "relation-duplicate-alias")
source.write_text(
    spelling.replace(
        "derive Rows",
        'relation Other = r1cs("other.json"); derive OtherRows = multilinear(Other, specialized); derive Rows',
    )
)
other = copy.deepcopy(relation)
other[5][0][0][0][1] = "2"
(directory / "other.json").write_text(json.dumps(other))
multiple = json.loads(run("protocol-resolve", source))
assert len(multiple[1][0]) == 2 and multiple[1][0][0][1] != multiple[1][0][1][1]
# Both staging routes bind exact canonical coefficients; shape is insufficient.
source.write_text(spelling.replace("specialized", "public_matrices"))
snapshot.write_text(run("protocol-resolve", source))
data_ir = run("protocol-import", snapshot)
matrix = ["2", "4", [["0", "2", "1"]]]
expected = hashlib.sha256(
    json.dumps(["zkc.matrix/1", FIELD, matrix], separators=(",", ":")).encode()
).hexdigest()
assert "matrix.identity_check" in data_ir and expected in data_ir
lowered = directory / "materialized.json"
lowered.write_text(run("protocol-materialize", snapshot))
materialized = json.loads(lowered.read_text())
assert materialized[0] == "zkc.protocol/1"
assert "matrix.identity_check" in lowered.read_text() and expected in lowered.read_text()
assert "Relation_" in lowered.read_text()
run("protocol-admit", lowered)
# Explicit lowering is stable and keeps executable checks, even though
# independent ordinary-source readers do not know the asset envelope.
assert json.loads(run("protocol-materialize", lowered)) == materialized
payload = json.loads(run("protocol-relation-data", snapshot, extra=("Rows",)))
assert payload[:3] == ["zkc.relation-matrices/1", "Rows", "Circuit"]
expected_relation = hashlib.sha256(
    (
        "zkc.relation-subject/1\n" + json.dumps(relation, separators=(",", ":"))
    ).encode()
).hexdigest()
assert payload[3] == expected_relation and payload[4][0] == matrix
source.write_text(
    spelling.replace("multilinear", "rank_one").replace(
        "specialized", "public_matrices"
    )
)
snapshot.write_text(run("protocol-resolve", source))
core_payload = json.loads(run("protocol-relation-data", snapshot, extra=("Rows",)))
assert core_payload[3] == expected_relation
assert core_payload[4][0] == ["1", "4", [["0", "2", "1"]]]

# Symlink escaping the selected dependency directory is rejected.
outside = records('outside')
external = Path(outside) / "relation.json"
external.write_text(json.dumps(relation))
asset.unlink()
asset.symlink_to(external)
source.write_text(spelling)
run("protocol-resolve", source, "relation-asset-path")
asset.unlink()
# AIR uses the same frozen loader/identity ownership, and its generated
# interface performs actual residual arithmetic under the selected schedule.
air = {
    "schema": "zkc.air.v1",
    "field": FIELD,
    "columns": 1,
    "public_inputs": 1,
    "constraints": [
        {
            "scope": {"kind": "transition", "lookahead": 1},
            "nodes": [
                {"op": "read", "offset": 1, "column": 0},
                {"op": "read", "offset": 0, "column": 0},
                {"op": "mul", "lhs": 1, "rhs": 1},
                {"op": "neg", "operand": 2},
                {"op": "add", "lhs": 0, "rhs": 3},
            ],
        },
        {
            "scope": {"kind": "first"},
            "nodes": [
                {"op": "read", "offset": 0, "column": 0},
                {"op": "public", "index": 0},
                {"op": "neg", "operand": 1},
                {"op": "add", "lhs": 0, "rhs": 2},
            ],
        },
    ],
}
(directory / "trace.json").write_text(json.dumps(air))
source.write_text(f'''module {{
      relation Trace = air("trace.json");
      derive Steps = arithmetic(Trace, specialized, 3);
      protocol Evaluate {{
        roles (Alice); inputs (Alice s: Vector<"{FIELD}"::Element>, Alice t: Vector<"{FIELD}"::Element>);
        outputs (Alice Vector<"{FIELD}"::Element>);
        local Alice: let residuals = Steps_Evaluate(s, t);
        return (residuals);
      }}
      instance Run: Evaluate {{ roles (Alice = Alice); }}
      entry main = Run;
    }}''')
snapshot.write_text(run("protocol-resolve", source))
air_ir = run("protocol-import", snapshot)
assert "relation.air @Trace" in air_ir and "relation = @Trace" in air_ir
projected = json.loads(run("protocol-project", snapshot))
bindings = {binding[0]: binding[1] for binding in projected[1]}
function = next(f for f in projected[3] if f[1] == "Steps_Evaluate")
assert evaluate(function, bindings, [[2], [2, 4, 16]]) == [[0, 0, 0]]
assert any(evaluate(function, bindings, [[2], [2, 5, 16]])[0])
assert any(evaluate(function, bindings, [[3], [2, 4, 16]])[0])
run("protocol-compile", snapshot)
# Ordinary pure source cannot smuggle a relation record through unknown tags.
bad = directory / "bad.json"
bad.write_text(json.dumps(["zkc.relations/1", [], ["zkc.relations/1", [], []]]))
run("protocol-admit", bad, "relation-source-shape")
# Only the top-level decoded format tag selects the larger asset budget.
ordinary = ["zkc.protocol/1", [], [], [], [], [["entry", "main", "zkc.relations/1"]]]
bad.write_text(json.dumps(ordinary) + " " * (1024 * 1024))
run("protocol-resolve", bad, "byte-limit")
escaped = frozen.replace('"zkc.relations/1"', '"zkc.relations\\u002f1"', 1)
bad.write_text(escaped)
run("protocol-admit", bad)
# Explicit dependency loading admits readable and snapshot forms equally.
unresolved = ["zkc.relations/1", [[["Circuit", relation]], []],
              ["zkc.protocol/1", [], [], [], [], [["entry", "main", "Missing"]]]]
bad.write_text(json.dumps(unresolved))
run("protocol-resolve", bad, "interactive-entry-instance")
asset.write_text(json.dumps(relation))
source.write_text('module { relation Circuit = r1cs("multiply.json"); entry main = Missing; }')
# Authored source resolves declaration kinds before common admission. The
# portable snapshot above still reaches the independent common diagnostic.
run("protocol-resolve", source, "source-name-unresolved")

# A relation captured as a static association enters type identities as well
# as the snapshot's relation table. The table is the one the view code is
# rebuilt from, so a snapshot whose table no longer holds a relation that a
# type identity names would enforce one relation while claiming another.
embedded = directory / "embedded"
embedded.mkdir()
(embedded / "multiply.json").write_text(json.dumps(relation))
mixed = embedded / "mixed.pir"
mixed.write_text(f'''module {{
  library(namespace="test", name="mixed", version="1", resolution="exact");
  relation Circuit = r1cs("multiply.json");
  derive Rows = multilinear(Circuit, specialized);
  interface Cell {{ type State drop; association Subject; local value(x: State) -> bool; }}
  component CellImpl<R: association>: Cell {{
    type State = bool; association Subject = R;
    local value(x: State) -> bool {{ return x; }}
  }}
  enum Outcome<C: Cell> {{ Ready(C::State), Invalid(bool) }}
  fn Select<C: Cell>(state: C::State, ready: bool) -> bool {{
    if ready capture(state, ready) -> (chosen) {{
      let choice: Outcome<C> = Outcome::Ready(state); yield (choice);
    }} else {{
      let choice: Outcome<C> = Outcome::Invalid(ready); yield (choice);
    }}
    match chosen capture() -> (answer) {{
      Ready(state) => {{ let answer = C::value(state); yield (answer); }},
      Invalid(error) => {{ yield (error); }}
    }}
    return answer;
  }}
  link Closed = Select<CellImpl<Circuit>>;
  fn Assemble(s: Vector<"{FIELD}"::Element>, w: Vector<"{FIELD}"::Element>) -> (Vector<"{FIELD}"::Element>) {{
    let a = Rows_Assemble(s, w); return (a);
  }}
}}''')
captured = run("protocol-resolve", mixed)
assert "variant:" in captured, captured
intact = embedded / "snapshot.json"
intact.write_text(captured)
run("protocol-admit", intact)
changed = json.loads(captured)
assert changed[1][0][0][1][5][0][2][0][1] == "1", changed[1][0][0]
changed[1][0][0][1][5][0][2][0][1] = "5"
tampered = embedded / "tampered.json"
tampered.write_text(json.dumps(changed))
run("protocol-admit", tampered, "relation-snapshot-subject")
run("protocol-materialize", tampered, "relation-snapshot-subject")

# A variant nominal nested past any relation encoding is refused, rather than
# handed to a reader that recurses once per level.
nodes = ["[" * 50000, "A", "bool", ["2"], ["1", "3"], ["4"], ["0", "5"]]
deep = "variant:" + json.dumps(["zkc.variant/1", nodes], separators=(",", ":")).encode().hex()
nested = json.loads(captured)
function = next(f for f in nested[2][2] if f[0] == "function")
function[2], function[3] = [["x", deep]], [deep]
deeply = embedded / "deeply-nested.json"
deeply.write_text(json.dumps(nested))
run("protocol-admit", deeply, "relation-snapshot-subject")
print(f"{commands.save()} relation authoring tool controls passed")
