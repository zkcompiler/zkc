"""Inline algebra survives projection; effects cannot enter a pure region."""

import copy
import json
from commands import Commands
from cases import case
from tools import corpus, records

commands = Commands(records())
run = commands.source
source = json.loads((corpus / "mathematical/pure-region.json").read_text())
text = json.dumps(source)

with case("inline import, carrier printing and role projection"):
    mlir = run("protocol-import", text)
    assert mlir.count('"pir.pure"') == 2
    assert '"pir.local_call"' not in mlir
    commands.verified(mlir)
    formatted = run("protocol-format", text)
    assert "pure [" in formatted
    assert json.loads(run("protocol-source", formatted)) == source
    projected = json.loads(run("protocol-project", text))
    assert not projected[3]
    bodies = {p[3]: p[7] for p in projected[4]}
    assert [op[0] for op in bodies["Alice"]] == ["pure", "send", "return"]
    assert [op[0] for op in bodies["Bob"]] == ["receive", "pure", "return"]
    assert bodies["Bob"][1][3][1][0] == "op"
    run("protocol-import", json.dumps(projected))

with case("outlining occurs at physical realization"):
    physical = json.loads(run("protocol-compile", text))
    assert physical[2] == "physical"
    assert len(physical[3]) == 2
    assert sum(op[0] == "local" for p in physical[4] for op in p[7]) == 2
    assert all(fn[5][0].startswith("pure_") for fn in physical[3])
    by_binding = {b[0]: b[1] for b in physical[1]}
    kernels = [by_binding[op[2]] for fn in physical[3] for op in fn[4] if op[0] == "op"]
    assert kernels == ["field.add", "field.from_nonzero", "field.mul"]
    commands.verified(run("protocol-physical-ir", text))

for label, change, code in [
    ("cross-role capture", lambda region: region.__setitem__(2, "Bob"), "interactive-pure-capture"),
    ("missing capture", lambda region: region.__setitem__(3, []), "interactive-unavailable"),
    ("duplicate capture", lambda region: region[3].append(region[3][0]), "interactive-pure-capture"),
    ("affine capture", lambda region: region[3][0].__setitem__(1, "rng:bls12-381.fr"), "interactive-pure-type"),
    ("ordered operation", lambda region: region[4].__setitem__(0, ["op","add_value","constant",["1"],[],["twice"]]), "interactive-pure-operation"),
    ("opaque local call", lambda region: region[4].__setitem__(0, ["local","add_value","Alice","fake",["x"],["twice"]]), "interactive-pure-instruction"),
    ("ordinary return", lambda region: region[4][-1].__setitem__(0, "return"), "interactive-pure-instruction"),
    ("false result type", lambda region: region[5][0].__setitem__(1, "bool"), "local-yield-types"),
]:
    with case(label):
        bad = copy.deepcopy(source)
        change(bad[3][0][7][0])
        run("protocol-import", json.dumps(bad), refuses=code)

with case("attribute-free ordered operation"):
    bad = copy.deepcopy(source)
    bad[1].append(["inverse", "field.inverse", ["bls12-381.fr"], ""])
    bad[3][0][7][0][4][0] = ["op", "inverse_value", "inverse", [], ["x"], ["twice"]]
    run("protocol-import", json.dumps(bad), refuses="interactive-pure-operation")

with case("MLIR role and stage boundaries"):
    mlir = run("protocol-import", text)
    commands.verified(mlir.replace('role = "Alice"', 'role = "Missing"', 1), "interactive-pure-context")
    empty = copy.deepcopy(source)
    empty[1] = []
    protocol = empty[3][0]
    protocol[4] = []
    protocol[5] = []
    protocol[7] = [["pure", "empty", "Alice", [], [["yield", []]], []], ["return", []]]
    projected = run("protocol-import", run("protocol-project", json.dumps(empty)))
    commands.verified(projected.replace('stage = "logical"', 'stage = "physical"'), "interactive-pure-context")

print(f"inline pure regions: {commands.save()} compiler checks")
