#!/usr/bin/env python3
"""Profile syntax elaborates once; current consumers only execute bindings."""
import copy
import json
from pathlib import Path
from commands import Commands
from tools import compiler, examples, records

root = Path(__file__).resolve().parents[2]


commands = Commands(records())


def run(command, path, refuses=None):
    """One subcommand over a source the compiler reads from a path."""
    return commands.run([compiler, command, path], refuses=refuses)


directory = records()
directory = Path(directory)
text = directory / "source.pir"
text.write_text('''module "arkworks.bls12-381/1" {
      fn Add(x: field, y: field) -> (field) {
        [sum] let z = field::add(x, y); return(z);
      }
      protocol Main {
        roles(P); inputs(P x: field, P y: field); outputs(P field);
        local [step] P: let z = Add(x, y); return(z);
      }
      instance root: Main { roles(P=P); } entry main=root;
    }''')
field = "field:bls12-381.fr"
# Authored independently of the frontend, including occurrence identity.
expected = ["zkc.protocol/1",
    [["field.add", "field.add", ["bls12-381.fr"], "arkworks/field.add"]],
    [["function", "Add", [["x", field], ["y", field]], [field],
      [["op", "sum", "field.add", [], ["x", "y"], ["z"]],
       ["return", ["z"]]], ["Add", []]]],
    [["protocol", "Main", ["P"], [], [["x", "P", field], ["y", "P", field]],
      [["P", field]], [], [["local", "step", "P", "Add", ["x", "y"], ["z"]],
                           ["return", ["z"]]]]],
    [["instance", "root", "Main", [], [], [["P", "P"]]]],
    [["entry", "main", "root"]]]
actual = json.loads(run("protocol-source", text))
assert actual == expected, actual
explicit = directory / "explicit.json"
explicit.write_text(json.dumps(expected))
assert json.loads(run("protocol-compile", text)) == json.loads(
    run("protocol-compile", explicit))

# Parsing/formatting stays structural, including unknown future contracts.
profile_text = text.read_text()
text.write_text(profile_text.replace("field::add(x, y)", "transcript::observe::future(x, y)"))
run("protocol-format", text)
run("protocol-source", text, "source-name-unresolved")

# The carrier holds explicit bindings only: a retired tag is refused, and so is
# a profile name where the binding list goes.
retired = copy.deepcopy(expected)
retired[0] = "zkc.protocol/2"
explicit.write_text(json.dumps(retired))
run("protocol-admit", explicit, "interactive-format")
named = copy.deepcopy(expected)
named[1] = "arkworks.bls12-381/1"
explicit.write_text(json.dumps(named))
run("protocol-admit", explicit, "interactive-shape")

for name in ("two-factor", "committed-two-factor", "dleq", "group-exchange"):
    source = examples / (name + ".pir")
    normalized = json.loads(run("protocol-source", source))
    assert normalized == json.loads(source.with_suffix(".json").read_text())
    assert normalized[0] == "zkc.protocol/1"
    for _, contract, args, implementation in normalized[1]:
        assert implementation == "arkworks/" + contract
        if contract.startswith("pcs."):
            assert args == ["multilinear.kzg.bls12-381/1"]
        if contract.startswith("curve.") and contract != "curve.response":
            assert args == ["bls12-381.g1"]

# Binding generation cannot capture a top-level declaration's symbol.
text.write_text(profile_text.replace("Add", "field.add"))
collision = json.loads(run("protocol-source", text))
assert collision[1][0][0] == "field.add_"
assert collision[2][0][4][0][2] == "field.add_"
assert collision[2][0][5] == ["field.add", []]


print(f"carrier consolidation: {commands.save()} tool checks passed")
