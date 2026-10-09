"""Canonical and resource boundaries through the public Program codec driver."""

import copy
import json

from cases import case
from commands import Commands
from tools import canonical_program, records

commands = Commands(records())
source = '''module { "protocol.module"() ({
  "protocol.func"() ({ ^entry(%n:ui64,%x:i1,%y:i1):
    %same = arith.andi %x,%y : i1
    "protocol.repeat"(%n) ({ ^round(%i:ui64):
      "protocol.yield"() : () -> ()
    }) {site="rounds",carried=0:i64,maximum=1048576:i64,roles=["P"],carried_roles=[]} : (ui64) -> ()
    "protocol.return"(%same) : (i1) -> ()
  }) {sym_name="main",function_type=(ui64,i1,i1)->i1,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }'''
physical = commands.verified(source, None, "--zkc-project-protocol",
                             "--zkc-lower-math", "--zkc-select-physical")
original = json.loads(commands.source("protocol-export", physical))
participant = original[3][0]
participant[7] = [["rng", "random.bls12-381.fr/1", str(len(participant[4]))]]
loop_index = next(i for i, row in enumerate(participant[6]) if row[0] == "loop")


def check(program, code=None):
    result = canonical_program(commands, json.dumps(program, separators=(",", ":")),
                               refuses=code)
    assert commands.last.returncode == (1 if code else 0), commands.last
    if code:
        assert commands.last.stderr.strip() == code, commands.last.stderr
    else:
        assert json.loads(result) == program


with case("canonical service index and maximum loop bound"):
    check(original)

for label, mutate, code in [
    ("noncanonical service index",
     lambda p: p[3][0][7][0].__setitem__(2, "03"), "service-port-index"),
    ("noncanonical loop bound",
     lambda p: p[3][0][6][loop_index][2].__setitem__(2, "01"), "interactive-loop-count"),
    ("overmaximum loop bound",
     lambda p: p[3][0][6][loop_index][2].__setitem__(2, "1048577"), "interactive-loop-count"),
    ("missing function origin slot",
     lambda p: p[2][0].pop(), "interactive-record"),
    ("malformed function origin",
     lambda p: p[2][0].__setitem__(5, []), "binding-logical-origin"),
    ("overlimit input string",
     lambda p: p[2][0].__setitem__(1, "x" * (1024 * 1024)), "byte-limit"),
]:
    with case(label):
        candidate = copy.deepcopy(original)
        mutate(candidate)
        check(candidate, code)

for depth, code in [(29, None), (30, "interactive-json-depth"), (65, "interactive-body")]:
    with case(f"nested local bodies: {depth}"):
        candidate = copy.deepcopy(original)
        boolean = "bool@native.bool/1"
        body = [["yield", ["x"]]]
        for level in range(depth):
            output = f"r{level}"
            body = [["if", f"branch{level}", "x", ["x"], body,
                     [["yield", ["x"]]], [output]], ["yield", [output]]]
        body[-1][0] = "return"
        candidate[2].append(["function", "nested", [["x", boolean]], [boolean],
                             body, ["nested", []]])
        check(candidate, code)

print(f"Program boundary checks: {commands.save()}")
