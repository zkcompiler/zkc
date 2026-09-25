#!/usr/bin/env python3
"""Authored modules through actual MLIR stages, plus hostile source/IR admission."""
import copy
import json
from pathlib import Path
from commands import Commands
from tools import compiler, examples, optimizer, records



commands = Commands(records())


def run(tool, *args, ok=True, code=None):
    return commands.run([tool, *args], refuses=None if ok else (code or True))


directory = records()
directory = Path(directory)
# Staged lowering reaches the same plan as compiling in one step, and each
# stage says which it is. protocol_verifiers.py runs the same two examples with
# canonicalization and common subexpression elimination interleaved, which is
# the separate claim that those passes leave the final plan alone.
for file in ["two-factor.json", "group-exchange.json"]:
    source = examples / file
    ir = directory / "common.mlir"
    ir.write_text(run(compiler, "protocol-import", source))
    logical = directory / "logical.mlir"
    logical.write_text(run(optimizer, "--zkc-project-participants", ir))
    logical_json = json.loads(run(compiler, "protocol-export", logical))
    physical = directory / "physical.mlir"
    physical.write_text(run(optimizer, "--zkc-plan-participants", logical))
    physical_json = json.loads(run(compiler, "protocol-export", physical))
    direct = json.loads(run(compiler, "protocol-compile", source))
    assert direct == physical_json
    assert logical_json[2] == "logical" and physical_json[2] == "physical"
    assert "plan.kernel" in physical.read_text() and "!plan.data" in physical.read_text()
    assert '"pir.message"' not in logical.read_text()
    if file == "two-factor.json":
        assert len(direct[4]) == 6
        assert sum(p[2] == "opening" for p in direct[4]) == 2
        for p in direct[4]:
            if p[3] == "V":
                assert all(t not in ["table", "prover_key"] for _, t in p[5])
    else:
        assert "poly." not in logical.read_text()
    run(optimizer, "--zkc-project-participants", physical, ok=False, code="interactive-projection-stage")
    run(optimizer, "--zkc-plan-participants", physical, ok=False, code="interactive-physical-stage")
    tampered = directory / "extra-attribute.mlir"
    tampered.write_text(physical.read_text().replace("}> :", '}> {untrusted = "claim"} :', 1))
    run(compiler, "protocol-export", tampered, ok=False, code="binding-attribute")
external = json.loads((examples / "two-factor.json").read_text())
external[2][0][4] = "external"
declaration = directory / "external.json"
declaration.write_text(json.dumps(external))
run(compiler, "protocol-admit", declaration)
run(compiler, "protocol-compile", declaration, ok=False, code="interactive-external-body")
supplied = examples / "supplied-participant.json"
run(compiler, "protocol-admit", supplied)
supplied_ir = directory / "supplied.mlir"
supplied_ir.write_text(run(compiler, "protocol-import", supplied))
supplied_export = json.loads(run(compiler, "protocol-export", supplied_ir))
assert len(supplied_export[4]) == 1 and supplied_export[4][0][3] == "P"
run(optimizer, "--zkc-project-participants", supplied_ir, ok=False, code="interactive-projection-stage")
source = json.loads((examples / "two-factor.json").read_text())

# Admission checks every declaration; projection emits only entry reachability.
unused = copy.deepcopy(source)
extra = copy.deepcopy(next(i for i in unused[4] if i[2] == "ProductSumcheck"))
extra[1] = "unused_sumcheck"
unused[4].append(extra)
file = directory / "unused.json"
file.write_text(json.dumps(unused))
assert len(json.loads(run(compiler, "protocol-compile", file))[4]) == 6
extra[2] = "MissingProtocol"
file.write_text(json.dumps(unused))
run(compiler, "protocol-compile", file, ok=False, code="interactive-instance-protocol")

# The interactive array-depth ceiling is independent of the generic parser.
for terminal in (["yield", []], ["stop", "halt", "P", "reject"]):
    for depth in (25, 29, 30):
        body = [terminal]
        for n in reversed(range(depth)):
            body = [["loop", f"loop_{n}", ["constant", "1"], [], [], body, []],
                    ["yield" if n else "return", []]]
        nested = ["zkc.protocol/1", [], [],
                  [["protocol", "Nested", ["P", "V"], [], [], [], [], body]],
                  [["instance", "nested", "Nested", [], [], [["P", "P"], ["V", "V"]]]],
                  [["entry", "main", "nested"]]]
        file = directory / f"nested-{depth}.json"
        file.write_text(json.dumps(nested))
        run(compiler, "protocol-compile", file, ok=depth < 30,
            code="interactive-json-depth" if depth == 30 else None)
# Libraries need no public entry, but cannot become executable artifacts.
library = copy.deepcopy(source)
library[5] = []
library_file = directory / "library.json"
library_file.write_text(json.dumps(library))
run(compiler, "protocol-admit", library_file)
run(compiler, "protocol-compile", library_file, ok=False, code="interactive-entry")
supplied_export[5] = []
empty_target = directory / "empty-target.json"
empty_target.write_text(json.dumps(supplied_export))
run(compiler, "protocol-admit", empty_target, ok=False, code="interactive-entry")

def check_mutation(change, code):
    altered = copy.deepcopy(source)
    change(altered)
    file = directory / "mutated.json"
    file.write_text(json.dumps(altered))
    run(compiler, "protocol-admit", file, ok=False, code=code)

check_mutation(lambda m: m.append([]), "interactive-shape")
check_mutation(lambda m: m[2][0][4][0].__setitem__(2, "uninstalled.kernel"), "binding-reference")
check_mutation(lambda m: m[3][2][7][0].__setitem__(2, "V"), "interactive-local-signature")
check_mutation(lambda m: m[3][2][7][1].__setitem__(4, "P"), "interactive-message-availability")
check_mutation(lambda m: m[3][2][7][0][4].__setitem__(1, "absent"), "interactive-unavailable")
check_mutation(lambda m: m[3][2][7][2].__setitem__(1, "root_f"), "interactive-site")
check_mutation(lambda m: m[4][2][4][0].__setitem__(1, "opening"), "interactive-dependency-protocol")
check_mutation(lambda m: m[4][0][5][1].__setitem__(1, "P"), "interactive-dependency-role")
check_mutation(lambda m: m[4][2][5][1].__setitem__(1, "P"), "interactive-role-binding")
check_mutation(lambda m: m[4][0][3][0].__setitem__(1, "01"), "noncanonical-natural")
check_mutation(lambda m: m[4][0][3][0].__setitem__(1, "1048577"), "interactive-binding")
check_mutation(lambda m: m[4][0][3][0].__setitem__(1, "2"), "interactive-dependency-parameter-agreement")
check_mutation(lambda m: m[3][2][6][0][2][0].__setitem__(0, "missing"), "interactive-dependency-parameter")
check_mutation(lambda m: m[3][2][6][0][2][0].__setitem__(1, "missing"), "interactive-dependency-parameter")
check_mutation(lambda m: m[3][2][6][0][2].append(["n", "n"]), "interactive-binding")
check_mutation(lambda m: m[3][2][6][0].pop(), "interactive-shape")
# Uninstantiated declarations must still have valid dependency interfaces.
check_mutation(lambda m: m[3].append(["protocol", "Unused", ["P"], [], [], [], [["child", "ProductSumcheck", []]], "external"]), "interactive-dependency-role")
check_mutation(lambda m: m[3].append(["protocol", "Unused", ["P", "V"], [], [], [], [["child", "Absent", []]], "external"]), "interactive-dependency-protocol")
check_mutation(lambda m: m[3][0][7][2][4].append("coins"), "interactive-loop-capture")
# One resource cannot supply two consumed operation operands through SSA reuse.
check_mutation(lambda m: m[2][3][4].insert(4, ["op", "draw_again", "random.draw", [], ["coins"], ["r2", "coins2"]]), "interactive-resource-reuse")
# Zero is a structural-loop control; actual PCS setup has its separate n>=1 guard.
zero = copy.deepcopy(source)
for instance in zero[4]:
    for binding in instance[3]: binding[1] = "0"
file = directory / "zero.json"
file.write_text(json.dumps(zero))
run(compiler, "protocol-compile", file)
# Source bodies must actually affect exported SSA and resulting role artifacts.
altered = copy.deepcopy(source)
altered[2][-1][4][0][2] = "field.add"
altered[1].append(["field.add", "field.add", ["bls12-381.fr"], "arkworks/field.add"])
file.write_text(json.dumps(altered))
candidate = json.loads(run(compiler, "protocol-compile", file))
original = json.loads(run(compiler, "protocol-compile", examples / "two-factor.json"))
assert candidate != original
print(f"interactive compiler: {commands.save()} tool checks passed")
