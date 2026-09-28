"""Closed root identity and query occurrences survive native role projection."""

import copy
import json

from cases import case
from commands import Commands
from tools import corpus, records

commands = Commands(records())
run = commands.source
source = json.loads((corpus / "mathematical/root-queries.json").read_text())
text = json.dumps(source)

with case("roots and ordered queries round trip"):
    mlir = run("protocol-import", text)
    assert mlir.count('"pir.root"') == 2
    assert mlir.count('"pir.query"') == 3
    assert mlir.count('"pir.guard"') == 1
    commands.verified(mlir)
    formatted = run("protocol-format", text)
    assert "owners" in formatted
    assert json.loads(run("protocol-source", formatted)) == source

with case("projection keeps root identities and distinct occurrences"):
    projected = json.loads(run("protocol-project", text))
    assert projected[6] == source[6]
    bodies = {p[3]: p[7] for p in projected[4]}
    prover = bodies["Prover"]
    assert [i[0] for i in prover] == ["query", "query", "return"]
    assert prover[0][2] == prover[1][2] == "nonce"
    assert prover[0][1] != prover[1][1]
    assert prover[0][4] != prover[1][4]
    assert [i[0] for i in bodies["Verifier"]] == ["query", "guard", "return"]
    run("protocol-import", json.dumps(projected))

with case("library preparation retains closed roots"):
    library = ["zkc.library/1", [], [], source]
    prepared = json.loads(run("protocol-prepare", json.dumps(library)))
    assert prepared[6] == source[6]
    assert json.loads(run("protocol-project", json.dumps(library)))[6] == source[6]

with case("closed root modules exclude unreachable instances"):
    bad = copy.deepcopy(source)
    definition = copy.deepcopy(bad[3][0])
    definition[1] = "Unreachable"
    bad[3].append(definition)
    instance = copy.deepcopy(bad[4][0])
    instance[1:3] = ["unused", "Unreachable"]
    bad[4].append(instance)
    run("protocol-import", json.dumps(bad), refuses="interactive-roots-unreachable-instance")


def body(module):
    return module[3][0][7]


for label, change, code in [
    ("missing root", lambda s: body(s)[0].__setitem__(3, "missing"), "interactive-query-root"),
    ("foreign query", lambda s: body(s)[0].__setitem__(2, "Verifier"), "interactive-query-permission"),
    ("query input", lambda s: body(s)[0].__setitem__(4, ["accept"]), "interactive-query-signature"),
    ("query arity", lambda s: body(s)[0].__setitem__(5, []), "interactive-query-signature"),
    ("unknown service", lambda s: s[6][0].__setitem__(2, "missing"), "interactive-root-service"),
    ("unknown owner", lambda s: s[6][0].__setitem__(3, ["Missing"]), "interactive-root-owner"),
    ("no owners", lambda s: s[6][0].__setitem__(3, []), "interactive-root-declaration"),
    ("unordered owners", lambda s: s[6][0].__setitem__(3, ["Verifier", "Prover"]), "interactive-root-declaration"),
    ("guard ownership", lambda s: body(s)[3].__setitem__(2, "Prover"), "interactive-guard-condition"),
    ("guard type", lambda s: body(s)[3].__setitem__(3, "c"), "interactive-guard-condition"),
    ("mixed affine port", lambda s: s[3][0][4][0].__setitem__(2, "rng:bls12-381.fr"), "interactive-root-affine-mixing"),
    ("generic root role", lambda s: s[4][0][5][0].__setitem__(1, "Other"), "interactive-roots-role-binding"),
    ("empty root extension", lambda s: s.__setitem__(6, []), "interactive-empty-roots"),
]:
    with case(label):
        bad = copy.deepcopy(source)
        change(bad)
        run("protocol-import", json.dumps(bad), refuses=code)

with case("only installed entropy contracts declare roots"):
    bad = copy.deepcopy(source)
    bad[1][0] = ["nonce_draw", "field.add", ["bls12-381.fr"], ""]
    run("protocol-import", json.dumps(bad), refuses="entropy-service-contract")

with case("physical carriers cannot contain unrealized roots"):
    projected = json.loads(run("protocol-project", text))
    projected[2] = "physical"
    run("protocol-import", json.dumps(projected), refuses="interactive-unrealized-roots")

print(f"closed root queries: {commands.save()} compiler checks")
