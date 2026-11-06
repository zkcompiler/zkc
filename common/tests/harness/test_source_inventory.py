"""Exact source inventories cannot confuse declaration identity with a use."""

from copy import deepcopy
import json

import pytest

from harness import language_interface, load

# The common bridge import establishes the package root for script consumers.
load("inventory_claims", "lean/bridges/pipeline/source_claims.py")
from bridges.common.lean_render import Refused  # noqa: E402
from bridges.pipeline.source_inventory import Inventory, decode, digest  # noqa: E402


def fixture():
    source = b"checked original"
    interface = json.dumps(language_interface("m::Proof", "entry", digest(source).split(":")[1]))
    span = {"module": "m", "begin": 0, "end": 10}
    node = {"owner": "m::Run", "path": []}
    block = ["block", [[["protocol_apply", "callee", []], [], [], [], "call"],
                      [["protocol_repeat", 0, 1, [], []], [], [],
                       [[[], [], ["block", [[["guard", "V"], [], [], [], "guard"]],
                                  ["stop", "reject", "stop"]]]], "loop"]], ["return", []]]
    def function(symbol, body):
        return ["function", symbol, "protocol", "public", [], [], ["protocol", [], [], []], [], ["m::Run" if symbol == "entry" else "m::Child", []] if symbol != "generated" else None, body]
    snapshot = ["zkc.structured-source/0", "original", digest(source), "entry", [], [], [],
                [function("entry", block), function("callee", ["block", [], ["return", []]]),
                 function("generated", ["block", [], ["return", []]])], [], [[], []], [[], [], []]]
    context = {"capture": "c" * 64, "installation": "a" * 64}
    def instance(symbol, owner):
        return {"symbol": symbol, "template": {"kind": "declaration", "owner": owner,
                "generated": False, "source": span, "candidates": [node]},
                "statics": [], "scoped": [], "domains": [], "layout": {"inputs": [], "captures": []},
                "oracle_obligations": []}
    document = {"format": "zkc.source-correspondence/0",
                "admission": {**context, "format": snapshot[0], "original_sha256": digest(source),
                              "protocol_symbol": "entry", "interface_sha256": digest(interface.encode())},
                "source_ast": {**context, "format": "zkc.source-ast/0",
                               "sources": [{"module": "m", "origin": "captured", "bytes": 10,
                                            "sha256": "b" * 64}],
                               "declarations": [{"owner": "m::Run", "nodes": [
                                   {"path": [], "kind": "declaration.protocol", "span": span}]}]},
                "bindings": {**context, "format": "zkc.source-bindings/0", "locals": [],
                             "unassociated_locals": [], "declarations": [], "units": []},
                "snapshot": snapshot,
                "instances": {**context, "format": "zkc.source-instances/0",
                              "instances": [instance("entry", "m::Run"), instance("callee", "m::Child")]},
                "instance_rows": [{"instance": 0, "rows": [[7, 0]]}, {"instance": 1, "rows": [[7, 1]]}],
                "generated": [{"symbol": "generated", "purpose": "control", "part": "then",
                               "origins": [{"definition": "entry", "site": "loop"}]}],
                "generated_rows": [{"generated": 0, "rows": [[7, 2]]}],
                "occurrences": [{"definition": "entry", "site": site, "nodes": [node]}
                                for site in ("call", "loop", "guard", "stop")],
                "rows": [{"row": [7, i], "operation": "protocol.func", "derivation": "direct",
                          "original": None, "sources": []} for i in range(3)]}
    arguments = {"source": source, "interface_text": interface, "original_text": json.dumps(snapshot)}
    return document, arguments


def test_inventory_keeps_origin_and_occurrence_separate():
    document, args = fixture()
    inventory = Inventory(document, **args)
    selected = inventory.authored("m::Run", statics=[], scoped=[], domains=[])
    assert selected.symbol == "entry" and selected.rows == ((7, 0),)
    assert list(inventory.occurrences) == [("entry", site) for site in ("call", "loop", "guard", "stop")]
    assert inventory.identity("generated").kind == "generated"
    # All four uses can share one written node; none is silently collapsed.
    assert len(inventory.occurrences) == 4
    document["instances"]["instances"][0]["template"]["owner"] = "edited"
    selected.declaration["template"]["owner"] = "edited too"
    assert inventory.authored("m::Run", statics=[], scoped=[], domains=[]).symbol == "entry"


def test_virtual_query_occurrence_is_required_even_without_a_written_node():
    document, args = fixture()
    kind = ["table", ["field", "koala-bear"], "16"]
    symbol = "virtual"
    document["snapshot"][7].append(["oracle", symbol, [], kind, "admissible", [], [],
        ["block", [[["oracle_query", None, kind], [0, 1], [["field", "koala-bear"]], [], "low"]],
         ["return", [0]]]])
    instance = deepcopy(document["instances"]["instances"][0])
    instance.update(symbol=symbol)
    document["instances"]["instances"].append(instance)
    document["instance_rows"].append({"instance": 2, "rows": [[7, 3]]})
    document["occurrences"].append({"definition": symbol, "site": "low", "nodes": []})
    args["original_text"] = json.dumps(document["snapshot"])
    assert Inventory(document, **args).occurrences[(symbol, "low")] == []
    document["occurrences"].pop()
    with pytest.raises(Refused, match="incomplete or reordered"):
        Inventory(document, **args)


def test_distinct_closed_substitutions_are_selected_exactly():
    document, args = fixture()
    instances = document["instances"]["instances"]
    for row, value in zip(instances, ("2", "3")):
        row["template"]["owner"] = "m::Run"
        row["statics"] = [["N", ["nat", value]]]
    for definition, row in zip(document["snapshot"][7], instances):
        definition[8] = ["m::Run", row["statics"]]
    args["original_text"] = json.dumps(document["snapshot"])
    inventory = Inventory(document, **args)
    assert inventory.authored("m::Run", statics=[["N", ["nat", "3"]]], scoped=[], domains=[]).symbol == "callee"
    with pytest.raises(Refused, match="missing or ambiguous"):
        inventory.authored("m::Run", statics=[], scoped=[], domains=[])


def test_installed_template_has_no_written_source():
    document, args = fixture()
    template = document["instances"]["instances"][1]["template"]
    template.update(owner="installed::plus", source=None, candidates=[])
    document["snapshot"][7][1][8] = ["installed::plus", []]
    args["original_text"] = json.dumps(document["snapshot"])
    assert Inventory(document, **args).identity("callee").declaration["template"]["source"] is None
    template["source"] = {"module": "installed", "begin": 0, "end": 0}
    with pytest.raises(Refused, match="outside captured unit"):
        Inventory(document, **args)


@pytest.mark.parametrize("change", [
    lambda d: d.update(extra=True),
    lambda d: d["admission"].update(installation="bad"),
    lambda d: d["source_ast"].update(capture="d" * 64),
    lambda d: d["instances"].update(installation="d" * 64),
    lambda d: d["bindings"].update(capture="d" * 64),
    lambda d: d["snapshot"][7].pop(),
    lambda d: d["occurrences"].pop(),
    lambda d: d["occurrences"].reverse(),
    lambda d: d["occurrences"][0].update(site="absent"),
    lambda d: d["occurrences"][0].update(definition="callee"),
    lambda d: d["occurrences"][0]["nodes"][0].update(path=[["body", 0]]),
    lambda d: d["instance_rows"][0].update(rows=[[7, 1]]),
    lambda d: d["instance_rows"][0].update(instance=True),
    lambda d: d["instance_rows"][1].update(rows=[[7, True]]),
    lambda d: d["instance_rows"].pop(),
    lambda d: d["instances"]["instances"][0].update(symbol="generated"),
    lambda d: d["instances"]["instances"][0].update(scoped=[False]),
    lambda d: d["instances"]["instances"][0].update(statics=[["N", ["nat", "01"]]]),
    lambda d: d["instances"]["instances"][0]["layout"].update(inputs=[True]),
    lambda d: d["generated"][0].update(purpose="invented"),
    lambda d: d["generated"][0].update(origins=[]),
    lambda d: d["generated"][0]["origins"][0].update(definition="absent"),
    lambda d: d["generated"][0]["origins"].append(deepcopy(d["generated"][0]["origins"][0])),
    lambda d: d["generated_rows"][0].update(rows=[]),
    lambda d: d["rows"][0].update(row=[7, 999]),
    lambda d: d["rows"][0].update(derivation="invented"),
    lambda d: d["rows"].append(deepcopy(d["rows"][0])),
])
def test_identity_mutations_refuse(change):
    document, args = fixture()
    change(document)
    with pytest.raises(ValueError):
        Inventory(document, **args)


@pytest.mark.parametrize("field,value", [("source", b"changed original"),
                                         ("interface_text", "{}"), ("original_text", "[]")])
def test_artifact_mismatch_refuses(field, value):
    document, args = fixture()
    args[field] = value
    with pytest.raises(ValueError):
        Inventory(document, **args)


def test_duplicate_json_keys_never_hide_identity_changes():
    with pytest.raises(ValueError, match="duplicate"):
        decode('{"instances": [], "instances": [1]}')


def test_unrelated_binding_never_changes_authored_selection():
    document, args = fixture()
    before = Inventory(document, **args).authored("m::Run", statics=[], scoped=[], domains=[])
    document["snapshot"][6].append(["binding", "new-binding", "contract", [], []])
    args["original_text"] = json.dumps(document["snapshot"])
    inventory = Inventory(document, **args)
    assert inventory.authored("m::Run", statics=[], scoped=[], domains=[]) == before
    assert inventory.row(6, 0).kind == "binding"
    assert inventory.single_target("entry", "protocol_apply").symbol == "callee"


def test_target_selection_refuses_ambiguity_instead_of_taking_first():
    document, args = fixture()
    block = document["snapshot"][7][0][9]
    block[1].append([["protocol_apply", "callee", []], [], [], [], "again"])
    document["occurrences"].append({"definition": "entry", "site": "again", "nodes": []})
    args["original_text"] = json.dumps(document["snapshot"])
    inventory = Inventory(document, **args)
    with pytest.raises(Refused, match="missing or ambiguous instruction"):
        inventory.single_target("entry", "protocol_apply")


def test_protocol_origin_and_static_selection_must_agree():
    document, args = fixture()
    document["instances"]["instances"][0]["statics"] = [["N", ["nat", "2"]]]
    with pytest.raises(Refused, match="protocol origin differs"):
        Inventory(document, **args)



def test_body_aliases_use_exact_source_owners():
    from bridges.pipeline.glue import body_names
    document, args = fixture()
    inventory = Inventory(document, **args)
    assert body_names(inventory.snapshot, "run", inventory,
                      {"m::Run": "run", "m::Child": "child"}) == {"entry": "run", "callee": "child"}
    with pytest.raises(Refused, match="conflicts"):
        body_names(inventory.snapshot, "run", inventory, {"m::Run": "different"})
    with pytest.raises(Refused, match="no unique closed instance"):
        body_names(inventory.snapshot, "run", inventory, {"missing": "child"})
    with pytest.raises(Refused, match="require the bound identity inventory"):
        body_names(inventory.snapshot, "run", owners={"m::Run": "run"})
    document["instances"]["instances"][1]["template"]["owner"] = "m::Run"
    document["snapshot"][7][1][8] = ["m::Run", []]
    args["original_text"] = json.dumps(document["snapshot"])
    inventory = Inventory(document, **args)
    with pytest.raises(Refused, match="no unique closed instance"):
        body_names(inventory.snapshot, "run", inventory, {"m::Run": "run"})



def test_body_printer_rejects_stale_data_before_running_lean(tmp_path, monkeypatch):
    from types import SimpleNamespace
    from bridges.structured import bodies
    inventory = SimpleNamespace(snapshot=["zkc.structured-source/0", "original", digest(b"source"),
        "entry", [], [], [], [], [], [[], []], [[], [], []]])
    monkeypatch.setattr(bodies, "LEAN", tmp_path)
    (tmp_path / "Example").mkdir()
    (tmp_path / "Example/Data.lean").write_text("stale retained data")
    with pytest.raises(Refused, match="data differs"):
        bodies.printed_module("Example.Data", "Example.Bodies", inventory=inventory)


@pytest.mark.parametrize("names,diagnostic", [
    ({"entry": "same", "callee": "same"}, "duplicate body presentation"),
    ({"missing": "unused"}, "absent definition"),
    ({"entry": "bad.name"}, "invalid body presentation"),
])
def test_body_printer_rejects_invalid_presentations(tmp_path, monkeypatch, names, diagnostic):
    from bridges.structured import bodies
    monkeypatch.setattr(bodies, "ROOT", tmp_path)
    monkeypatch.setattr(bodies, "elaborate", lambda *_: (
        "HELPER\tentry\t.local\t[]\t[]\nHELPER\tcallee\t.local\t[]\t[]\n"))
    with pytest.raises(Refused, match=diagnostic):
        bodies.printed_module("Example.Data", "Example.Bodies", names=names, fresh=True)
