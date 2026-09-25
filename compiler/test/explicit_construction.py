"""Explicit construction, origins and physical lowering, without proof execution.

Legacy fixtures supply contrasting control graphs. Their monomorphic operations
are explicitly bound here as test inputs, never through a production profile.
"""
import copy
from bls_fixture import module
import json
from pathlib import Path
from commands import Commands
from tools import corpus, examples, optimizer, records

field, group, pcs = "bls12-381.fr", "bls12-381.g1", "multilinear.kzg.bls12-381/1"
suite = "merlin3.bls12-381.fr64be/1"


commands = Commands(records())


def run(mode, source, *files, refuses=None):
    """A source given as text or as the record it serializes to."""
    printed = commands.source(mode, source if isinstance(source, str) else json.dumps(source),
                              *files, refuses=refuses)
    if refuses:
        assert commands.last.returncode == 1, commands.last.stderr
    return printed


def explicit(source, implementation=""):
    source = copy.deepcopy(source)
    assert source[0] == "zkc.protocol/1"
    for binding in source[1]:
        binding[3] = implementation if binding[1] == "poly.fold" else ""
    return source


def inspect(source, result):
    assert result[0] == "zkc.construction-result/1"
    common = result[2]
    assert common[0] == "zkc.protocol/1"
    bindings = {b[0]: b for b in common[1]}
    functions = {f[1]: f for f in common[2]}
    prepared = json.loads(run("protocol-prepare", source))
    originals = {f[1]: f for f in prepared[2]}
    for _, contract, args, _ in bindings.values():
        if contract.startswith("transcript."):
            assert args[0] == suite
            if contract.startswith("transcript.observe."):
                kind = contract.removeprefix("transcript.observe.")
                codecs = {
                    "bool": ([], "zkcv.bool/1"),
                    "field": ([field], "zkcv.field.bls12-381.fr/1"),
                    "table": ([field], "zkcv.table.bls12-381.fr/1"),
                    "point": ([field], "zkcv.point.bls12-381.fr/1"),
                    "round": ([field], "zkcv.round.bls12-381.fr/1"),
                    "group": ([group], "zkcv.group.bls12-381.g1/1"),
                    "groups": ([group], "zkcv.groups.bls12-381.g1/1"),
                    "commitment": ([pcs], "zkcv.commitment.multilinear-kzg.bls12-381/1"),
                    "proof": ([pcs], "zkcv.proof.multilinear-kzg.bls12-381/1"),
                }
                identity, codec = codecs[kind]
                assert args == [suite, *identity, codec]
    challenges = 0
    for name, site, protocol, call, function, op_site, role, kind in result[4]:
        helper = functions[name]
        assert len(helper) == 6 and helper[5] == [name, []]
        generated_op = next(op for op in helper[4] if op[0] == "op" and op[1] == site)
        operation = bindings[generated_op[2]]
        if operation[1] == "transcript.challenge":
            challenges += 1
            assert kind == "construction" and function in originals
            original_op = next(op for op in originals[function][4]
                               if op[0] == "op" and op[1] == op_site)
            original_binding = next(b for b in prepared[1] if b[0] == original_op[2])
            assert original_binding[1] == "random.draw"
            assert generated_op[3] == [protocol, call, function, op_site, role]
        elif operation[1].startswith("transcript.observe."):
            assert function == "" and kind == "construction"
        elif kind in ("original", "recipe"):
            original_op = next(op for op in originals[function][4]
                               if op[0] == "op" and op[1] == op_site)
            original_binding = next(b for b in prepared[1] if b[0] == original_op[2])
            assert operation == original_binding  # Includes fixed implementations.
    assert challenges > 0
    plan = json.loads(run("protocol-compile", common))
    assert plan[0] == "zkc.participants/1" and plan[2] == "physical"
    # SSA names may change on roundtrip; both exported forms must re-admit.
    run("protocol-admit", run("protocol-export", run("protocol-import", common)))
    return plan


def descriptor_size_fixture(n):
    sites = ["draw_" + "x" * 100 + str(k) for k in range(n)]
    draw, state = [], "rng"
    for k, site in enumerate(sites):
        after = "state" + str(k)
        draw.append(["op", site, "random", [], [state], ["value" + str(k), after]])
        state = after
    draw.append(["return", [state]])
    functions = [
        ["function", "Draw", [["rng", "rng:" + field]], ["rng:" + field],
         draw, ["Draw", []]],
        ["function", "Accept", [], ["bool"], [
            ["op", "zero", "constant", ["0"], [], ["z"]],
            ["op", "equal", "equal", [], ["z", "z"], ["ok"]],
            ["return", ["ok"]]], ["Accept", []]],
    ]
    bindings = [["random", "random.draw", [field], ""],
                ["constant", "field.constant", [field], ""],
                ["equal", "field.equal", [field], ""]]
    protocol = ["protocol", "Subject", ["P", "V"], [],
                [["coins", "V", "rng:" + field]],
                [["V", "bool"], ["V", "rng:" + field]], [], [
                    ["local", "draw", "V", "Draw", ["coins"], ["after"]],
                    ["local", "accept", "V", "Accept", [], ["accepted"]],
                    ["return", ["accepted", "after"]]]]
    source = ["zkc.protocol/1", bindings, functions, [protocol],
              [["instance", "subject", "Subject", [], [], [["P", "P"], ["V", "V"]]]],
              [["entry", "main", "subject"]]]
    descriptor = ["zkc.construction/1", "main", "P", "V", [],
                  ["coins", [["Draw", site] for site in sites]], "0", suite, "normalized"]
    return source, descriptor


temporary = records()
temporary = Path(temporary)
for example in ("two-factor", "committed-two-factor", "dleq"):
    # The origin checks read the author's site labels, which exact identity keeps.
    descriptor = temporary / f"{example}.exact.construction.pir"
    descriptor.write_text((examples / f"{example}.construction.pir").read_text().replace(
        "construction main {", "construction main identity exact {"))
    legacy = json.loads((examples / f"{example}.json").read_text())
    if example == "dleq":
        source = json.loads(run("protocol-source", (corpus / "generic-dleq.pir").read_text()))
    else:
        source = explicit(legacy, "arkworks-msb/poly.fold")
    result = json.loads(run("protocol-construct", source, descriptor))
    plan = inspect(source, result)
    ir = run("protocol-construct-ir", source, descriptor)
    for option in ("--zkc-project-participants", "--zkc-plan-participants"):
        ir = commands.run([optimizer, option, "-"], stdin=ir)
    assert json.loads(run("protocol-export", ir)) == plan
    if example != "dleq":
        assert any(b[1] == "table.relayout" for b in plan[1])
    candidate = temporary / "construction.json"
    candidate.write_text(json.dumps(result))
    assert run("protocol-check-construction", source, descriptor, candidate).strip() == "construction-checked"
    changed = copy.deepcopy(result)
    changed[4][0][7] = "forged"
    candidate.write_text(json.dumps(changed))
    run("protocol-check-construction", source, descriptor, candidate, refuses="construction-candidate-mismatch")
    if example == "dleq":
        alias = copy.deepcopy(source)
        alias[2].append(["configure", "DrawAlias", "DLEQDraw", [], []])
        for protocol in alias[3][3]:
            for op in protocol[7]:
                if op[0] == "local" and op[3] == "DLEQDraw":
                    op[3] = "DrawAlias"
        alias_descriptor = json.loads(run("protocol-source", descriptor.read_text()))
        alias_descriptor[5][1] = [["DrawAlias", "draw"]]
        alias_path = temporary / "alias-descriptor.json"
        alias_path.write_text(json.dumps(alias_descriptor))
        alias_result = json.loads(run("protocol-construct", alias, alias_path))
        inspect(alias, alias_result)
        assert alias_result != result
        challenge_rows = [row for row in alias_result[4] if row[5] == "draw"]
        assert challenge_rows and all(row[4] == "DrawAlias" for row in challenge_rows)
        # The definition selects the alias, its one materialized configuration,
        # and the certificate keeps the selector it was given. The configuration
        # the alias refines is not materialized, so nothing answers to its name.
        for identity in ("exact", "normalized"):
            alias_descriptor[8] = identity
            alias_descriptor[5][1] = [["DrawAlias", "draw"]]
            alias_path.write_text(json.dumps(alias_descriptor))
            by_alias = json.loads(run("protocol-construct", alias, alias_path))
            alias_descriptor[5][1] = [["DLEQDrawAlgorithm", "draw"]]
            alias_path.write_text(json.dumps(alias_descriptor))
            by_definition = json.loads(run("protocol-construct", alias, alias_path))
            assert by_definition[1] == alias_descriptor
            assert by_definition[2:] == by_alias[2:]
            alias_descriptor[5][1] = [["DLEQDraw", "draw"]]
            alias_path.write_text(json.dumps(alias_descriptor))
            run("protocol-construct", alias, alias_path, refuses="construction-draw-selector")
        # Whole source authority includes undemanded generic definitions.
        changed = copy.deepcopy(source)
        changed[1].append(["generic_function", "Unused", [], [], [], [], [["return", []]]])
        other = json.loads(run("protocol-construct", changed, descriptor))
        assert other != result
        assert [row[2:] for row in other[4]] == [row[2:] for row in result[4]]
        candidate.write_text(json.dumps(result))
        run("protocol-check-construction", changed, descriptor, candidate, refuses="construction-candidate-mismatch")
        changed[1][-1][6] = [["op", "unknown", "missing", [], [], [], []], ["return", []]]
        run("protocol-construct", changed, descriptor, refuses="generic-operation")
    # Selectors name source configurations, not generated shared bodies.
    bad = json.loads(run("protocol-source", descriptor.read_text()))
    bad[5][1][0][0] = "missing_configuration"
    path = temporary / "bad-descriptor.json"
    path.write_text(json.dumps(bad))
    run("protocol-construct", source, path, refuses="construction-draw-selector")

# Exact-once private slots overwritten before observation need typed seeds.
accept = ["function", "Accept", [], ["bool"], [
    ["op", "zero", "field.constant", ["0"], [], ["z"]],
    ["op", "equal", "field.equal", [], ["z", "z"], ["yes"]], ["return", ["yes"]]]]
for kind, constructor in (("bool", None), ("field", "field.constant"),
                          ("group", "curve.generator"), ("groups", "curve.empty"),
                          ("point", "poly.empty_point")):
    functions = [accept]
    function = "Accept"
    if constructor:
        function = "SeedResult"
        functions.append(["function", function, [], [kind], [
            ["op", "make", constructor, ["0"] if kind == "field" else [], [], ["new"]],
            ["return", ["new"]]]])
    loop = ["loop", "once", ["constant", "1"], [["x", "private"]], [], [
        ["local", "make", "V", function, [], ["new"]], ["yield", ["new"]]], ["last"]]
    body = [loop, ["message", "result", kind, "V", "P", "last", "received"],
            ["local", "accept", "V", "Accept", [], ["accepted"]], ["return", ["accepted"]]]
    protocol = ["protocol", "Subject", ["P", "V"], [],
                [["private", "V", kind], ["coins", "V", "rng"]], [["V", "bool"]], [], body]
    source = module(functions, [protocol],
              [["instance", "subject", "Subject", [], [], [["P", "P"], ["V", "V"]]]],
              [["entry", "main", "subject"]])
    descriptor = temporary / "seed-descriptor.json"
    descriptor.write_text(json.dumps(["zkc.construction/1", "main", "P", "V", [],
                                     ["coins", []], "0", suite, "exact"]))
    result = json.loads(run("protocol-construct", explicit(source), descriptor))
    candidate = temporary / ("seed-" + kind + ".json")
    candidate.write_text(json.dumps(result))
    run("protocol-check-construction", explicit(source), descriptor, candidate)
    run("protocol-compile", result[2])

# Restoring authored selector names after normalized construction may push
# the final certificate over its limit even when the internal form fits.
source, descriptor = descriptor_size_fixture(300)
padding = [["op", "pad" + str(k), "constant", ["0"], [], ["z" + str(k)]]
           for k in range(7250)] + [["return", []]]
source[2].append(["function", "Padding", [], [], padding, ["Padding", []]])
long_source, long_descriptor = copy.deepcopy(source), copy.deepcopy(descriptor)
for k, op in enumerate(source[2][0][4][:-1]):
    op[1] = "site" + str(k)
for k, selector in enumerate(descriptor[5][1]):
    selector[1] = "site" + str(k)
path = temporary / "size-descriptor.json"
path.write_text(json.dumps(descriptor))
short = run("protocol-construct", source, path).strip()
def compact(value):
    return json.dumps(value, separators=(",", ":"))
delta = len(compact(long_descriptor)) - len(compact(descriptor))
assert len(short) <= 1024 * 1024 < len(short) + delta
path.write_text(json.dumps(long_descriptor))
run("protocol-construct", long_source, path, refuses="construction-byte-limit")
# So may an exact descriptor whose authored origin selects a function's draws
# under a longer name than the function's own.
origin = "Draw" + "x" * 124
grouped = copy.deepcopy(source)
grouped[2][0][5] = [origin, []]
by_function = copy.deepcopy(descriptor)
by_function[8] = "exact"
path.write_text(json.dumps(by_function))
internal = run("protocol-construct", grouped, path).strip()
by_origin = copy.deepcopy(by_function)
for selector in by_origin[5][1]:
    selector[0] = origin
delta = len(compact(by_origin)) - len(compact(by_function))
assert len(internal) <= 1024 * 1024 < len(internal) + delta
path.write_text(json.dumps(by_origin))
run("protocol-construct", grouped, path, refuses="construction-byte-limit")

# Authored explicit origins may group functions; only actual selected sites
# participate, independently of an unrelated helper call elsewhere in the module.
source, descriptor = descriptor_size_fixture(1)
source[2][0][5] = ["Shared", []]
source[2][1][5] = ["Shared", []]  # Accept has no selected draw site.
descriptor[5][1][0][0] = "Shared"
path = temporary / "group-descriptor.json"
for identity, with_call in (("exact", False), ("exact", True),
                             ("normalized", False), ("normalized", True)):
    descriptor[8] = identity
    path.write_text(json.dumps(descriptor))
    subject = copy.deepcopy(source)
    if with_call:
        subject[2].append(["function", "Unused", [], ["bool"], [
            ["apply", "call", "Accept", [], [], ["result"]],
            ["return", ["result"]]], ["Unused", []]])
    # This case exercises authoring's origin-group expansion. The formatter
    # emits closed carrier text, whose descriptors follow the JSON contract.
    authored = run("protocol-format", subject).replace("carrier module", "module", 1)
    result = json.loads(run("protocol-construct", authored, path))
    bindings = {binding[0]: binding[1] for binding in result[2][1]}
    functions = {function[1]: function for function in result[2][2]}
    challenges = []
    for row in result[4]:
        operation = next(op for op in functions[row[0]][4]
                         if op[0] == "op" and op[1] == row[1])
        if bindings[operation[2]] == "transcript.challenge":
            challenges.append(row)
    # Prover and verifier replay the same selected challenge occurrence.
    assert len(challenges) == 2, challenges
    assert all(row[4] == "Draw" and row[7] == "construction" for row in challenges)
    assert challenges[0][2:] == challenges[1][2:], challenges
    # A group has no site map of its own, so only normalized identity needs it
    # written out as the functions that carry the site.
    written = [["Draw", descriptor[5][1][0][1]]] if identity == "normalized" else descriptor[5][1]
    assert result[1][5][1] == written, result[1]
    absent = copy.deepcopy(descriptor)
    absent[5][1][0][1] = "absent"
    bad = temporary / "group-absent.json"
    bad.write_text(json.dumps(absent))
    run("protocol-construct", authored, bad,
        refuses="source-site-selection" if identity == "normalized" else "construction-draw-selector")
# With no project to bind it first, the group's name selects the site in every
# function the group holds.
subject = copy.deepcopy(source)
again = copy.deepcopy(subject[2][0])
again[1] = "Again"
subject[2].append(again)
body = subject[3][0][7]
body.insert(1, ["local", "again", "V", "Again", ["after"], ["again_after"]])
body[-1][1][1] = "again_after"
descriptor[8] = "exact"
path.write_text(json.dumps(descriptor))
result = json.loads(run("protocol-construct", subject, path))
bindings = {binding[0]: binding[1] for binding in result[2][1]}
functions = {function[1]: function for function in result[2][2]}
drawn = [row[4] for row in result[4]
         if bindings[next(op[2] for op in functions[row[0]][4]
                          if op[0] == "op" and op[1] == row[1])] == "transcript.challenge"]
assert sorted(drawn) == ["Again", "Again", "Draw", "Draw"], drawn

# The project binds a definition selector to the definition itself, and
# construction selects its copies: here two nested in one caller, one reached
# through a partial configuration. Under normalized identity the definition's
# site map renames the site, so the project and its carrier choose the same work.
nested = corpus / "generic-construction.pir"
nested_carrier = commands.source("protocol-source", None, nested)
for identity in ("exact", "normalized"):
    notation = temporary / f"nested-{identity}.construction.pir"
    notation.write_text(f"construction main identity {identity} {{\n  producer P;\n  validator V;\n"
                        f"  random coins at (Draw sample);\n  accept 0;\n  suite \"{suite}\";\n}}\n")
    by_project = json.loads(commands.source("protocol-construct", None, nested, notation))
    assert by_project[1][5][1] == [["Draw", "sample"]], by_project[1]
    path = temporary / "nested-descriptor.json"
    path.write_text(json.dumps(by_project[1]))
    by_carrier = json.loads(run("protocol-construct", nested_carrier, path))
    assert by_carrier[2:] == by_project[2:]
    bindings = {binding[0]: binding[1] for binding in by_project[2][1]}
    functions = {function[1]: function for function in by_project[2][2]}
    drawn = {(row[4], row[5]) for row in by_project[4]
             if bindings[next(op[2] for op in functions[row[0]][4]
                              if op[0] == "op" and op[1] == row[1])] == "transcript.challenge"}
    assert len(drawn) == 2 and {function for function, _ in drawn} == {"DrawTwo"}, drawn

# A definition selector selects each materialized configuration of that
# definition, in a carrier without local calls as in one with them. The project
# binds the same draws to the configured functions' own names; both spellings
# choose the same work, and the certificate keeps the selector it was given.
application = examples.parent / "projects/air/main.pir"
library = "--library=" + str(examples.parent / "libraries/air/lib.pir")
carrier = commands.source("protocol-source", None, application, library)
configured = json.loads(commands.source(
    "protocol-construct", None, application,
    application.with_suffix(".construction.pir"), library))[1]
origins = {function[1]: function[5][0]
           for function in json.loads(run("protocol-prepare", carrier))[2]}
path = temporary / "air-descriptor.json"
for identity in ("exact", "normalized"):
    descriptor = copy.deepcopy(configured)
    descriptor[8] = identity
    path.write_text(json.dumps(descriptor))
    by_configuration = json.loads(run("protocol-construct", carrier, path))
    descriptor[5][1] = [[origins[name], site] for name, site in descriptor[5][1]]
    assert descriptor[5][1] == [["DrawAlgorithm", "draw"], ["QueryAlgorithm", "draw"]]
    path.write_text(json.dumps(descriptor))
    by_definition = json.loads(run("protocol-construct", carrier, path))
    assert by_definition[1] == descriptor
    assert by_definition[2:] == by_configuration[2:]
    selected = {origins[row[4]] for row in by_definition[4]
                if row[7] == "construction" and row[4]}
    assert selected == {"DrawAlgorithm", "QueryAlgorithm"}, selected
    # Selectors that reach the same copies select them once; naming one
    # selector twice is malformed.
    both = copy.deepcopy(descriptor)
    both[5][1] = configured[5][1][:1] + descriptor[5][1]
    path.write_text(json.dumps(both))
    by_both = json.loads(run("protocol-construct", carrier, path))
    assert by_both[1] == both and by_both[2:] == by_configuration[2:]
    both[5][1] = descriptor[5][1][:1] + descriptor[5][1]
    path.write_text(json.dumps(both))
    run("protocol-construct", carrier, path, refuses="construction-draw-selector")
    descriptor[5][1][0][1] = "absent"
    path.write_text(json.dumps(descriptor))
    run("protocol-construct", carrier, path,
        refuses="source-site-selection" if identity == "normalized" else "construction-draw-selector")

print(f"explicit construction: {commands.save()} checks; generic DLEQ, polynomial/PCS control, origins, bindings, identity, refusals")
