#!/usr/bin/env python3
"""Check structured constructor strings with Lean's actual parser and kernel."""

import argparse
import copy
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import support.evidence  # noqa: E402
import support.lake  # noqa: E402

spec = importlib.util.spec_from_file_location("structured_snapshot", HERE / "bridges/structured/snapshot.py")
renderer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(renderer)

# Exported catalogue rows: none for Boolean and index units, and the native
# BLS12-381 rows (with the random service when a unit draws) otherwise.
NO_ROWS = [[], []]
BLS_NOMINALS = [
    ["nominal", "bls12-381.fr", "Field",
     [["PairingG1", "bls12-381.g1"], ["PairingG2", "bls12-381.g2"], ["PairingGT", "bls12-381.gt"]],
     ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"],
     "52435875175126190479447740508185965837690552500527637822603658699938581184513"],
    ["nominal", "bls12-381.g2", "Group", [["Scalar", "bls12-381.fr"]], ["Group", "ScalarAction"], None],
    ["nominal", "bls12-381.gt", "Group", [["Scalar", "bls12-381.fr"]], ["Group", "ScalarAction"], None],
    ["nominal", "bls12-381.g1", "Group", [["Scalar", "bls12-381.fr"]], ["Group", "ScalarAction"], None],
]
BLS_ROWS = [BLS_NOMINALS, []]
BLS_SERVICE_ROWS = [BLS_NOMINALS, [["service", "random.bls12-381.fr/0", "bls12-381.fr", ["draw"]]]]


def check(output, lake):
    output.mkdir(parents=True, exist_ok=True)
    names = ["plain", 'quote"slash\\literal\\u0041', "line\nreturn\rtab\t",
             "\x00\x08\x0c\x1f\x7f", "증명_α_🙂", "α" * 256,
             '"\nend Rendered\naxiom injected : False\n--']
    modules = []
    for kind in ["protocol", "local"]:
        try:
            renderer.function_origin(kind, [])
        except ValueError:
            continue
        raise AssertionError("renderer accepted a missing function origin")
    for index, name in enumerate(names):
        helper = ["function", name, "math", "private", [["bool"]], [["bool"]], [], [], [],
                  ["block", [], ["return", [0]]]]
        entry = ["function", "main", "protocol", "public", [["bool"]], [["bool"]],
                 ["protocol", ["P"], [["P"]], [["P"]]], [], ["main", []],
                 ["block", [[["call", name], [0], [["bool"]], [], ""]], ["return", [0]]]]
        data = ["zkc.structured-source/0", "original", "sha256:" + "0" * 64,
                "main", [], [], [], [helper, entry], [["main", []]], NO_ROWS, [[], []]]
        namespace = f"RenderedCase{index}"
        if index == 4:
            # Exercise the actual CLI under an ASCII locale as well as the
            # in-process renderer. File encoding must not depend on the host.
            snapshot_path = output / "unicode.json"
            snapshot_path.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
            rendered_path = output / "Unicode.lean"
            environment = dict(os.environ, LC_ALL="C", PYTHONUTF8="0", PYTHONCOERCECLOCALE="0")
            subprocess.run([sys.executable, renderer.__file__, snapshot_path, rendered_path,
                            "--namespace", namespace], env=environment, check=True, timeout=30)
            if not (rendered_path.read_bytes() == renderer.render(data, namespace).encode("utf-8")):
                raise AssertionError('checks/check_structured_renderer.py:62: rendered_path.read_bytes() == renderer.render(data, namespace).encode("utf-8")')
        source = renderer.render(data, namespace).replace("module\n\n", "", 1)
        # Numeric codepoints are an independent expectation; never render this
        # expected value through the string function being tested.
        points = str([ord(char) for char in name])
        source += f'''
example : ({namespace}.snapshot.definitions[0]?.map
    (fun definition => definition.name.toList.map Char.toNat)) = some {points} := by
  decide +kernel
example : (Zkc.Source.Structured.check {namespace}.snapshot).isOk = true := by
  decide +kernel
'''
        modules.append(source)
    # Exercise metadata and every new operation constructor independently of
    # admission. Numeric codepoints are the expected string values; the test
    # does not use the renderer to construct its own expectation.
    name = 'opaque_증명"\\\n'
    field = ["field", "bls12-381.fr"]
    group = ["group", "bls12-381.g1"]
    service = ["service", "random.bls12-381.fr/0"]
    operations = [
        [["group.identity", group[1]], [], [group], [], ""],
        [["group.add", group[1]], [0, 0], [group], [], ""],
        [["group.scale", group[1], field[1]], [0, 2], [group], [], ""],
        [["group.equal", group[1]], [0, 1], [["bool"]], [], ""],
        [["restrict", [name]], [0], [["bool"]], [], ""],
        [["exchange", name, "V"], [0], [["bool"]], [], name],
        [["draw", "V", field[1]], [7], [field], [], "draw"],
        [["statement", name, [name], 0, name], [6], [], [], ""],
        [["field.embed", "extension", "base"], [0], [["field", "extension"]], [], ""],
    ]
    data = ["zkc.structured-source/0", "original", "sha256:" + "0" * 64, "main", [],
            [["relation", name, "public", name, name, name, [], [group], [["bool"]], ["statement"], None]], [],
            [["function", "main", "protocol", "public", [group, field, service], [["bool"]],
              ["protocol", [name, "V"], [[name, "V"], [name], ["V"]], [["V"]]], [], ["main", []],
              ["block", operations, ["return", [1]]]]], [["main", []]], BLS_SERVICE_ROWS, [[], []]]
    source = renderer.render(data, "RenderedOpen").replace("module\n\n", "", 1)
    points = str([ord(char) for char in name])
    source += f'''
open Zkc.Source.Structured in
example : (RenderedOpen.snapshot.relations.map fun relation =>
    (relation.name.toList.map Char.toNat, relation.kind.toList.map Char.toNat,
     relation.key.toList.map Char.toNat, relation.revision.toList.map Char.toNat)) =
    [({points}, {points}, {points}, {points})] := by decide +kernel
open Zkc.Source.Structured in
example : (RenderedOpen.snapshot.definitions[0]?.bind fun definition =>
    match definition with
    | .function function => function.interface.map fun interface =>
        interface.roles.map (fun role => role.toList.map Char.toNat)
    | _ => none) = some [{points}, [86]] := by decide +kernel
open Zkc.Source.Structured in
example : (RenderedOpen.snapshot.definitions[0]?.map fun definition =>
    match definition with
    | .function function =>
      let .block instructions _ := function.body
      instructions.map fun (.instruction descriptor _ _ _ _) => match descriptor with
        | .groupIdentity _ => 0 | .groupAdd _ => 1 | .groupScale _ _ => 2
        | .groupEqual _ => 3 | .restrict _ => 4 | .exchange _ _ => 5
        | .draw _ _ => 6 | .statement _ _ _ _ => 7 | .fieldEmbed _ _ => 8 | _ => 99
    | _ => []) = some [0, 1, 2, 3, 4, 5, 6, 7, 8] := by decide +kernel
open Zkc.Source.Structured in
example : (RenderedOpen.snapshot.definitions[0]?.bind fun definition =>
    match definition with
    | .function function =>
      let .block instructions _ := function.body
      instructions[7]?.bind fun (.instruction descriptor _ _ _ _) => match descriptor with
        | .statement _ _ _ target => target.map fun name => name.toList.map Char.toNat
        | _ => none
    | _ => none) = some {points} := by decide +kernel
'''
    modules.append(source)
    # Aggregate names remain escaped data, including inside recursive types.
    # Inspect codepoints and typed components independently in the kernel.
    aggregate_identity = 'query_증명"\\\n'
    constructor = 'make_α"\\\n'
    sequence = ["sequence", field]
    product = ["product", aggregate_identity, constructor, [["bool"], sequence]]
    nested = ["sequence", product]
    make = ["function", "make", "math", "private", [["bool"], sequence], [product], [], [], [],
            ["block", [[["product.make", constructor], [0, 1], [product], [], ""]], ["return", [0]]]]
    get = ["function", "get", "math", "private", [product], [sequence], [], [], [],
           ["block", [[["product.get", 1], [0], [sequence], [], ""]], ["return", [0]]]]
    entry = ["function", "main", "protocol", "public", [nested], [nested],
             ["protocol", ["P"], [["P"]], [["P"]]], [], ["main", []], ["block", [], ["return", [0]]]]
    aggregate_data = ["zkc.structured-source/0", "original", "sha256:" + "0" * 64,
                      "main", [], [], [], [make, get, entry], [["main", []]], BLS_ROWS, [[], []]]
    source = renderer.render(aggregate_data, "RenderedAggregates").replace("module\n\n", "", 1)
    identity_points = str([ord(char) for char in aggregate_identity])
    constructor_points = str([ord(char) for char in constructor])
    source += f'''
open Zkc.Source.Structured in
example : (RenderedAggregates.snapshot.definitions[2]?.bind fun definition =>
    match definition.inputs with
    | [.sequence (.product identity constructor fields)] =>
      some (identity.toList.map Char.toNat, constructor.toList.map Char.toNat, fields.toList)
    | _ => none) = some ({identity_points}, {constructor_points},
      [.boolean, .sequence (.field "bls12-381.fr")]) := by decide +kernel
example : (Zkc.Source.Structured.check RenderedAggregates.snapshot).isOk = true := by
  decide +kernel
'''
    modules.append(source)
    malformed_aggregates = [
        (renderer.ty, ["sequence"]), (renderer.ty, ["sequence", field, field]),
        (renderer.ty, ["product", "id", "make", None]),
        (renderer.ty, ["product", "id", "make", [field] * 513]),
        (renderer.descriptor, ["product.make", constructor, "extra"]),
        (renderer.descriptor, ["product.get", True]),
        (renderer.descriptor, ["product.get", 512]),
    ]
    too_deep = field
    for _ in range(64):
        too_deep = ["sequence", too_deep]
    malformed_aggregates.append((renderer.ty, too_deep))
    for render, invalid in malformed_aggregates:
        try:
            render(invalid)
        except ValueError:
            continue
        raise AssertionError("renderer accepted a malformed aggregate")
    # Contract strings go through the same injection-resistant boundary as
    # executable names. Check exact directions, ports, roles and formula links
    # with Lean rather than comparing the renderer with itself.
    contract_name = 'clause_증명"\\\n'
    contract_data = copy.deepcopy(data)
    contract_data[5][0][-1] = contract_name
    contract_data[8] = [["main", [["continuation", contract_name,
        [name, [["input", 0, name]]],
        [name, [["output", 0, "V"]]], ["output", 0, "V"]]]]]
    source = renderer.render(contract_data, "RenderedContracts").replace("module\n\n", "", 1)
    contract_points = str([ord(char) for char in contract_name])
    source += f'''
open Zkc.Source.Structured in
example : (RenderedContracts.snapshot.relations[0]?.bind fun relation =>
    relation.formula.map fun name => name.toList.map Char.toNat) =
    some {contract_points} := by decide +kernel
open Zkc.Source.Structured in
example : (RenderedContracts.snapshot.contracts[0]?.bind fun contract =>
    contract.clauses[0]?.map fun clause =>
      (clause.kind, clause.name.toList.map Char.toNat,
       clause.subject.selectors.map fun selector =>
         (selector.direction, selector.port, selector.role.toList.map Char.toNat),
       clause.decision)) =
    some (.continuation, {contract_points}, [(.input, 0, {points})],
      some ⟨.output, 0, "V", false⟩) := by rfl
'''
    modules.append(source)
    # Closed source declarations and static-only relation arguments survive the
    # constructor boundary independently of executable ABI types.
    declaration_data = copy.deepcopy(contract_data)
    declaration_data[5][0][6] = [["field", "bls12-381.fr"], ["nat", "7"]]
    declaration_data[10] = [[[["nominal", "record", "sample::Pending", [["field", "bls12-381.fr"]]],
                             "linear", True, [[contract_name, ["field", "bls12-381.fr"]]]]],
                            [["main", [[contract_name, ["bool"], ["V"], 1, 1]], []]]]
    source = renderer.render(declaration_data, "RenderedDeclarations").replace("module\n\n", "", 1)
    source += f'''
open Zkc.Source.Structured in
example : (RenderedDeclarations.snapshot.relations[0]?.map (·.staticArguments)) =
    some [.field "bls12-381.fr", .natural "7"] := by rfl
open Zkc.Source.Structured in
example : (RenderedDeclarations.snapshot.sourceDeclarations.records.map fun record =>
    (record.type, record.resource, record.sealed, record.fields.map fun (name, type) =>
      (name.toList.map Char.toNat, type))) =
    [(.nominal .record "sample::Pending" [.field "bls12-381.fr"], "linear", true,
      [({contract_points}, .field "bls12-381.fr")])] := by rfl
open Zkc.Source.Structured in
example : (RenderedDeclarations.snapshot.sourceDeclarations.protocols.map fun protocol =>
    (protocol.name, protocol.inputs.map fun port =>
      (port.name.toList.map Char.toNat, port.type, port.roles, port.offset, port.count), protocol.outputs)) =
    [("main", [({contract_points}, .boolean, ["V"], 1, 1)], [])] := by rfl
'''
    modules.append(source)
    anchor_data = copy.deepcopy(contract_data)
    anchor_data[8][0][1][0][2][1] = [["anchor", "input", 0]]
    source = renderer.render(anchor_data, "RenderedAnchor").replace("module\n\n", "", 1)
    source += """
open Zkc.Source.Structured in
example : (RenderedAnchor.snapshot.contracts[0]?.bind fun owner =>
  owner.clauses[0]?.map fun clause => clause.subject.selectors) =
    some [⟨.input, 0, "", true⟩] := by rfl
"""
    modules.append(source)
    malformed_contracts = [
        (renderer.contract_selector, ["anchor", "input", 0, "V"]),
        (renderer.contract_selector, ["anchor", "other", 0]),
        (renderer.contract_selector, ["anchor", "input", True]),
        (renderer.contract_selector, ["unknown", 0, "P"]),
        (renderer.contract_selector, ["input", True, "P"]),
        (renderer.contract_selector, ["input", 0, "P", "extra"]),
        (renderer.relation_application, ["R", ["input", 0, "P"]]),
        (renderer.contract_clause, ["assert", "c", ["R", []], None, None]),
        (renderer.contract_clause, ["target", "c", ["R", []], None]),
        (renderer.protocol_contract, ["main", [], "extra"]),
        (renderer.relation, data[5][0][:-1]),
        (renderer.source_declarations, [[]]),
        (renderer.source_record, [["bool"], "linear", 1, []]),
        (renderer.source_record, [["bool"], "shared", True, []]),
        (renderer.source_port, ["p", ["bool"], ["P"], 0, 513]),
        (renderer.source_port, ["p", ["bool"], ["P"] * 17, 0, 1]),
        (renderer.descriptor, ["statement", "R", [], 0]),
        (renderer.descriptor, ["statement", "R", [], 0, True]),
        (renderer.descriptor, ["statement", "R", [], 0, None, "extra"]),
    ]
    for render, invalid in malformed_contracts:
        try:
            render(invalid)
        except ValueError:
            continue
        raise AssertionError("renderer accepted malformed contract metadata")
    # Parse the full u64 endpoint through Lean's own string/constructor syntax.
    # Admission, rather than the renderer, checks the primitive contract.
    maximum = "18446744073709551615"
    binding_rows = [["binding", "max_index", "index.constant", [], ""],
                    ["binding", "sum", "vector.sum", [field[1]], ""]]
    limit = ["function", "limit", "local", "private", [], [["index"]], [], [], ["limit", []],
             ["block", [[["exec", "exec.apply", "max_index", [maximum]],
                         [], [["index"]], [], "maximum"]], ["return", [0]]]]
    entry = ["function", "main", "protocol", "public", [], [["bool"]],
             ["protocol", ["P"], [], [["P"]]], [], ["main", []],
             ["block", [
                 [["index.constant", maximum], [], [["index"]], [], ""],
                 [["local_call", "limit", "P"], [], [["index"]], [], "limit_call"],
                 [["index.equal"], [0, 1], [["bool"]], [], ""],
             ], ["return", [0]]]]
    primitive_data = ["zkc.structured-source/0", "original", "sha256:" + "0" * 64,
                      "main", [], [], binding_rows, [limit, entry], [["main", []]], BLS_ROWS, [[], []]]
    source = renderer.render(primitive_data, "RenderedPrimitives").replace("module\n\n", "", 1)
    source += '''
example : (RenderedPrimitives.snapshot.bindings.map fun binding =>
    (binding.name, binding.contract, binding.arguments, binding.implementation)) =
    [("max_index", "index.constant", [], ""),
     ("sum", "vector.sum", ["bls12-381.fr"], "")] := by decide +kernel
example : (RenderedPrimitives.snapshot.definitions[0]?.bind fun definition =>
    match definition with
    | .function function =>
      let .block instructions _ := function.body
      instructions[0]?.bind fun (.instruction descriptor _ _ _ _) => match descriptor with
        | .exec operation binding parameters => some (operation, binding, parameters)
        | _ => none
    | _ => none) = some ("exec.apply", "max_index", ["18446744073709551615"]) := by
  decide +kernel
example : (Zkc.Source.Structured.check RenderedPrimitives.snapshot).isOk = true := by
  decide +kernel
open Zkc.Source.Structured in
example : (RenderedPrimitives.snapshot.catalogue.nominals.map fun row =>
    (row.identity, row.sort, row.members.length, row.capabilities.length, row.modulus)) =
    [("bls12-381.fr", .field, 3, 5,
      some 52435875175126190479447740508185965837690552500527637822603658699938581184513),
     ("bls12-381.g2", .group, 1, 2, none), ("bls12-381.gt", .group, 1, 2, none),
     ("bls12-381.g1", .group, 1, 2, none)] := by decide +kernel
'''
    modules.append(source)
    malformed_rows = [
        (renderer.nominal, BLS_NOMINALS[0][:-1]),
        (renderer.nominal, ["nominal", "x", "Ring", [], [], None]),
        (renderer.nominal, ["nominal", "x", "Field", [], [], "012"]),
        (renderer.nominal, ["nominal", "x", "Field", [], [], 5]),
        (renderer.nominal, ["nominal", "x", "Field", [["BaseField"]], [], None]),
        (renderer.service_row, ["service", "random.x/0", "x"]),
        (renderer.service_row, ["draw", "random.x/0", "x", ["draw"]]),
        (renderer.catalogue, [[]]),
    ]
    for render, invalid in malformed_rows:
        try:
            render(invalid)
        except ValueError:
            continue
        raise AssertionError("renderer accepted a malformed catalogue row")
    malformed = [primitive_data[:-1], primitive_data + [[]]]  # Exact current envelope.
    for data in malformed:
        try:
            renderer.render(data, "Rejected")
        except ValueError:
            continue
        raise AssertionError("renderer accepted an obsolete envelope")
    # Preserve preparation identity and the interleaved scalar/vector mask.
    # The expected constructors below are independent of the Python renderer.
    vector = ["vector", field[1]]
    inputs = [field, vector, field, vector]
    identity = ["function", "identity", "math", "private", [vector], [vector], [], [], [],
                ["block", [], ["return", [0]]]]
    formula = ["function", "formula", "math", "private", [field] * 4, [field], [], [], [],
               ["block", [], ["return", [0]]]]
    realization = ["realize", "realized", [vector], [vector], "identity"]
    mapping = ["map", "mapped", inputs, [vector], "formula", [False, True, False, True]]
    local = ["function", "work", "local", "private", inputs, [vector], [], [], ["work", []],
             ["block", [
                 [["apply", "mapped"], [0, 1, 2, 3], [vector], [], "map"],
                 [["apply", "realized"], [0], [vector], [], "realize"],
             ], ["return", [0]]]]
    entry = ["function", "main", "protocol", "public", inputs, [vector],
             ["protocol", ["P"], [["P"]] * 4, [["P"]]], [], ["main", []],
             ["block", [[["local_call", "work", "P"], [0, 1, 2, 3], [vector], [], "work"]],
              ["return", [0]]]]
    preparation_data = ["zkc.structured-source/0", "original", "sha256:" + "0" * 64,
                        "main", [], [], [], [identity, formula, realization, mapping, local, entry], [["main", []]],
                        BLS_ROWS, [[], []]]
    source = renderer.render(preparation_data, "RenderedPreparations").replace("module\n\n", "", 1)
    source += '''
example : (RenderedPreparations.snapshot.definitions[2]?.bind fun definition =>
    match definition with
    | .realization declaration => some (declaration.name, declaration.helper)
    | _ => none) = some ("realized", "identity") := by decide +kernel
example : (RenderedPreparations.snapshot.definitions[3]?.bind fun definition =>
    match definition with
    | .map declaration => some (declaration.name, declaration.helper, declaration.rowwise)
    | _ => none) = some ("mapped", "formula", [false, true, false, true]) := by decide +kernel
example : (Zkc.Source.Structured.check RenderedPreparations.snapshot).isOk = true := by
  decide +kernel
'''
    modules.append(source)
    malformed_preparations = []
    for mask in [[0, 1, 0, 1], [False, "true", False, True], None]:
        invalid = copy.deepcopy(mapping)
        invalid[5] = mask
        malformed_preparations.append(invalid)
    malformed_preparations.extend([mapping + ["extra"], mapping[:-1],
                                   realization + ["extra"], realization[:-1]])
    for invalid in malformed_preparations:
        try:
            renderer.definition(invalid)
        except ValueError:
            continue
        raise AssertionError("renderer accepted a malformed preparation record")
    child = ["function", "child", "protocol", "public", [["bool"]], [["bool"]],
             ["protocol", ["A", "B"], [["A", "B"]], [["A", "B"]]], [], ["child", []],
             ["block", [], ["return", [0]]]]
    entry = ["function", "main", "protocol", "public", [["bool"]], [["bool"]],
             ["protocol", ["P", "V"], [["P", "V"]], [["P", "V"]]], [], ["main", []],
             ["block", [[["protocol_apply", "child", ["V", "P"]], [0],
                         [["bool"]], [], "nested"]], ["return", [0]]]]
    application = ["zkc.structured-source/0", "original", "sha256:" + "0" * 64,
                   "main", [], [], [], [entry, child], [["main", []], ["child", []]], NO_ROWS, [[], []]]
    source = renderer.render(application, "RenderedApplication").replace("module\n\n", "", 1)
    source += '''
open Zkc.Source.Structured in
example : (RenderedApplication.snapshot.definitions[0]?.map fun definition =>
    match definition with
    | .function function =>
      let .block instructions _ := function.body
      instructions.map fun (.instruction descriptor _ _ _ _) => match descriptor with
        | .protocolApply callee roles => some (callee, roles)
        | _ => none
    | _ => []) = some [some ("child", ["V", "P"])] := by decide +kernel
example : (Zkc.Source.Structured.check RenderedApplication.snapshot).isOk = true := by
  decide +kernel
'''
    modules.append(source)
    malformed_applications = [["protocol_apply"], ["protocol_apply", "child"],
                              ["protocol_apply", "child", ["P"], "extra"],
                              ["protocol_apply", "child", "P"],
                              ["protocol_apply", "child", [0]],
                              ["protocol_apply", 7, ["P"]]]
    for invalid in malformed_applications:
        try:
            renderer.descriptor(invalid)
        except ValueError:
            continue
        raise AssertionError("renderer accepted a malformed protocol application")
    # Retain the six complete original payloads. These kernel checks inspect
    # constructor data only; full admission belongs to the formal clients.
    repeat_subjects = [
        ("repeat", "Repeat", 2, 4, 2),
        ("repeat-nested", "RepeatNested", 1, 3, 1),
        ("repeat-service", "RepeatService", 2, 3, 2),
        ("repeat-service-wrapper", "RepeatServiceWrapper", 2, 3, 2),
        ("sumcheck-reduce", "SumcheckReduce", 6, 4, 2),
        ("sumcheck-source", "SumcheckSource", 6, 2, 2),
    ]
    modules.append('''
open Zkc.Source.Structured in
private def renderedRepeatHeaders (snapshot : Snapshot) :=
  snapshot.definitions.flatMap fun definition => match definition with
    | .function function =>
      let .block instructions _ := function.body
      instructions.filterMap fun (.instruction descriptor _ _ _ _) => match descriptor with
        | .protocolRepeat carried maximum roles scopes => some (carried, maximum, roles, scopes)
        | _ => none
    | _ => []
''')
    for stem, name, carried, maximum, role_count in repeat_subjects:
        data = json.loads((HERE / f"bridges/structured/fixtures/{stem}.json").read_text())
        namespace = f"ZkcExamples.Structured.{name}Data"
        rendered = renderer.render(data, namespace)
        maintained = HERE / f"ZkcExamples/Structured/{name}Data.lean"
        if not (rendered.encode("utf-8") == maintained.read_bytes()):
            raise AssertionError(maintained)
        roster = [f"role{i:08x}" for i in range(role_count)]
        scopes = [[roster[0]]] * (carried - 2) + [[roster[1]], [roster[1]]] if carried == 6 else [[r] for r in roster]
        source = rendered.replace("module\n\n", "", 1)
        expected = f"[({carried}, {maximum}, {json.dumps(roster)}, {json.dumps(scopes)})]"
        source += f'''
example : renderedRepeatHeaders {namespace}.snapshot = {expected} := by decide +kernel
'''
        modules.append(source)
    malformed_repeats = [
        ["protocol_repeat", 1, True, ["P"], [["P"]]],
        ["protocol_repeat", 1, -1, ["P"], [["P"]]],
        ["protocol_repeat", 1, 1048577, ["P"], [["P"]]],
        ["protocol_repeat", True, 0, ["P"], [["P"]]],
        ["protocol_repeat", -1, 0, ["P"], [["P"]]],
        ["protocol_repeat", 513, 0, ["P"], [["P"]]],
        ["protocol_repeat", 1, 0, ["P"]],
        ["protocol_repeat", 1, 0, ["P"], [["P"]], "extra"],
        ["protocol_repeat", 1, 0, [0], [["P"]]],
        ["protocol_repeat", 1, 0, ["P"], ["P"]],
    ]
    for invalid in malformed_repeats:
        try:
            renderer.descriptor(invalid)
        except ValueError:
            continue
        raise AssertionError("renderer accepted a malformed protocol repeat")
    # Imports/section commands from each rendering are legal at the file top
    # only. One import serves all independently named data declarations.
    header = "module\n\npublic import Zkc.Source.Structured.Import\n\n@[expose] public section\nset_option maxRecDepth 4096\n"
    bodies = [source.replace("public import Zkc.Source.Structured.Import\n", "")
              .replace("@[expose] public section\n", "") for source in modules]
    path = output / "Rendered.lean"
    path.write_text(header + "\n".join(bodies), encoding="utf-8")
    run = subprocess.run([lake, "lean", path], cwd=HERE,
                         capture_output=True, encoding="utf-8", timeout=60)
    (output / "lean.log").write_text(run.stdout + run.stderr, encoding="utf-8")
    if run.returncode:
        raise AssertionError(run.stdout + run.stderr)
    for invalid in ["α" * 257, "🙂" * 129, "\ud800"]:
        try:
            renderer.text(invalid)
        except ValueError:
            continue
        raise AssertionError("renderer accepted an invalid or oversized UTF-8 string")
    report = {"status": "pass", "kernel_cases": len(names), "refusal_cases": 3,
              "missing_origin_refusal_cases": 2,
              "open_metadata_kernel_cases": 3,
              "aggregate_kernel_cases": 2, "aggregate_refusal_cases": len(malformed_aggregates),
              "contract_metadata_kernel_cases": 2,
              "relation_static_arguments_kernel_cases": 1,
              "source_declaration_kernel_cases": 2,
              "contract_metadata_refusal_cases": len(malformed_contracts),
              "primitive_metadata_kernel_cases": 4, "obsolete_envelope_refusal_cases": 2,
              "catalogue_refusal_cases": len(malformed_rows),
              "preparation_metadata_kernel_cases": 3, "preparation_refusal_cases": 7,
              "application_metadata_kernel_cases": 2, "application_refusal_cases": 6,
              "repeat_data_kernel_cases": len(repeat_subjects),
              "repeat_descriptor_refusal_cases": len(malformed_repeats),
              "ascii_locale_cli_cases": 1,
              "renderer_sha256": support.lake.sha(Path(renderer.__file__)),
              "subject_sha256": support.lake.sha(path)}
    (output / "result.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=support.evidence.records("structured-renderer"))
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    print(json.dumps(check(args.output.resolve(), support.lake.resolve(args.lake)), indent=2))
