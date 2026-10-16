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


def check(output, lake):
    output.mkdir(parents=True, exist_ok=True)
    names = ["plain", 'quote"slash\\literal\\u0041', "line\nreturn\rtab\t",
             "\x00\x08\x0c\x1f\x7f", "증명_α_🙂", "α" * 256,
             '"\nend Rendered\naxiom injected : False\n--']
    modules = []
    for index, name in enumerate(names):
        helper = ["function", name, "math", "private", [["bool"]], [["bool"]], [], [], [],
                  ["block", [], ["return", [0]]]]
        entry = ["function", "main", "protocol", "public", [["bool"]], [["bool"]],
                 ["protocol", ["P"], [["P"]], [["P"]]], [], [],
                 ["block", [[["call", name], [0], [["bool"]], [], ""]], ["return", [0]]]]
        data = ["zkc.structured-source/0", "original", "sha256:" + "0" * 64,
                "main", [], [], [], [helper, entry], [["main", []]]]
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
            assert rendered_path.read_bytes() == renderer.render(data, namespace).encode("utf-8")
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
    ]
    data = ["zkc.structured-source/0", "original", "sha256:" + "0" * 64, "main", [],
            [["relation", name, "public", name, name, name, [group], [["bool"]], ["statement"], None]], [],
            [["function", "main", "protocol", "public", [group, field, service], [["bool"]],
              ["protocol", [name, "V"], [[name, "V"], [name], ["V"]], [["V"]]], [], [],
              ["block", operations, ["return", [1]]]]], [["main", []]]]
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
        | .draw _ _ => 6 | .statement _ _ _ _ => 7 | _ => 99
    | _ => []) = some [0, 1, 2, 3, 4, 5, 6, 7] := by decide +kernel
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
      some ⟨.output, 0, "V"⟩) := by rfl
'''
    modules.append(source)
    malformed_contracts = [
        (renderer.contract_selector, ["unknown", 0, "P"]),
        (renderer.contract_selector, ["input", True, "P"]),
        (renderer.contract_selector, ["input", 0, "P", "extra"]),
        (renderer.relation_application, ["R", ["input", 0, "P"]]),
        (renderer.contract_clause, ["assert", "c", ["R", []], None, None]),
        (renderer.contract_clause, ["target", "c", ["R", []], None]),
        (renderer.protocol_contract, ["main", [], "extra"]),
        (renderer.relation, data[5][0][:-1]),
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
             ["block", [[["exec", "algebra.exec.index_constant", "max_index", [maximum]],
                         [], [["index"]], [], "maximum"]], ["return", [0]]]]
    entry = ["function", "main", "protocol", "public", [], [["bool"]],
             ["protocol", ["P"], [], [["P"]]], [], [],
             ["block", [
                 [["index.constant", maximum], [], [["index"]], [], ""],
                 [["local_call", "limit", "P"], [], [["index"]], [], "limit_call"],
                 [["index.equal"], [0, 1], [["bool"]], [], ""],
             ], ["return", [0]]]]
    primitive_data = ["zkc.structured-source/0", "original", "sha256:" + "0" * 64,
                      "main", [], [], binding_rows, [limit, entry], [["main", []]]]
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
    | _ => none) = some ("algebra.exec.index_constant", "max_index", ["18446744073709551615"]) := by
  decide +kernel
example : (Zkc.Source.Structured.check RenderedPrimitives.snapshot).isOk = true := by
  decide +kernel
'''
    modules.append(source)
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
             ["protocol", ["P"], [["P"]] * 4, [["P"]]], [], [],
             ["block", [[["local_call", "work", "P"], [0, 1, 2, 3], [vector], [], "work"]],
              ["return", [0]]]]
    preparation_data = ["zkc.structured-source/0", "original", "sha256:" + "0" * 64,
                        "main", [], [], [], [identity, formula, realization, mapping, local, entry], [["main", []]]]
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
             ["protocol", ["A", "B"], [["A", "B"]], [["A", "B"]]], [], [],
             ["block", [], ["return", [0]]]]
    entry = ["function", "main", "protocol", "public", [["bool"]], [["bool"]],
             ["protocol", ["P", "V"], [["P", "V"]], [["P", "V"]]], [], [],
             ["block", [[["protocol_apply", "child", ["V", "P"]], [0],
                         [["bool"]], [], "nested"]], ["return", [0]]]]
    application = ["zkc.structured-source/0", "original", "sha256:" + "0" * 64,
                   "main", [], [], [], [entry, child], [["main", []], ["child", []]]]
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
        assert rendered.encode("utf-8") == maintained.read_bytes(), maintained
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
    header = "import Zkc.Source.Structured.Import\nset_option maxRecDepth 4096\n"
    bodies = [source.replace("public import Zkc.Source.Structured.Import\n", "")
              .replace("@[expose] public section\n", "") for source in modules]
    path = output / "Rendered.lean"
    path.write_text(header + "\n".join(bodies), encoding="utf-8")
    run = subprocess.run([lake, "env", "lean", path], cwd=HERE,
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
              "open_metadata_kernel_cases": 3,
              "contract_metadata_kernel_cases": 2,
              "contract_metadata_refusal_cases": len(malformed_contracts),
              "primitive_metadata_kernel_cases": 3, "obsolete_envelope_refusal_cases": 2,
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
