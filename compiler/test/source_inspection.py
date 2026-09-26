"""Checked source inspection, generic diagnostics and MLIR provenance."""

import json
from pathlib import Path
import re
from commands import Commands
from tools import corpus, records


root = Path(__file__).resolve().parents[2]


commands = Commands(records())


def run(mode, text, *options, refuses=None):
    """The whole result, for a caller that reads more than one stream."""
    commands.source(mode, text, *options, refuses=refuses)
    return commands.last


def operation_locations(ir, *needles):
    """Read the actual operation's location, not an unrelated printed alias."""
    aliases = {
        alias: (int(line), int(column))
        for alias, line, column in re.findall(
            r'^(#loc\d*) = loc\("-":(\d+):(\d+)\)$', ir, re.MULTILINE
        )
    }
    result = []
    for line in ir.splitlines():
        if all(needle in line for needle in needles):
            match = re.search(r' loc\((#loc\d*)\)$', line)
            assert match, line
            result.append(aliases[match[1]])
    assert result, needles
    return result


source = """module {
  fn Identity<F: domain Field>(x: F::Element) -> (F::Element) {
    return (x);
  }
  configure Open = Identity();
  configure First = Open(F = "bls12-381.fr");
  configure Second = Identity(F = "bls12-381.fr");
  protocol Example {
    roles (Alice);
    inputs (Alice x: "bls12-381.fr"::Element);
    outputs (Alice "bls12-381.fr"::Element);
    local [first] Alice: let a = First(x);
    local [second] Alice: let b = Second(a);
    return (b);
  }
  instance concrete: Example { roles (Alice = Alice); }
  entry main = concrete;
}
"""

report = json.loads(run("protocol-inspect", source).stdout)
assert report["format"] == "zkc.source-inspection/1"
configs = {c["name"]: c for c in report["configurations"]}
assert configs["Open"]["remaining"] == [["F", "Field"]]
assert not configs["Open"]["demanded"]
assert configs["First"]["arguments"] == [["F", "bls12-381.fr"]]
assert configs["First"]["demanded"] and configs["Second"]["demanded"]
specializations = dict(report["specializations"])
assert specializations["First"] == specializations["Second"]
assert len(report["source"][2]) == 1
assert len(report["source"][3][0][7]) == 3  # Two occurrences, one shared body.
assert report["definitions"][0]["declared"] == []
assert report["definitions"][0]["inferred"] == []
assert [(o["owner"], o["site"]) for o in report["occurrences"]] == [
    ("Example", "first"), ("Example", "second")
]
assert report["occurrences"][0]["path"] == [3, 3, 0, 7, 0]
assert report["occurrences"][0]["location"]["line"] == 12
portable = run("protocol-source", source).stdout
transport = json.loads(run("protocol-inspect", portable).stdout)
assert transport["snapshot"] == report["snapshot"]
assert all(o["location"]["line"] >= 1 for o in transport["occurrences"])
# The directory name carries a space on purpose: a tool that split
# its arguments would fail here and nowhere else.
directory = records() / 'source selection'
directory.mkdir()
selection = Path(directory) / "selection.json"
selection.write_text(json.dumps(report["selection_template"]))
option = f"--implementations={selection}"
assert run("protocol-compile", source, option).stdout == run(
    "protocol-compile", source
).stdout
run("protocol-compile", "// cosmetic comment\n" + source, option)
run("protocol-compile", source.replace("Identity", "Other"), option,
    refuses="binding-stale-selection")
malformed = list(report["selection_template"])
malformed[1] = "G" * 64
selection.write_text(json.dumps(malformed))
run("protocol-compile", source, option, refuses="binding-selection-snapshot")
human = run("protocol-explain", source).stdout
assert "configure Open" in human and "remaining parameters: F = Field" in human
assert "1 local functions" in human

# A stale selector can remain type/contract-compatible while selecting a
# different occurrence. Coverage and implementation admission cannot recover
# the original author's intent. Snapshot checking catches the actual edit.
folds = (corpus / "bound-operations.pir").read_text()
fold_report = json.loads(run("protocol-inspect", folds).stdout)
# The directory name carries a space on purpose: a tool that split
# its arguments would fail here and nowhere else.
directory = records('stale') / 'stale compatible selection'
directory.mkdir()
selection = Path(directory) / "choice.json"
chosen = [["fold_left", "arkworks-msb/poly.fold"]]
template = fold_report["selection_template"]
template[2] = chosen
selection.write_text(json.dumps(template))
option = f"--implementations={selection}"
run("protocol-compile", folds, option)
located_folds = run("protocol-physical-ir", folds, option, "--locations").stdout
assert operation_locations(located_folds, '"pir.operation_binding"',
                           'sym_name = "fold_left"') == [(2, 3)]
assert operation_locations(located_folds, '"plan.kernel"',
                           'binding = @fold_left') == [(7, 5)]
assert set(operation_locations(located_folds, '"plan.kernel"',
                               'kernel = "arkworks/table.relayout"')) == {(7, 5), (8, 5)}
assert operation_locations(located_folds, '"pir.local_call"',
                           'site = "left"') == [(36, 5)]
swapped = folds.replace("= fold_left(", "= TEMP(").replace(
    "= fold_right(", "= fold_left("
).replace("= TEMP(", "= fold_right(")
assert swapped != folds
run("protocol-compile", swapped, option, refuses="binding-stale-selection")
selection.write_text(json.dumps(chosen))
# A bare selection list has no source snapshot to establish freshness.
run("protocol-compile", swapped, option)
selection.write_text(json.dumps([["fold_left", "arkworks/field.add"]]))
error = run("protocol-compile", folds, option, refuses="binding-implementation")
assert "-\":2:3" in error.stderr or "-:2:3" in error.stderr, error.stderr

binding_error = """module {
  bind bad = unknown.operation();
  fn Identity<>() -> () { return (); }
  configure Closed = Identity();
  protocol Example { roles (Alice); local Alice: Closed(); return (); }
  instance concrete: Example { roles (Alice = Alice); }
  entry main = concrete;
}
"""
error = run("protocol-source", binding_error, refuses="binding-contract")
assert "-:2:3:" in error.stderr, error.stderr

# Recursion must retain an inner failure, but a successful body must not steal
# the location of a subsequent outer-result failure.
loop_error = """module {
  protocol Example {
    roles (Alice);
    inputs (Alice x: bool);
    outputs (Alice bool);
    loop [outer] 1 carry (a = x) -> (x) {
      yield (a);
    }
    return (x);
  }
}
"""
error = run("protocol-source", loop_error, refuses="source-value-duplicate")
assert "-:6:5:" in error.stderr, error.stderr
error = run("protocol-source", loop_error.replace("yield (a)", "yield (missing)"),
            refuses="source-name-unresolved")
assert "-:7:7:" in error.stderr, error.stderr

# Formatting and syntax inspection do not authorize unresolved calls.
broken = source.replace("First(x)", "Missing(x)")
run("protocol-format", broken)
raw = json.loads(run("protocol-parse", broken).stdout)
assert raw["kind"] == "syntax-inspection" and raw["format"] == "pir-text"
assert raw["content"]["protocols"][0]["body"][0]["callee"] == "Missing"
error = run("protocol-import", broken, refuses="source-name-unresolved")
assert "-:12:" in error.stderr, error.stderr
sort_error = source.replace('Open(F = "bls12-381.fr")',
                            'Open(F = "bls12-381.g1")')
error = run("protocol-inspect", sort_error, refuses="generic-configuration-binding")
assert "-:6:" in error.stderr, error.stderr
value_error = source.replace("return (x);", "return (unknown);")
error = run("protocol-inspect", value_error, refuses="source-name-unresolved")
assert "-:3:" in error.stderr, error.stderr
mixed_error = source.replace("module {", """module {
  fn Bad(x: "bls12-381.fr"::Element) -> (bool) {
    return (x);
  }
""", 1)
error = run("protocol-import", mixed_error, refuses="source-type-mismatch")
assert "-:3:" in error.stderr, error.stderr

# Locations are opt-in display metadata. They survive common -> participant ->
# physical lowering, while exporting the IR yields the same portable program.
plain = run("protocol-import", source).stdout
located = run("protocol-import", source, "--locations").stdout
assert 'loc("-":3:5)' in located and 'loc("-":12:5)' in located
assert "#loc" not in plain
assert run("protocol-export", plain).stdout == run("protocol-export", located).stdout
physical = run("protocol-physical-ir", source, "--locations").stdout
assert 'loc("-":12:5)' in physical and 'loc("-":13:5)' in physical
assert run("protocol-export", physical).stdout == run("protocol-compile", source).stdout

for stem in ("generic-dleq", "generic-committed-two-factor", "generic-openings"):
    text = (corpus / f"{stem}.pir").read_text()
    report = json.loads(run("protocol-inspect", text).stdout)
    assert report["definitions"] and report["specializations"]
    # The reported source is the actual closed source used by the compiler.
    assert run("protocol-compile", json.dumps(report["source"])).stdout == run(
        "protocol-compile", text
    ).stdout
    assert "declared requirements:" in run("protocol-explain", text).stdout
    if stem == "generic-dleq":
        ir = run("protocol-import", text, "--locations").stdout
        assert operation_locations(ir, '"pir.operation_binding"',
                                   'contract = "curve.empty"') == [(8, 5)]

print(f"{commands.save()} source inspection and provenance checks passed")
